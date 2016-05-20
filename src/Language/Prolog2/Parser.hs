{-# LANGUAGE
    ViewPatterns
  , ScopedTypeVariables
  #-}

module Language.Prolog2.Parser
   ( Parser , consult, consultString , parseQuery
   , program, whitespace, comment, clause, terms, term, bottom, vname
   ) where

import Import.NoFoundation hiding (many, (<|>) , cons, try)
import qualified Prelude

import Text.Parsec
import qualified Text.Parsec.PrologExpr as P.Prolog

import qualified Text.Parsec.Error as P
import qualified Text.Parsec.Pos as P

import Control.Monad.State
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Char

import System.Directory

import Language.Prolog2.Syntax hiding (atom)
import qualified Language.Prolog2.Syntax as Prolog
import Language.Prolog2.Types
import Language.Prolog2.InterpreterCommon
import qualified Language.Prolog2.Database as DB
import qualified Language.Prolog2.Token as Token

import CCGraph
import DBFS

import Control.Monad.Trans.Either

type Parser m a   = ParsecT Text (ParserState m) m a

------------------------  Top level parsers --------------------------
consult :: FilePath -> PrologT IO (Either ParseError DB.Database)
consult source = do exists <- liftIO $ doesFileExist source
                    if exists
                      then do  s <- liftIO $ T.readFile source
                               runParserT p emptyState source s
                      else return $ Left $ fileDoesNotExist source
  where p = (whiteSpace >> program <* eof)
        fileDoesNotExist file = P.newErrorMessage (P.Message "File does not exist") (P.newPos file 0 0)

consultText :: (Monad m) => Text -> PrologT m (Either ParseError DB.Database)
consultText s = runParserT p emptyState "(input)" s
  where p = (whiteSpace >> program <* eof)

consultDBFS :: MonadIO m
               => UserAccountId -> ModuleName
               -> PrologT (SqlPersistT m) (Either ParseError DB.Database)
consultDBFS uid mod = do
  ecode <- runEitherT $ do
    Entity dir dirContent  <- EitherT $ lift $ uid `opendir` mod
    return (directoryCode dirContent)

  case ecode of
    Right code ->  runParserT p emptyState (T.unpack mod) code
    Left  err  ->  return $ Left $ fileNotReadable (T.unpack mod)

  where
    p = (whiteSpace >> program <* eof)
    fileNotReadable file = P.newErrorMessage (P.Message "File not readable") (P.newPos file 0 0)

parseQuery :: Monad m => Text -> PrologT m (Either ParseError [Term])
parseQuery s = runParserT p  emptyState "(query)" s
  where p = (whiteSpace >> terms <* eof)

isOperator :: Text -> Bool
isOperator s = runParserT (operator <* eof) emptyState "" s == Right (Right ())

isIdentifier :: Text -> Bool
isIdentifier s = runParserT (identifier <* eof) emptyState "" s == Right (Right ())

------------------------  Individual parsers  ------------------------
program :: Monad m => Parser m DB.Database
program = do many ( (directive <|> (clause >>= insertClause) ) <* dot)
             st <- getState
             return $ database st


directive :: Monad m => Parser m ()
directive = do lexeme $ reservedOp ":-"
               moduleDirective <|> useModuleDirective <|> opDirective

moduleDirective :: Monad m => Parser m ()
moduleDirective = do reserved "module"
                     name <- parens atom
                     comma
                     sigs <- publicList
                     defineModule name sigs

publicList :: Monad m => Parser m [DB.Signature]
publicList = many $ do name  <- lexeme atom
                       lexeme $ reservedOp "/"
                       arity <- lexeme $ decimal
                       return $ DB.Signature name (fromInteger arity)


useModuleDirective :: Monad m => Parser m ()
useModuleDirective = do reserved "use_module"
                        file <- parens (lexeme atom)
                        useModule file

opDirective :: Monad m => Parser  m ()
opDirective = do parens $ do priority   <- decimal
                             comma
                             assoc      <- associativity
                             comma
                             name       <- atom
                             defineOperator (fromInteger priority) assoc name

associativity :: Monad m => Parser m Assoc
associativity = (reserved "xfx" >> return XFX )
                <|> (reserved "xfy" >> return XFY )
                <|> (reserved "yfx" >> return YFX )
                <|> (reserved "fx"  >> return FX )
                <|> (reserved "fy"  >> return FY )
                <|> (reserved "xf"  >> return XF )
                <|> (reserved "yf"  >> return YF )

clause :: Monad m => Parser m Clause
clause = do resetState
            t <- struct
            dcg t <|> normal t
   where
     normal :: (Functor m, Applicative m, Monad m) => Term -> Parser m Clause
     normal t = do
       ts <- option [] $ do reservedOp ":-"
                            terms
       return (UClause t ts)

     dcg :: (Functor m, Applicative m, Monad m) => Term -> Parser  m Clause
     dcg t = do
            _ <- reservedOp "-->"
            ts <- terms
            translate (t,ts)

     translate :: (Monad m) => (Term, [Term]) -> Parser m Clause
     translate ((UTerm (TStruct a ts)), rhs'') = do
       vars <- lift $ getFreeVars (length rhs'' + 1)
       let lhs' = UTerm (TStruct a (arguments ts (Prelude.head vars) (Prelude.last vars)))
           rhs' = zipWith3 translate' rhs'' vars (Prelude.tail vars)
       return $ UClause lhs' rhs'
     translate _ = error "Internal Parser Error"

     translate' t s s0 | isList t   = let l = foldr_pl cons s0 t
                                      in  case l of
                                      Just l' ->  UTerm (TStruct (T.pack "=") [ s, l' ])     -- Terminal
                                      Nothing ->  error "This is impossible"
     translate' (UTerm (TStruct a ts)) s s0 | a == (T.pack "{}")  =
                                                foldr and_ (UTerm (TStruct (T.pack "=") [ s, s0 ])) ts
                                                -- Braced terms
     translate' (UTerm (TStruct a ts))  s s0 = UTerm (TStruct a (arguments ts s s0))    -- Non-Terminal
     translate' _ _ _ = error "Internal parser error"

     and_ x y = UTerm (TStruct (T.pack ",") [x,y])


isList :: Term -> Bool
isList (UTerm (TStruct n [_,_])) | n == (T.pack ".")  = True
isList (UTerm (TStruct n []))    | n == (T.pack "[]") = True
isList _                  = False

terms :: (Functor m, Applicative m, Monad m) => Parser m [Term]
terms = sepBy1 termWithoutConjunction (charWs ',')

term :: (Functor m, Applicative m, Monad m) => Parser  m Term
term = term' False
termWithoutConjunction :: (Functor m, Applicative m, Monad m) => Parser m Term
termWithoutConjunction = term' True


term' :: (Monad m) => Bool -> Parser  m Term
term' ignoreConjunction = expressionParser <$> getState <*> pure ignoreConjunction

bottom :: (Functor m, Applicative m, Monad m) => Parser m Term
bottom = lexeme $
         variable
         <|> struct
         <|> list
         <|> stringLiteral
         <|> cut <$ char '!'
         <|> ((UTerm . TStruct (T.pack "{}"))  <$> between (charWs '{') (char '}') terms)
         <|> between (charWs '(') (char ')') term

toParser :: (Monad m)
            => Prolog.Operator -> P.Prolog.Operator Text (ParserState m) (PrologT m) Term
toParser (PrefixOp assoc name)  = P.Prolog.Prefix ( do reservedOp (T.unpack name)
                                                       return (\t -> UTerm (TStruct name [t])) ) assoc

toParser (PostfixOp assoc name) = P.Prolog.Postfix ( do reservedOp (T.unpack name)
                                                        return (\t -> UTerm (TStruct name [t])) ) assoc

toParser (InfixOp assoc name)   = P.Prolog.Infix ( do reservedOp (T.unpack name)
                                                      return (\t1 t2 -> UTerm (TStruct name [t1, t2]))) assoc



struct :: Monad m => Parser  m Term
struct = do a  <- atom
            ts <- option [] $ between (charWs '(') (char ')') terms
            return (UTerm (TStruct (T.pack a) ts))

list :: Monad m => Parser m Term
list = between (charWs '[') (char ']') $
         flip (foldr cons) <$> option []  terms
                           <*> option nil (charWs '|' >> term)


-- Prolog token definitions
operatorNames :: [Text]
operatorNames = [ ";", ",", "<", "=..", "=:=", "=<", "=", ">=", ">", "\\="
                , "is", "/" , "*", "+", "-", "\\", "mod", "\\+" ]

type PrologLanguageDef m = Token.GenLanguageDef Text (ParserState m)  m

genPrologDef   :: (Monad m) => PrologLanguageDef  m
genPrologDef  = Token.LanguageDef
               { Token.commentStart   = "/*"
               , Token.commentEnd     = "*/"
               , Token.commentLine    = "%"
               , Token.nestedComments = False
               , Token.identStart     = alphaNonUpper
               , Token.identLetter    = alphaNum <|> char "_"
               , Token.opStart        = oneOf "#$&*+-./:<=>?@^~\\"
               , Token.opLetter       = oneOf "#$&*+-./:<=>?@^~\\"
               , Token.reservedOpNames= operatorNames
               , Token.reservedNames  = ["module", "use_module", "op"]
               , Token.caseSensitive  = True
               }

lexer = Token.makeTokenParser $ genPrologDef
lexeme = Token.lexeme lexer

whiteSpace = Token.whiteSpace lexer

identifier :: Monad m => Parser  m ()
identifier = Token.identifier lexer

reserved = Token.reserved lexer

operator :: Monad m => Parser  m ()
operator = Token.operator lexer

reservedOp :: (Monad m) => String -> Parser m ()
reservedOp = Token.reservedOp lexer

decimal = Token.decimal lexer
natural = Token.natural lexer

dot    = Token.dot lexer
comma  = Token.comma lexer
parens = Token.parens lexer


skip :: (Monad m) => Parser m a -> Parser m ()
skip = (>> return ())


charWs :: (Monad m) => Char -> Parser m Char
charWs c = lexeme (char c)


variable :: (Monad m) => Parser  m Term
variable = lexeme (do _ <- try (char '_' <* notFollowedBy (alphaNum <|> char '_'))
                      wildcard)
           <|> var =<< vname
           <?> "variable"

wildcard :: (Monad m) => Parser m Term
wildcard  = do v <- lift $ getFreeVar
               insertWildcard "_" v
               return v

var :: (Monad m) => String -> Parser m Term
var v = do mx <- lookupVarMap v
           case mx of
             Just x  -> return x
             Nothing -> do x <- lift $ getFreeVar
                           insertVarMap v x
                           return x

vname :: (Monad m) => Parser  m String
vname = lexeme (((:) <$> upper    <*> many  (alphaNum <|> char '_') <|>
                 (:) <$> char '_' <*> many1 (alphaNum <|> char '_')))

atom :: (Monad m) => Parser m Atom
atom = identifier
   <|> operator
   <|> (natural >>= return . show)
   <|> (between (char '\'') (char '\'') (many (noneOf "'")))
   <?> "atom"



alphaNonUpper :: (Monad m) => Parser m Char
alphaNonUpper = satisfy (\c -> isAlpha c && not (isUpper c))


stringLiteral :: (Monad m) => Parser m Term
stringLiteral = foldr cons nil . map representChar <$> between (char '"') (char '"') (try (many (noneOf "\"")))

representChar :: Char -> Term
representChar c = UTerm (TStruct (T.pack (show (fromEnum c))) []) -- This is the classical Prolog representation of chars as code points.
--representChar c = Struct [c] [] -- This is the more natural representation as one-character atoms.
--representChar c = Struct "char" [Struct (show (fromEnum c)) []] -- This is a representation as tagged code points.
--toChar :: Term -> Maybe Char
--toChar (Struct "char" [Struct (toEnum . read->c) []]) = Just c
--toChar _                                              = Nothing


----------------------------  User state  ----------------------------
data ParserState m  = ParserState
                    { moduleFileName    :: Maybe Atom
                    , moduleName  :: Maybe Atom
                    , varMap      :: Map String Term
                    , wildcards   :: [(String, Term)]
                    , operatorTable    :: Bool -> P.Prolog.OperatorTable String (ParserState m) m Term
                    , expressionParser :: Bool -> ParsecT String (ParserState m)  m Term
                    , database :: DB.Database
                    }

emptyState :: Monad m => ParserState m
emptyState = ParserState
             { moduleName = Nothing
             , varMap = Map.empty
             , wildcards = []
             , operatorTable = \ignoreConjunction ->  toExpressionTable $ defaultHierarchy ignoreConjunction
             , expressionParser = \ignoreConjunction ->
             P.Prolog.buildExpressionParser (operatorTable ignoreConjunction) bottom
             , database = DB.empty
             }
toExpressionTable :: [(Int, [Operator])] -> P.Prolog.OperatorTable s u m a
toExpressionTable table = map toPrologOperators table
  where
    toPrologOperators :: (Int, [Operator]) -> (Int, [P.Prolog.Operator s u m a])
    toPrologOperators (prio, ops) = (prio, map toPrologOperator ops)
toPrologOperator :: Operator -> P.Prolog.Operator s u m a
toPrologOperator (InfixOp  assoc text) | isOperator   text = P.Prolog.Infix  (reservedOp text binary) assoc
                                       | isIdentifier text = P.Prolog.Infix  (reserved   text binary) assoc
toPrologOperator (PrefixOp assoc text) | isOperator   text = P.Prolog.Prefix (reservedOp text unary) assoc
                                       | isIdentifier text = P.Prolog.Prefix (reserved   text unary) assoc
toPrologOperator (PostfixOp assoc text) | isOperator   text = P.Prolog.Postfix (reservedOp text unary) assoc
                                        | isIdentifier text = P.Prolog.Postfix (reserved   text unary) assoc


binary :: Atom -> Term -> Term -> Term
binary a t1 t2 = UTerm (TStruct a [t1,t2])

unary :: Atom -> Term -> Term
unary a t1 = UTerm (TStruct a [t1])


resetState :: (Monad m) => Parser m ()
resetState = updateState (\st  -> st { varMap = Map.empty , wildcards = [] } )

lookupVarMap :: (Monad m) => String -> Parser m (Maybe Term)
lookupVarMap v = do
  m <- varMap <$> getState
  return $ Map.lookup v m

insertVarMap :: (Monad m) => String -> Term -> Parser m ()
insertVarMap v x = do
  ParserState vmap wild_ op expr <- getState
  let vmap' = Map.insert v x vmap
  setState $ ParserState vmap' wild_ op expr

insertWildcard :: (Monad m) => String -> Term -> Parser m ()
insertWildcard v x = do
  ParserState vmap wild_ op expr <- getState
  let wildcards' = (v,x) : wild_
  setState $ ParserState vmap wildcards' op expr

setFileName :: Monad m => Atom -> Parser  m ()
setFileName name = do
  st <- getState
  setState st { moduleFileName = Just name }

defineModule :: Monad m => Atom -> [ DB.Signature ] -> Parser m ()
defineModule mod ss = do
  st <- getState
  setState st { moduleName = Just mod
              , database   = DB.setPublicTable ss }

useModule :: Monad m => Atom -> Parser  m ()
useModule mod = do
  db <- runPrologT $ consultDBFS mod
  st <- getState
  setState st { database = DB.merge db (database st) }


data Assoc = XFX
           | XFY
           | YFX
           | XF
           | YF
           | FX
           | FY
           deriving (Eq,Show)

defineOperator :: Int -> Assoc -> Atom -> Parser  m ()
defineOperator prio assoc atom = do
  st <- getState
  let table = insertOp prio assoc atom (operatorTable st)
  setState st { operatorTable = table
              , expressionParser = \ignoreConjunction ->
              P.Prolog.buildExpressionParser (table ignoreConjunction) bottom }

insertOp  :: Int -> Operator
             -> (Bool -> P.Prolog.OperatorTable String (ParserState m) m Term)
             -> (Bool -> P.Prolog.OperatorTable String (ParserState m) m Term)
insertOp prio op table ignoreConjunction = insert (toPrologOperator op) (table ignoreConjunction)
  where
    insert op t = Map.insertWith (++) prio [op] t

insertClause :: Clause -> Parser  m ()
insertClause clause = do
  st <- getState
  let database' = DB.insertClause (moduleName st) clause (database st)
  setState st { database = database' }
