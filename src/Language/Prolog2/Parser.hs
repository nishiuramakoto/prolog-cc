{-# LANGUAGE
    ViewPatterns
  , ScopedTypeVariables
  , TypeFamilies
  #-}

module Language.Prolog2.Parser
   ( Parser , consult, consultText , consultTextDbfs , parseQuery
   , program, whiteSpace, clause, terms, term, bottom, vname
   , ParserState(..)
   ) where

import Import.NoFoundation hiding (many, (<|>) , cons, try , parseQuery)
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

runPrologParser :: Monad m => Parser (PrologT m) a -> ParserState (PrologT m) -> SourceName -> Text
                   -> m (Either RuntimeError (Either ParseError a))
runPrologParser p state source s = evalPrologT (runParserT p state source s)


------------------------  Top level parsers --------------------------
consult :: ( YesodPersist site
           , YesodPersistBackend site ~ SqlBackend)
           => UserAccountId -> ModuleName
           -> PrologT (HandlerT site IO)  (Either ParseError (ParserState (PrologT (HandlerT site IO))))
consult uid mod = do
  ecode <- runEitherT $ do
    Entity dir dirContent  <- EitherT $ lift $ runDB $ uid `opendir` mod
    return (directoryCode dirContent)

  case ecode of
    Right code ->  runParserT p emptyState { moduleFileName = Just mod } (T.unpack mod) code
    Left  err  ->  return $ Left $ fileNotReadable (T.unpack mod)

  where
    p = (whiteSpace >> program <* eof)
    fileNotReadable file = P.newErrorMessage (P.Message "File not readable") (P.newPos file 0 0)

consultTextDbfs :: ( YesodPersist site, YesodPersistBackend site ~ SqlBackend )
                   => UserAccountId -> ModuleName -> Text
                   -> PrologT (HandlerT site IO) (Either ParseError (ParserState (PrologT (HandlerT site IO))))
consultTextDbfs uid mod code = do
  runParserT p emptyState { moduleFileName = Nothing } (T.unpack mod) code

  where
    p = (whiteSpace >> program <* eof)
    fileNotReadable file = P.newErrorMessage (P.Message "File not readable") (P.newPos file 0 0)


consultText :: (Monad m) => Text -> PrologT m (Either ParseError (ParserState (PrologT m)))
consultText s = runParserT p emptyState "(input)" s
  where p = (whiteSpace >> programNoDirectives <* eof)


parseQuery :: Monad m => Text -> PrologT m (Either ParseError [Term])
parseQuery s = runParserT p  emptyState "(query)" s
  where p = (whiteSpace >> terms <* eof)

isOperator :: Text -> Bool
isOperator s = case runIdentity $ runPrologParser (operator <* eof >> return ()) emptyState "" s of
  Right (Right ()) -> True
  _ -> False

isIdentifier :: Text -> Bool
isIdentifier s = case runIdentity $ runPrologParser (identifier <* eof >> return ()) emptyState "" s of
  Right (Right ()) -> True
  _ -> False

------------------------  Individual parsers  ------------------------
program :: ( YesodPersist site, YesodPersistBackend site ~ SqlBackend )
           => Parser (PrologT (HandlerT site IO)) (ParserState (PrologT (HandlerT site IO)))
program = do many (directive)
             many ( (directive <|> (clause >>= insertClause) ) <* dot)
             getState

programNoDirectives :: Monad m => Parser (PrologT m) (ParserState (PrologT m))
programNoDirectives = do many ( (clause >>= insertClause) <* dot)
                         getState


directive :: ( YesodPersist site, YesodPersistBackend site ~ SqlBackend )
             => Parser (PrologT (HandlerT site IO)) ()
directive = do lexeme $ reservedOp ":-"
               moduleDirective <|> useModuleDirective <|> opDirective

moduleDirective :: Monad m => Parser (PrologT m) ()
moduleDirective = do reserved "module"
                     lexeme $ parens $ do
                       name <- atom
                       lexeme comma
                       sigs <- publicList
                       defineModule name sigs
                     return ()

publicList :: Monad m => Parser (PrologT m) [DB.Signature]
publicList = many $ do name  <- lexeme atom
                       lexeme $ reservedOp "/"
                       arity <- lexeme $ decimal
                       return $ DB.Signature name (fromInteger arity)


useModuleDirective :: ( YesodPersist site, YesodPersistBackend site ~ SqlBackend )
                      => Parser (PrologT (HandlerT site IO)) ()
useModuleDirective = do reserved "use_module"
                        file <- parens (lexeme atom)
                        useModule file

opDirective :: Monad m => Parser (PrologT m) ()
opDirective = do parens $ do priority   <- decimal
                             comma
                             assoc      <- associativity
                             comma
                             name       <- atom
                             defineOperator (fromInteger priority) assoc name

associativity :: Monad m => Parser (PrologT m) Assoc
associativity = (reserved "xfx" >> return XFX )
                <|> (reserved "xfy" >> return XFY )
                <|> (reserved "yfx" >> return YFX )
                <|> (reserved "fx"  >> return FX )
                <|> (reserved "fy"  >> return FY )
                <|> (reserved "xf"  >> return XF )
                <|> (reserved "yf"  >> return YF )

clause :: Monad m => Parser (PrologT m) Clause
clause = do resetState
            t <- struct
            dcg t <|> normal t
   where
     normal :: (Functor m, Applicative m, Monad m) => Term -> Parser (PrologT m) Clause
     normal t = do
       ts <- option [] $ do reservedOp ":-"
                            terms
       return (UClause t ts)

     dcg :: (Functor m, Applicative m, Monad m) => Term -> Parser (PrologT m) Clause
     dcg t = do
            _ <- reservedOp "-->"
            ts <- terms
            translate (t,ts)

     translate :: (Monad m) => (Term, [Term]) -> Parser (PrologT m) Clause
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

terms :: (Functor m, Applicative m, Monad m) => Parser (PrologT m) [Term]
terms = sepBy1 termWithoutConjunction (charWs ',')

term :: (Functor m, Applicative m, Monad m) => Parser  (PrologT m) Term
term = term' False
termWithoutConjunction :: (Functor m, Applicative m, Monad m) => Parser (PrologT m) Term
termWithoutConjunction = term' True


term' :: (Monad m) => Bool -> Parser  (PrologT m) Term
term' ignoreConjunction = do
  st <- getState
  expressionParser st ignoreConjunction

bottom :: (Functor m, Applicative m, Monad m) => Parser (PrologT m) Term
bottom = lexeme $
         variable
         <|> struct
         <|> list
         <|> stringLiteral
         <|> cut <$ char '!'
         <|> ((UTerm . TStruct (T.pack "{}"))  <$> between (charWs '{') (char '}') terms)
         <|> between (charWs '(') (char ')') term

toParser :: (Monad m)
            => Prolog.Operator -> P.Prolog.Operator Text (ParserState (PrologT m)) (PrologT m) Term
toParser (PrefixOp assoc name)  = P.Prolog.Prefix ( do reservedOp  name
                                                       return (\t -> UTerm (TStruct name [t])) ) assoc

toParser (PostfixOp assoc name) = P.Prolog.Postfix ( do reservedOp name
                                                        return (\t -> UTerm (TStruct name [t])) ) assoc

toParser (InfixOp assoc name)   = P.Prolog.Infix ( do reservedOp name
                                                      return (\t1 t2 -> UTerm (TStruct name [t1, t2]))) assoc



struct :: Monad m => Parser  (PrologT m) Term
struct = do a  <- atom
            ts <- option [] $ between (charWs '(') (char ')') terms
            return (UTerm (TStruct a ts))

list :: Monad m => Parser (PrologT m) Term
list = between (charWs '[') (char ']') $
         flip (foldr cons) <$> option []  terms
                           <*> option nil (charWs '|' >> term)


-- Prolog token definitions
operatorNames :: [String]
operatorNames = [ ";", ",", "<", "=..", "=:=", "=<", "=", ">=", ">", "\\="
                , "is", "/" , "*", "+", "-", "\\", "mod", "\\+" ]

type PrologLanguageDef m = Token.GenLanguageDef Text (ParserState m)  m

genPrologDef   :: (Monad m) => PrologLanguageDef  (PrologT m)
genPrologDef  = Token.LanguageDef
               { Token.commentStart    = "/*"
               , Token.commentEnd      = "*/"
               , Token.commentLine     = "%"
               , Token.nestedComments  = False
               , Token.identStart      = alphaNonUpper
               , Token.identLetter     = alphaNum <|> char '_'
               , Token.opStart         = oneOf "#$&*+-./:<=>?@^~\\"
               , Token.opLetter        = oneOf "#$&*+-./:<=>?@^~\\"
               , Token.reservedOpNames = operatorNames
               , Token.reservedNames   = ["module", "use_module", "op"]
               , Token.caseSensitive   = True
               }

lexer = Token.makeTokenParser $ genPrologDef
lexeme = Token.lexeme lexer

whiteSpace = Token.whiteSpace lexer

identifier :: Monad m => Parser  (PrologT m) Text
identifier = Token.identifier lexer >>= return . T.pack

reserved :: Monad m => Text -> Parser (PrologT m) ()
reserved = Token.reserved lexer . T.unpack

operator :: Monad m => Parser  (PrologT m) Text
operator = Token.operator lexer >>= return . T.pack

reservedOp :: (Monad m) => Text -> Parser (PrologT m) ()
reservedOp = Token.reservedOp lexer . T.unpack

decimal = Token.decimal lexer
natural = Token.natural lexer

charLiteral = Token.charLiteral lexer
stringLiteralToken = Token.stringLiteral lexer

dot    = Token.dot lexer
comma  = Token.comma lexer
parens = Token.parens lexer


skip :: (Monad m) => Parser m a -> Parser m ()
skip = (>> return ())


charWs :: (Monad m) => Char -> Parser (PrologT m) Char
charWs c = lexeme (char c)


variable :: (Monad m) => Parser  (PrologT m) Term
variable = lexeme (do _ <- try (char '_' <* notFollowedBy (alphaNum <|> char '_'))
                      wildcard)
           <|> var =<< vname
           <?> "variable"

wildcard :: (Monad m) => Parser (PrologT m) Term
wildcard  = do v <- lift $ getFreeVar
               insertWildcard "_" v
               return v

var :: (Monad m) => String -> Parser (PrologT m) Term
var v = do mx <- lookupVarMap v
           case mx of
             Just x  -> return x
             Nothing -> do x <- lift $ getFreeVar
                           insertVarMap v x
                           return x

vname :: (Monad m) => Parser  (PrologT m) String
vname = lexeme (((:) <$> upper    <*> many  (alphaNum <|> char '_') <|>
                 (:) <$> char '_' <*> many1 (alphaNum <|> char '_')))

atom :: (Monad m) => Parser (PrologT m) Atom
atom = identifier
   <|> operator
   <|> (natural >>= return . T.pack . show)
   <|> (charLiteral >>= return . T.pack )
   <?> "atom"


alphaNonUpper :: (Monad m) => Parser m Char
alphaNonUpper = satisfy (\c -> isAlpha c && not (isUpper c))


stringLiteral :: (Monad m) => Parser (PrologT m) Term
stringLiteral = foldr cons nil . map representChar <$> stringLiteralToken

representChar :: Char -> Term
representChar c = UTerm (TStruct (T.pack (show (fromEnum c))) []) -- This is the classical Prolog representation of chars as code points.
--representChar c = Struct [c] [] -- This is the more natural representation as one-character atoms.
--representChar c = Struct "char" [Struct (show (fromEnum c)) []] -- This is a representation as tagged code points.
--toChar :: Term -> Maybe Char
--toChar (Struct "char" [Struct (toEnum . read->c) []]) = Just c
--toChar _                                              = Nothing


----------------------------  User state  ----------------------------
data ParserState m  = ParserState
                    { userAccountId :: Maybe UserAccountId
                    , moduleFileName    :: Maybe Atom
                    , moduleName  :: Atom
                    , varMap      :: Map String Term
                    , wildcards   :: [(String, Term)]
                    , operatorTable    :: Bool -> P.Prolog.OperatorTable Text (ParserState m) m Term
                    , expressionParser :: Bool -> ParsecT Text (ParserState m)  m Term
                    , database :: DB.Database
                    }

emptyState :: Monad m => ParserState (PrologT m)
emptyState = ParserState
             { userAccountId = Nothing
             , moduleFileName = Nothing
             , moduleName = "main"
             , varMap = Map.empty
             , wildcards = []
             , operatorTable = \ignoreConjunction ->  toExpressionTable $ defaultHierarchy ignoreConjunction
             , expressionParser = \ignoreConjunction ->
             P.Prolog.buildExpressionParser (operatorTable emptyState ignoreConjunction) bottom
             , database = DB.empty
             }
toExpressionTable :: Monad m => [(Int, [Operator])]
                     -> P.Prolog.OperatorTable Text (ParserState (PrologT m)) (PrologT m) Term
toExpressionTable table = map toPrologOperators table
  where
    toPrologOperators :: Monad m => (Int, [Operator])
                         -> (Int, [P.Prolog.Operator Text (ParserState (PrologT m)) (PrologT m) Term])
    toPrologOperators (prio, ops) = (prio, map toPrologOperator ops)
toPrologOperator :: Monad m => Operator
                    -> P.Prolog.Operator Text (ParserState (PrologT m)) (PrologT m) Term
toPrologOperator (InfixOp  assoc text)
  | isOperator   text = P.Prolog.Infix  (reservedOp text >> return (binary text) ) assoc
  | isIdentifier text = P.Prolog.Infix  (reserved   text >> return (binary text) ) assoc
toPrologOperator (PrefixOp assoc text)
  | isOperator   text = P.Prolog.Prefix (reservedOp text >> return (unary text)) assoc
  | isIdentifier text = P.Prolog.Prefix (reserved   text >> return (unary text)) assoc
toPrologOperator (PostfixOp assoc text)
  | isOperator   text = P.Prolog.Postfix (reservedOp text >> return (unary text)) assoc
  | isIdentifier text = P.Prolog.Postfix (reserved   text >> return (unary text)) assoc


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
  st <- getState
  let vmap  = varMap st
  let vmap' = Map.insert v x vmap
  setState $ st { varMap =  vmap' }

insertWildcard :: (Monad m) => String -> Term -> Parser m ()
insertWildcard v x = do
  st <- getState
  let wild  = wildcards st
  let wild' = (v,x) : wild
  setState $ st { wildcards = wild' }

setFileName :: Monad m => Atom -> Parser  m ()
setFileName name = do
  st <- getState
  setState st { moduleFileName = Just name }

defineModule :: Monad m => Atom -> [ DB.Signature ] -> Parser m ()
defineModule mod ss = do
  st <- getState
  setState st { moduleName = mod
              , database   = DB.setPublicTable mod ss (database st) }

useModule :: ( YesodPersist site
             , YesodPersistBackend site ~ SqlBackend )
             => Atom -> Parser (PrologT (HandlerT site IO)) ()
useModule mod = do
  st <- getState
  case userAccountId st of
    Just uid -> do
      est <- lift $ lift $ evalPrologT $ consult uid mod
      case est of
        Right (Right st') -> setState st { database = DB.merge (database st') (database st) }
        _ -> parserFail $  "parse error in module" ++  T.unpack mod
    Nothing -> do
      fail "Unknown UserAccountId"


data Assoc = XFX
           | XFY
           | YFX
           | XF
           | YF
           | FX
           | FY
           deriving (Eq,Show)

assocToOperator :: Assoc -> Atom -> Operator
assocToOperator XFX = InfixOp  AssocXFX
assocToOperator XFY = InfixOp  AssocXFY
assocToOperator YFX = InfixOp  AssocYFX
assocToOperator XF  = PostfixOp  AssocXF
assocToOperator YF  = PostfixOp  AssocYF
assocToOperator FX  = PrefixOp   AssocFX
assocToOperator FY  = PrefixOp   AssocFY

defineOperator :: Monad m => Int -> Assoc -> Atom -> Parser  (PrologT m) ()
defineOperator prio assoc atom = do
  st <- getState
  let table = insertOp prio (assocToOperator assoc atom) (operatorTable st)
  setState st { operatorTable = table
              , expressionParser = \ignoreConjunction ->
              P.Prolog.buildExpressionParser (table ignoreConjunction) bottom }

insertOp  :: Monad m
             => Int -> Operator
             -> (Bool -> P.Prolog.OperatorTable Text (ParserState (PrologT m)) (PrologT m) Term)
             -> (Bool -> P.Prolog.OperatorTable Text (ParserState (PrologT m)) (PrologT m) Term)
insertOp prio op table ignoreConjunction = insert (toPrologOperator op) (table ignoreConjunction)
  where
    insert op [] = [(prio, [op]) ]
    insert op ((pr , ops) : t)  | pr == prio = (pr, ops ++ [op]) : t
                                | pr <  prio = (prio , [op]) : (pr, ops) : t
                                | pr >  prio = (pr , ops) : insert op t


insertClause :: Monad m => Clause -> Parser  (PrologT m) ()
insertClause clause = do
  st <- getState
  let database' = DB.insertClause (moduleName st) clause (database st)
  setState st { database = database' }
