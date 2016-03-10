{-# LANGUAGE
    ViewPatterns
  , ScopedTypeVariables
  #-}


module Language.Prolog2.Parser
   ( Parser , consult, consultString , parseQuery
   , program, whitespace, comment, clause, terms, term, bottom, vname
   ) where
import Prelude
import Text.Parsec
import Text.Parsec.Expr hiding (Assoc(..))
import qualified Text.Parsec.Expr as Parsec
import qualified Text.Parsec.Token as P
import qualified Text.Parsec.Error as P
import qualified Text.Parsec.Pos as P
-- import Text.Parsec.Language (emptyDef)
-- import Control.Applicative (Applicative,(<$>),(<*>),(<$),(<*))
import Control.Monad.State
-- import Control.Unification.IntVar
-- import Data.Text(Text)
import qualified Data.Text as T
import Data.Map(Map)
import qualified Data.Map as Map
-- import Data.Set(Set)
-- import qualified Data.Set as Set
import System.Directory


import Language.Prolog2.Syntax hiding (atom)
import qualified Language.Prolog2.Syntax as Prolog
import Language.Prolog2.Interpreter


type Parser m a = ParsecT String ParserState (PrologT m) a

------------------------  Top level parsers --------------------------
consult :: FilePath -> PrologT IO (Either ParseError Program)
consult source = do exists <- liftIO $ doesFileExist source
                    if exists
                      then do  s <- liftIO $ readFile source
                               runParserT p emptyState source s
                      else return $ Left $ fileDoesNoExist source
  where p = (whitespace >> program <* eof)
        fileDoesNoExist file = P.newErrorMessage (P.Message "File does not exist") (P.newPos file 0 0)

consultString :: (Functor m, Applicative m, Monad m) => String -> PrologT m (Either ParseError Program)
consultString s = runParserT p emptyState "(input)" s
  where p = (whitespace >> program <* eof)

parseQuery :: (Functor m, Applicative m, Monad m) => String -> PrologT m (Either ParseError [Term])
parseQuery s = runParserT p  emptyState "(query)" s
  where p = (whitespace >> terms <* eof)
------------------------  Individual parsers  ------------------------
program :: (Functor m, Applicative m, Monad m) => Parser m Program
program = many (clause <* char '.' <* whitespace)

whitespace :: (Functor m, Applicative m, Monad m) => Parser m ()
whitespace = skipMany (try comment <|> skip space <?> "")

comment :: (Functor m, Applicative m, Monad m) => Parser m ()
comment = skip $ choice
          [ string "/*" >> (manyTill anyChar $ try $ string "*/")
          , char '%' >> (manyTill anyChar $ try $ skip newline <|> eof)
          ]

skip :: (Functor m, Applicative m, Monad m) => Parser m a -> Parser m ()
skip = (>> return ())

clause :: (Functor m, Applicative m, Monad m) => Parser m Clause
clause = do resetState
            t <- struct <* whitespace
            dcg t <|> normal t
   where
     normal :: (Functor m, Applicative m, Monad m) => Term -> Parser m Clause
     normal t = do
       ts <- option [] $ do _ <- string ":-" <* whitespace
                            terms
       return (UClause t ts)

     dcg :: (Functor m, Applicative m, Monad m) => Term -> Parser m Clause
     dcg t = do
            _ <- string "-->" <* whitespace
            ts <- terms
            translate (t,ts)

     translate :: (Functor m, Applicative m, Monad m) => (Term, [Term]) -> Parser m Clause
     translate ((UTerm (TStruct a ts)), rhs'') = do
       vars <- lift $ getFreeVars (length rhs'' + 1)
       let lhs' = UTerm (TStruct a (arguments ts (head vars) (last vars)))
           rhs' = zipWith3 translate' rhs'' vars (tail vars)
       return $ UClause lhs' rhs'
     translate _ = error "Internal Parser Error"

     translate' t s s0 | isList t   = let l = foldr_pl cons s0 t
                                      in  case l of
                                      Just l' ->  UTerm (TStruct (T.pack "=") [ s, l' ])     -- Terminal
                                      Nothing ->  error "This is impossible"
     translate' (UTerm (TStruct a ts)) s s0 | a == (T.pack "{}")  =
                                                foldr and_ (UTerm (TStruct (T.pack "=") [ s, s0 ])) ts -- Braced terms
     translate' (UTerm (TStruct a ts))  s s0 = UTerm (TStruct a (arguments ts s s0))    -- Non-Terminal
     translate' _ _ _ = error "Internal parser error"

     and_ x y = UTerm (TStruct (T.pack ",") [x,y])


isList :: Term -> Bool
isList (UTerm (TStruct n [_,_])) | n == (T.pack ".")  = True
isList (UTerm (TStruct n []))    | n == (T.pack "[]") = True
isList _                  = False

terms :: (Functor m, Applicative m, Monad m) => Parser m [Term]
terms = sepBy1 termWithoutConjunction (charWs ',')

term :: (Functor m, Applicative m, Monad m) => Parser m Term
term = term' False
termWithoutConjunction :: (Functor m, Applicative m, Monad m) => Parser m Term
termWithoutConjunction = term' True


term' :: (Functor m, Applicative m, Monad m) => Bool -> Parser m Term
term' ignoreConjunction = buildExpressionParser (reverse $ map (map toParser) $ hierarchy ignoreConjunction) (bottom <* whitespace)

bottom :: (Functor m, Applicative m, Monad m) => Parser m Term
bottom = variable
      <|> struct
      <|> list
      <|> stringLiteral
      <|> cut <$ char '!'
      <|> ((UTerm . TStruct (T.pack "{}"))  <$> between (charWs '{') (char '}') terms)
      <|> between (charWs '(') (char ')') term

toParser :: (Functor m, Applicative m, Monad m) => Prolog.Operator -> Parsec.Operator String ParserState (PrologT m) Term
toParser (PrefixOp name)      = Prefix $ reservedOp (T.unpack name) >> return (\t -> UTerm (TStruct name [t]))
toParser (InfixOp assoc name) = Infix   ( do reservedOp (T.unpack name)
                                             return (\t1 t2 -> UTerm (TStruct name [t1, t2])))
                                     (case assoc of AssocLeft  -> Parsec.AssocLeft
                                                    AssocRight -> Parsec.AssocRight)


type PrologLanguageDef m = P.GenLanguageDef String ParserState  m

genPrologDef   :: (Functor m, Applicative m, Monad m) => PrologLanguageDef m
genPrologDef    = P.LanguageDef
               { P.commentStart   = ""
               , P.commentEnd     = ""
               , P.commentLine    = ""
               , P.nestedComments = True
               , P.identStart     = letter <|> char '_'
               , P.identLetter    = alphaNum <|> oneOf "_'"
               , P.opStart        = oneOf ";,<=>\\i*+m@"
               , P.opLetter       = oneOf "=.:<+/>"
               , P.reservedOpNames= operatorNames
               , P.reservedNames  = []
               , P.caseSensitive  = True
               }

reservedOp :: (Functor m, Applicative m, Monad m) => String -> Parser m ()
reservedOp = P.reservedOp $ P.makeTokenParser $ genPrologDef

-- reservedOp = P.reservedOp $ P.makeTokenParser $ emptyDef
--    { P.opStart = oneOf ";,<=>\\i*+m@"
--    , P.opLetter = oneOf "=.:<+"
--    , P.reservedOpNames = operatorNames
--    , P.caseSensitive = True
--    }

charWs :: (Functor m, Applicative m, Monad m) => Char -> Parser m Char
charWs c = char c <* whitespace

operatorNames :: [String]
operatorNames = [ ";", ",", "<", "=..", "=:=", "=<", "=", ">=", ">", "\\=", "is", "/" , "*", "+", "-", "\\", "mod", "\\+" ]

variable :: (Functor m, Applicative m, Monad m) => Parser m Term
variable = (do _ <- try (char '_' <* notFollowedBy (alphaNum <|> char '_'))
               wildcard)
       <|> var =<< vname
       <?> "variable"

wildcard :: (Functor m, Applicative m, Monad m) => Parser m Term
wildcard  = do v <- lift $ getFreeVar
               insertWildcard "_" v
               return v

var :: (Functor m, Applicative m, Monad m) => String -> Parser m Term
var v = do mx <- lookupVarMap v
           case mx of
             Just x  -> return x
             Nothing -> do x <- lift $ getFreeVar
                           insertVarMap v x
                           return x

vname :: (Functor m, Applicative m, Monad m) => Parser m String
vname = ((:) <$> upper    <*> many  (alphaNum <|> char '_') <|>
         (:) <$> char '_' <*> many1 (alphaNum <|> char '_'))

atom :: (Functor m, Applicative m, Monad m) => Parser m String
atom = (:) <$> lower <*> many (alphaNum <|> char '_')
   <|> many1 digit
   <|> choice (map string operatorNames)
   <|> many1 (oneOf "#$&*+/.<=>\\^~")
   <|> between (char '\'') (char '\'') (many (noneOf "'"))
   <?> "atom"

struct :: (Functor m, Applicative m, Monad m) => Parser m Term
struct = do a <- atom
            ts <- option [] $ between (charWs '(') (char ')') terms
            return (UTerm (TStruct (T.pack a) ts))

list :: (Functor m, Applicative m, Monad m) => Parser m Term
list = between (charWs '[') (char ']') $
         flip (foldr cons) <$> option []  terms
                           <*> option nil (charWs '|' >> term)

stringLiteral :: (Functor m, Applicative m, Monad m) => Parser m Term
stringLiteral = foldr cons nil . map representChar <$> between (char '"') (char '"') (try (many (noneOf "\"")))

representChar :: Char -> Term
representChar c = UTerm (TStruct (T.pack (show (fromEnum c))) []) -- This is the classical Prolog representation of chars as code points.
--representChar c = Struct [c] [] -- This is the more natural representation as one-character atoms.
--representChar c = Struct "char" [Struct (show (fromEnum c)) []] -- This is a representation as tagged code points.
--toChar :: Term -> Maybe Char
--toChar (Struct "char" [Struct (toEnum . read->c) []]) = Just c
--toChar _                                              = Nothing


----------------------------  User state  ----------------------------
data ParserState = ParserState { varMap    :: Map String Term
                               , wildcards :: [(String, Term)]
                               }
                      deriving (Show)

emptyState :: ParserState
emptyState = ParserState { varMap = Map.empty , wildcards = [] }

resetState :: (Functor m, Applicative m, Monad m) => Parser m ()
resetState = updateState (\_ -> emptyState)

lookupVarMap :: (Functor m, Applicative m, Monad m) => String -> Parser m (Maybe Term)
lookupVarMap v = do
  m <- varMap <$> getState
  return $ Map.lookup v m

insertVarMap :: (Functor m, Applicative m, Monad m) => String -> Term -> Parser m ()
insertVarMap v x = do
  ParserState vmap wild_ <- getState
  let vmap' = Map.insert v x vmap
  setState $ ParserState vmap' wild_

insertWildcard :: (Functor m, Applicative m, Monad m) => String -> Term -> Parser m ()
insertWildcard v x = do
  ParserState vmap wild_ <- getState
  let wildcards' = (v,x) : wild_
  setState $ ParserState vmap wildcards'
