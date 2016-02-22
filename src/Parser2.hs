{-# LANGUAGE
    ViewPatterns
  , ScopedTypeVariables
  #-}


module Parser2
   ( Parser(..) , consult, consultString , parseQuery
   , program, whitespace, comment, clause, terms, term, bottom, vname
   ) where

import Text.Parsec
import Text.Parsec.Expr hiding (Assoc(..))
import qualified Text.Parsec.Expr as Parsec
import qualified Text.Parsec.Token as P
import qualified Text.Parsec.Error as P
import qualified Text.Parsec.Pos as P
import Text.Parsec.Language (emptyDef)
import Control.Applicative ((<$>),(<*>),(<$),(<*))
import Control.Monad.State
import Control.Unification.IntVar
import Data.Text(Text)
import qualified Data.Text as T
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
import System.Directory


import Syntax2 hiding (atom)
import Interpreter2


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

consultString :: Monad m => String -> PrologT m (Either ParseError Program)
consultString s = runParserT p emptyState "(input)" s
  where p = (whitespace >> program <* eof)

parseQuery :: Monad m => String -> PrologT m (Either ParseError [Term])
parseQuery s = runParserT p  emptyState "(query)" s
  where p = (whitespace >> terms <* eof)
------------------------  Individual parsers  ------------------------
program :: Monad m => Parser m Program
program = many (clause <* char '.' <* whitespace)

whitespace :: Monad m => Parser m ()
whitespace = skipMany (comment <|> skip space <?> "")

comment :: Monad m => Parser m ()
comment = skip $ choice
   [ string "/*" >> (manyTill anyChar $ try $ string "*/")
   , char '%' >> (manyTill anyChar $ try $ skip newline <|> eof)
   ]

skip :: Monad m => Parser m a -> Parser m ()
skip = (>> return ())

clause :: Monad m => Parser m Clause
clause = do resetState
            t <- struct <* whitespace
            dcg t <|> normal t
   where
     normal :: Monad m => Term -> Parser m Clause
     normal t = do
       ts <- option [] $ do string ":-" <* whitespace
                            terms
       return (UClause t ts)

     dcg :: Monad m => Term -> Parser m Clause
     dcg t = do
            string "-->" <* whitespace
            ts <- terms
            translate (t,ts)

     translate :: Monad m => (Term, [Term]) -> Parser m Clause
     translate ((UTerm (TStruct a ts)), rhs) = do
       vars <- lift $ getFreeVars (length rhs + 1)
       let lhs' = UTerm (TStruct a (arguments ts (head vars) (last vars)))
           rhs' = zipWith3 translate' rhs vars (tail vars)
       return $ UClause lhs' rhs'

     translate' t s s0 | isList t   = UTerm (TStruct (T.pack "=") [ s, foldr_pl cons s0 t ])     -- Terminal
     translate' t@(UTerm (TStruct a ts)) s s0 | a == (T.pack "{}")  =
                                                  foldr and (UTerm (TStruct (T.pack "=") [ s, s0 ])) ts -- Braced terms
     translate' (UTerm (TStruct a ts))  s s0 = UTerm (TStruct a (arguments ts s s0))    -- Non-Terminal

     and x y = UTerm (TStruct (T.pack ",") [x,y])


isList :: Term -> Bool
isList (UTerm (TStruct n [_,_])) | n == (T.pack ".")  = True
isList (UTerm (TStruct n []))    | n == (T.pack "[]") = True
isList _                  = False

terms :: Monad m => Parser m [Term]
terms = sepBy1 termWithoutConjunction (charWs ',')

term :: Monad m => Parser m Term
term = term' False
termWithoutConjunction :: Monad m => Parser m Term
termWithoutConjunction = term' True


term' :: Monad m => Bool -> Parser m Term
term' ignoreConjunction = buildExpressionParser (reverse $ map (map toParser) $ hierarchy ignoreConjunction) (bottom <* whitespace)

bottom :: Monad m => Parser m Term
bottom = variable
      <|> struct
      <|> list
      <|> stringLiteral
      <|> ((UTerm . TStruct (T.pack "{}"))  <$> between (charWs '{') (char '}') terms)
      <|> between (charWs '(') (char ')') term

toParser :: Monad m => Syntax2.Operator -> Parsec.Operator String ParserState (PrologT m) Term
toParser (PrefixOp name)      = Prefix $ reservedOp (T.unpack name) >> return (\t -> UTerm (TStruct name [t]))
toParser (InfixOp assoc name) = Infix   ( do reservedOp (T.unpack name)
                                             return (\t1 t2 -> UTerm (TStruct name [t1, t2])))
                                     (case assoc of AssocLeft  -> Parsec.AssocLeft
                                                    AssocRight -> Parsec.AssocRight)


type PrologLanguageDef m = P.GenLanguageDef String ParserState  m

genPrologDef   :: Monad m => PrologLanguageDef m
genPrologDef    = P.LanguageDef
               { P.commentStart   = ""
               , P.commentEnd     = ""
               , P.commentLine    = ""
               , P.nestedComments = True
               , P.identStart     = letter <|> char '_'
               , P.identLetter    = alphaNum <|> oneOf "_'"
               , P.opStart        = oneOf ";,<=>\\i*+m@"
               , P.opLetter       = oneOf "=.:<+"
               , P.reservedOpNames= operatorNames
               , P.reservedNames  = []
               , P.caseSensitive  = True
               }

reservedOp :: Monad m => String -> Parser m ()
reservedOp = P.reservedOp $ P.makeTokenParser $ genPrologDef

-- reservedOp = P.reservedOp $ P.makeTokenParser $ emptyDef
--    { P.opStart = oneOf ";,<=>\\i*+m@"
--    , P.opLetter = oneOf "=.:<+"
--    , P.reservedOpNames = operatorNames
--    , P.caseSensitive = True
--    }

charWs :: Monad m => Char -> Parser m Char
charWs c = char c <* whitespace

operatorNames :: [String]
operatorNames = [ ";", ",", "<", "=..", "=:=", "=<", "=", ">=", ">", "\\=", "is", "*", "+", "-", "\\", "mod", "\\+" ]

variable :: Monad m => Parser m Term
variable = (do _ <- try (char '_' <* notFollowedBy (alphaNum <|> char '_'))
               wildcard)
       <|> var =<< vname
       <?> "variable"

wildcard :: Monad m => Parser m Term
wildcard  = do v <- lift $ getFreeVar
               insertWildcard "_" v
               return v

var :: Monad m => String -> Parser m Term
var v = do mx <- lookupVarMap v
           case mx of
             Just x  -> return x
             Nothing -> do x <- lift $ getFreeVar
                           insertVarMap v x
                           return x

vname :: Monad m => Parser m String
vname = ((:) <$> upper    <*> many  (alphaNum <|> char '_') <|>
         (:) <$> char '_' <*> many1 (alphaNum <|> char '_'))

atom :: Monad m => Parser m String
atom = (:) <$> lower <*> many (alphaNum <|> char '_')
   <|> many1 digit
   <|> choice (map string operatorNames)
   <|> many1 (oneOf "#$&*+/.<=>\\^~")
   <|> between (char '\'') (char '\'') (many (noneOf "'"))
   <?> "atom"

struct :: Monad m => Parser m Term
struct = do a <- atom
            ts <- option [] $ between (charWs '(') (char ')') terms
            return (UTerm (TStruct (T.pack a) ts))

list :: Monad m => Parser m Term
list = between (charWs '[') (char ']') $
         flip (foldr cons) <$> option []  terms
                           <*> option nil (charWs '|' >> term)

stringLiteral :: Monad m => Parser m Term
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

resetState :: Monad m => Parser m ()
resetState = updateState (\_ -> emptyState)

lookupVarMap :: Monad m => String -> Parser m (Maybe Term)
lookupVarMap v = do
  map <- varMap <$> getState
  return $ Map.lookup v map

insertVarMap :: Monad m => String -> Term -> Parser m ()
insertVarMap v x = do
  ParserState vmap wildcards <- getState
  let vmap' = Map.insert v x vmap
  setState $ ParserState vmap' wildcards

insertWildcard :: Monad m => String -> Term -> Parser m ()
insertWildcard v x = do
  ParserState vmap wildcards <- getState
  let wildcards' = (v,x) : wildcards
  setState $ ParserState vmap wildcards'
