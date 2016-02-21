module Parser2
   ( consult, parseQuery
   , program, whitespace, comment, clause, terms, term, bottom, vname
   ) where

import Text.Parsec
import Text.Parsec.Expr hiding (Assoc(..))
import qualified Text.Parsec.Expr as Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (emptyDef)
import Control.Applicative ((<$>),(<*>),(<$),(<*))

import Syntax2

consult :: FilePath -> PrologMonad IO (Either ParseError Program)
consult = fmap consultString . readFile

consultString :: String -> Either ParseError Program
consultString = parse (whitespace >> program <* eof) "(input)"

parseQuery = parse (whitespace >> terms <* eof) "(query)"

program = many (clause <* char '.' <* whitespace)

whitespace = skipMany (comment <|> skip space <?> "")
comment = skip $ choice
   [ string "/*" >> (manyTill anyChar $ try $ string "*/")
   , char '%' >> (manyTill anyChar $ try $ skip newline <|> eof)
   ]

skip = (>> return ())

clause = do t <- struct <* whitespace
            dcg t <|> normal t
   where
      normal t = do
            ts <- option [] $ do string ":-" <* whitespace
                                 terms
            return (UClause t ts)

      dcg t = do
            string "-->" <* whitespace
            ts <- terms
            return (translate (t,ts))

      translate ((UTerm (TStruct a ts)), rhs) =
         let lhs' = TStruct a (arguments ts (head vars) (last vars))
             vars = map (var.("d_"++).(a++).show) [0..length rhs] -- We explicitly choose otherwise invalid variable names
             rhs' = zipWith3 translate' rhs vars (tail vars)
         in Clause lhs' rhs'

      translate' t s s0 | isList t   = UTerm (TStruct "=" [ s, foldr_pl cons s0 t ])     -- Terminal
      translate' t@(UTerm (TStruct "{}" ts)) s s0 = foldr and (UTerm (TStruct "=" [ s, s0 ])) ts -- Braced terms
      translate' (UTerm (TStruct a ts))  s s0 = UTerm (TStruct a (arguments ts s s0))    -- Non-Terminal

      and x y = UTerm (TStruct "," [x,y])



isList (UTerm (TStruct "." [_,_])) = True
isList (UTerm (TStruct "[]" []))   = True
isList _                  = False


terms = sepBy1 termWithoutConjunction (charWs ',')

term = term' False
termWithoutConjunction = term' True



term' ignoreConjunction = buildExpressionParser (reverse $ map (map toParser) $ hierarchy ignoreConjunction) (bottom <* whitespace)

bottom = variable
      <|> struct
      <|> list
      <|> stringLiteral
      <|> (UTerm (TStruct "{}" <$> between (charWs '{') (char '}') terms))
      <|> between (charWs '(') (char ')') term

toParser (PrefixOp name)      = Prefix $ reservedOp name >> return (\t -> UTerm (TStruct name [t]))
toParser (InfixOp assoc name) = Infix  (reservedOp name >> return (\t1 t2 -> UTerm (TStruct name [t1, t2])))
                                       (case assoc of AssocLeft  -> Parsec.AssocLeft
                                                      AssocRight -> Parsec.AssocRight)
reservedOp = P.reservedOp $ P.makeTokenParser $ emptyDef
   { P.opStart = oneOf ";,<=>\\i*+m@"
   , P.opLetter = oneOf "=.:<+"
   , P.reservedOpNames = operatorNames
   , P.caseSensitive = True
   }

charWs c = char c <* whitespace

operatorNames = [ ";", ",", "<", "=..", "=:=", "=<", "=", ">=", ">", "\\=", "is", "*", "+", "-", "\\", "mod", "\\+" ]

variable = (Wildcard <$ try (char '_' <* notFollowedBy (alphaNum <|> char '_')))
       <|> Var <$> vname
       <?> "variable"

vname = VariableName 0 <$> ((:) <$> upper    <*> many  (alphaNum <|> char '_') <|>
                            (:) <$> char '_' <*> many1 (alphaNum <|> char '_'))

atom = (:) <$> lower <*> many (alphaNum <|> char '_')
   <|> many1 digit
   <|> choice (map string operatorNames)
   <|> many1 (oneOf "#$&*+/.<=>\\^~")
   <|> between (char '\'') (char '\'') (many (noneOf "'"))
   <?> "atom"

struct = do a <- atom
            ts <- option [] $ between (charWs '(') (char ')') terms
            return (UTerm (TStruct a ts))

list = between (charWs '[') (char ']') $
         flip (foldr cons) <$> option []  terms
                           <*> option nil (charWs '|' >> term)


stringLiteral = foldr cons nil . map representChar <$> between (char '"') (char '"') (try (many (noneOf "\"")))

representChar c = (UTerm TStruct (show (fromEnum c))) [] -- This is the classical Prolog representation of chars as code points.
--representChar c = Struct [c] [] -- This is the more natural representation as one-character atoms.
--representChar c = Struct "char" [Struct (show (fromEnum c)) []] -- This is a representation as tagged code points.
--toChar :: Term -> Maybe Char
--toChar (Struct "char" [Struct (toEnum . read->c) []]) = Just c
--toChar _                                              = Nothing
