import Text.Parsec
import Text.Parsec.PrologExpr
import qualified Text.Parsec.Token as P

import Control.Monad.Identity
import Data.Char

predefinedOp :: [String]
predefinedOp = [ ":-" , "-->"
               , ":-" , "?-"
               , ";"
               , "->"
               , ","
               , "=","\\=","==","\\==","@<","@=<","@>","@>=","is" , "=:=","=\\=","<","=<",">" ,">=", "=.."
               , "+", "-" , "/\\" , "\\/"
               , "*" , "/" , "//" , "rem" , "mod" , "<<", ">>"
               , "**"
               , "^"
               , "\\", "-"
               , "@"
               , ":"
               ]


prologDef :: P.GenLanguageDef String u Identity
prologDef = P.LanguageDef
            { P.commentStart = "/*"
            , P.commentEnd   = "*/"
            , P.commentLine  = "%"
            , P.nestedComments = False
            , P.identStart  = upper <|> char '_'
            , P.identLetter = alphaNum <|> char '_'
            , P.opStart     = oneOf "#$&*+-./:<=>?@^~\\"
            , P.opLetter    = oneOf "#$&*+-./:<=>?@^~\\"
            , P.reservedNames = []
            , P.reservedOpNames = []
            , P.caseSensitive = True
            }

lexer = P.makeTokenParser prologDef

vname = P.identifier lexer

atom =  do x <- ((:) <$> lowerNonUpper <*> many (alphaNum <|> char '_'))
                <|> P.operator lexer
           return (Term x [])

atomOf s =  try $ do atom <- (:) <$> lowerNonUpper <*> many (alphaNum <|> char '_')
                             <|> P.operator lexer
                     guard $ atom == s

operator s = P.lexeme lexer (atomOf s) >> notFollowedBy (char '(')

lowerNonUpper = satisfy (\c -> isAlpha c && not (isUpper c))

data Term a = Term a [ Term a]
            deriving (Eq,Show)

binary :: String -> Term String -> Term String -> Term String
binary x t1 t2 = Term x [t1, t2]

unary :: String -> Term String -> Term String
unary x t1 = Term x [t1]

expr :: ParsecT String () Identity (Term String)
expr = buildExpressionParser [[ Infix   (do {operator "+" ; return (binary "+") }) AssocXFY
                              , Infix   (do {operator "-" ; return (binary "-") }) AssocYFX
                              , Infix   (do {operator ">" ; return (binary "*") }) AssocXFX
                              , Prefix  (do {operator "#" ; return (unary  "#") }) AssocFX
                              , Prefix  (do {operator "!" ; return (unary  "!") }) AssocFY
                              , Postfix (do {operator "^" ; return (unary  "^") }) AssocXF
                              , Postfix (do {operator "^" ; return (unary  "&") }) AssocYF
                              ]]

       (P.lexeme lexer atom)


test s = runParser (do {x <- expr; string "."; return x}) () "" s
