-----------------------------------------------------------------------------
-- |
-- Module      :  Text.Parsec.Expr
-- Copyright   :  (c) Daan Leijen 1999-2001, (c) Paolo Martini 2007
-- License     :  BSD-style (see the LICENSE file)
--
-- Maintainer  :  derek.a.elkins@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- A helper module to parse \"expressions\".
-- Builds a parser given a table of operators and associativities.
--
-----------------------------------------------------------------------------

module Text.Parsec.PrologExpr
    ( InfixAssoc(..), PrefixAssoc(..), PostfixAssoc(..), Operator(..), OperatorTable
    , buildExpressionParser
    ) where

import Text.Parsec.Prim
import Text.Parsec.Combinator

-----------------------------------------------------------
-- Assoc and OperatorTable
-----------------------------------------------------------

-- |  This data type specifies the associativity of operators: left, right
-- or none.

data InfixAssoc           = AssocXFX
                          | AssocYFX
                          | AssocXFY

data PrefixAssoc          = AssocFX
                          | AssocFY

data PostfixAssoc         = AssocXF
                          | AssocYF

-- | This data type specifies operators that work on values of type @a@.
-- An operator is either binary infix or unary prefix or postfix. A
-- binary operator has also an associated associativity.

data Operator s u m a   = Infix (ParsecT s u m (a -> a -> a)) InfixAssoc
                        | Prefix (ParsecT s u m (a -> a))     PrefixAssoc
                        | Postfix (ParsecT s u m (a -> a))    PostfixAssoc

-- | An @OperatorTable s u m a@ is a list of @Operator s u m a@
-- lists. The list is ordered in descending
-- precedence. All operators in one list have the same precedence (but
-- may have a different associativity).

type OperatorTable s u m a = [[Operator s u m a]]

-----------------------------------------------------------
-- Convert an OperatorTable and basic term parser into
-- a full fledged expression parser
-----------------------------------------------------------

-- | @buildExpressionParser table term@ builds an expression parser for
-- terms @term@ with operators from @table@, taking the associativity
-- and precedence specified in @table@ into account. Prefix and postfix
-- operators of the same precedence can only occur once (i.e. @--2@ is
-- not allowed if @-@ is prefix negate). Prefix and postfix operators
-- of the same precedence associate to the left (i.e. if @++@ is
-- postfix increment, than @-2++@ equals @-1@, not @-3@).
--
-- The @buildExpressionParser@ takes care of all the complexity
-- involved in building expression parser. Here is an example of an
-- expression parser that handles prefix signs, postfix increment and
-- basic arithmetic.
--
-- >  expr    = buildExpressionParser table term
-- >          <?> "expression"
-- >
-- >  term    =  parens expr
-- >          <|> natural
-- >          <?> "simple expression"
-- >
-- >  table   = [ [prefix "-" negate, prefix "+" id ]
-- >            , [postfix "++" (+1)]
-- >            , [binary "*" (*) AssocLeft, binary "/" (div) AssocLeft ]
-- >            , [binary "+" (+) AssocLeft, binary "-" (-)   AssocLeft ]
-- >            ]
-- >
-- >  binary  name fun assoc = Infix (do{ reservedOp name; return fun }) assoc
-- >  prefix  name fun       = Prefix (do{ reservedOp name; return fun })
-- >  postfix name fun       = Postfix (do{ reservedOp name; return fun })

buildExpressionParser :: (Stream s m t)
                      => OperatorTable s u m a
                      -> ParsecT s u m a
                      -> ParsecT s u m a
buildExpressionParser operators simpleExpr
    = foldl (makeParser) simpleExpr operators
    where
      makeParser term ops
        = let (xfy,yfx,xfx
               ,fx,fy,xf,yf)      = foldr splitOp ([],[],[],[],[],[],[]) ops

              xfyOp      = choice xfy
              yfxOp      = choice yfx
              xfxOp      = choice xfx
              fxOp       = choice fx  <?> "fx"
              fyOp       = choice fy  <?> "fy"
              xfOp       = choice xf  <?> "xf"
              yfOp       = choice yf  <?> "yf"

              ambigious assoc op = try $ do  op
                                             fail ("ambiguous use of a " ++ assoc
                                                 ++ " operator")

              ambigiousXFY      = ambigious "xfy" xfyOp
              ambigiousYFX      = ambigious "yfx" yfxOp
              ambigiousXFX      = ambigious "xfx" xfxOp
              ambigiousXF       = ambigious "xf"  xfOp
              ambigiousYF       = ambigious "yf"  yfOp
              ambigiousFX       = ambigious "fx"  fxOp
              ambigiousFY       = ambigious "fy"  fyOp

              termXP            = do fx <- fxOp
                                     x  <- term
                                     return (fx x)
                                  <|>
                                  do x  <- term
                                     xf <- xfOp0
                                     return (xf x)

              xfOp0         = xfOp <|> return id

              prefixedTermP = do fys <- many1 fyOp
                                 x   <- termXP
                                 return (foldr1 (.) fys $ x)
                              <|> termXP

              postfixedTermP = do x     <- termXP
                                  yfs   <- many yfOp
                                  return (foldr (.) id yfs $ x)

              yfxP y     = do  yfx <- yfxOp
                               x   <- term
                               yfxP0 (y `yfx` x)

                           <|> ambigiousXFX
                           <|> ambigiousXFY
                           <|> ambigiousXF
                           <|> ambigiousYF
                           <|> ambigiousFX
                           <|> ambigiousFY


              yfxP0 y    = yfxP y <|>  return y

              xfyP x     = do xfy  <- xfyOp
                              do { y    <- do { x' <- term; xfyP0 x' }
                                 ; return (x `xfy` y) }
                                <|>
                                do { y <- prefixedTermP
                                   ; return (x `xfy` y) }

                           <|> ambigiousYFX
                           <|> ambigiousXFX
                           <|> ambigiousXF
                           <|> ambigiousYF
                           <|> ambigiousFX
                           <|> ambigiousFY

              xfyP0 x    = xfyP x  <|> do { xf <- xfOp; return $ xf x } <|> return x


              xfxP  x  = do  xfx <- xfxOp
                             x'  <- term
                             return (x `xfx` x')

                         <|> ambigiousYFX
                         <|> ambigiousXFY
                         <|> ambigiousXF
                         <|> ambigiousYF
                         <|> ambigiousFX
                         <|> ambigiousFY


              postfixOps = do f   <- xfOp <|> yfOp
                              yfs <- many yfOp
                              return $ foldr (.) f (reverse yfs)

          in do fx    <- fxOp
                x     <- term
                yfs   <- many yfOp
                yfxP0 (foldr (.) fx (reverse yfs) $ x)
             <|>
             do x <- term
                do {post <- postfixOps ; yfxP0 (post x)}  <|> xfyP x <|> yfxP x <|> xfxP x <|> return x
             <|>
             prefixedTermP
             <?> "operator"


      splitOp (Infix op assoc) (xfy,yfx,xfx,fx,fy,xf,yf)
        = case assoc of
            AssocXFX   -> (xfy,yfx,op:xfx,fx,fy,xf,yf)
            AssocYFX   -> (xfy,op:yfx,xfx,fx,fy,xf,yf)
            AssocXFY   -> (op:xfy,yfx,xfx,fx,fy,xf,yf)

      splitOp (Prefix op assoc) (xfy,yfx,xfx,fx,fy,xf,yf)
        = case assoc of
            AssocFX -> (xfy,yfx,xfx,op:fx,fy,xf,yf)
            AssocFY -> (xfy,yfx,xfx,fx,op:fy,xf,yf)

      splitOp (Postfix op assoc) (xfy,yfx,xfx,fx,fy,xf,yf)
        = case assoc of
            AssocXF -> (xfy,yfx,xfx,fx,fy,op:xf,yf)
            AssocYF -> (xfy,yfx,xfx,fx,fy,xf,op:yf)
