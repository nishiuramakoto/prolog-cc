{-# LANGUAGE DeriveDataTypeable
           , ViewPatterns
           , ScopedTypeVariables
           , DeriveFunctor
           , DeriveFoldable
           , DeriveTraversable
           , Rank2Types
           , FlexibleInstances
           , OverloadedStrings
           #-}

module Syntax2
   ( Term(..) , T(..), UTerm(..)
   , Failure
   , Clause(..), rhs
   , UClause(..)
   , UClauseList(..)
   , Goal, Program, Atom
   , atom, cut
   , hierarchy
   , Operator(..), Assoc(..)
   , arguments
   , foldr_pl
   , cons, nil
   , everywhere'
   , ppTerm
   )
where
import Data.List.Extras.Pair  (pairWith)
import Data.Generics (Data(..), Typeable(..))
import Data.List (intercalate)
import Data.Char (isLetter)
import Control.Unification hiding (getFreeVars)
import Control.Unification.IntVar
import Control.Unification.Types
import Control.Monad.Except
import Control.Applicative
import Data.Text(Text)
import qualified Data.Text as T

data T a = TStruct Text [a]
         | TCut {-# UNPACK #-} !Int
         deriving (Eq, Show, Functor,Data,Typeable , Foldable)

-- Manually defining Traversable adds a bit to the speed
instance Traversable T where
  traverse f (TStruct n ts) = TStruct n <$> traverse f ts
  traverse f (TCut n)       = pure (TCut n)

instance Eq (UTerm T IntVar) where
  (UTerm (TStruct a ts)) == (UTerm (TStruct b ss)) = b == a && ts == ss
  (UTerm (TCut n)) == (UTerm (TCut m)) = n == m
  (UVar x) == (UVar y) = x == y

instance Unifiable T where
  zipMatch (TStruct m ls) (TStruct n rs)
    | m /= n = Nothing
    | otherwise = (TStruct n <$> pairWith (\l r -> Right (l,r)) ls rs)

type Term    = UTerm T IntVar
type Atom    = Text
type Goal    = Term
type Program = [Clause]
type Failure = UFailure T IntVar

everywhere' :: (forall a. T a -> T a) -> [Term] -> [Term]
everywhere' f = map (everywhere'' f)
  where
    everywhere'' :: (forall a. T a -> T a) -> Term -> Term
    everywhere'' f (UTerm (TStruct n ts)) = UTerm (f (TStruct n (everywhere' f ts)))
    everywhere'' f (UTerm (TCut n))       = UTerm (f (TCut n))
    everywhere'' f (UVar v)               = UVar v

data UClause t = UClause   { lhs :: t , rhs_ :: [t] }
               | UClauseFn { lhs :: t , fn   :: [Term] -> [Goal] }
              deriving (Functor,Foldable,Traversable)

rhs :: Clause ->  [Term] -> [Goal]
rhs (UClause   _ rhs_) =  const rhs_
rhs (UClauseFn _ fn  ) =  fn

newtype UClauseList t = UClauseList [UClause t]
                      deriving (Functor,Foldable,Traversable)
type Clause = UClause Term


atom n = UTerm $ TStruct n []
cut = (UTerm (TCut 0))



foldr_pl :: ( Term -> c -> c) -> c -> Term -> c
foldr_pl f k (UTerm (TStruct "." [h,t])) = f h (foldr_pl f k t)
foldr_pl _ k (UTerm (TStruct "[]" []))   = k

cons t1 t2 = UTerm $ TStruct "."  [t1,t2]
nil        = UTerm $ TStruct "[]" []


-- instance Show (UTerm T IntVar) where
--   show = prettyPrint False 0
ppTerm :: Term -> Text
ppTerm t = prettyPrint False 0 t


prettyPrint :: Bool -> Int -> Term -> Text

prettyPrint True _ t@(UTerm (TStruct "," [_,_])) =
  T.concat [ "(" , prettyPrint False 0 t ,  ")" ]

prettyPrint f n (UTerm (TStruct (flip lookup operatorTable->Just (p,InfixOp assoc name)) [l,r])) =
   parensIf (n >= p) $ T.concat [ prettyPrint f n_l l , spaced name , prettyPrint f n_r r ]
     where (n_l,n_r) = case assoc of
                           AssocLeft  -> (p-1, p)
                           AssocRight -> (p, p-1)

prettyPrint f n (UTerm (TStruct (flip lookup operatorTable->Just (p,PrefixOp name)) [r])) =
  parensIf (n >= p) $ T.concat [name , prettyPrint f (p {- Non-associative -}) r ]

prettyPrint _ _ t@(UTerm (TStruct "." [_,_])) =
  let (ts,rest) = g [] t in
      --case guard (isNil rest) >> sequence (map toChar ts) of
      --   Just str -> prettyPrint str
      --   Nothing  ->
  T.concat [ "["
           , T.intercalate "," (map (prettyPrint True 0) ts)
           , if isNil rest then "" else T.concat [ "|" , (prettyPrint True 0) rest ]
           ,  "]"
           ]
   where g ts (UTerm (TStruct "." [h,t])) = g (h:ts) t
         g ts t = (reverse ts, t)
         isNil (UTerm (TStruct "[]" [])) = True
         isNil _                = False

prettyPrint _ _ (UTerm (TStruct a []))  = a
prettyPrint _ _ (UTerm (TStruct a ts))  = T.concat [ a
                                                   , "("
                                                   , T.intercalate ", " (map (prettyPrint True 0) ts)
                                                   , ")" ]
prettyPrint _ _ (UVar (IntVar x))    = T.concat [ "X" , T.pack $ show (x - minBound) ]
prettyPrint _ _ ((==cut)->True)      = "!"
prettyPrint _ _ (UTerm (TCut n))     = T.concat ["!^" , T.pack $ show n ]


spaced :: Text -> Text
spaced s = let h = T.head s
               l = T.last s
           in T.concat [spaceIf (isLetter h) , s , spaceIf (isLetter l || ',' == l) ]

spaceIf :: Bool -> Text
spaceIf True  = " "
spaceIf False = ""

parensIf :: Bool -> Text -> Text
parensIf True  s = T.concat [ "(" , s , ")" ]
parensIf False s = s


operatorTable :: [(Text, (Int,Operator))]
operatorTable = concat $ zipWith (map . g) [1..] $ hierarchy False
 where g p op@(InfixOp _ name) = (name,(p,op))
       g p op@(PrefixOp name)  = (name,(p,op))

-- prettyPrint :: UTerm T IntVar -> String
-- prettyPrint  (UTerm (TStruct "[]" [])) =  "[]"
-- prettyPrint  (UTerm (TStruct "." [x,UTerm (TStruct "." [y,z])]))
--   =  "[" ++ prettyPrint x ++ "," ++ prettyPrint y ++ prettyPrint z ++
-- prettyPrint  (UTerm (TStruct "." [x,y] ))  =  "[" ++ prettyPrint x ++ "|" ++ prettyPrint y ++ "]"

-- prettyPrint  (UTerm (TStruct binop [x,y]))
--   | elem binop [ "=", ">" , "<" , "is"]  = prettyPrint x ++ binop ++ prettyPrint y
-- prettyPrint  (UTerm (TStruct binop xs))
--   | elem binop [ "=", ">" , "<" , "is"]  = error "prettyPrint"
-- prettyPrint  (UTerm (TStruct f   []))   =  f
-- prettyPrint  (UTerm (TStruct f   xs))   =  f ++ "(" ++ ppList xs ++ ")"
-- prettyPrint  (UTerm (TCut n)) = "!" ++ show n
-- prettyPrint  (UVar (IntVar x)) = "X" ++ show (x - minBound)

-- ppList :: [UTerm T IntVar] -> String
-- ppList ts = foldr  (\t acc -> show t ++ "," ++ acc) "" ts



instance Show t => Show (UClause t) where
   show (UClause   lhs [] ) = show $ show lhs
   show (UClause   lhs rhs) = show $ show lhs ++ " :- " ++ intercalate ", " (map show rhs)


data Operator = PrefixOp Text
              | InfixOp Assoc Text
data Assoc = AssocLeft
           | AssocRight

hierarchy :: Bool -> [[Operator]]
hierarchy ignoreConjunction =
   --[ [ InfixOp NonAssoc "-->", InfixOp NonAssoc ":-" ]
   [ [ infixR ";" ] ] ++
   (if ignoreConjunction then [] else [ [ infixR "," ] ])  ++
   [ [ prefix "\\+" ]
   , map infixL ["<", "=..", "=:=", "=\\=", "=<", "=", ">=", ">", "\\=", "is", "==", "@<", "@=<", "@>=", "@>"]
   , map infixL ["+", "-", "\\"]
   , [ infixL "*"]
   , [ infixL "mod" ]
   , [ prefix "-" ]
   , [ prefix "$" ] -- used for quasi quotation
   ]
 where
   prefix = PrefixOp
   infixL = InfixOp AssocLeft
   infixR = InfixOp AssocRight

arguments ts xs ds = ts ++ [ xs, ds ]

----------------------------------------------------------------
fib :: Int -> Int
fib 0 = 1
fib 1 = 1
fib n = fib (n-1) + fib (n-2)
{-# INLINE fib #-}
----------------------------------------------------------------
