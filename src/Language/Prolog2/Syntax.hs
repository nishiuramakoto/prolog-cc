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

module Language.Prolog2.Syntax
   ( Term , T(..), UTerm(..)
   , Failure
   , Clause, rhs
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
   , ppTerm , ppClause , ppProgram
   )
where

#ifdef YESOD
import Import.NoFoundation hiding(cons)
import Data.Generics (Data(..))
#else
import Data.List (intercalate)
import Data.Generics (Data(..), Typeable)
import Data.Text(Text)
#endif

import qualified Data.Text as T
import Data.List.Extras.Pair  (pairWith)
import Data.Char (isLetter)
-- import Data.Traversable
-- import Data.Foldable(Foldable)
import Control.Unification hiding (getFreeVars)
import Control.Unification.IntVar
import Control.Unification.Types
-- import Control.Monad.Except
-- import Control.Applicative


data T a = TStruct Text [a]
         | TCut {-# UNPACK #-} !Int
         deriving (Eq, Show, Functor,Data,Typeable , Foldable)

-- Manually defining Traversable adds a bit to the speed
instance Traversable T where
  traverse f  (TStruct n ts) = TStruct n <$> traverse f ts
  traverse _f (TCut n)       = pure (TCut n)

instance Eq (UTerm T IntVar) where
  (UTerm (TStruct a ts)) == (UTerm (TStruct b ss)) = b == a && ts == ss
  (UTerm (TCut n)) == (UTerm (TCut m)) = n == m
  (UVar x) == (UVar y) = x == y
  _ == _ = False


instance Unifiable T where
  zipMatch (TStruct m ls) (TStruct n rs)
    | m /= n = Nothing
    | otherwise = (TStruct n <$> pairWith (\l r -> Right (l,r)) ls rs)
  zipMatch _ _ = Nothing -- unifying cut with cut returns Nothing

type Term    = UTerm T IntVar
type Atom    = Text
type Goal    = Term
type Program = [Clause]
type Failure = UFailure T IntVar

everywhere' :: (forall a. T a -> T a) -> [Term] -> [Term]
everywhere' f = map (everywhere'' f)
  where
    everywhere'' :: (forall a. T a -> T a) -> Term -> Term
    everywhere'' f'  (UTerm (TStruct n ts)) = UTerm (f' (TStruct n (everywhere' f' ts)))
    everywhere'' f'  (UTerm (TCut n))       = UTerm (f' (TCut n))
    everywhere'' _f' (UVar v)               = UVar v


data UClause  t = UClause   { lhs :: t , rhs_ :: [t] }
                | UClauseFn { lhs :: t , fn   :: [Term] -> [Goal] }
              deriving (Functor,Foldable,Traversable)

rhs :: Clause ->  [Term] -> [Goal]
rhs (UClause   _ rhs') =  const rhs'
rhs (UClauseFn _ fn'  ) =  fn'


newtype UClauseList  t = UClauseList [UClause t]
                       deriving (Functor,Foldable,Traversable)
type Clause = UClause  Term




atom :: Text -> UTerm T v
atom n = UTerm $ TStruct n []
cut :: UTerm T v
cut = (UTerm (TCut 0))



foldr_pl :: (Term -> c -> c) -> c -> Term -> Maybe c
foldr_pl f k (UTerm (TStruct "." [h,t])) = f h <$> foldr_pl f k t
foldr_pl _ k (UTerm (TStruct "[]" []))   = Just k
foldr_pl _ _ _  = Nothing


cons :: UTerm T v -> UTerm T v -> UTerm T v
cons t1 t2 = UTerm $ TStruct "."  [t1,t2]
nil :: UTerm T v
nil        = UTerm $ TStruct "[]" []


ppProgram :: [Clause] -> Text
ppProgram cls = T.intercalate "\n" $ map ppClause cls

ppClause :: Clause  -> Text
ppClause (UClause   lhs' [])   = T.concat [ ppTerm lhs' , "."]
ppClause (UClause   lhs' rhs') = T.concat [ ppTerm lhs' , " :- " , ppRHS rhs' ]
ppClause (UClauseFn lhs' _fn)  = T.concat [ ppTerm lhs' , " :- " , "<FUNCTION>" ]

ppRHS :: [Term] -> Text
ppRHS rhs' = T.concat [ T.intercalate ", " $ map ppTerm rhs' , "." ]

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
   where g ts (UTerm (TStruct "." [h,t'])) = g (h:ts) t'
         g ts t' = (reverse ts, t')
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


instance Show t => Show (UClause t) where
   show (UClause   lhs' [] )  = show $ show lhs'
   show (UClause   lhs' rhs') = show $ show lhs' ++ " :- " ++ intercalate ", " (map show rhs')
   show (UClauseFn lhs' _f)   = show lhs' ++ "<FUNCTION>"

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
   , [ infixL "*", infixL "/"]
   , [ infixL "mod" ]
   , [ prefix "-" ]
   , [ prefix "$" ] -- used for quasi quotation
   ]
 where
   prefix = PrefixOp
   infixL = InfixOp AssocLeft
   infixR = InfixOp AssocRight

arguments :: [a] -> a -> a -> [a]
arguments ts xs ds = ts ++ [ xs, ds ]

----------------------------------------------------------------
_fib :: Int -> Int
_fib 0 = 1
_fib 1 = 1
_fib n = _fib (n-1) + _fib (n-2)
{-# INLINE _fib #-}
----------------------------------------------------------------
