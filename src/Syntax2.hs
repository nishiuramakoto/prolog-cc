{-# LANGUAGE DeriveDataTypeable
           , ViewPatterns
           , ScopedTypeVariables
           , DeriveFunctor
           , DeriveFoldable
           , DeriveTraversable
           #-}

module Syntax2
   ( Term(..) , T(..)
   , Failure
   , Clause(..), rhs
   , UClause(..)
   , UClauseList(..)
   , Goal, Program, Atom
   , atom
   , getFreeVar
   , hierarchy
   , Operator(..), Assoc(..)
   , arguments
   , foldr_pl
   , cons, nil
   )
where
import Data.List.Extras.Pair  (pairWith)
import Data.Generics (Data(..), Typeable(..))
import Data.List (intercalate)
import Data.Char (isLetter)
import Control.Unification
import Control.Unification.IntVar
import Control.Unification.Types
import Control.Monad.Except


data T a = TStruct String [a]
         deriving (Show, Functor,Foldable, Traversable)

instance Unifiable T where
  zipMatch (TStruct m ls) (TStruct n rs)
    | m /= n = Nothing
    | otherwise = TStruct n <$> pairWith (\l r -> Right (l,r)) ls rs

type Term    = UTerm T IntVar
type Atom    = String
type Goal    = Term
type Program = [Clause]
type Failure = UFailure T IntVar


data UClause t = UClause { lhs :: t , rhs_ :: [t] }
              deriving (Functor,Foldable,Traversable)
newtype UClauseList t = UClauseList [UClause t]
                      deriving (Functor,Foldable,Traversable)
type Clause = UClause Term

atom n = UTerm $ TStruct n []

rhs :: Clause ->  [Goal]
rhs (UClause   _ rhs_) =  rhs_

getFreeVar :: (Applicative m, Monad m)
              => ExceptT Failure (IntBindingT T m) Term
getFreeVar = lift (UVar <$> freeVar)



foldr_pl :: ( Term -> c -> c) -> c -> Term -> c
foldr_pl f k (UTerm (TStruct "." [h,t])) = f h (foldr_pl f k t)
foldr_pl _ k (UTerm (TStruct "[]" []))   = k

cons t1 t2 = TStruct "."  [t1,t2]
nil        = TStruct "[]" []

instance Show t => Show (UClause t) where
   show (UClause   lhs [] ) = show $ show lhs
   show (UClause   lhs rhs) = show $ show lhs ++ " :- " ++ intercalate ", " (map show rhs)


data Operator = PrefixOp String
              | InfixOp Assoc String
data Assoc = AssocLeft
           | AssocRight

hierarchy :: Bool -> [[Operator]]
hierarchy ignoreConjunction =
   --[ [ InfixOp NonAssoc "-->", InfixOp NonAssoc ":-" ]
   [ [ infixR ";" ] ] ++
   (if ignoreConjunction then [] else [ [ infixR "," ] ])  ++
   [ [ prefix "\\+" ]
   , map infixL ["<", "=..", "=:=", "=<", "=", ">=", ">", "\\=", "is", "==", "@<", "@=<", "@>=", "@>"]
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
