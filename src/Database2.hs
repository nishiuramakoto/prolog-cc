module Database2
   ( createDB
   , hasPredicate
   , getClauses
   , Signature(), signature
   , Database(..)
   )
where

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Unification
import Control.Unification.IntVar

import Syntax2


data Signature = Signature Atom Int deriving (Ord, Eq)
instance Show Signature where
   show (Signature name arity) = name ++ "/" ++ show arity

signature :: Term -> Signature
signature (UTerm (TStruct name ts)) = Signature name (length ts)


newtype Database = DB (Map Signature [Clause])

hasPredicate sig (DB index) = Map.member sig index

createDB clauses emptyPredicates = DB $
   foldr (\clause -> Map.insertWith' (++) (signature (lhs clause)) [clause])
         (Map.fromList [ (signature (UTerm (TStruct name [])), []) | name <- emptyPredicates ])
         clauses

getClauses :: Term -> Database -> [Clause]
getClauses term (DB index) = maybe [] id $ Map.lookup (signature term) index
