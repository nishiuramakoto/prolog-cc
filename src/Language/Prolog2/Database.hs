{-# LANGUAGE
    TypeFamilies,
    ScopedTypeVariables,
    DeriveTraversable
  #-}

module Language.Prolog2.Database
   ( createDB
   , insertProgram
   , empty
   , size
   , hasPredicate
   , getClauses
   , getClauseM
   , asserta
   , assertz
   , abolish
   , Signature(..), signature
   , Database
   , GenDatabase(..)
   )
where

#ifdef YESOD
-- import Import
import Prelude
#endif

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text(Text)
import qualified Data.Text as T
-- import Data.Maybe

import Control.Unification
-- import Control.Unification.IntVar

import Language.Prolog2.Syntax
import Language.Prolog2.NamedGraph


data Signature = Signature Atom Int deriving (Ord, Eq)
instance Show Signature where
   show (Signature name arity) = T.unpack name ++ "/" ++ show arity

signature :: Term -> Maybe Signature
signature (UTerm (TStruct name ts)) =  Just (Signature name (length ts))
signature  _  = Nothing


newtype GenDatabase a = DB { dbClauseMap :: (Map (Maybe Signature) a) }
                      deriving (Foldable, Traversable, Functor)
type Database  = GenDatabase [Clause]


empty :: GenDatabase a
empty = DB Map.empty

size :: GenDatabase a -> Int
size (DB db) = Map.size db

hasPredicate :: Signature -> GenDatabase a -> Bool
hasPredicate sig (DB index) = Map.member (Just sig) index

createDB :: Foldable t => t (UClause Term) -> [Text] -> Database
createDB clauses emptyPredicates = DB $
   foldr (\clause  -> Map.insertWith' (++) (signature (lhs clause)) [clause])
         (Map.fromList [ (signature (UTerm (TStruct name [])), []) | name <- emptyPredicates ])
         clauses

insertProgram :: Foldable t => t (UClause Term) -> Database -> Database
insertProgram clauses (DB db) = DB $
   foldr (\clause  -> Map.insertWith' (++) (signature (lhs clause)) [clause])
   db
   clauses


getClauses :: Term -> GenDatabase [a] -> [a]
getClauses term (DB index) = maybe [] id $ Map.lookup (signature term) index

getClauseM :: Term -> GenDatabase a -> Maybe a
getClauseM term (DB index) = Map.lookup (signature term) index

asserta :: Term -> Database  -> Database
asserta fact (DB index') = DB $ Map.insertWith (++)  (signature fact) [UClause fact []] index'

assertz :: Term -> Database -> Database
assertz fact (DB index') = DB $ Map.insertWith (flip (++)) (signature fact) [UClause fact []] index'

abolish :: Term -> Database -> Database
abolish fact (DB index') = DB $ Map.adjust deleteFact (signature fact) index'
   where deleteFact (UClause t []:cs) | t == fact = cs
         deleteFact (_           :cs)             = cs
         deleteFact []                            = []
