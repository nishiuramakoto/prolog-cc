{-# LANGUAGE
    TypeFamilies,
    ScopedTypeVariables
  #-}

module Language.Prolog2.Database
   ( createDB
   , hasPredicate
   , getClauses
   , asserta
   , Signature(), signature
   , Database(..)
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


data Signature = Signature Atom Int deriving (Ord, Eq)
instance Show Signature where
   show (Signature name arity) = T.unpack name ++ "/" ++ show arity

signature :: Term -> Maybe Signature
signature (UTerm (TStruct name ts)) =  Just (Signature name (length ts))
signature  _  = Nothing


newtype Database = DB (Map (Maybe Signature) [Clause])

hasPredicate :: Signature -> Database -> Bool
hasPredicate sig (DB index) = Map.member (Just sig) index

createDB :: Foldable t => t (UClause Term) -> [Text] -> Database
createDB clauses emptyPredicates = DB $
   foldr (\clause  -> Map.insertWith' (++) (signature (lhs clause)) [clause])
         (Map.fromList [ (signature (UTerm (TStruct name [])), []) | name <- emptyPredicates ])
         clauses

getClauses :: Term -> Database -> [Clause]
getClauses term (DB index) = maybe [] id $ Map.lookup (signature term) index

asserta :: Term -> Database -> Database
asserta fact (DB index') = DB $ Map.insertWith (++)  (signature fact) [UClause fact []] index'
