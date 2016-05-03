{-# LANGUAGE
    TypeFamilies,
    ScopedTypeVariables,
    DeriveTraversable
  #-}

module Language.Prolog2.Database
   ( insertProgram
   , insertSystemProgram
   , empty
   , size
   , hasUserPredicate
   , hasSystemPredicate
   , getClauses
   , getSystemClause
   , asserta
   , assertz
   , abolish
   , Signature(..), signature
   , Database
   , dbUserTable , dbSystemTable
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
import Data.Monoid
import Control.Unification
import Language.Prolog2.Syntax
import Language.Prolog2.NamedGraph(NamedGraph)
import qualified Language.Prolog2.NamedGraph as NG


data Signature = Signature Atom Int deriving (Ord, Eq)
instance Show Signature where
   show (Signature name arity) = T.unpack name ++ "/" ++ show arity

signature :: Term -> Maybe Signature
signature (UTerm (TStruct name ts)) =  Just (Signature name (length ts))
signature  _  = Nothing


type UserTable            = Map (Maybe ModuleName, Maybe Signature) [Clause]
type SystemTable state m  = Map (Maybe Signature) (ClauseM state m)
data Database state m  = DB { dbModuleGraph :: NamedGraph ModuleName
                            , dbUserTable   :: UserTable
                            , dbSystemTable :: SystemTable state m
                            }

empty :: Database state m
empty = DB  NG.empty  initialUT  Map.empty
  where
    initialUT = Map.fromList [ ((Nothing, signature (UTerm (TStruct name []))), [])
                             | name <- emptyPredicates ]
    emptyPredicates = [ "false" , "fail" ]

size :: Database state m -> Int
size (DB _ ut st) = Map.size ut + Map.size st

hasUserPredicate :: ModuleName -> Signature -> Database state m -> Bool
hasUserPredicate mod sig (DB _ ut _) = Map.member  (Just mod, Just sig) ut

hasSystemPredicate :: Signature -> Database state m -> Bool
hasSystemPredicate sig (DB _ _ st) = Map.member (Just sig) st

insertClause :: ModuleName -> Clause -> Database state m -> Database state m
insertClause mod clause db = db { dbUserTable = update $ dbUserTable db }
  where update map = Map.insertWith' (++) (Just mod, signature (lhs clause)) [clause] map

insertSystemProgram :: Monad m => [ (UClauseM state m Term) ] -> Database state m  -> Database state m
insertSystemProgram clauses db =  db { dbSystemTable = update $ dbSystemTable db }
  where update st =
          foldr (\clause  -> Map.insert (signature (lhsM clause)) clause)
          st
          clauses

insertProgram :: Foldable t => Maybe ModuleName -> t (UClause Term) -> Database state m -> Database state m
insertProgram mod clauses (DB gr ut st) = DB gr ut' st
  where
    ut' = foldr (\clause  -> Map.insertWith' (++) (mod, signature (lhs clause)) [clause])
          ut
          clauses

getClauses :: ModuleName -> Term -> Database state m -> [Clause]
getClauses mod term (DB gr ut _) =
  let c0 = Map.lookup (Nothing , signature term) ut
      c  = Map.lookup (Just mod, signature term) ut
      cs = map (\n -> Map.lookup (Just n, signature term) ut) (NG.suc mod gr)
      d  = getFirst $ foldl1 mappend (map First $ [c0, c ] ++ cs)
  in maybe [] id d


getSystemClause :: Term -> Database state m -> Maybe (ClauseM state m)
getSystemClause term (DB _ _ st) = Map.lookup (signature term) st

asserta :: ModuleName -> Term -> Database state m  -> Database state m
asserta mod fact db = db { dbUserTable = update $ dbUserTable db }
  where update ut = Map.insertWith (++)  (Just mod,signature fact) [UClause fact []] ut

assertz :: ModuleName -> Term -> Database state m  -> Database state m
assertz mod fact db = db { dbUserTable = update $ dbUserTable db }
  where update ut = Map.insertWith (flip (++))  (Just mod,signature fact) [UClause fact []] ut


abolish :: ModuleName -> Term -> Database state m -> Database state m
abolish mod fact db = db { dbUserTable = update $ dbUserTable db }
  where update ut =  Map.adjust deleteFact (Just mod,signature fact) ut
        deleteFact (UClause t []:cs) | t == fact = cs
        deleteFact (_           :cs)             = cs
        deleteFact []                            = []
