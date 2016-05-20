{-# LANGUAGE
    TypeFamilies,
    ScopedTypeVariables,
    DeriveTraversable
  #-}

module Language.Prolog2.Database
   ( insertProgram
   , insertClause
   , empty
   , size
   , merge
   , hasUserPredicate
   , getClauses
   , setPublicTable
   , isPublic
   , Signature(..), signature
   , Database
   , dbUserTable
   , asserta
   , assertz
   , abolish
   )
where

#ifdef YESOD
-- import Import
import Prelude
#endif

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
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


type UserTable            = Map (Maybe ModuleName, Maybe Signature) ([Clause])
type PublicTable          = Set (Maybe ModuleName, Maybe Signature)

data Database   = DB { dbModuleGraph :: NamedGraph ModuleName
                     , dbUserTable   :: UserTable
                     , dbPublicTable :: PublicTable
                     }

merge :: Database -> Database  -> Database
merge (DB gr1 ut1 pt1) (DB gr2 ut2 pt2) = DB
                                          (NG.merge gr1 gr2)
                                          (mergeUT ut1 ut2)
                                          (mergePT pt1 pt2)
  where
    mergeUT = Map.unionWith (++)
    mergePT = Set.union


empty :: Database
empty = DB  NG.empty  initialUT  Set.empty
  where
    initialUT = Map.fromList [ ((Nothing, signature (UTerm (TStruct name []))), [])
                             | name <- emptyPredicates ]
    emptyPredicates = [ "false" , "fail" ]

size :: Database -> Int
size (DB _ ut _) = Map.size ut

setPublicTable :: ModuleName -> [ Signature ] -> Database -> Database
setPublicTable mod ss db = db { dbPublicTable = Set.fromList (zip (repeat (Just mod)) (map Just ss)) }

isPublic :: Maybe ModuleName -> Maybe Signature -> Database -> Bool
isPublic mod s db = Set.member (mod,s) (dbPublicTable db)

hasUserPredicate :: ModuleName -> Signature -> Database -> Bool
hasUserPredicate mod sig db = Map.member  (Just mod, Just sig) (dbUserTable db)


insertClause :: ModuleName -> Clause -> Database  -> Database
insertClause mod clause db = db { dbUserTable = update $ dbUserTable db }
  where update map = Map.insertWith' (++) (Just mod, signature (lhs clause)) [clause] map


insertProgram :: Foldable t => Maybe ModuleName -> t (UClause Term) -> Database -> Database
insertProgram mod clauses db = db { dbUserTable = ut' }
  where
    ut' = foldr (\clause  -> Map.insertWith' (++) (mod, signature (lhs clause)) [clause])
          (dbUserTable db)
          clauses

getClauses :: ModuleName -> Term -> Database -> [Clause]
getClauses mod term (DB gr ut _) =
  let c0 = Map.lookup (Nothing , signature term) ut
      c  = Map.lookup (Just mod, signature term) ut
      cs = map (\n -> Map.lookup (Just n, signature term) ut) (NG.suc mod gr)
      d  = getFirst $ foldl1 mappend (map First $ [c0, c ] ++ cs)
  in maybe [] id d


asserta :: ModuleName -> Term -> Database -> Database
asserta mod fact db = db { dbUserTable = update $ dbUserTable db }
  where update ut = Map.insertWith (++)  (Just mod,signature fact) [UClause fact []] ut

assertz :: ModuleName -> Term -> Database -> Database
assertz mod fact db = db { dbUserTable = update $ dbUserTable db }
  where update ut = Map.insertWith (flip (++))  (Just mod,signature fact) [UClause fact []] ut


abolish :: ModuleName -> Term -> Database -> Database
abolish mod fact db = db { dbUserTable = update $ dbUserTable db }
  where update ut =  Map.adjust deleteFact (Just mod,signature fact) ut
        deleteFact (UClause t []:cs) | t == fact = cs
        deleteFact (_           :cs)             = cs
        deleteFact []                            = []
