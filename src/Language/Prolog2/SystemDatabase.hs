module Language.Prolog2.SystemDatabase
       ( SystemDatabase
       , insertSystemProgram
       , hasSystemPredicate
       , getSystemClause
       , Stack, Branch , Resolver , UClauseM(..), ClauseM
       ) where

#ifdef YESOD
import Import.NoFoundation hiding(cons,trace,mapM_,sort,get, maximum)
#endif

import Language.Prolog2.Syntax
import Language.Prolog2.Database
import Control.Unification.IntVar
import qualified Data.Map as Map

type Stack = [(IntBindingState T, [Goal], [Branch])]
type Branch = (IntBindingState T, [Goal])

type Resolver state m = state -> ModuleName -> Int -> Int -> IntBindingState T -> [Goal] -> Stack
                        -> SystemDatabase state m
                        -> m [IntBindingState T]

data UClauseM state  m  t = UClauseM  { lhsM :: t , rhsM :: Resolver state m -> Resolver state m }

type ClauseM state  m  = UClauseM state m Term


newtype SystemDatabase state m  = SysDB (Map (Maybe Signature) (ClauseM state m))

hasSystemPredicate :: Signature -> SystemDatabase state m -> Bool
hasSystemPredicate sig (SysDB db) = Map.member (Just sig) db

insertSystemProgram :: Monad m
                       => [ (UClauseM state m Term) ] -> SystemDatabase state m  -> SystemDatabase state m
insertSystemProgram clauses (SysDB db) =  SysDB (updateDB db)
  where updateDB st =
          foldr (\clause  -> Map.insert (signature (lhsM clause)) clause)
          st
          clauses

getSystemClause :: Term -> SystemDatabase state m -> Maybe (ClauseM state m)
getSystemClause term (SysDB st) = Map.lookup (signature term) st
