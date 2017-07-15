{-# LANGUAGE
    ViewPatterns
  , MultiParamTypeClasses
  , GeneralizedNewtypeDeriving
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  , IncoherentInstances
  , ScopedTypeVariables
  , DeriveTraversable
  , OverloadedStrings
  , CPP
  #-}

module Language.Prolog2.InterpreterIO
   ( resolve
   , resolveToTerms
   , PrologT
   , getFreeVar , getFreeVars
   , createDB
   , createSysDB
   , RuntimeError
   , NonUnificationError(..)
   )  where

#ifdef YESOD
import Import hiding(cons,trace,mapM_,sort,get, maximum)
import qualified Prelude
#endif

-----------------------------------------------------------------------------------------------
import Control.Monad.Reader hiding(filterM)
import Control.Monad.State  hiding(filterM)
import Control.Monad.Except hiding(filterM)
import Control.Unification hiding (getFreeVars)
import qualified Control.Unification as U
import Control.Unification.IntVar
import qualified Data.Text as T
import Language.Prolog2.Types
import Language.Prolog2.Syntax
import qualified Language.Prolog2.Database as DB
import qualified Language.Prolog2.SystemDatabase as SysDB
import Language.Prolog2.InterpreterCommon
import Language.Prolog2.Types
import Language.Prolog2.Builtins
import Control.Monad.Logger

-- import Language.Prolog2.Trace

-------------------------- Monadic Builtins --------------------------


type IOResolver m = SysDB.Resolver () (PrologDatabaseT m)

asserta :: Monad m => IOResolver m -> IOResolver m
asserta resolver st mod depth nf usf (UTerm (TStruct "asserta" [fact]):gs) stack sysdb = do
        nf' <- liftProlog $ countFreeVars [[UClause fact [] ]]
        local (DB.asserta mod fact) $  resolver st mod depth (max nf nf')  usf gs stack sysdb

assertz :: Monad m =>IOResolver m -> IOResolver m
assertz resolver st mod depth nf usf (UTerm (TStruct "asserta" [fact]):gs) stack sysdb  = do
        nf' <- liftProlog $ countFreeVars [[UClause fact [] ]]
        local (DB.assertz mod fact) $  resolver st mod depth (max nf nf')  usf gs stack sysdb

retract :: MonadLogger m => IOResolver m -> IOResolver m
retract resolver st mod depth nf usf (UTerm (TStruct "retract" [t]):gs) stack sysdb  = do
  $logInfo $ T.pack $ "retract:" ++ show t

  clauses <- asks (DB.getClauses mod t)
  ts <- filterM (liftProlog . PrologT . unifyWith t) [ t' | UClause t' [] <- clauses ]
  case ts of
    [] -> do $logInfo $ T.pack $ "retract failed:"
             return (fail "retract/1")
    (fact:_) -> local (DB.abolish mod fact) $ resolver st mod depth nf usf gs stack sysdb
    where
      unifyWith t t' = (t =:= t' >> return True) `catchError` const (return False)



builtinM :: MonadLogger m => PrologT m [SysDB.ClauseM () (PrologDatabaseT m)]
builtinM = do
  [x,x',x'',query,v]  <- getFreeVars 5
  return [ SysDB.UClauseM (UTerm (TStruct "asserta" [x  ])) asserta
         , SysDB.UClauseM (UTerm (TStruct "assertz" [x' ])) assertz
         , SysDB.UClauseM (UTerm (TStruct "retract" [x''])) retract
         ]


createDB :: MonadLogger m => PrologT m DB.Database
createDB = do
  db <- createBuiltinDatabase
  return db

createSysDB :: MonadLogger m => PrologT m (SysDB.SystemDatabase () (PrologDatabaseT m))
createSysDB = do
  ls <- builtinM
  return $ SysDB.insertSystemProgram ls SysDB.empty
