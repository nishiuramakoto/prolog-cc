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
  , LiberalTypeSynonyms
  , CPP
  #-}

module Language.Prolog2.Interpreter
   ( resolve
   , resolveToTerms
   , PrologT
   , runPrologT , evalPrologT, execPrologT
   , getFreeVar , getFreeVars
   , RuntimeError
   , NonUnificationError(..)
   , createDB
   , createSysDB
   )  where

import Import hiding(cons,trace,mapM_,sort,get, maximum , lhs)
import qualified Prelude
import Control.Monad.CC.CCCxe
import Data.Typeable
import CCGraph
import Inquire
import Form

-----------------------------------------------------------------------------------------------

import qualified Control.Monad
import Control.Monad.Reader hiding(filterM)
import Control.Monad.State hiding(filterM)
import Control.Monad.Except hiding(filterM)
import Control.Unification hiding (getFreeVars)
import qualified Control.Unification as U
import Control.Unification.IntVar
import qualified Data.Text as T
import qualified Data.Map.Strict as Map

import Language.Prolog2.Types
import Language.Prolog2.Syntax
import Language.Prolog2.Database(Database)
import qualified Language.Prolog2.Database as DB
import qualified Language.Prolog2.SystemDatabase as SysDB
import Language.Prolog2.InterpreterCommon
import Language.Prolog2.Builtins

-- import Language.Prolog2.Trace

type UserState   = CCState
trace = lift . lift . lift . $logInfo . T.pack



-------------------------- Monadic Builtins --------------------------

type CCResolver = SysDB.Resolver UserState (CCPrologT App Handler)

asserta :: CCResolver -> CCResolver
asserta resolver st mod depth nf usf (UTerm (TStruct "asserta" [fact]):gs) stack sysdb = do
        nf' <- liftProlog $ countFreeVars [[UClause fact [] ]]
        local (DB.asserta mod fact) $  resolver st mod depth (max nf nf')  usf gs stack sysdb

assertz :: CCResolver -> CCResolver
assertz resolver st mod depth nf usf (UTerm (TStruct "asserta" [fact]):gs) stack sysdb = do
        nf' <- liftProlog $ countFreeVars [[UClause fact [] ]]
        local (DB.assertz mod fact) $  resolver st mod depth (max nf nf')  usf gs stack sysdb

retract :: CCResolver -> CCResolver
retract resolver st mod depth nf usf (UTerm (TStruct "retract" [t]):gs) stack sysdb = do
  $logInfo $ T.pack $ "retract:" ++ show t

  clauses <- asks (DB.getClauses mod t)
  ts <- filterM (liftProlog . PrologT . unifyWith t) [ t' | UClause t' [] <- clauses ]
  case ts of
    [] -> do $logInfo $ T.pack $ "retract failed:"
             return (fail "retract/1")
    (fact:_) -> local (DB.abolish mod fact) $ resolver st mod depth nf usf gs stack sysdb
    where
      unifyWith t t' = (t =:= t' >> return True) `catchError` const (return False)


----------------  Yesod specific language extensions  ----------------
inquire_bool :: CCResolver -> CCResolver
inquire_bool resolver st mod depth nf usf (UTerm (TStruct "inquire_bool" [query,v]):gs) stack sysdb = do
  -- $logInfo "resolve''"
  st' <-  inquirePrologBool st query

  let result = case ccsCurrentForm st' of
        CCFormResult form' ->  case cast form' of
          Just (FormSuccess (PrologInquireBoolForm True))   -> UTerm (TStruct "true" [])
          Just (FormSuccess (PrologInquireBoolForm False))  -> UTerm (TStruct "false" [])
          _ -> UTerm (TStruct "false" [])

  -- $logInfo "resolve''"
  resolver st' mod depth nf usf ((UTerm (TStruct "=" [v, result])) : gs) stack sysdb
---------------------------------------------------------------------


builtinM :: (Monad m, MonadTrans t, MonadPrologDatabase (t m))
            => t m [SysDB.ClauseM UserState (CCPrologT App Handler)]
builtinM = do
  [x,x',x'',query,v]  <- getFreeVars 5
  return [ SysDB.UClauseM (UTerm (TStruct "asserta" [x  ])) asserta
         , SysDB.UClauseM (UTerm (TStruct "assertz" [x' ])) assertz
         , SysDB.UClauseM (UTerm (TStruct "retract" [x''])) retract
         , SysDB.UClauseM (UTerm (TStruct "inquire_bool" [query,v])) inquire_bool
         ]



createDB :: Monad m => PrologT m Database
createDB = do
  db <- createBuiltinDatabase
  return db

createSysDB :: (Monad m, MonadTrans t, MonadPrologDatabase (t m))
               => t m (SysDB.SystemDatabase UserState (CCPrologT App Handler))
createSysDB = do
  cs <- builtinM
  return $ SysDB.insertSystemProgram cs SysDB.empty
