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
   , PrologT , RunPrologT , PrologIO
   , runPrologT , evalPrologT, execPrologT
   , runRunPrologT, evalRunPrologT, execRunPrologT
   , getFreeVar , getFreeVars
   , createDB
   , IODatabase
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
import Language.Prolog2.SystemDatabase
import Language.Prolog2.InterpreterCommon
import Language.Prolog2.Types
import Language.Prolog2.Builtins
import Control.Monad.Logger

-- import Language.Prolog2.Trace

-------------------------- Monadic Builtins --------------------------


newtype RunPrologT m a = RunPrologT {unRunPrologT :: PrologDatabaseT () (RunPrologT m) m a }
                         deriving ( Functor
                                  , Applicative
                                  , Monad
                                  , MonadReader (DB.Database () (RunPrologT m))
                                  , MonadState  (IntBindingState T))

runRunPrologT :: Monad m => RunPrologT m a -> IODatabase m -> m (Either RuntimeError a, IntBindingState T)
runRunPrologT (RunPrologT m) db = runPrologDatabaseT m db

evalRunPrologT :: Monad m => RunPrologT m a -> IODatabase m -> m (Either RuntimeError a)
evalRunPrologT (RunPrologT m) db = evalPrologDatabaseT m db

execRunPrologT :: Monad m => RunPrologT m a -> IODatabase m -> m (IntBindingState T)
execRunPrologT (RunPrologT m) db = execPrologDatabaseT m db



type PrologIO a = RunPrologT (LoggingT IO) a

instance MonadTrans RunPrologT where
  lift = RunPrologT . lift

instance MonadProlog RunPrologT where
  liftProlog = RunPrologT . liftProlog

instance Monad m => MonadPrologDatabase RunPrologT () (RunPrologT m) m  where
  liftPrologDatabase = RunPrologT

instance MonadLogger m => MonadLogger (RunPrologT m)



type IODatabase m = DB.Database () (RunPrologT m)
type IOResolver m = Resolver () (RunPrologT m)

asserta :: Monad m => IOResolver m -> IOResolver m
asserta resolver st mod depth nf usf (UTerm (TStruct "asserta" [fact]):gs) stack = do
        nf' <- liftProlog $ countFreeVars [[UClause fact [] ]]
        local (DB.asserta mod fact) $  resolver st mod depth (max nf nf')  usf gs stack

assertz :: Monad m =>IOResolver m -> IOResolver m
assertz resolver st mod depth nf usf (UTerm (TStruct "asserta" [fact]):gs) stack  = do
        nf' <- liftProlog $ countFreeVars [[UClause fact [] ]]
        local (DB.assertz mod fact) $  resolver st mod depth (max nf nf')  usf gs stack

retract :: MonadLogger m => IOResolver m -> IOResolver m
retract resolver st mod depth nf usf (UTerm (TStruct "retract" [t]):gs) stack  = do
  $logInfo $ T.pack $ "retract:" ++ show t

  clauses <- asks (DB.getClauses mod t)
  ts <- filterM (liftProlog . PrologT . unifyWith t) [ t' | UClause t' [] <- clauses ]
  case ts of
    [] -> do $logInfo $ T.pack $ "retract failed:"
             return (fail "retract/1")
    (fact:_) -> local (DB.abolish mod fact) $ resolver st mod depth nf usf gs stack
    where
      unifyWith t t' = (t =:= t' >> return True) `catchError` const (return False)



builtinM :: MonadLogger m => PrologT m [ClauseM () (RunPrologT m)]
builtinM = do
  [x,x',x'',query,v]  <- getFreeVars 5
  return [ UClauseM (UTerm (TStruct "asserta" [x  ])) asserta
         , UClauseM (UTerm (TStruct "assertz" [x' ])) assertz
         , UClauseM (UTerm (TStruct "retract" [x''])) retract
         ]


createDB :: MonadLogger m => PrologT m (IODatabase m)
createDB = do
  db <- createBuiltinDatabase
  ls <- builtinM
  return $ DB.insertSystemProgram ls db
