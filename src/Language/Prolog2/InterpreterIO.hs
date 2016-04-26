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
   , runPrologT , evalPrologT, execPrologT
   , getFreeVar , getFreeVars
   , RuntimeError
   , NonUnificationError(..)
   )  where

#ifdef YESOD
import Import hiding(cons,trace,mapM_,sort,get, maximum)
import qualified Prelude
#endif

-----------------------------------------------------------------------------------------------
import Control.Monad.Reader
import Control.Monad.State
import Control.Unification hiding (getFreeVars)
import qualified Control.Unification as U
import Control.Unification.IntVar

import Language.Prolog2.Types
import Language.Prolog2.Syntax
import qualified Language.Prolog2.Database as DB
import Language.Prolog2.InterpreterCommon
import Language.Prolog2.Builtins

-- import Language.Prolog2.Trace

type UserState = ()



resolveToTerms ::  Monad m =>  UserState ->  Program ->  [Goal] -> PrologT m  [[Term]]
resolveToTerms st program goals = do
  vs <- PrologT $ lift $ U.getFreeVarsAll goals
  usfs <- resolve st program goals
  -- lift $ lift $ $(logInfo) $ T.pack $ "resolveToTerms: " ++ show usfs
  Prelude.mapM (f (map UVar vs)) usfs
    where
      f :: (Functor m, Applicative m, Monad m) => [Term] -> IntBindingState T -> PrologT m [Term]
      f vs usf = do put usf
                    PrologT $ Prelude.mapM applyBindings vs


resolve ::  Monad m  => UserState -> Program ->  [Goal] -> PrologT m [IntBindingState T]
resolve st program goals = do

  usf <- get
  bs  <- builtins

  numFreeVars <- countFreeVars [bs ++ program]

  bindings <- runReaderT (unPrologDatabaseT (resolveWithDatabase st 1 numFreeVars usf goals []))
              (DB.createDB (bs ++ program) ["false","fail"])
  return bindings


resolveWithDatabase ::  Monad m  => UserState -> Int -> Int -> IntBindingState T -> [Goal] -> Stack
                        -> PrologDatabaseT m  [IntBindingState T]
resolveWithDatabase  depth nf usf_ gs_ stack_ = resolve'' depth nf usf_ gs_ stack_


resolve'' :: Monad m => UserState -> Int -> Int -> IntBindingState T -> [Goal] -> Stack
                   -> PrologDatabaseT m  [IntBindingState T]

resolve'' st depth nf usf [] stack =  do
        (usf:) <$> backtrack st depth nf stack

resolve'' st depth nf usf (UTerm (TCut n):gs) stack =  resolve'' st depth nf usf gs (drop n stack)


resolve'' st depth nf  usf (UTerm (TStruct "asserta" [fact]):gs) stack = do
        nf' <- PrologDatabaseT $ lift $ countFreeVars (Identity [UClause fact [] ])
        local (DB.asserta fact) $ resolve'' st depth (max nf nf')  usf gs stack


resolve'' st depth nf usf (nextGoal:gs) stack = do
        -- trace $ show $ "==resolve'=="
        -- trace $ show $  ("usf:",usf)
        -- trace $ show $  ("goals:",(nextGoal:gs))
        -- trace $ show $  ("stack:", stack)

        put usf
        updateNextFreeVar depth nf

        usf' <- get
        branches <- getBranches usf' nextGoal gs
        -- traceLn $  ("branches:" , show $ length branches, branches)

        choose st depth nf usf gs branches stack


choose :: Monad m => UserState -> Int -> Int -> IntBindingState T -> [Goal] -> [Branch] -> Stack
             -> PrologDatabaseT m [IntBindingState T]
choose  st depth  nf _usf _gs  (_branches@[]) stack =
  backtrack st depth nf stack
choose  st depth  nf usf  gs ((u',gs'):alts)  stack =
  resolve'' st (succ depth) nf u' gs' ((usf,gs,alts) : stack)

backtrack :: Monad m => UserState -> Int -> Int -> Stack -> PrologDatabaseT m [ IntBindingState T ]
backtrack _  _ _ []                  =  return (fail "Goal cannot be resolved!")
backtrack st depth nf  ((u,gs,alts):stack) = choose st (pred depth) nf  u gs alts stack
