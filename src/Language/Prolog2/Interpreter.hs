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

module Language.Prolog2.Interpreter
   ( resolve
   , resolveToTerms
   , PrologT
   , runPrologT , evalPrologT, execPrologT
   , getFreeVar , getFreeVars
   , RuntimeError
   , NonUnificationError(..)
   )  where

import Import hiding(cons,trace,mapM_,sort,get, maximum)
import qualified Prelude
import Control.Monad.CC.CCCxe
import Data.Typeable
import CCGraph
import Inquire
import Form

-----------------------------------------------------------------------------------------------

import qualified Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Unification hiding (getFreeVars)
import qualified Control.Unification as U
import Control.Unification.IntVar
import qualified Data.Text as T

import Language.Prolog2.Types
import Language.Prolog2.Syntax
import Language.Prolog2.Database(Database)
import qualified Language.Prolog2.Database as DB
import  Language.Prolog2.InterpreterCommon

-- import Language.Prolog2.Trace

type UserState   = CCState
trace = lift . lift . lift . $logInfo . T.pack


resolveToTerms ::  UserState ->  Program ->  [Goal] -> CCPrologHandler   [[Term]]
resolveToTerms st program goals = do
  db <- ask
  -- $(logInfo) $ T.pack $ "resolveToTerms: " ++ show (DB.size db)

  vs <- liftProlog $ PrologT $ lift $ U.getFreeVarsAll goals
  usfs <- resolve st program goals
  Prelude.mapM (f (map UVar vs)) usfs
    where
      f :: [Term] -> IntBindingState T -> CCPrologHandler  [Term]
      f vs usf = do put usf
                    liftProlog $ PrologT $ Prelude.mapM applyBindings vs


-- Yield all unifiers that resolve <goal> using the clauses from <program>.
resolve ::  ()       => UserState -> Program ->  [Goal] -> CCPrologHandler  [IntBindingState T]
resolve st  program goals = do
  local (DB.insertProgram  program) (resolveWithDatabase st 1 goals [])

resolveWithDatabase ::  UserState -> Int -> [Goal] -> Stack
                        -> CCPrologHandler   [IntBindingState T]
resolveWithDatabase  st depth goals stack = do
  db <- ask
  usf <- get
  -- $(logInfo) $ T.pack $ "resolveWithDatabase: " ++ (show $ DB.size db)
  numFreeVars <- liftProlog $ countFreeVars db
  -- $(logInfo) $ T.pack $ "resolveWithDatabase: " ++ show numFreeVars
  bindings <- resolve'' st depth numFreeVars usf goals stack
  -- $(logInfo) $ T.pack $ "resolveWithDatabase: " ++ show numFreeVars
  return bindings

resolve'' ::  UserState -> Int -> Int -> IntBindingState T -> [Goal] -> Stack
              -> CCPrologHandler   [IntBindingState T]

resolve'' st depth nf usf [] stack =  do
        (usf:) <$> backtrack st depth nf stack

resolve'' st depth nf usf (UTerm (TCut n):gs) stack =  resolve'' st depth nf usf gs (drop n stack)


resolve'' st depth nf  usf goals'@(UTerm (TStruct "asserta" [fact]):gs) stack = do
  -- $(logInfo) $ T.pack $ "asserta "

  nf' <- liftProlog $ countFreeVars [[UClause fact [] ]]
  local (DB.asserta fact) $  resolve'' st depth (max nf nf')  usf gs stack

----------------  Yesod specific language extensions  ----------------
resolve'' st depth nf usf (UTerm (TStruct "inquire_bool" [query,v]):gs) stack = do
  -- $logInfo "resolve''"
  st' <-  inquirePrologBool st query

  let result = case ccsCurrentForm st' of
        CCFormResult form' ->  case cast form' of
          Just (FormSuccess (PrologInquireBoolForm True))
            -> UTerm (TStruct "true" [])
          _ -> UTerm (TStruct "false" [])
          Nothing -> UTerm (TStruct "false" [])

  -- $logInfo "resolve''"
  resolve'' st' depth nf usf ((UTerm (TStruct "=" [v, result])) : gs) stack
---------------------------------------------------------------------

resolve'' st depth nf usf (nextGoal:gs) stack = do
        -- trace $ show $ "==resolve'=="
        -- trace $ show $  ("usf:",usf)
        -- trace $ show $  ("goals:",(nextGoal:gs))
        -- trace $ show $  ("stack:", stack)
  -- $logInfo $ T.pack $ "resolve''" ++ show nf
  put usf
  updateNextFreeVar depth nf
  usf' <- get
  -- $logInfo $ T.pack $ "resolve''" ++ show nf
  branches <- CCPrologT $ lift $ getBranches usf' nextGoal gs
  -- $logInfo $ T.pack $ "resolve''" ++ show nf
  choose st depth nf usf gs branches stack

choose :: UserState -> Int -> Int -> IntBindingState T -> [Goal] -> [Branch] -> Stack
             -> CCPrologHandler  [IntBindingState T]
choose  st depth  nf _usf _gs  (_branches@[]) stack = backtrack st depth nf stack
choose  st depth  nf usf  gs ((u',gs'):alts)  stack = resolve'' st (succ depth) nf u' gs' ((usf,gs,alts) : stack)

backtrack :: UserState -> Int -> Int -> Stack -> CCPrologHandler  [ IntBindingState T ]
backtrack _  _ _ []                  =  return (fail "Goal cannot be resolved!")
backtrack st depth nf  ((u,gs,alts):stack) = choose st (pred depth) nf  u gs alts stack
