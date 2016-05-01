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
  staticDB <- liftProlog getSystemDB
  -- $(logInfo) $ T.pack $ "resolveWithDatabase: " ++ (show $ DB.size db)
  numFreeVars <- liftProlog $ countFreeVars db
  -- $(logInfo) $ T.pack $ "resolveWithDatabase: " ++ show numFreeVars
  resolve'' st depth numFreeVars usf goals stack staticDB

resolve'' ::  UserState -> Int -> Int -> IntBindingState T -> [Goal] -> Stack -> SystemDB UserState (CCPrologT Handler)
              -> CCPrologHandler   [IntBindingState T]

resolve'' st depth nf usf [] stack staticDB =  do
        (usf:) <$> backtrack st depth nf stack staticDB

resolve'' st depth nf usf (UTerm (TCut n):gs) stack staticDB =
  resolve'' st depth nf usf gs (drop n stack) staticDB

resolve'' st depth nf  usf (goal:gs) stack staticDB |
  Just (UClauseM lhs m) <- DB.getClauseM goal staticDB = do
    m resolve'' st depth nf usf (goal:gs) stack staticDB

resolve'' st depth nf usf (nextGoal:gs) stack staticDB= do
        -- trace $ show $ "==resolve'=="
        -- trace $ show $  ("usf:",usf)
        -- trace $ show $  ("goals:",(nextGoal:gs))
        -- trace $ show $  ("stack:", stack)
  -- $logInfo $ T.pack $ "resolve''" ++ show nf
  put usf
  updateNextFreeVar depth nf
  usf' <- get
  branches <- CCPrologT $ lift $ getBranches usf' nextGoal gs
  choose st depth nf usf gs branches stack staticDB

choose :: UserState -> Int -> Int -> IntBindingState T -> [Goal] -> [Branch] -> Stack -> SystemDB UserState (CCPrologT Handler) -> CCPrologHandler  [IntBindingState T]
choose  st depth  nf _usf _gs  (_branches@[]) stack staticDB = backtrack st depth nf stack staticDB
choose  st depth  nf usf  gs ((u',gs'):alts)  stack staticDB =
  resolve'' st (succ depth) nf u' gs' ((usf,gs,alts) : stack) staticDB

backtrack :: UserState -> Int -> Int -> Stack -> SystemDB UserState (CCPrologT Handler)
             -> CCPrologHandler  [ IntBindingState T ]
backtrack _  _ _ [] _                 =  return (fail "Goal cannot be resolved!")
backtrack st depth nf  ((u,gs,alts):stack) staticDB = choose st (pred depth) nf  u gs alts stack staticDB

-------------------------- Monadic Builtins --------------------------


--type Resolver = UserState -> Int -> Int -> IntBindingState T -> [Goal] -> Stack -> SystemDB (CCPrologT Handler)
--                -> CCPrologHandler [IntBindingState T]

asserta :: Resolver UserState (CCPrologT Handler) -> Resolver UserState (CCPrologT Handler)
asserta resolver st depth nf usf (UTerm (TStruct "asserta" [fact]):gs) stack staticDB = do
        nf' <- liftProlog $ countFreeVars [[UClause fact [] ]]
        local (DB.asserta fact) $  resolver st depth (max nf nf')  usf gs stack staticDB

assertz :: Resolver UserState (CCPrologT Handler) -> Resolver UserState (CCPrologT Handler)
assertz resolver st depth nf usf (UTerm (TStruct "asserta" [fact]):gs) stack staticDB = do
        nf' <- liftProlog $ countFreeVars [[UClause fact [] ]]
        local (DB.assertz fact) $  resolver st depth (max nf nf')  usf gs stack staticDB

retract :: Resolver UserState (CCPrologT Handler) -> Resolver UserState (CCPrologT Handler)
retract resolver st depth nf usf (UTerm (TStruct "retract" [t]):gs) stack staticDB = do
  $logInfo $ T.pack $ "retract:" ++ show t

  clauses <- asks (DB.getClauses t)
  ts <- filterM (liftProlog . PrologT . unifyWith t) [ t' | UClause t' [] <- clauses ]
  case ts of
    [] -> do $logInfo $ T.pack $ "retract failed:"
             return (fail "retract/1")
    (fact:_) -> local (DB.abolish fact) $ resolver st depth nf usf gs stack staticDB
    where
      unifyWith t t' = (t =:= t' >> return True) `catchError` const (return False)


----------------  Yesod specific language extensions  ----------------
inquire_bool :: Resolver UserState (CCPrologT Handler) -> Resolver UserState (CCPrologT Handler)
inquire_bool resolver st depth nf usf (UTerm (TStruct "inquire_bool" [query,v]):gs) stack staticDB = do
  -- $logInfo "resolve''"
  st' <-  inquirePrologBool st query

  let result = case ccsCurrentForm st' of
        CCFormResult form' ->  case cast form' of
          Just (FormSuccess (PrologInquireBoolForm True))
            -> UTerm (TStruct "true" [])
          _ -> UTerm (TStruct "false" [])
          Nothing -> UTerm (TStruct "false" [])

  -- $logInfo "resolve''"
  resolver st' depth nf usf ((UTerm (TStruct "=" [v, result])) : gs) stack staticDB
---------------------------------------------------------------------


builtinM :: Monad m => PrologT m [ClauseM UserState (CCPrologT Handler)]
builtinM = do
  [x,x',x'',query,v]  <- getFreeVars 5
  return [ UClauseM (UTerm (TStruct "asserta" [x  ])) asserta
         , UClauseM (UTerm (TStruct "assertz" [x' ])) assertz
         , UClauseM (UTerm (TStruct "retract" [x''])) retract
         , UClauseM (UTerm (TStruct "inquire_bool" [query,v])) inquire_bool
         ]


insertProgramM :: Monad m => [ (UClauseM state m Term) ] -> SystemDB state m  -> SystemDB state m
insertProgramM clauses (DB.DB db) = DB.DB $
   foldr (\clause  -> Map.insert (DB.signature (lhsM clause)) clause)
   db
   clauses

getSystemDB :: Monad m => PrologT m (SystemDB UserState (CCPrologT Handler))
getSystemDB = do
  ls <- builtinM
  return $ insertProgramM ls DB.empty
