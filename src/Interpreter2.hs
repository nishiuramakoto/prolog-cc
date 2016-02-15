{-# LANGUAGE ViewPatterns
  , GeneralizedNewtypeDeriving
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  , IncoherentInstances
  , ScopedTypeVariables
  , DeriveTraversable
  #-}
module Interpreter2
   ( resolve
   , PrologMonad
   , runPrologMonad , evalPrologMonad, execPrologMonad
   )
where
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity
import Control.Unification
import Control.Unification.IntVar
import Data.Maybe (isJust)
import Data.Generics (everywhere, mkT)
import Control.Applicative ((<$>),(<*>),(<$),(<*), Applicative(..), Alternative(..))

import Syntax2
import Database2
import Trace2

type PrologMonad a = ExceptT Failure (IntBindingT T IO) a
type PrologDatabaseMonad a = ReaderT Database (ExceptT Failure (IntBindingT T IO)) a

instance MonadIO m => MonadIO (IntBindingT T m) where
  liftIO = lift . liftIO

runPrologMonad :: PrologMonad a -> IO (Either Failure a, IntBindingState T)
runPrologMonad = runIntBindingT . runExceptT

evalPrologMonad :: PrologMonad a -> IO (Either Failure a)
evalPrologMonad = evalIntBindingT . runExceptT

execPrologMonad :: PrologMonad a -> IO (IntBindingState T)
execPrologMonad = execIntBindingT . runExceptT


builtins :: PrologMonad [Clause]
builtins = do
  x <-  getFreeVar
  a <-  getFreeVar
  b <-  getFreeVar
  return [ UClause (UTerm (TStruct "="   [x, x])) []
         , UClause (UTerm (TStruct "true" [])) []
         , UClause (UTerm (TStruct "," [a,b])) [a, b]
         ]

type Stack = [(IntBindingState T, [Goal], [Branch])]
type Branch = (IntBindingState T, [Goal])



-- Yield all unifiers that resolve <goal> using the clauses from <program>.
resolve ::  Program ->  [Goal] -> PrologMonad  [IntBindingState T]
resolve program goals = do
  usf <- get
  bs  <- builtins

  runReaderT (resolve' usf goals []) (createDB (bs ++ program) ["false","fail"])

  where
      resolve' ::  IntBindingState T -> [Goal] -> Stack  -> PrologDatabaseMonad  [IntBindingState T]
      resolve' usf [] stack =  (usf:) <$> backtrack stack

      resolve' usf (nextGoal:gs) stack = do
        trace $ "resolve':"
        trace usf
        trace $  (nextGoal,gs,stack)

        branches <- getBranches usf nextGoal gs
        choose usf gs branches stack

      getBranches ::  IntBindingState T -> Goal -> [Goal] -> PrologDatabaseMonad [Branch]
      getBranches usf nextGoal gs = do
        clauses  <- asks (getClauses nextGoal)
        clauses' <- lift $ freshenClauses clauses
        lift $ join <$>  forM clauses' unifyM
          where
            unifyM :: Clause -> PrologMonad [Branch]
            unifyM clause = do
              put usf
              trace $ "unify:" ++ show (nextGoal,lhs clause)
              unified <- (Just <$> unify nextGoal (lhs clause))  `catchError` (\e -> return Nothing)
              case unified of
                Nothing -> return []
                Just u  -> do
                  trace $ "unified:" ++ show unified
                  usf' <- get
                  return [(usf', rhs clause ++ gs)]

      choose :: IntBindingState T -> [Goal] -> [Branch] -> Stack -> PrologDatabaseMonad [IntBindingState T]
      choose  _usf _gs  (_branches@[]) stack = backtrack stack
      choose   usf  gs ((u',gs'):alts) stack = resolve' u' gs' ((usf,gs,alts) : stack)

      backtrack ::   Stack -> PrologDatabaseMonad [ IntBindingState T ]
      backtrack  []                  =   return (fail "Goal cannot be resolved!")
      backtrack  ((u,gs,alts):stack) =   do
        trace $ "backtrack:" ++ show ((u,gs,alts):stack)
        choose  u gs alts stack


freshenClauses :: [Clause] -> PrologMonad [Clause]
freshenClauses clauses = do
  (UClauseList freshened) <- freshenAll (UClauseList clauses)
  return freshened
