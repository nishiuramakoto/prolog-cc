{-# LANGUAGE
    ViewPatterns
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
   , resolveToTerms
   , PrologMonad
   , runPrologMonad , evalPrologMonad, execPrologMonad
   )
where
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity
import Control.Unification hiding (getFreeVars)
import qualified Control.Unification as U
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

getFreeVar2 = do
  x <- getFreeVar
  y <- getFreeVar
  return (x,y)

builtins :: PrologMonad [Clause]
builtins = do
  x <-  getFreeVar
  a <-  getFreeVar
  b <-  getFreeVar
  c <-  getFreeVar
  d <-  getFreeVar
  (x0,y0) <- getFreeVar2
  (x1,y1) <- getFreeVar2
  (x2,y2) <- getFreeVar2
  (x3,y3) <- getFreeVar2
  (x4,y4) <- getFreeVar2
  (x5,y5) <- getFreeVar2
  return [ UClause (UTerm (TStruct "="   [x, x])) []
         , UClause (UTerm (TStruct "true" [])) []
         , UClause (UTerm (TStruct "," [a,b])) [a, b]

         , UClauseFn (UTerm (TStruct "is"  [x0, y0])) is
         , UClauseFn (UTerm (TStruct "<"   [x1, y1])) (binaryIntegerPredicate (<))
         , UClauseFn (UTerm (TStruct ">"   [x2, y2])) (binaryIntegerPredicate (>))
         , UClauseFn (UTerm (TStruct "=<"  [x3, y3])) (binaryIntegerPredicate (<=))
         , UClauseFn (UTerm (TStruct ">="  [x4, y4])) (binaryIntegerPredicate (>=))
         , UClauseFn (UTerm (TStruct "=:=" [x5, y5])) (binaryIntegerPredicate (==))
         , UClauseFn (UTerm (TStruct "=\\=" [c,d])) (binaryIntegerPredicate (/=))
         ]
  where
    binaryIntegerPredicate :: (Integer -> Integer -> Bool) -> ([Term] -> [Goal])
    binaryIntegerPredicate p [eval->Just n, eval->Just m] | n `p` m = []
    binaryIntegerPredicate p _ = [ UTerm $ TStruct "false" []]
--    binaryIntegerPredicate p _ = [ UTerm $ TStruct "true" []]

    is [t, eval->Just n] = [UTerm (TStruct "=" [t, (UTerm (TStruct (show n) [])) ]) ]
    is _                 = [UTerm (TStruct "false" [])]

    eval :: Term -> Maybe Integer
    eval (UTerm (TStruct (reads->[(n,"")]) [])) = return n :: Maybe Integer
    eval (UTerm (TStruct "+"   [t1, t2]))       = (+) <$> eval t1 <*> eval t2
    eval (UTerm (TStruct "*"   [t1, t2]))       = (*) <$> eval t1 <*> eval t2
    eval (UTerm (TStruct "-"   [t1, t2]))       = (-) <$> eval t1 <*> eval t2
    eval (UTerm (TStruct "mod" [t1, t2]))       = mod <$> eval t1 <*> eval t2
    eval (UTerm (TStruct "-" [t]))              = negate <$> eval t
    eval _                        = mzero

type Stack = [(IntBindingState T, [Goal], [Branch])]
type Branch = (IntBindingState T, [Goal])

resolveToTerms ::  Program ->  [Goal] -> PrologMonad  [[Term]]
resolveToTerms program goals = do
  vs <- lift ((join <$> mapM (U.getFreeVars) goals) :: IntBindingT T IO [IntVar]) :: PrologMonad [IntVar]
  usfs <- resolve program goals
  mapM (f (map UVar vs)) usfs
    where
      f :: [Term] -> IntBindingState T -> PrologMonad [Term]
      f vs usf = do put usf
                    mapM applyBindings vs

-- Yield all unifiers that resolve <goal> using the clauses from <program>.
resolve ::  Program ->  [Goal] -> PrologMonad  [IntBindingState T]
resolve program goals = do
  usf <- get
  bs  <- builtins

  bindings <- runReaderT (resolve' usf goals []) (createDB (bs ++ program) ["false","fail"])
  -- trace "Finished:"
  -- traceLn bindings
  return bindings

  where
      resolve' ::  IntBindingState T -> [Goal] -> Stack  -> PrologDatabaseMonad  [IntBindingState T]
      resolve' usf [] stack =  (usf:) <$> backtrack stack

      resolve' usf (UTerm (TCut n):gs) stack =  resolve' usf gs (drop n stack)

      resolve' usf (nextGoal:gs) stack = do
        -- traceLn $ "==resolve'=="
        -- traceLn $  ("usf:",usf)
        -- traceLn $  ("goals:",(nextGoal:gs))
        -- traceLn $  ("stack:", stack)

        let depth = length stack
        -- trace "depth" >> traceLn (show depth)

        put usf
        lift $ getFreeVars (10 * (depth + 1))
        usf' <- get

        branches <- getBranches usf' nextGoal gs
        -- traceLn $  ("branches:" , show $ length branches, branches)

        choose usf gs branches stack

      getBranches ::  IntBindingState T -> Goal -> [Goal] -> PrologDatabaseMonad [Branch]
      getBranches  usf nextGoal gs = do
        clauses  <- asks (getClauses nextGoal)
        clauses' <- lift $ freshenClauses clauses
        -- trace "nextGoal:" >> traceLn nextGoal
        -- trace "clauses:" >> traceLn clauses
        -- trace "freshenedClauses:" >>  traceLn clauses'

        lift $ join <$>  forM clauses' unifyM
          where
            unifyM :: Clause -> PrologMonad [Branch]
            unifyM clause = do
              put usf
              -- traceLn $ "CurrentBindings:"
              -- traceLn usf
              -- traceLn $ ("unify:",nextGoal,lhs clause)
              unified <- (Just <$> unify nextGoal (lhs clause))  `catchError` (\e -> return Nothing)
              case unified of
                Nothing -> do  -- traceLn "failed to unify:"
                               nextGoal' <- applyBindings nextGoal
                               lhs'      <- applyBindings (lhs clause)
                               -- traceLn $ nextGoal'
                               -- traceLn $ lhs'
                               return []
                Just u  -> do
                  -- traceLn $ ("unified:" , unified)
                  usf' <- get
                  gs'  <-  case nextGoal of
                        UTerm (TStruct n ts) -> do
                          ts' <- applyBindingsAll ts
                          return $ rhs clause ts' ++ gs
                        UTerm _              -> error "unifying nonterm  for arithmetic goal"
                        UVar  _              -> error "unifying variable for arithmetic goal"
                  let gs'' = everywhere' shiftCut gs'
                  return [(usf', gs'')]

      choose :: IntBindingState T -> [Goal] -> [Branch] -> Stack -> PrologDatabaseMonad [IntBindingState T]
      choose  _usf _gs  (_branches@[]) stack = backtrack stack
      choose   usf  gs ((u',gs'):alts) stack = resolve' u' gs' ((usf,gs,alts) : stack)

      backtrack ::   Stack -> PrologDatabaseMonad [ IntBindingState T ]
      backtrack  []                  =   do
        -- traceLn "backtracking an empty stack!"
        return (fail "Goal cannot be resolved!")
      backtrack  ((u,gs,alts):stack) =   do
        -- -- traceLn $ ("backtrack:" , ((u,gs,alts):stack))
        choose  u gs alts stack


shiftCut :: T a -> T a
shiftCut (TCut n) = TCut (succ n)
shiftCut t        = t


freshenClauses :: [Clause] -> PrologMonad [Clause]
freshenClauses clauses = do
  (UClauseList freshened) <- freshenAll (UClauseList clauses)
  return freshened
