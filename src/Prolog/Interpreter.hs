{-# LANGUAGE ViewPatterns, GeneralizedNewtypeDeriving, FlexibleInstances, FlexibleContexts, UndecidableInstances, IncoherentInstances , ScopedTypeVariables #-}
module Interpreter
   ( resolve
   )
where
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Data.Maybe (isJust)
import Data.Generics (everywhere, mkT)
import Control.Applicative ((<$>),(<*>),(<$),(<*), Applicative(..), Alternative(..))
import Data.List (sort, nub)

import Syntax
import Unifier
import Database


builtins :: [Clause]
builtins =
   [ Clause (Struct "="   [var "X", var "X"]) []
   , Clause (Struct "\\+" [var "A"]) [var "A", cut, Struct "false" []]
   , Clause (Struct "\\+" [var "A"]) []
   , Clause (Struct "true" []) []
   , Clause (Struct "," [var "A", var "B"]) [var "A", var "B"]
   , Clause (Struct ";" [var "A", Wildcard]) [var "A"]
   , Clause (Struct ";" [Wildcard, var "B"]) [var "B"]
   , ClauseFn (Struct "is"  [var "L", var "R"]) is
   , ClauseFn (Struct "<"   [var "N", var "M"]) (binaryIntegerPredicate (<))
   , ClauseFn (Struct ">"   [var "N", var "M"]) (binaryIntegerPredicate (>))
   , ClauseFn (Struct "=<"  [var "N", var "M"]) (binaryIntegerPredicate (<=))
   , ClauseFn (Struct ">="  [var "N", var "M"]) (binaryIntegerPredicate (>=))
   , ClauseFn (Struct "=:=" [var "N", var "M"]) (binaryIntegerPredicate (==))
   , ClauseFn (Struct "=\\=" [var "N", var "M"]) (binaryIntegerPredicate (/=))
   ]
 where
   binaryIntegerPredicate :: (Integer -> Integer -> Bool) -> ([Term] -> [Goal])
   binaryIntegerPredicate p [eval->Just n, eval->Just m] | n `p` m = []
   binaryIntegerPredicate p _ = [Struct "false" []]

   is [t, eval->Just n] = [Struct "=" [t, Struct (show n) []]]
   is _                 = [Struct "false" []]

   eval (Struct (reads->[(n,"")]) []) = return n :: Maybe Integer
   eval (Struct "+" [t1, t2])   = (+) <$> eval t1 <*> eval t2
   eval (Struct "*" [t1, t2])   = (*) <$> eval t1 <*> eval t2
   eval (Struct "-" [t1, t2])   = (-) <$> eval t1 <*> eval t2
   eval (Struct "mod" [t1, t2]) = mod <$> eval t1 <*> eval t2
   eval (Struct "-" [t])        = negate <$> eval t
   eval _                       = mzero

type Stack = [(Unifier, [Goal], [Branch])]
type Branch = (Unifier, [Goal])

trace :: (MonadIO m , Show a) => a -> m ()
trace x = liftIO $ putStrLn $ show x
-- Yield all unifiers that resolve <goal> using the clauses from <program>.
resolve :: (Functor m, Monad m, MonadIO m) => Program -> [Goal] -> m [Unifier]
resolve program goals = map cleanup <$> runReaderT (resolve' 1 [] goals []) (createDB (builtins ++ program) ["false","fail"])   -- NOTE Is it a good idea to "hardcode" the builtins like this?
  where
      cleanup = filter ((\(VariableName i _) -> i == 0) . fst)

      resolve' :: (Functor m, MonadReader Database m , MonadIO m )
                  => Int -> Unifier -> [Goal] -> Stack -> m [Unifier]
      resolve' depth usf []         stack = (cleanup usf:) <$> backtrack depth stack
      resolve' depth usf (Cut n:gs) stack =  resolve' depth usf gs (drop n stack)

      resolve' depth usf (nextGoal:gs) stack = do
        -- trace $ ("getBranches" , depth, usf , nextGoal, gs)
        -- trace $ ("getBranches" , nextGoal,gs)
         branches <- getBranches depth usf nextGoal gs
         -- trace $ ("branches",length branches, branches)
         choose depth usf gs branches stack

      getBranches :: (MonadReader Database m , MonadIO m)
                     => Int -> Unifier -> Goal -> [Goal] -> m [Branch]
      getBranches depth usf nextGoal gs = do
            clauses <- asks (getClauses nextGoal)
            return  [ f u clause |
                     clause <- renameVars depth clauses,
                     u      <- unify (apply usf nextGoal) (lhs clause) ]
            where
              f :: Unifier ->  Clause -> Branch
              f u clause = let newGoals = rhs clause (map snd u)
                               u' = usf +++ u
                               gs'  = map (apply u') $ newGoals ++ gs
                               gs'' = everywhere (mkT shiftCut) gs'
                           in (u', gs'')

      choose :: (Monad m, MonadReader Database m, MonadIO m)
                => Int -> Unifier -> [Goal] -> [Branch] -> Stack -> m [Unifier]
      choose depth _usf _gs  (_branches@[]) stack = backtrack depth stack
      choose depth  usf  gs ((u',gs'):alts) stack = resolve' (succ depth) u' gs' ((usf,gs,alts) : stack)

      backtrack :: (Monad m, MonadReader Database m , MonadIO m)
                   => Int -> Stack -> m [ Unifier ]
      backtrack _     []                  =   return (fail "Goal cannot be resolved!")
      backtrack depth ((u,gs,alts):stack) =   choose (pred depth) u gs alts stack

      shiftCut :: Goal -> Goal
      shiftCut (Cut n) = Cut (succ n)
      shiftCut t       = t

      renameVars :: Int -> [Clause] ->  [Clause]
      renameVars depth = everywhere $ mkT $ \(VariableName _ v) -> VariableName depth v
