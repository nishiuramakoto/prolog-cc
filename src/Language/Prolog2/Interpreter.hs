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
  #-}
module Language.Prolog2.Interpreter
   ( resolve
   , resolveToTerms
   , PrologT
   , runPrologT , evalPrologT, execPrologT
   , getFreeVar , getFreeVars
   , RuntimeError(..)
   , NonUnificationError(..)
   )
where
import Control.Exception.Base
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity
import Control.Unification hiding (getFreeVars)
import qualified Control.Unification as U
import Control.Unification.IntVar
import Data.Text(Text)
import qualified Data.Text as T
import Data.Maybe (isJust)
import Data.Generics (everywhere, mkT)
import Control.Applicative ((<$>),(<*>),(<$),(<*), Applicative(..), Alternative(..))

import Language.Prolog2.Syntax
import Language.Prolog2.Database
import Language.Prolog2.Trace


data NonUnificationError = InstantiationError Term
                         | NonStructGoal Term
                 deriving (Show)

type RuntimeError = Either Failure NonUnificationError

instance Fallible T IntVar RuntimeError where
  occursFailure v t     = Left $ occursFailure v t
  mismatchFailure t1 t2 = Left $ mismatchFailure t1 t2

----------------  TODO: Unroll the monad stack  ----------------
newtype PrologT m a = PrologT { unPrologT :: ExceptT RuntimeError (IntBindingT T m) a }
                        deriving ( Functor
                                 , Applicative
                                 , Monad
                                 , MonadState (IntBindingState T)
                                 , MonadError RuntimeError
                                 )
type PrologDatabaseMonad m a = ReaderT Database (PrologT m) a

instance MonadTrans PrologT where
  lift  m =  PrologT (lift $ lift m)

instance MonadIO m => MonadIO (IntBindingT T m) where
  liftIO = lift . liftIO

instance MonadIO m => MonadIO (PrologT m) where
  liftIO = lift . liftIO

runPrologT :: Monad m => PrologT m a -> m (Either RuntimeError a, IntBindingState T)
runPrologT = runIntBindingT . runExceptT . unPrologT

evalPrologT :: Monad m => PrologT m a -> m (Either RuntimeError a)
evalPrologT = evalIntBindingT . runExceptT . unPrologT

execPrologT :: Monad m => PrologT m a -> m (IntBindingState T)
execPrologT = execIntBindingT . runExceptT . unPrologT
---------------------- End Unrolled Monad stack ----------------------


getFreeVar :: (Applicative m, Monad m) => PrologT m Term
getFreeVar = PrologT $ lift (UVar <$> freeVar)

getFreeVars ::(Applicative m, Monad m) => Int -> PrologT m [Term]
getFreeVars 0 = return []
getFreeVars 1 = getFreeVar >>= return . return
getFreeVars n = do x  <- getFreeVar
                   xs <- getFreeVars (n-1)
                   return (x:xs)


builtins :: Monad m => PrologT m [Clause]
builtins = do
  [x,x',x''] <-  getFreeVars 3
  [a,b,c,d,e] <- getFreeVars 5
  [x0,x1,x2,x3,x4,x5] <- getFreeVars 6
  [y0,y1,y2,y3,y4,y5] <- getFreeVars 6
  [_1,_2,_3,_4,_5,_6] <- getFreeVars 6

  return [ UClause (UTerm (TStruct "="   [x, x])) []
         , UClause (UTerm (TStruct "\\+" [x'])) [x', cut, UTerm (TStruct "false" []) ]
         , UClause (UTerm (TStruct "\\+" [x''])) []

         , UClause (UTerm (TStruct "true" [])) []
         , UClause (UTerm (TStruct "," [a,b])) [a, b]
         , UClause (UTerm (TStruct ";" [c, _1])) [c]
         , UClause (UTerm (TStruct ";" [_2, d])) [d]

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

    is [t, eval->Just n] = [UTerm (TStruct "=" [t, (UTerm (TStruct (T.pack $ show n) [])) ]) ]
    is _                 = [UTerm (TStruct "false" [])]

    eval :: Term -> Maybe Integer
    eval (UTerm (TStruct ((reads . T.unpack) ->[(n,"")]) [])) = return n :: Maybe Integer
    eval (UTerm (TStruct "+"   [t1, t2]))       = (+) <$> eval t1 <*> eval t2
    eval (UTerm (TStruct "*"   [t1, t2]))       = (*) <$> eval t1 <*> eval t2
    eval (UTerm (TStruct "-"   [t1, t2]))       = (-) <$> eval t1 <*> eval t2
    eval (UTerm (TStruct "mod" [t1, t2]))       = mod <$> eval t1 <*> eval t2
    eval (UTerm (TStruct "-" [t]))              = negate <$> eval t
    eval _                        = mzero

type Stack = [(IntBindingState T, [Goal], [Branch])]
type Branch = (IntBindingState T, [Goal])

resolveToTerms :: Monad m =>  Program ->  [Goal] -> PrologT m  [[Term]]
resolveToTerms program goals = do
  vs <- PrologT $ lift ((join <$> mapM (U.getFreeVars) goals)) -- :: IntBindingT T IO [IntVar]) :: PrologT [IntVar]
  usfs <- resolve program goals
  mapM (f (map UVar vs)) usfs
    where
      f :: Monad m => [Term] -> IntBindingState T -> PrologT m [Term]
      f vs usf = do put usf
                    PrologT $ mapM applyBindings vs

-- Yield all unifiers that resolve <goal> using the clauses from <program>.
resolve :: Monad m =>  Program ->  [Goal] -> PrologT  m [IntBindingState T]
resolve program goals = do
  usf <- get
  bs  <- builtins

  numFreeVars <- countFreeVars (bs ++ program)

  bindings <- runReaderT (resolve' 1 numFreeVars usf goals []) (createDB (bs ++ program) ["false","fail"])
  -- trace "Finished:"
  -- traceLn bindings
  return bindings

  where
    resolve' ::  Monad m
                 => Int -> Int -> IntBindingState T -> [Goal] -> Stack
                 -> PrologDatabaseMonad m  [IntBindingState T]
    resolve' depth nf usf gs stack = resolve'' depth usf gs stack
      where
      resolve'' ::  Monad m
                   => Int -> IntBindingState T -> [Goal] -> Stack
                   -> PrologDatabaseMonad m  [IntBindingState T]
      resolve'' depth usf [] stack =  do
        (usf:) <$> backtrack depth stack

      resolve'' depth usf (UTerm (TCut n):gs) stack =  resolve'' depth usf gs (drop n stack)

      resolve'' depth usf (nextGoal:gs) stack = do
        -- traceLn $ "==resolve'=="
        -- traceLn $  ("usf:",usf)
        -- traceLn $  ("goals:",(nextGoal:gs))
        -- traceLn $  ("stack:", stack)

        put usf
        updateNextFreeVar depth

        usf' <- get
        branches <- getBranches usf' nextGoal gs
        -- traceLn $  ("branches:" , show $ length branches, branches)

        choose depth usf gs branches stack

      getBranches ::  Monad m => IntBindingState T -> Goal -> [Goal] -> PrologDatabaseMonad m [Branch]
      getBranches  usf (UVar n) gs = do
        nextGoal <- lift $ PrologT $ applyBindings (UVar n)
        case nextGoal of
          (UVar x) -> throwError $ Right (InstantiationError (UVar x))
          _        -> getBranches usf nextGoal gs

      getBranches  usf nextGoal gs = do

        clauses  <- asks (getClauses nextGoal)
        lift $ do
          clauses' <- freshenClauses clauses
          join <$>  forM clauses' unifyM
        -- trace "nextGoal:" >> traceLn nextGoal
        -- trace "clauses:" >> traceLn clauses
        -- trace "freshenedClauses:" >>  traceLn clauses'

          where
            unifyM :: Monad m => Clause -> PrologT m [Branch]
            unifyM clause = do
              put usf
              -- traceLn $ "CurrentBindings:"
              -- traceLn usf
              -- traceLn $ ("unify:",nextGoal,lhs clause)
              unified <- (Just <$> PrologT (unify nextGoal (lhs clause)))
                         `catchError` (\e -> return Nothing)
              case unified of
                Nothing -> do  -- traceLn "failed to unify:"
                  nextGoal' <- PrologT $ applyBindings nextGoal
                  lhs'      <- PrologT $ applyBindings (lhs clause)
                               -- traceLn $ nextGoal'
                               -- traceLn $ lhs'
                  return []
                Just u  -> do
                  -- traceLn $ ("unified:" , unified)
                  gs'  <-  case nextGoal of
                    UTerm (TStruct n ts) -> do
                      case clause of
                        UClause lhs rhs -> return $ rhs ++ gs
                        UClauseFn lhs fn -> do
                          ts' <- PrologT $ applyBindingsAll ts
                          return $ rhs clause ts' ++ gs
                    UTerm (TCut n)       -> throwError $ Right $ NonStructGoal (UTerm (TCut n))
                    UVar  n              -> throwError $ Right $ NonStructGoal (UVar n)
                  let gs'' = everywhere' shiftCut gs'
                  usf' <- get
                  return [(usf', gs'')]

      choose :: Monad m =>  Int -> IntBindingState T -> [Goal] -> [Branch] -> Stack
             -> PrologDatabaseMonad m [IntBindingState T]
      choose  depth  _usf _gs  (_branches@[]) stack = backtrack depth stack
      choose  depth   usf  gs ((u',gs'):alts) stack = resolve'' (succ depth) u' gs' ((usf,gs,alts) : stack)

      backtrack :: Monad m => Int -> Stack -> PrologDatabaseMonad m [ IntBindingState T ]
      backtrack  _ []                  =   do
        -- traceLn "backtracking an empty stack!"
        return (fail "Goal cannot be resolved!")
      backtrack  depth  ((u,gs,alts):stack) =   do
        -- -- traceLn $ ("backtrack:" , ((u,gs,alts):stack))
        choose (pred depth)   u gs alts stack


shiftCut :: T a -> T a
shiftCut (TCut n) = TCut (succ n)
shiftCut t        = t


freshenClauses :: Monad m => [Clause] -> PrologT m [Clause]
freshenClauses clauses = do
  (UClauseList freshened) <- PrologT $ freshenAll (UClauseList clauses)
  return freshened

countFreeVars :: Monad m => Program -> PrologT m Int
countFreeVars program = maximum <$> mapM count program
  where
    count :: Monad m => Clause -> PrologT m Int
    count (UClause   lhs rhs) = length <$> (PrologT $ lift $ getFreeVarsAll rhs)
    count (UClauseFn lhs fn)  = return 2

updateNextFreeVar depth  =
  modify (\s -> case s of
            IntBindingState nextFreeVar varBindings ->
              IntBindingState (nextFreeVar + 4096 * depth) varBindings )
