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
   )
where

#ifdef YESOD
import Import hiding(cons,trace,mapM_,sort,get, maximum)
import qualified Prelude
import Control.Monad.CC.CCCxe
import Data.Typeable
import CCGraph
import Inquire
import Form

#endif

import qualified Control.Monad
-- import Control.Exception.Base
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
-- import Control.Monad.Identity hiding (mapM)
import Control.Unification hiding (getFreeVars)
import qualified Control.Unification as U
import Control.Unification.IntVar
-- import Data.Text(Text)
import qualified Data.Text as T
-- import Data.Maybe (isJust)
-- import Data.Generics (everywhere, mkT)
-- import Control.Applicative ((<$>),(<*>),(<$),(<*), Applicative(..), Alternative(..))

import Language.Prolog2.Syntax
import Language.Prolog2.Database

-- import Language.Prolog2.Trace


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


builtins :: (Functor m, Applicative m, Monad m ) => PrologT m [Clause]
builtins = do
  [x,x',x''] <-  getFreeVars 3
  [a,b,c,d,_e] <- getFreeVars 5
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
    binaryIntegerPredicate _p _ = [ UTerm $ TStruct "false" []]
--    binaryIntegerPredicate p _ = [ UTerm $ TStruct "true" []]

    is [t, eval->Just n] = [UTerm (TStruct "=" [t, (UTerm (TStruct (T.pack $ show n) [])) ]) ]
    is _                 = [UTerm (TStruct "false" [])]

    eval :: Term -> Maybe Integer
    eval (UTerm (TStruct ((Prelude.reads . T.unpack) ->[(n,"")]) [])) = return n :: Maybe Integer
    eval (UTerm (TStruct "+"   [t1, t2]))       = (+) <$> eval t1 <*> eval t2
    eval (UTerm (TStruct "*"   [t1, t2]))       = (*) <$> eval t1 <*> eval t2
    eval (UTerm (TStruct "-"   [t1, t2]))       = (-) <$> eval t1 <*> eval t2
    eval (UTerm (TStruct "mod" [t1, t2]))       = mod <$> eval t1 <*> eval t2
    eval (UTerm (TStruct "-" [t]))              = negate <$> eval t
    eval _                        = mzero

type Stack = [(IntBindingState T, [Goal], [Branch])]
type Branch = (IntBindingState T, [Goal])

#ifdef YESOD
type UserState   = CCState
type UserMonad   = CC CCP Handler
#else
type UserState = ()
#endif

-- TODO: Clean up those ugly ifdefs with a nifty type class
#ifdef YESOD
resolveToTerms ::  UserState ->  Program ->  [Goal] -> PrologT UserMonad  [[Term]]
#else
resolveToTerms ::  Monad m
                   => UserState -> Program ->  [Goal] -> PrologT m  [[Term]]
#endif

resolveToTerms st program goals = do
  vs <- PrologT $ lift $ U.getFreeVarsAll goals
  usfs <- resolve st program goals
  Prelude.mapM (f (map UVar vs)) usfs
    where
      f :: (Functor m, Applicative m, Monad m) => [Term] -> IntBindingState T -> PrologT m [Term]
      f vs usf = do put usf
                    PrologT $ Prelude.mapM applyBindings vs

-- Yield all unifiers that resolve <goal> using the clauses from <program>.
#ifdef YESOD
resolve ::  UserState -> Program ->  [Goal] -> PrologT UserMonad [IntBindingState T]
#else
resolve ::  Monad m  => UserState -> Program ->  [Goal] -> PrologT m [IntBindingState T]
#endif

resolve st program goals = do
  usf <- get
  bs  <- builtins

  numFreeVars <- countFreeVars (bs ++ program)

  bindings <- runReaderT (resolve' st 1 numFreeVars usf goals []) (createDB (bs ++ program) ["false","fail"])
  -- trace "Finished:"
  -- traceLn bindings
  return bindings

  where
#ifdef YESOD
    resolve' ::  UserState -> Int -> Int -> IntBindingState T -> [Goal] -> Stack
                 -> PrologDatabaseMonad UserMonad  [IntBindingState T]
#else
    resolve' ::   Monad m => UserState -> Int -> Int -> IntBindingState T -> [Goal] -> Stack
                    -> PrologDatabaseMonad m  [IntBindingState T]
#endif

    resolve' depth_ _nf usf_ gs_ stack_ = resolve'' depth_ usf_ gs_ stack_
      where

#ifdef YESOD
      resolve'' :: UserState -> Int -> IntBindingState T -> [Goal] -> Stack
                   -> PrologDatabaseMonad UserMonad  [IntBindingState T]
#else
      resolve'' :: Monad m => UserState -> Int -> IntBindingState T -> [Goal] -> Stack
                   -> PrologDatabaseMonad m  [IntBindingState T]
#endif

      resolve'' st depth usf [] stack =  do
        (usf:) <$> backtrack st depth stack

      resolve'' st depth usf (UTerm (TCut n):gs) stack =  resolve'' st depth usf gs (drop n stack)


----------------  Yesod specific language extensions  ----------------
#ifdef YESOD
      resolve'' st depth usf (UTerm (TStruct "inquire_bool" [query,v]):gs) stack = do
        st'@(CCState _ form) <- lift $ lift $ inquirePrologBool st query

        let result = case cast form of
              Just (FormSuccess (PrologInquireBoolForm True))
                -> UTerm (TStruct "true" [])
              _ -> UTerm (TStruct "false" [])
        resolve'' st' depth usf ((UTerm (TStruct "=" [v, result])) : gs) stack
#endif
---------------------------------------------------------------------

      resolve'' st depth usf (nextGoal:gs) stack = do
        -- traceLn $ "==resolve'=="
        -- traceLn $  ("usf:",usf)
        -- traceLn $  ("goals:",(nextGoal:gs))
        -- traceLn $  ("stack:", stack)

        put usf
        updateNextFreeVar depth

        usf' <- get
        branches <- getBranches usf' nextGoal gs
        -- traceLn $  ("branches:" , show $ length branches, branches)

        choose st depth usf gs branches stack

      getBranches ::  Monad m
                      => IntBindingState T -> Goal -> [Goal] -> PrologDatabaseMonad m [Branch]
      getBranches  usf (UVar n) gs = do
        nextGoal <- lift $ PrologT $ applyBindings (UVar n)
        case nextGoal of
          (UVar x) -> throwError $ Right (InstantiationError (UVar x))
          _        -> getBranches usf nextGoal gs

      getBranches  usf nextGoal gs = do

        clauses  <- asks (getClauses nextGoal)
        lift $ do
          clauses' <- freshenClauses clauses
          join <$>  Control.Monad.forM clauses' unifyM
        -- trace "nextGoal:" >> traceLn nextGoal
        -- trace "clauses:" >> traceLn clauses
        -- trace "freshenedClauses:" >>  traceLn clauses'

          where
            unifyM ::  Monad m => Clause -> PrologT m [Branch]
            unifyM clause = do
              put usf
              -- traceLn $ "CurrentBindings:"
              -- traceLn usf
              -- traceLn $ ("unify:",nextGoal,lhs clause)
              unified <- (Just <$> PrologT (unify nextGoal (lhs clause)))
                         `catchError` (\_e -> return Nothing)
              case unified of
                Nothing -> do  -- traceLn "failed to unify:"
                  _nextGoal' <- PrologT $ applyBindings nextGoal
                  _lhs'      <- PrologT $ applyBindings (lhs clause)
                               -- traceLn $ nextGoal'
                               -- traceLn $ lhs'
                  return []
                Just _u  -> do
                  -- traceLn $ ("unified:" , unified)
                  gs'  <-  case nextGoal of
                    UTerm (TStruct _n ts) -> do
                      case clause of
                        UClause _lhs rhs' -> return $ rhs' ++ gs
                        UClauseFn _lhs _fn -> do
                          ts' <- PrologT $ applyBindingsAll ts
                          return $ rhs clause ts' ++ gs
                    UTerm (TCut n)       -> throwError $ Right $ NonStructGoal (UTerm (TCut n))
                    UVar  n              -> throwError $ Right $ NonStructGoal (UVar n)
                  let gs'' = everywhere' shiftCut gs'
                  usf' <- get
                  return [(usf', gs'')]

#ifdef YESOD
      choose :: UserState -> Int -> IntBindingState T -> [Goal] -> [Branch] -> Stack
             -> PrologDatabaseMonad UserMonad [IntBindingState T]
#else
      choose :: Monad m => UserState -> Int -> IntBindingState T -> [Goal] -> [Branch] -> Stack
             -> PrologDatabaseMonad m [IntBindingState T]
#endif

      choose  st depth  _usf _gs  (_branches@[]) stack = backtrack st depth stack
      choose  st depth   usf  gs ((u',gs'):alts) stack = resolve'' st (succ depth) u' gs' ((usf,gs,alts) : stack)


#ifdef YESOD
      backtrack :: UserState -> Int -> Stack -> PrologDatabaseMonad UserMonad [ IntBindingState T ]
#else
      backtrack :: Monad m => UserState -> Int -> Stack -> PrologDatabaseMonad m  [ IntBindingState T ]
#endif
      backtrack _  _ []                  =  return (fail "Goal cannot be resolved!")
      backtrack st depth  ((u,gs,alts):stack) = choose st (pred depth)  u gs alts stack


shiftCut :: T a -> T a
shiftCut (TCut n) = TCut (succ n)
shiftCut t        = t


freshenClauses :: (Functor m, Applicative m, Monad m) => [Clause] -> PrologT m [Clause]
freshenClauses clauses = do
  (UClauseList freshened) <- PrologT $ freshenAll (UClauseList clauses)
  return freshened

countFreeVars :: (Functor m, Applicative m, Monad m) => Program -> PrologT m Int
countFreeVars program = Prelude.maximum <$> Control.Monad.mapM count' program
  where
    count' :: (Functor m, Applicative m, Monad m) => Clause -> PrologT m Int
    count' (UClause   _lhs rhs') = length <$> (PrologT $ lift $ getFreeVarsAll rhs')
    count' (UClauseFn _lhs _fn)  = return 2


updateNextFreeVar :: MonadState (IntBindingState t) m => Int -> m ()
updateNextFreeVar depth  =
  modify (\s -> case s of
            IntBindingState nextFreeVar' varBindings' ->
              IntBindingState (nextFreeVar' + 4096 * depth) varBindings' )
