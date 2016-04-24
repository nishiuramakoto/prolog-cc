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

#ifdef YESOD_INTERPRETER_IO
module Language.Prolog2.InterpreterIO
   ( resolve
   , resolveToTerms
   , PrologT
   , runPrologT , evalPrologT, execPrologT
   , getFreeVar , getFreeVars
   , RuntimeError
   , NonUnificationError(..)
   )  where

#else
module Language.Prolog2.Interpreter
   ( resolve
   , resolveToTerms
   , PrologT
   , runPrologT , evalPrologT, execPrologT
   , getFreeVar , getFreeVars
   , RuntimeError
   , NonUnificationError(..)
   )  where
#endif


#ifdef YESOD_INTERPRETER_IO
import Import hiding(cons,trace,mapM_,sort,get, maximum)
import qualified Prelude

#elif defined YESOD
import Import hiding(cons,trace,mapM_,sort,get, maximum)
import qualified Prelude
import Control.Monad.CC.CCCxe
import Data.Typeable
import CCGraph
import Inquire
import Form
#endif

-----------------------------------------------------------------------------------------------

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

#ifdef YESOD
#define CONTEXT   ()
#define USERMONAD (CC CCP Handler)
type UserState   = CCState
trace = lift . lift . lift . $logInfo . T.pack
#else
#define CONTEXT    (Monad m)
#define USERMONAD  m
type UserState = ()
#endif


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


-- TODO: Clean up those ugly macros with some nifty type class
resolveToTerms ::  CONTEXT =>  UserState ->  Program ->  [Goal] -> PrologT USERMONAD  [[Term]]
resolveToTerms st program goals = do
  vs <- PrologT $ lift $ U.getFreeVarsAll goals
  usfs <- resolve st program goals
  -- lift $ lift $ $(logInfo) $ T.pack $ "resolveToTerms: " ++ show usfs
  Prelude.mapM (f (map UVar vs)) usfs
    where
      f :: (Functor m, Applicative m, Monad m) => [Term] -> IntBindingState T -> PrologT m [Term]
      f vs usf = do put usf
                    PrologT $ Prelude.mapM applyBindings vs

-- Yield all unifiers that resolve <goal> using the clauses from <program>.
resolve ::  CONTEXT  => UserState -> Program ->  [Goal] -> PrologT (USERMONAD) [IntBindingState T]
resolve st program goals = do
  usf <- get
  bs  <- builtins

  numFreeVars <- countFreeVars (bs ++ program)

  bindings <- runReaderT (resolveWithDatabase st 1 numFreeVars usf goals [])
              (createDB (bs ++ program) ["false","fail"])
  return bindings


resolveWithDatabase ::  CONTEXT  => UserState -> Int -> Int -> IntBindingState T -> [Goal] -> Stack
                        -> PrologDatabaseMonad (USERMONAD)  [IntBindingState T]
resolveWithDatabase  depth nf usf_ gs_ stack_ = resolve'' depth nf usf_ gs_ stack_
  where
      resolve'' :: CONTEXT => UserState -> Int -> Int -> IntBindingState T -> [Goal] -> Stack
                   -> PrologDatabaseMonad (USERMONAD)  [IntBindingState T]

      resolve'' st depth nf usf [] stack =  do
        (usf:) <$> backtrack st depth nf stack

      resolve'' st depth nf usf (UTerm (TCut n):gs) stack =  resolve'' st depth nf usf gs (drop n stack)


      resolve'' st depth nf  usf goals'@(UTerm (TStruct "asserta" [fact]):gs) stack = do
        nf' <- lift $ countFreeVars [UClause fact [] ]
        local (asserta fact) $ resolve'' st depth (max nf nf')  usf gs stack

----------------  Yesod specific language extensions  ----------------
#ifdef YESOD
      resolve'' st depth nf usf (UTerm (TStruct "inquire_bool" [query,v]):gs) stack = do
        st'@(CCState _ form) <- lift $ lift $ inquirePrologBool st query
        -- lift $ lift $ lift $ $logInfo $ T.pack $ show form
        let result = case form of
              Just (CCFormResult form') ->  case cast form' of
                Just (FormSuccess (PrologInquireBoolForm True))
                  -> UTerm (TStruct "true" [])
                _ -> UTerm (TStruct "false" [])
              Nothing -> UTerm (TStruct "false" [])


        resolve'' st' depth nf usf ((UTerm (TStruct "=" [v, result])) : gs) stack
#endif
---------------------------------------------------------------------

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

      choose :: CONTEXT => UserState -> Int -> Int -> IntBindingState T -> [Goal] -> [Branch] -> Stack
             -> PrologDatabaseMonad (USERMONAD) [IntBindingState T]
      choose  st depth  nf _usf _gs  (_branches@[]) stack = backtrack st depth nf stack
      choose  st depth  nf usf  gs ((u',gs'):alts)  stack = resolve'' st (succ depth) nf u' gs' ((usf,gs,alts) : stack)


      backtrack :: CONTEXT => UserState -> Int -> Int -> Stack
                           -> PrologDatabaseMonad (USERMONAD) [ IntBindingState T ]
      backtrack _  _ _ []                  =  return (fail "Goal cannot be resolved!")
      backtrack st depth nf  ((u,gs,alts):stack) = choose st (pred depth) nf  u gs alts stack

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
    count' (UClause   lhs rhs') = do rvs <- PrologT $ lift $ getFreeVarsAll rhs'
                                     lvs <- PrologT $ lift $ getFreeVarsAll [lhs]
                                     return $ length rvs + length lvs
    count' (UClauseFn lhs _fn)  = do lvs <- PrologT $ lift $ getFreeVarsAll [lhs]
                                     return $ 2 + length lvs


updateNextFreeVar :: MonadState (IntBindingState t) m => Int -> Int -> m ()
updateNextFreeVar depth nf  =
  modify (\s -> case s of
            IntBindingState nextFreeVar' varBindings' ->
              IntBindingState (nextFreeVar' +  nf + 1024  ) varBindings' )
