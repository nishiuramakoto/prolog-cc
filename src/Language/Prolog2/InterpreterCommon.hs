{-# LANGUAGE
    LiberalTypeSynonyms
  , CPP
  #-}

module Language.Prolog2.InterpreterCommon
       ( getFreeVar
       , getFreeVars
       , resolveToTerms
       , resolve
       , countFreeVars
       )
where

#ifdef YESOD
import Import hiding(cons,trace,mapM_,sort,get, maximum)
import qualified Prelude
#endif

import qualified Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Unification hiding (getFreeVars)
import qualified Control.Unification as U
import Control.Unification.IntVar
import qualified Data.Text as T
import qualified Data.Map as Map

import Language.Prolog2.Types
import Language.Prolog2.Syntax
import Language.Prolog2.Database(Database)
import Language.Prolog2.SystemDatabase
import qualified Language.Prolog2.Database as DB


getFreeVar :: (Monad m) =>  m Term
getFreeVar = (UVar <$> freeVar)

-- getFreeVar :: (Monad m, MonadProlog t) => t m Term
-- getFreeVar = liftProlog $ PrologT $ lift $ (UVar <$> freeVar)

-- getFreeVars ::(Monad m, MonadProlog t) => Int -> t m [Term]
getFreeVars 0 = return []
getFreeVars 1 = getFreeVar >>= return . return
getFreeVars n = do x  <- getFreeVar
                   xs <- getFreeVars (n-1)
                   return (x:xs)


resolveToTerms ::  forall t state m.
                   ( MonadPrologDatabase t m
                   , MonadReader Database (t m)
                   , MonadState (IntBindingState T) (t m)
                   , MonadLogger m
                   , MonadLogger (t m))
                   => state ->  ModuleName ->  [Goal] -> Database -> SystemDatabase state (t m)
                   -> t m   [[Term]]
resolveToTerms st mod goals db sysdb = do
  db <- ask
  -- $(logInfo) $ T.pack $ "resolveToTerms: " ++ show (DB.size db)

  vs <- liftProlog $ PrologT $ lift $ U.getFreeVarsAll goals
  usfs <- resolve st mod goals db sysdb
  Prelude.mapM (f (map UVar vs)) usfs
    where
      f :: [Term] -> IntBindingState T -> t m  [Term]
      f vs usf = do put usf
                    liftProlog $ PrologT $ Prelude.mapM applyBindings vs


-- Yield all unifiers that resolve <goal> using the clauses from <program>.
resolve :: ( MonadPrologDatabase t m
           , MonadReader Database (t m)
           , MonadState (IntBindingState T) (t m)
           , MonadLogger m
           , MonadLogger (t m))
           => state -> ModuleName ->  [Goal] -> Database -> SystemDatabase state (t m)
           -> t m  [IntBindingState T]
resolve st  mod goals db sysdb = do
  local (\_ -> db) (resolveWithDatabase st mod 1 goals [] sysdb)

resolveWithDatabase ::  ( MonadPrologDatabase t m
                        , MonadReader Database (t m)
                        , MonadState (IntBindingState T) (t m)
                        , MonadLogger m
                        , MonadLogger (t m))
                        => state -> ModuleName -> Int -> [Goal] -> Stack -> SystemDatabase state (t m)
                        -> t m  [IntBindingState T]
resolveWithDatabase  st mod depth goals stack sysdb = do
  db <- ask
  usf <- get
  numFreeVars <- liftProlog $ countFreeVars (DB.dbUserTable db)
  resolve'' st mod depth numFreeVars usf goals stack sysdb

resolve'' :: forall t state m.
             ( MonadPrologDatabase t m
             , MonadReader Database (t m)
             , MonadState (IntBindingState T) (t m)
             , MonadLogger m
             , MonadLogger (t m) )
             => state -> ModuleName -> Int -> Int -> IntBindingState T -> [Goal] -> Stack
             -> SystemDatabase state (t m)
             -> t m [IntBindingState T]

resolve'' st mod depth nf usf [] stack sysdb  =  do
        (usf:) <$> backtrack st mod depth nf stack sysdb

resolve'' st mod depth nf usf (UTerm (TCut n):gs) stack sysdb =
  resolve'' st mod depth nf usf gs (drop n stack) sysdb

resolve'' st mod depth nf usf (nextGoal:gs) stack sysdb = do
        -- trace $ show $ "==resolve'=="
        -- trace $ show $  ("usf:",usf)
        -- trace $ show $  ("goals:",(nextGoal:gs))
        -- trace $ show $  ("stack:", stack)
  -- $logInfo $ T.pack $ "resolve''" ++ show nf
  let msystem = getSystemClause nextGoal sysdb
  db <- ask
  -- $logInfo $ T.pack $ show ("system db size=", Map.size sysdb)
  case msystem of
    Just (UClauseM lhs m) ->
      m resolve'' st mod depth nf usf (nextGoal:gs) stack sysdb
    Nothing -> do


      put usf
      updateNextFreeVar depth nf
      usf' <- get

      let f = getBranches mod usf' nextGoal gs :: PrologDatabaseT m [Branch]
      branches <- liftPrologDatabase $ f

      choose st mod depth nf usf gs branches stack sysdb

choose :: ( MonadPrologDatabase t m
          , MonadReader Database (t m)
          , MonadState (IntBindingState T) (t m)
          , MonadLogger m
          , MonadLogger (t m) )
          => state -> ModuleName -> Int -> Int -> IntBindingState T -> [Goal] -> [Branch] -> Stack
          -> SystemDatabase state (t m)
          -> t m   [IntBindingState T]
choose  st mod depth  nf _usf _gs  (_branches@[]) stack sysdb  = backtrack st mod depth nf stack sysdb
choose  st mod depth  nf usf  gs ((u',gs'):alts)  stack sysdb  =
  resolve'' st mod (succ depth) nf u' gs' ((usf,gs,alts) : stack) sysdb

backtrack :: ( MonadPrologDatabase t  m
             , MonadReader Database  (t m)
             , MonadState (IntBindingState T) (t m)
             , MonadLogger m
             , MonadLogger (t m))
             => state -> ModuleName -> Int -> Int -> Stack
             -> SystemDatabase state (t m)
             -> t m  [ IntBindingState T ]
backtrack _  _ _ _ [] _               =  return (fail "Goal cannot be resolved!")
backtrack st mod depth nf  ((u,gs,alts):stack) sysdb = choose st mod (pred depth) nf  u gs alts stack sysdb



getBranches ::  (MonadLogger m) => ModuleName -> IntBindingState T -> Goal -> [Goal]
                -> PrologDatabaseT m [Branch]
getBranches  mod usf (UVar n) gs = do
        nextGoal <-  liftProlog $ PrologT $ applyBindings (UVar n)
        case nextGoal of
          (UVar x) -> throwError $ Right (InstantiationError (UVar x))
          _        -> getBranches mod usf nextGoal gs

getBranches  mod usf nextGoal gs = do

        clauses  <- asks (DB.getClauses mod nextGoal)
        $logInfo $ T.pack $ show (mod, nextGoal, clauses)
        liftProlog $ do
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


shiftCut :: T a -> T a
shiftCut (TCut n) = TCut (succ n)
shiftCut t        = t


freshenClauses :: (Functor m, Applicative m, Monad m) => [Clause] -> PrologT m [Clause]
freshenClauses clauses = do
  (UClauseList freshened) <- PrologT $ freshenAll (UClauseList clauses)
  return freshened

countFreeVars :: (Monad m, Traversable t, Foldable t) => t [Clause] -> PrologT m Int
countFreeVars program = maximum' <$> mapM countClauses program
  where
    countClauses :: Monad m => [Clause] -> PrologT m Int
    countClauses cs = maximum' <$> mapM countClause cs

    countClause :: (Monad m) => Clause -> PrologT m Int
    countClause (UClause   lhs rhs') = do rvs <- PrologT $ lift $ getFreeVarsAll rhs'
                                          lvs <- PrologT $ lift $ getFreeVarsAll [lhs]
                                          return $ length rvs + length lvs
    countClause (UClauseFn lhs _fn)  = do lvs <- PrologT $ lift $ getFreeVarsAll [lhs]
                                          return $ 2 + length lvs

    -- maximum' xs | Prelude.null xs =  error "countFreeVars: empty list"
    maximum' xs | Prelude.null xs = 0
    maximum' xs = Prelude.maximum xs

updateNextFreeVar :: MonadState (IntBindingState t) m => Int -> Int -> m ()
updateNextFreeVar depth nf  =
  modify (\s -> case s of
            IntBindingState nextFreeVar' varBindings' ->
              IntBindingState (nextFreeVar' +  nf + 1024  ) varBindings' )
