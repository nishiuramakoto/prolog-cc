module Language.Prolog2.InterpreterCommon
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

import Language.Prolog2.Types
import Language.Prolog2.Syntax
import Language.Prolog2.Database(Database)
import qualified Language.Prolog2.Database as DB

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


getBranches ::  ( Monad m)
                => IntBindingState T -> Goal -> [Goal] -> PrologDatabaseT m [Branch]
getBranches  usf (UVar n) gs = do
        nextGoal <-  PrologDatabaseT $ lift $ PrologT $ applyBindings (UVar n)
        case nextGoal of
          (UVar x) -> throwError $ Right (InstantiationError (UVar x))
          _        -> getBranches usf nextGoal gs

getBranches  usf nextGoal gs = do

        clauses  <- asks (DB.getClauses nextGoal)
        PrologDatabaseT $ lift $ do
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

countFreeVars :: (Monad m, Traversable t) => t [Clause] -> PrologT m Int
countFreeVars program = Prelude.maximum <$> mapM countClauses program
  where
    countClauses :: Monad m => [Clause] -> PrologT m Int
    countClauses cs = Prelude.maximum <$> mapM countClause cs

    countClause :: (Monad m) => Clause -> PrologT m Int
    countClause (UClause   lhs rhs') = do rvs <- PrologT $ lift $ getFreeVarsAll rhs'
                                          lvs <- PrologT $ lift $ getFreeVarsAll [lhs]
                                          return $ length rvs + length lvs
    countClause (UClauseFn lhs _fn)  = do lvs <- PrologT $ lift $ getFreeVarsAll [lhs]
                                          return $ 2 + length lvs


updateNextFreeVar :: MonadState (IntBindingState t) m => Int -> Int -> m ()
updateNextFreeVar depth nf  =
  modify (\s -> case s of
            IntBindingState nextFreeVar' varBindings' ->
              IntBindingState (nextFreeVar' +  nf + 1024  ) varBindings' )
