module Language.Prolog2.Types
       ( NonUnificationError(..)
       , IntBindingT
       , IntBindingState(..)
       , T(..)
       , RuntimeError
       , PrologT(..)
       , PrologDatabaseT(..)
       , runPrologT
       , evalPrologT
       , execPrologT
       , runPrologDatabaseT
       , evalPrologDatabaseT
       , execPrologDatabaseT
       , MonadProlog(..)
       ) where

#ifdef YESOD
import Import.NoFoundation hiding(cons,trace,mapM_,sort,get, maximum)
#endif


import             Language.Prolog2.Database
import             Language.Prolog2.Syntax

import             Control.Monad.Reader
import             Control.Monad.State
import             Control.Monad.Except
-- import Control.Monad.Identity hiding (mapM)
import             Control.Unification hiding (getFreeVars)
import             Control.Unification.IntVar


data NonUnificationError = InstantiationError Term
                         | NonStructGoal Term
                 deriving (Show)

type RuntimeError = Either Failure NonUnificationError

instance Fallible T IntVar RuntimeError where
  occursFailure v t     = Left $ occursFailure v t
  mismatchFailure t1 t2 = Left $ mismatchFailure t1 t2

----------------  Prolog monad  ----------------
newtype PrologT m a = PrologT { unPrologT :: ExceptT RuntimeError (IntBindingT T m) a }
                        deriving ( Functor
                                 , Applicative
                                 , Monad
                                 , MonadState (IntBindingState T)
                                 , MonadError RuntimeError
                                 )
newtype PrologDatabaseT m a = PrologDatabaseT { unPrologDatabaseT :: ReaderT Database (PrologT m) a }
                              deriving (Functor
                                       , Applicative
                                       , Monad
                                       , MonadReader Database
                                       , MonadState  (IntBindingState T)
                                       , MonadError  RuntimeError
                                       )

class MonadProlog t where
  liftProlog :: Monad m => PrologT m a -> t m a

instance MonadProlog PrologDatabaseT where
  liftProlog = PrologDatabaseT . lift

instance MonadIO m => MonadIO (IntBindingT T m) where
  liftIO = lift . liftIO

instance MonadTrans PrologT where
  lift  m =  PrologT (lift $ lift m)

instance MonadIO m => MonadIO (PrologT m) where
  liftIO = lift . liftIO

instance MonadTrans PrologDatabaseT where
  lift  m =  PrologDatabaseT (lift $ lift m)


instance MonadIO m => MonadIO (PrologDatabaseT m) where
  liftIO = lift . liftIO



runPrologT :: Monad m => PrologT m a -> m (Either RuntimeError a, IntBindingState T)
runPrologT = runIntBindingT . runExceptT . unPrologT

evalPrologT :: Monad m => PrologT m a -> m (Either RuntimeError a)
evalPrologT = evalIntBindingT . runExceptT . unPrologT

execPrologT :: Monad m => PrologT m a -> m (IntBindingState T)
execPrologT = execIntBindingT . runExceptT . unPrologT

runPrologDatabaseT :: Monad m => PrologDatabaseT m a -> Database
                      -> m (Either RuntimeError a, IntBindingState T)
runPrologDatabaseT p d = runPrologT $ runReaderT (unPrologDatabaseT p) d

evalPrologDatabaseT :: Monad m => PrologDatabaseT m a -> Database
                       -> m (Either RuntimeError a)
evalPrologDatabaseT p d = evalPrologT $ runReaderT (unPrologDatabaseT p) d

execPrologDatabaseT :: Monad m => PrologDatabaseT m a -> Database
                       -> m (IntBindingState T)
execPrologDatabaseT p d = execPrologT $ runReaderT (unPrologDatabaseT p) d

-------------------------------------------------------------------------
