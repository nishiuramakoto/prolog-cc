{-# LANGUAGE
    TypeFamilies
  , StandaloneDeriving
  , CPP
  #-}


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
       , MonadProlog(..), MonadPrologDatabase(..)
       ) where

#ifdef YESOD
import Import.NoFoundation hiding(cons,trace,mapM_,sort,get, maximum)
#endif


import             Language.Prolog2.Syntax
import             Language.Prolog2.Database
import             Language.Prolog2.SystemDatabase

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
newtype PrologDatabaseT m a =
  PrologDatabaseT { unPrologDatabaseT :: ReaderT Database m a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader  Database
           )

deriving instance (MonadState (IntBindingState T) m) => MonadState (IntBindingState T) (PrologDatabaseT m)
deriving instance (MonadError RuntimeError m) => MonadError RuntimeError (PrologDatabaseT m)


class  (MonadTrans t) => MonadPrologTrans t  where
  liftProlog  :: Monad m => PrologT m a -> t m a
  liftBinding :: Monad m =>  IntBindingT T m a -> t m a

instance Monad m => MonadPrologTrans PrologT  where
  liftProlog  = id
  liftBinding = PrologT . lift

instance MonadPrologTrans m => MonadProlog (PrologDatabaseT m)  where
  liftProlog  = lift . liftProlog
  liftBinding = lift . liftBinding

class (MonadProlog m, MonadReader Database m)
      => MonadPrologDatabase m where
  liftPrologDatabase :: (Monad n, MonadTrans t, t n ~ m) => PrologDatabaseT n a ->  m a

instance Monad m => MonadPrologDatabase (PrologDatabaseT m) where
  liftPrologDatabase = id

instance MonadIO m => MonadIO (IntBindingT T m) where
  liftIO = lift . liftIO

instance MonadTrans PrologT where
  lift  m =  PrologT (lift $ lift m)

instance MonadIO m => MonadIO (PrologT m) where
  liftIO = lift . liftIO

instance MonadTrans PrologDatabaseT  where
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
