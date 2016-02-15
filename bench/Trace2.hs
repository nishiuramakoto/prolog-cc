{-# LANGUAGE ViewPatterns
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  , IncoherentInstances
  , ScopedTypeVariables
  , DeriveTraversable
  , OverloadedStrings
  #-}

module Trace2 where
-- require icu libraries


import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity
import Control.Unification
import Control.Unification.IntVar
import Data.Text.ICU
import Data.Text.ICU.Replace
import Data.Text(Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Maybe (isJust)
import Syntax2

class Trace m a where
  trace :: a -> m ()

instance MonadIO m => Trace m String where
  trace x =  liftIO $  putStrLn $ x

instance (MonadIO m, Trace m a, Trace m b) => Trace m (a,b) where
  trace (a,b) =  trace a >> trace b

instance (MonadIO m, Trace m a, Trace m b,Trace m c) => Trace m (a,b,c) where
  trace (a,b,c) =  trace a >> trace b >> trace c

instance (MonadIO m, Trace m a, Trace m b,Trace m c,Trace m d) => Trace m (a,b,c,d) where
  trace (a,b,c,d) =  trace a >> trace b >> trace c >> trace d

instance MonadIO m => Trace m (IntBindingState T) where
  trace x = liftIO $ T.putStrLn $ replaceAll "(-\\d{5}\\d+)"  (rtfn f) (T.pack (show x))
    where
      f :: Match -> Text
      f match = case group 1 match of
        Just t  -> case (reads (T.unpack t) :: [(Int,String)]) of
          [(n,[])] -> T.pack ("X" ++ (show (n - minBound)))
          _        -> t
        Nothing -> ""

instance (Show v, Show (t (UTerm t v)) ,  MonadIO m) => Trace m (UTerm t v) where
  trace x = liftIO $ putStrLn $ show x

instance (MonadIO m, Trace m a) => Trace m [a] where
  trace xs = mapM_ trace xs
