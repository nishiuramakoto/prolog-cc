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

module Language.Prolog2.Trace where
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
import Language.Prolog2.Syntax

class MonadIO m => Trace m a where
  trace    :: a -> m ()
  traceLn  :: a -> m ()
  traceLn x = do trace x
                 liftIO $ putStrLn ""

instance MonadIO m => Trace m String where
  trace   x =  liftIO $  putStr   $ x

instance (MonadIO m , Trace m a) => Trace m (Maybe a) where
  trace (Just x) = do liftIO $ putStr "Just "
                      trace x
  trace Nothing  = liftIO $ putStr "Nothing"

instance (MonadIO m, Trace m a, Trace m b) => Trace m (a,b) where
    trace (a,b) =  trace ("(" :: String) >> sepBy (trace ("," :: String)) ([trace a,trace b]) >> (trace (")" :: String))

instance (MonadIO m, Trace m a, Trace m b,Trace m c) => Trace m (a,b,c) where
  trace (a,b,c) =  trace ("(" :: String) >> sepBy (trace ("," :: String)) ([trace a,trace b,trace c]) >> (trace (")" :: String))

instance (MonadIO m, Trace m a, Trace m b,Trace m c,Trace m d) => Trace m (a,b,c,d) where
    trace (a,b,c,d) =  trace ("(" :: String) >> sepBy (trace ("," :: String)) ([trace a,trace b,trace c,trace d]) >> (trace (")" :: String))

sepBy :: (MonadIO m ) => m () -> [m ()] -> m ()
sepBy s [] = return ()
sepBy s [m] = m
sepBy s (m:ms) = m >> s >> sepBy s ms

instance MonadIO m => Trace m (IntBindingState T) where
  trace x = liftIO $ T.putStr $ replaceAll "(-\\d{5}\\d+)"  (rtfn f) (T.pack (show x))
    where
      f :: Match -> Text
      f match = case group 1 match of
        Just t  -> case (reads (T.unpack t) :: [(Int,String)]) of
          [(n,[])] -> T.pack ("X" ++ (show (n - minBound)))
          _        -> t
        Nothing -> ""


-- instance (Show v, Show (t (UTerm t v)) ,  MonadIO m) => Trace m (UTerm t v) where
--  trace x = liftIO $ putStrLn $ show x

instance (MonadIO m) => Trace m (UTerm T IntVar) where
  trace x = liftIO $ T.putStr $ ppTerm x

instance (MonadIO m, Trace m a) => Trace m [a] where
  trace xs = mapM_ trace xs

instance (MonadIO m) => Trace m (UClause Term) where
  trace (UClause lhs rhs) = do trace lhs
                               trace (" :- " :: String)
                               trace  rhs
                               traceStr "."
  trace (UClauseFn lhs fn) = do trace lhs
                                traceStr " :- <FUNCTION>."

traceStr :: MonadIO m => String -> m ()
traceStr x = trace x
