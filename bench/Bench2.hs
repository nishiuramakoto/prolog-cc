{-# LANGUAGE OverloadedStrings, QuasiQuotes, StandaloneDeriving , FlexibleInstances #-}
module Bench2 (main) where

import Prolog2

import System.Environment (getArgs)
import Control.DeepSeq (deepseq, NFData(rnf))
import Control.Unification
import Control.Unification.IntVar
import Control.Unification.Types
import Control.Monad.Identity
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity
import Control.Unification
import Control.Unification.IntVar
import Data.Maybe (isJust)
import Data.Generics (everywhere, mkT)
import Control.Applicative ((<$>),(<*>),(<$),(<*), Applicative(..), Alternative(..))

instance NFData (UTerm T IntVar) where
   rnf (UTerm (TStruct a ts)) = rnf a `seq` rnf ts



bear     = atom "bear"
elephant = atom "elephant"
cat      = atom "cat"

big   x = UTerm $ TStruct "big"   [x]
small x = UTerm $ TStruct "small" [x]
brown x = UTerm $ TStruct "brown" [x]
black x = UTerm $ TStruct "black" [x]
gray  x = UTerm $ TStruct "gray"  [x]
dark  x = UTerm $ TStruct "dark"  [x]

program  :: PrologMonad Program
program = do
  z  <- getFreeVar
  z' <- getFreeVar
  return [ UClause (big bear) []
         , UClause (big elephant) []
         , UClause (small cat) []
         , UClause (brown bear) []
         , UClause (black cat) []
         , UClause (gray elephant) []
         , UClause (dark z)  [black z]
         , UClause (dark z') [brown z']
         ]

goals :: PrologMonad [Goal]
goals = do
  x <- getFreeVar
--  return [ big x, gray x]
  --return [ big x, dark x]
  return [ dark x,big x ]

main = do
   args <- getArgs
   let n = case args of { [] -> 6; (x:_) -> read x }

   putStrLn "Starting benchmark..."

   let monad = (do { ps <- program ; gs <- goals ;  resolve ps gs }) :: PrologMonad [IntBindingState T]

   qs <- evalPrologMonad $ monad

   case qs of
     Left  failure -> putStrLn $ "failure:" ++ show failure
     -- Right qs      -> putStrLn $ qs `deepseq` "Number of solutions: " ++ show (length qs)
     Right qs      -> do putStrLn $ "Number of solutions: " ++ show (length qs)
                         putStrLn $ show qs
