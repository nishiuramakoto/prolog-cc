{-# LANGUAGE OverloadedStrings, QuasiQuotes, StandaloneDeriving #-}
module Main (main) where

import Language.Prolog (consult, resolve, VariableName(..), Term(..))
import Language.Prolog.Quote (ts)

import System.Environment (getArgs)
import Control.DeepSeq (deepseq, NFData(rnf))

instance NFData Term where
   rnf (Struct a ts) = rnf a `seq` rnf ts
   rnf (Var v)       = rnf v
   rnf (Cut n)       = rnf n
   rnf Wildcard      = ()
instance NFData VariableName where
   rnf (VariableName i s) = rnf i `seq` rnf s


main = do
   args <- getArgs
   let n = case args of { [] -> 6; (x:_) -> read x }
   Right p <- consult "bench/queens.pl"
   putStrLn "Starting benchmark..."
--   qs <- resolve p [ts| [a] |]
   qs <- resolve p [ts|queens($n,Qs)|]
--   Right p <- consult "test2.pl"
--   qs <- resolve p [ts|member(X,[a,b,c])|]
   putStrLn $ qs `deepseq` "Number of solutions: " ++ show (length qs)

main2 = do
   args <- getArgs
   let n = case args of { [] -> 6; (x:_) -> read x }
   parseResult <- consult "bench/queens1.pl"
   case parseResult of
     Right p -> do
       putStrLn "Starting benchmark..."
       qs <- resolve p [ts|template(S),solution(S)|]
       putStrLn $ qs `deepseq` "Number of solutions: " ++ show (length qs)
     Left err -> putStrLn (show err)
