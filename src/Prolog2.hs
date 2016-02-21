module Prolog2
   ( Term(..), T(..) , atom, cons,nil
   , Clause(..), rhs
   , UClause(..)
   , Atom,  Program, Goal
   , PrologT
   , runPrologT , execPrologT, evalPrologT
   , getFreeVar, getFreeVars
   , resolve , resolveToTerms
   )
where

-- import Parser2
-- import Quote2
import Interpreter2
import Syntax2
