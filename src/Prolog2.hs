module Prolog2
   ( Term(..), T(..) , atom
   , Clause(..), rhs
   , UClause(..)
   , Atom,  Program, Goal
   , PrologMonad
   , runPrologMonad , execPrologMonad, evalPrologMonad
   , getFreeVar
   , resolve , resolveToTerms
   )
where

import Syntax2
-- import Parser2
import Interpreter2
