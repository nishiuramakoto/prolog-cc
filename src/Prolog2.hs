module Prolog2
   ( Term(..), T(..) , atom, cons,nil
   , Clause(..), rhs
   , UClause(..)
   , Atom,  Program, Goal , Failure
   , PrologT
   , runPrologT , execPrologT, evalPrologT
   , getFreeVar, getFreeVars
   , resolve , resolveToTerms
   , consult , consultString
   , parseQuery
   , term,terms,clause,program,whitespace
   , ppTerm, ppClause, ppProgram
   )
where

import Parser2
-- import Quote2
import Interpreter2
import Syntax2
