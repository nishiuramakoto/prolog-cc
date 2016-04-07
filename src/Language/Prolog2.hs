module Language.Prolog2
   ( Term, T(..) , atom, cons,nil
   , Clause, rhs
   , UClause(..)
   , Atom,  Program, Goal , Failure , RuntimeError, ParseError
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

import Language.Prolog2.Parser
-- import Quote2
import Language.Prolog2.Interpreter
import Language.Prolog2.Syntax
import Text.Parsec
