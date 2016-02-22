module Language.Prolog
   ( Term(..), var, cut
   , Clause(..), rhs
   , VariableName(..), Atom, Unifier, Substitution, Program, Goal
   , unify, unify_with_occurs_check
   , apply
   , resolve
   , (+++)
   , consult, parseQuery
   , program, whitespace, comment, clause, terms, term, bottom, vname
   )
where

import Language.Prolog.Syntax
import Language.Prolog.Parser
import Language.Prolog.Unifier
import Language.Prolog.Interpreter
