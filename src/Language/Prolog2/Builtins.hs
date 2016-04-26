module Language.Prolog2.Builtins
       (builtins,
        createBuiltinDatabase
       )
where
#ifdef YESOD
import Import.NoFoundation
import qualified Prelude
#endif
import Language.Prolog2.Syntax
import Language.Prolog2.Types
import Language.Prolog2.InterpreterCommon
import Language.Prolog2.Database
import qualified Data.Text as T

builtins :: (Functor m, Applicative m, Monad m ) => PrologT m [Clause]
builtins = do
  [x,x',x''] <-  getFreeVars 3
  [a,b,c,d,_e] <- getFreeVars 5
  [x0,x1,x2,x3,x4,x5] <- getFreeVars 6
  [y0,y1,y2,y3,y4,y5] <- getFreeVars 6
  [_1,_2,_3,_4,_5,_6] <- getFreeVars 6

  return [ UClause (UTerm (TStruct "="   [x, x])) []
         , UClause (UTerm (TStruct "\\+" [x'])) [x', cut, UTerm (TStruct "false" []) ]
         , UClause (UTerm (TStruct "\\+" [x''])) []

         , UClause (UTerm (TStruct "true" [])) []
         , UClause (UTerm (TStruct "," [a,b])) [a, b]
         , UClause (UTerm (TStruct ";" [c, _1])) [c]
         , UClause (UTerm (TStruct ";" [_2, d])) [d]

         , UClauseFn (UTerm (TStruct "is"  [x0, y0])) is
         , UClauseFn (UTerm (TStruct "<"   [x1, y1])) (binaryIntegerPredicate (<))
         , UClauseFn (UTerm (TStruct ">"   [x2, y2])) (binaryIntegerPredicate (>))
         , UClauseFn (UTerm (TStruct "=<"  [x3, y3])) (binaryIntegerPredicate (<=))
         , UClauseFn (UTerm (TStruct ">="  [x4, y4])) (binaryIntegerPredicate (>=))
         , UClauseFn (UTerm (TStruct "=:=" [x5, y5])) (binaryIntegerPredicate (==))
         , UClauseFn (UTerm (TStruct "=\\=" [c,d])) (binaryIntegerPredicate (/=))
         ]
  where
    binaryIntegerPredicate :: (Integer -> Integer -> Bool) -> ([Term] -> [Goal])
    binaryIntegerPredicate p [eval->Just n, eval->Just m] | n `p` m = []
    binaryIntegerPredicate _p _ = [ UTerm $ TStruct "false" []]
--    binaryIntegerPredicate p _ = [ UTerm $ TStruct "true" []]

    is [t, eval->Just n] = [UTerm (TStruct "=" [t, (UTerm (TStruct (T.pack $ show n) [])) ]) ]
    is _                 = [UTerm (TStruct "false" [])]

    eval :: Term -> Maybe Integer
    eval (UTerm (TStruct ((Prelude.reads . T.unpack) ->[(n,"")]) [])) = return n :: Maybe Integer
    eval (UTerm (TStruct "+"   [t1, t2]))       = (+) <$> eval t1 <*> eval t2
    eval (UTerm (TStruct "*"   [t1, t2]))       = (*) <$> eval t1 <*> eval t2
    eval (UTerm (TStruct "-"   [t1, t2]))       = (-) <$> eval t1 <*> eval t2
    eval (UTerm (TStruct "mod" [t1, t2]))       = mod <$> eval t1 <*> eval t2
    eval (UTerm (TStruct "-" [t]))              = negate <$> eval t
    eval _                        = mzero


createBuiltinDatabase :: Monad m => PrologT m Database
createBuiltinDatabase = do
  createDB <$> builtins <*>  pure ["false","fail"]
