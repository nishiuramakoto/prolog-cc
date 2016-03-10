{-# LANGUAGE OverloadedStrings
  #-}

{-# OPTIONS_GHC -w #-}

module PrologSpec (spec) where

import TestImport
import Test.QuickCheck

import Control.Exception (evaluate)
import Control.Monad.Identity
import qualified Data.Text as T
import Data.Either

import Language.Prolog2 hiding (clause)
import Language.Prolog2.Syntax


empty = return []

clause lhs rhs = return $ UClause lhs rhs
struct  s x     = UTerm $ TStruct s [x]
struct2 s x y   = UTerm $ TStruct s [x,y]
struct3 s x y z = UTerm $ TStruct s [x,y,z]

not' = struct  "\\+"
(|||)  = struct2 ";"

(|=|)   = struct2 "="
(|\=|)   = struct2 "\\="
(|<|)   = struct2 "<"
(|>|)   = struct2 ">"
(|=<|)  = struct2 "=<"
(|>=|)  = struct2 ">="
(|=:=|) = struct2 "=:="
(|=\=|) = struct2 "=\\="
(|==|)  = struct2 "=="
(|@<|)  = struct2 "@<"
is = struct2 "is"
(|+|) = struct2 "+"
(|-|) = struct2 "-"
(|*|) = struct2 "*"
(|/|) = struct2 "/"

infixr 0 |||
infixr 1 |=| , |\=|, |==|
infixr 2 `is`, |=:=|, |=\=|, |<|, |=<|, |>|,|>=|, |@<|
infixl 3 |+|, |-|
infixl 4 |*|, |/|

num n = atom (T.pack $ show n)
one = num 1
two = num 2
three = num 3
four  = num 4
[a,b,c,d,e] = map atom ["a","b","c","d","e"]


plist :: [Term] -> Term
plist = foldr cons nil


bear     = atom "bear"
elephant = atom "elephant"
cat      = atom "cat"

big   = struct "big"
small = struct "small"
brown = struct "brown"
black = struct "black"
gray  = struct "gray"
dark  = struct "dark"


program1  :: PrologT Identity Program
program1 = do
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

goal1 :: PrologT Identity [Goal]
goal1 = do
  x <- getFreeVar
  return [ dark x,big x ]

goal1a :: PrologT Identity [Goal]
goal1a = do
  x <- getFreeVar
  return [ dark x , dark x]


------------------------ Program 3 (n queens) ------------------------
queens = struct2 "queens"
queens3 = struct3 "queens3"
attack = struct2 "attack"
attack3 = struct3 "attack3"
selectq = struct3 "selectq"
rangeList2 = struct3 "rangeList2"

program3 :: PrologT Identity Program
program3 = do
  sequence $ [ do [n,qs,ns] <- getFreeVars 3
                  clause (queens n qs)  [ rangeList2 (num 1) n ns
                                        , queens3 ns nil qs ]
             , do [unplacedQs,safeQs, qs, q, unplacedQs1] <- getFreeVars 5
                  clause (queens3 unplacedQs safeQs qs)  [ selectq q unplacedQs unplacedQs1
                                                         , not' (attack q safeQs)
                                                         , queens3 unplacedQs1 (cons q safeQs) qs ]
             , do qs <- getFreeVar
                  clause (queens3 nil qs qs)            []

             , do [x,xs] <- getFreeVars 2
                  clause (attack x xs)                  [ attack3 x one xs ]

             , do [x,n,y,wildcard] <- getFreeVars 4
                  clause (attack3 x n (cons y wildcard))   [ (x |=:=| (y |+|  n)) ]
--                                                             ||| (x |=:=| (y |-| n)) ]
             , do [x,n,y,wildcard] <- getFreeVars 4
                  clause (attack3 x n (cons y wildcard))   [ (x |=:=| (y |-| n)) ]

             , do [x,n,ys,n1,wildcard] <- getFreeVars 5
                  clause (attack3 x n (cons wildcard ys)) [ n1 `is` (n |+| one)
                                                          , attack3 x n1 ys ]

             , do [x,xs] <- getFreeVars 2
                  clause (selectq x (cons x xs) xs) []
             , do [x,y,ys,zs] <- getFreeVars 4
                  clause (selectq x (cons y ys) (cons y zs)) [ selectq x ys zs ]

             , do [m,n] <- getFreeVars 2
                  clause (rangeList2 m n (cons m nil))  [ m |>=| n ]
             , do [m,n,tail,m1] <- getFreeVars 4
                  clause (rangeList2 m n (cons m tail)) [ m |<| n
                                                        , m1 `is` (m |+| one)
                                                        , rangeList2 m1 n tail ]
             ]


goal3 :: Int ->  PrologT Identity [Goal]
goal3 n = do [qs,l,x,xs] <- getFreeVars 4
--            return [ not' (attack three (plist [one])) ]
                           -- return [ attack3 one one (plist [two]) ]
--            return [ rangeList2 (num 1) (num 0) qs ]
--            return [ selectq c (plist [a,b,c,d ]) l ]
             return [ queens (num n) qs ]


member = struct2 "member"
program5 = do
  [x,tail,head] <- getFreeVars 3
  sequence
    [ clause (member x (cons x tail)) []
    , clause (member x (cons head tail)) [member x tail]
    ]

--------------------------------------------------------------------------
conc = struct3 "conc"
program9 :: PrologT Identity Program
program9 = do
  [l,l1,l2,l3,x] <- getFreeVars 5
  sequence
    [ clause (conc nil l l) []
    , clause (conc (cons x l1) l2 (cons x l3)) [ conc l1 l2 l3 ]
    ]


-----------------------------------------------------------------------------------------------------


ok =  True `shouldBe` True
failure = False `shouldBe` True

run :: PrologT Identity Program -> PrologT Identity [Goal] -> Either RuntimeError [[Term]]
run prog goal = runIdentity $ evalPrologT $ do { ps <- prog ; gs <- goal ; resolveToTerms ps gs }

right :: Either a b -> b
right (Right x) = x

shouldBeRight :: (Show b, Eq b) => Either a b -> b -> IO ()
shouldBeRight (Left x) _ = error "should be right"
shouldBeRight (Right x) y = x `shouldBe` y

spec :: Spec
spec =  do
  describe "Prelude.head" $ do
    it "returns the first element of a list" $ do
      head [23 ..] `shouldBe` (23 :: Int)

    it "returns the first element of an *arbitrary* list" $
      property $ \x xs -> head (x:xs) == (x :: Int)

    it "throws an exception if used with an empty list" $ do
      evaluate (head []) `shouldThrow` anyException

  describe "Program1 Goal1" $ do
    it "says a dark and big animal is a bear" $ do
      run program1 goal1 `shouldBeRight` [[bear]]

  describe "Program1 Goal1a" $ do
    it "says dark animals are cats and bears" $ do
      run program1 goal1a `shouldBeRight` [[cat] , [bear]]

  describe "Arithmetic operators" $ do
    it "says 1 < 2" $ do
      let program2 = return []
          goal2    = return [ atom "1" |<|  atom "2" ]
      run program2 goal2 `shouldBeRight` [[]]


    it "says: 1 > 2 or 3 > 1" $ do
      let prog = return []
          goal = return [ atom "1" |>|  atom "2"  ||| atom "3" |>| atom "1" ]
      run prog goal `shouldBeRight` [[] ]

    it "says: 1 < 2 or 3 > 1" $ do
      let prog = return []
          goal = return [ atom "1" |<|  atom "2"  ||| atom "3" |>| atom "1" ]
      run prog goal `shouldBeRight` [[],[] ]

    it "says: 1 < 2 , 3 > 1 or 5 > 2" $ do
      let prog = return []
          goal = return [ atom "1" |<|  atom "2"  ||| atom "3" |>| atom "1" ||| atom "5" |>| atom "2" ]
      run prog goal `shouldBeRight` [[] ,[], [] ]

    it "says: 1 < 2 , 3 > 1 and 5 > 2" $ do
      let prog = return []
          goal = return [ atom "1" |<|  atom "2"  , atom "3" |>| atom "1" , atom "5" |>| atom "2" ]
      run prog goal `shouldBeRight` [[] ]

  describe "n-queens" $ do
    it "says 0-queens has one solution" $ do
      length (right (run program3 (goal3 0))) `shouldBe` 1

    it "says 1-queens has one solution" $ do
      length (right (run program3 (goal3 1))) `shouldBe` 1

    it "says 2-queens has no solutions" $ do
      length (right (run program3 (goal3 2))) `shouldBe` 0

    it "says 3-queens has no solutions" $ do
      length (right (run program3 (goal3 3))) `shouldBe` 0

    it "says 4-queens has two solutions" $ do
      length (right (run program3 (goal3 4))) `shouldBe` 2

    it "says 5-queens has 10 solutions" $ do
      length (right (run program3 (goal3 5))) `shouldBe` 10

    it "says 6-queens has 4 solutions" $ do
      length (right (run program3 (goal3 6))) `shouldBe` 4

    -- Very slow( ~ 30s) , needs further optimization
    -- Or even implement the WAM

    -- it "says 7-queens has 40 solutions" $ do
    --   length (right (run program3 (goal3 7))) `shouldBe` 40

    -- it "says 8-queens has 40 solutions" $ do
    --   length (right (run program3 (goal3 8))) `shouldBe` 92


  describe "cons" $ do
    it "can construct a list of elements" $ do
      let  goal   = do x <- getFreeVar
                       return [x |=| cons (atom "a") (cons (atom "b") nil) ]
      run empty goal `shouldBeRight` [[plist [atom "a", atom "b"]]]

  describe "member" $ do

    it "tests whether an element is a member of a list" $ do
      let goal = do x <- getFreeVar
                    return [ member x (plist [a,b,c,d]) ]

      run program5 goal `shouldBeRight` [[a],[b],[c],[d]]

    it "can also be used to generate lists" $ do
      let goal = do [l,x,y,z] <- getFreeVars 4
                    return [ l |=| plist[ x,y,z] ,  member a l , member b l , member c l ]

      length (right ( run program5 goal)) `shouldBe` 6

    it "can be used to generate lists of any length" $ do
      let goal = do [l,x,y,z,w] <- getFreeVars 5
                    return [ l |=| plist [x,y,z,w] ,  member a l , member b l , member c l , member d l]
      length (right ( run program5 goal)) `shouldBe` 24

    it "can also be used to translate a list" $ do
      let pair = struct2 "pair"
      let [one,two,three,uno,dos,tres] = map atom ["one","two","three","uno","dos","tres" ]
      let dictList = plist [ pair one uno , pair two dos, pair three tres]
      let goal = do [dict,sp,en] <- getFreeVars 3
                    return [ dict |=| dictList
                           , member (pair two sp) dict
                           , member (pair en tres) dict ]

      run program5 goal `shouldBeRight` [ [dictList, dos , three  ]]
    -- program 9

  describe "conc" $ do
    it "concatenates lists" $ do

      let goal9 = do
            l <- getFreeVar
            return [ conc (plist [a,b,c]) (plist [one,two,three]) l ]

      run program9 goal9 `shouldBeRight` [[plist [a,b,c,one,two,three]]]

    it "can also be used to generate sublists of a list" $ do
      let goal10 = do  [l1,l2] <- getFreeVars 2
                       return [ conc l1 l2 (plist [a,b,c]) ]
      length (right $ run program9 goal10) `shouldBe` 4

    it "can also be used to split a list" $ do
      let months = ["jan","feb","mar","apr","may","jun","jul","aug","sep","oct","nov","dec"]
      let [apr,may,jun] = map atom ["apr", "may", "jun" ]
      let goal11 = do [month1,month2,wildcard,wildcard2] <- getFreeVars 4
                      return $ [ conc wildcard (cons month1 (cons may (cons month2 wildcard2)))
                                 (plist (map atom months)) ]

      case run program9 goal11 of
        Right [[apr , jun , _ , _  ]] -> ok
        _                             -> failure


    -- Program 12 --
    -- TODO
