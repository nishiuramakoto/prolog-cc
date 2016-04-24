{-# OPTIONS_GHC -w #-}

module ParserSpec (spec) where

import TestImport hiding (runIO)
import Test.QuickCheck


import Text.Parsec
import Text.Parsec.Expr hiding (Assoc(..))
import qualified Text.Parsec.Expr  as Parsec
import qualified Text.Parsec.Token as P
import qualified Text.Parsec.Char  as P
import qualified Text.Parsec.Error as P
import qualified Text.Parsec.Pos   as P
import qualified Text.Parsec.Combinator as P


-- numbers = P.commaSep P.integer

fromRight :: Show a => Either a b -> b
fromRight (Right x) = x
fromRight (Left x) = error $ "must be right:" ++ show x

shouldBeRight :: (Show b, Eq b) => Either a b -> b -> IO ()
shouldBeRight (Left x) _ = error "should be right"
shouldBeRight (Right x) y = x `shouldBe` y

ok =  True `shouldBe` True
failure = False `shouldBe` True

spec :: Spec
spec = do
  describe "unicode parser" $ do
    it "parses a char" $ do
      parse (P.char 'a')  "" "a" `shouldBe` Right 'a'

    it "parses a unicode char" $ do
      parse (P.char 'あ')  "" "あ" `shouldBe` Right 'あ'

    it "parses a unicode word" $ do
      parse (P.many1 P.letter)  "" "あいうえお" `shouldBe` Right "あいうえお"

    it "parses a unicode word" $ do
      parse (P.many1 P.alphaNum)  "" "あいうえお " `shouldBe` Right "あいうえお"

    it "parses a unicode word" $ do
      parse (P.many1 P.alphaNum)  "" "あいうえお " `shouldBe` Right "あいうえお"
