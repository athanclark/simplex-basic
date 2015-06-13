module Linear.Simplex.BasicSpec (main, spec) where

import Linear.Simplex.BasicSpec.Types
import Linear.Simplex.Basic
import Linear.Simplex.Basic.Types
import Linear.Grammar

import Test.Hspec
import Test.QuickCheck
import Data.Maybe
import qualified Data.Map as M
import Control.Applicative


main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "`populate`" $ do
    it "should be idempotent" $
      property prop_populate_Idempotent
    it "should have a uniform result" $
      property prop_populate_Uniform
  describe "`diffZip`" $
    it "should be all 0 when ran on self" $
      property prop_diffZip_Zero
  describe "`flatten`" $ do
    it "should have 1 at its oriented column in it's result" $
      property prop_flatten_One
    it "should be idempotent" $
      property prop_flatten_Idempotent
  describe "`compensate`" $
    it "should have 0 at its oriented column in it's result" $
      property prop_compensate_Zero
  describe "`nextRow`" $
    it "should have the smallest ratio" $
      property prop_nextRow_MinRatio
  describe "`nextColumn`" $
    it "should have the smallest value" $
      property prop_nextColumn_MinValue
  describe "unit tests" $ do
    it "should pass Finite Mathematics Lesson 4, Example 1" $
      let f1 = EVar "x" .+. EVar "y" .+. EVar "z" .<=. ELit 600
          f2 = EVar "x" .+. (3 :: Double) .*. EVar "y" .<=. ELit 600
          f3 = (2 :: Double) .*. EVar "x" .+. EVar "z" .<=. ELit 900
          obj = EVar "M" .==. (60 :: Double) .*. EVar "x" .+. (90 :: Double) .*. EVar "y"
                .+. (300 :: Double) .*. EVar "z"
          test = M.fromList (simplex (standardForm obj) (standardForm <$> [f1,f2,f3]) Max)
      in
      test `shouldBe` M.fromList [("M",180000),("x",0),("y",0),("z",600),("s0",0),("s1",600),("s2",300)]
    it "should pass Finite Mathematics Lesson 4, Example 2" $
      let f1 = EVar "a" .+. EVar "b" .+. EVar "c" .<=. ELit 100
          f2 = (5 :: Double) .*. EVar "a" .+. (4 :: Double) .*. EVar "b"
               .+. (4 :: Double) .*. EVar "c" .<=. ELit 480
          f3 = (40 :: Double) .*. EVar "a" .+. (20 :: Double) .*. EVar "b"
               .+. (30 :: Double) .*. EVar "c" .<=. ELit 3200
          obj = EVar "M" .==. (70 :: Double) .*. EVar "a" .+. (210 :: Double) .*. EVar "b"
                .+. (140 :: Double) .*. EVar "c"
          test = M.fromList (simplex (standardForm obj) (standardForm <$> [f1,f2,f3]) Max)
      in
      test `shouldBe` M.fromList [("M",21000),("a",0),("b",100),("c",0),("s0",0),("s1",80),("s2",1200)]
    it "should pass Example of Simplex Procedure" $
      let f1 = (2 :: Double) .*. EVar "x1" .+. EVar "x2" .+. EVar "x3" .<=. ELit 14
          f2 = (4 :: Double) .*. EVar "x1" .+. (2 :: Double) .*. EVar "x2"
               .+. (3 :: Double) .*. EVar "x3" .<=. ELit 28
          f3 = (2 :: Double) .*. EVar "x1" .+. (5 :: Double) .*. EVar "x2"
               .+. (5 :: Double) .*. EVar "x3" .<=. ELit 30
          obj = EVar "Z" .==. EVar "x1" .+. (2 :: Double) .*. EVar "x2"
                .+. (-1 :: Double) .*. EVar "x3"
          test = M.fromList (simplex (standardForm obj) (standardForm <$> [f1,f2,f3]) Max)
      in
      test `shouldBe` M.fromList [("Z",13),("x1",5),("x2",4),("x3",0),("s0",0),("s1",0),("s2",0)]



prop_populate_Idempotent :: [IneqSlack] -> Bool
prop_populate_Idempotent x = populate x == populate (populate x)

prop_populate_Uniform :: [IneqSlack] -> Property
prop_populate_Uniform x =
  length x > 0 ==>
    let x' = map (\z -> length (getStdVars $ slackIneq z)
                      + length (slackVars z)) $ populate x
    in
    allTheSame x'

prop_diffZip_Zero :: EquSlackQC -> Bool
prop_diffZip_Zero x' =
  let x = fromEquSlack x'
      r  = diffZip x x
      ss = map varCoeff $ slackVars r
      c  = getStdConst $ slackIneq r
      vs = map varCoeff $ getStdVars $ slackIneq r
  in
  all (== 0) (ss ++ vs ++ [c])

prop_flatten_One :: IneqSlack -> Int -> Property
prop_flatten_One x n =
  n >= 0 && n < length (getStdVars $ slackIneq x) ==>
    let r = varCoeff (getStdVars (slackIneq $ flatten x n) !! n) in
    r == 1

prop_flatten_Idempotent :: IneqSlack -> Int -> Property
prop_flatten_Idempotent x n =
  n >= 0 && n < length (getStdVars $ slackIneq x) ==>
    flatten (flatten x n) n == flatten x n

prop_compensate_Zero :: EquSlackQC -> EquSlackQC -> Int -> Property
prop_compensate_Zero nfocal ntarget n =
  let focal = fromEquSlack nfocal
      target = fromEquSlack ntarget
      [focal',target'] = populate [focal,target]
      focal'' = flatten focal' n
  in
  n >= 0 && n < (length (getStdVars $ slackIneq focal) `max` length (getStdVars $ slackIneq target)) ==>
    varCoeff (getStdVars (slackIneq (compensate focal'' target' n)) !! n) == 0


prop_nextRow_MinRatio :: [IneqSlack] -> Int -> Property
prop_nextRow_MinRatio xs n =
  let xs' = populate xs in
  not (null xs) && n >= 0 && n < length (getStdVars $ slackIneq $ head xs') ==>
    case nextRow xs' n of
      Nothing -> True
      Just r  ->
        let ratios = mapMaybe (`coeffRatio` n) xs'
            ratio  = fromJust $ coeffRatio (xs' !! r) n
        in
        minimum ratios == ratio


prop_nextColumn_MinValue :: EquSlackQC -> Property
prop_nextColumn_MinValue x' =
  let x = fromEquSlack x'
      vars = varCoeff <$> getStdVars (slackIneq x)
  in
  length (filter (< 0) vars) > 0 ==>
    vars !! fromJust (nextColumn x) == minimum vars


allTheSame :: (Eq a) => [a] -> Bool
allTheSame xs = all (== head xs) (tail xs)
