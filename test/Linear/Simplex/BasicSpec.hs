module Linear.Simplex.BasicSpec (main, spec) where

import Linear.Simplex.BasicSpec.Types
import Linear.Simplex.Basic
import Linear.Simplex.Basic.Types
import Linear.Grammar

import Test.Hspec
import Test.QuickCheck
import Data.Maybe


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
  describe "`compensate`" $ do
    it "should have 0 at its oriented column in it's result" $
      property prop_compensate_Zero
  describe "`nextRow`" $
    it "should have the smallest ratio" $
      property prop_nextRow_MinRatio


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


isEquStd :: IneqSlack -> Bool
isEquStd (IneqSlack (EquStd _ _) _) = True
isEquStd _ = False

allTheSame :: (Eq a) => [a] -> Bool
allTheSame xs = all (== head xs) (tail xs)
