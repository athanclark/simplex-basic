module Linear.Simplex.BasicSpec (main, spec) where

import Linear.Simplex.Basic
import Linear.Grammar

import Data.Maybe
import Test.Hspec
import Test.QuickCheck
import Test.QuickCheck.Instances

import Debug.Trace


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
  describe "`flatten`" $
    it "should have 1 at its oriented column in it's result" $
      property prop_flatten_One
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
    traceShow x' $
    minimum x' == maximum x' -- TODO: Need actual mass-equality

prop_diffZip_Zero :: IneqSlack -> Property
prop_diffZip_Zero x =
  let r  = diffZip x x
      ss = map varCoeff $ slackVars r
      c  = getStdConst $ slackIneq r
      vs = map varCoeff $ getStdVars $ slackIneq r
  in
  isEqStd x ==> all (== 0) (ss ++ vs ++ [c])
  where
    isEqStd :: IneqSlack -> Bool
    isEqStd (IneqSlack (EquStd _ _) _) = True
    isEqStd _ = False

prop_flatten_One :: IneqSlack -> Int -> Property
prop_flatten_One x n =
  n >= 0 && n < length (getStdVars $ slackIneq x) ==>
    let r = varCoeff (getStdVars (slackIneq $ flatten x n) !! n) in
    r > 0.9999 && r < 1.0001

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
        if length xs' > r
        then minimum ratios == ratio
        else error "what"
