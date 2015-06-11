module Linear.Simplex.BasicSpec (main, spec) where

import Linear.Simplex.Basic
import Linear.Grammar

import Data.Maybe
import Test.Hspec
import Test.QuickCheck
import Test.QuickCheck.Instances


main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "`populate`" $
    it "should be idempotent" $
      property prop_populate_Idempotent
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
  not (null xs) && n >= 0 && n < length (getStdVars $ slackIneq $ head xs) ==>
    let mr = nextRow xs n in
    case mr of
      Nothing -> True
      Just r  ->
        let ratios = unMaybes $ map (`coeffRatio` n) xs
            ratio = fromJust $ coeffRatio (xs !! r) n
        in
        minimum ratios == ratio
  where
    unMaybes :: [Maybe a] -> [a]
    unMaybes [] = []
    unMaybes (Nothing:xs) = unMaybes xs
    unMaybes (Just x :xs) = x:unMaybes xs
