module Linear.Simplex.Basic.Types where

import Linear.Grammar

import Test.QuickCheck
import Data.List
import Control.Monad


-- | Standard-form inequality populated with arbitrary slack variables.
data IneqSlack = IneqSlack
  { slackIneq :: IneqStdForm
  , slackVars :: [LinVar]
  } deriving (Show, Eq)

-- | Boolean equality with @e^-6@ precision.
eqIneqSlack :: IneqSlack -> IneqSlack -> Bool
eqIneqSlack (IneqSlack x xs) (IneqSlack y ys) = eqIneqStdForm x y && eqLinVars xs ys

-- TODO: Find unique arbitrary instance for lists of strings
instance Arbitrary IneqSlack where
  arbitrary = liftM2 IneqSlack arbitrary (arbitrary `suchThat` isUniquelyNamed)
              `suchThat` slackNamesAreDisjoint
    where
      isUniquelyNamed x = let x' = map varName x in nub x' == x'
      slackNamesAreDisjoint x = null $ slackVars x `intersect` getStdVars (slackIneq x)
