module Linear.Simplex.Primal.Types where

import Linear.Grammar

import Test.QuickCheck
import Data.List
import Control.Monad


type Objective = IneqSlack

-- | Standard-form inequality populated with arbitrary slack variables.
data IneqSlack = IneqSlack
  { slackIneq :: IneqStdForm
  , slackVars :: [LinVar]
  } deriving (Show, Eq)

-- TODO: Find unique arbitrary instance for lists of strings
instance Arbitrary IneqSlack where
  arbitrary = liftM2 IneqSlack arbitrary (arbitrary `suchThat` isUniquelyNamed)
              `suchThat` slackNamesAreDisjoint
    where
      isUniquelyNamed x = hasNoDups $ map varName x
      slackNamesAreDisjoint x = null $ slackVars x `intersect` getStdVars (slackIneq x)
