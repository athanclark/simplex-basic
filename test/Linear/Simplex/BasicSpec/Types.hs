module Linear.Simplex.BasicSpec.Types where

import Linear.Grammar
import Linear.Simplex.Basic.Types

import Data.List
import Control.Monad
import Control.Applicative

import Test.QuickCheck


newtype EquStdQC = EquStdQC {fromEquStd :: IneqStdForm}
  deriving (Show, Eq)

instance Arbitrary EquStdQC where
  arbitrary = EquStdQC <$> liftM2 EquStd (arbitrary `suchThat` isUniquelyNamed) (choose (-1000,1000))
    where
      isUniquelyNamed x = let x' = map varName x in
        nub x' == x'

newtype EquSlackQC = EquSlackQC {fromEquSlack :: IneqSlack}
  deriving (Show, Eq)

instance Arbitrary EquSlackQC where
  arbitrary = EquSlackQC <$> liftM2 IneqSlack (fromEquStd <$> arbitrary)
                                              (arbitrary `suchThat` isUniquelyNamed)
              `suchThat` slackNamesAreDisjoint
    where
      isUniquelyNamed x = let x' = map varName x in nub x' == x'
      slackNamesAreDisjoint x = null $ slackVars x `intersect` getStdVars (slackIneq x)
