module Tests where

import Linear.Grammar
import Linear.Simplex.Basic
import Linear.Simplex.Basic.Types

import Data.Maybe
import Control.Monad.State

import Debug.Trace


f1 = EVar "a" .+. EVar "b" .+. EVar "c" .<=. ELit 100
f2 = (5 :: Double) .*. EVar "a" .+. (4 :: Double) .*. EVar "b" .+. (4 :: Double) .*. EVar "c" .<=. ELit 480
f3 = (40 :: Double) .*. EVar "a" .+. (20 :: Double) .*. EVar "b" .+. (30 :: Double) .*. EVar "c" .<=. ELit 3200
obj = (-70 :: Double) .*. EVar "a" .+. (-210 :: Double) .*. EVar "b" .+. (-140 :: Double) .*. EVar "c" .+. EVar "M" .==. ELit 0
solution = [("b", 100), ("M", 21000)]
test = simplex (standardForm obj) (standardForm <$> [f1,f2,f3]) Max
tableau = populate $ evalState (mapM (makeSlackVars . standardForm) [obj,f1,f2,f3]) 0


runOnce :: [IneqSlack] -> [IneqSlack]
runOnce (objective:constrs) =
  let mCol = nextColumn objective
      mRow = nextRow constrs =<< mCol
  in
  if isNothing mCol || isNothing mRow
  then objective:constrs -- solved
  else pivot (fromJust mRow, fromJust mCol) objective constrs
