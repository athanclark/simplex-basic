{-# LANGUAGE
    FlexibleContexts
  , TupleSections
  #-}

module Linear.Simplex.Basic where

import Linear.Grammar
import Data.List
import Data.Maybe
import Data.Bifunctor

import Control.Monad
import Control.Monad.State


data Optimize = Max | Min
  deriving (Show, Eq)

type Objective = IneqSlack

-- | Takes an objective function, a set of constraints, and an operation mode,
-- then returns a substitution.
-- .
-- Objective function should be in the form of @Ax + By + Cz + P = 0@
simplex :: IneqStdForm -> [IneqStdForm] -> Optimize -> [(LinVar, Double)]
simplex (LteStd _ _) _ _ = error "Can't run simplex over an inequality - objective function must be literal."
simplex (GteStd _ _) _ _ = error "Can't run simplex over an inequality - objective function must be literal."
simplex f cs Max =
  let
    -- objective function is not an inequality, so no slacks will be introduced.
    tableau = populate $ evalState (mapM makeSlackVars (f:cs)) 0
  in
  getSubst $ run tableau
  where
    -- list of inequalities includes objective function.
    run :: [IneqSlack] -> [IneqSlack]
    run (objective:constrs) =
      let mCol = nextColumn objective
          mRow = mCol >>= nextRow constrs
      in
      if isNothing mCol || isNothing mRow
      then objective:constrs -- solved
      else run $ pivot (fromJust mCol, fromJust mRow) objective constrs

-- | finds next column index from objective function
nextColumn :: IneqSlack -> Maybe Int
nextColumn (IneqSlack (EquStd xs _) _)
  | minimum (map varCoeff xs) < 0 = findIndex (hasCoeff $ minimum (map varCoeff xs)) xs
  | otherwise = Nothing -- simplex is finished
nextColumn _ = error "`nextColumn` called on an inequality."


-- | Finds next pivot row based on ratios of each row - note, row list should be non-empty
nextRow :: [IneqSlack] -> Int -> Maybe Int
nextRow xs col = fst <$> go 0 Nothing xs
  where
    -- manually recurse down tableau, with accumulator
    go :: Int -> Maybe (Int, Double) -> [IneqSlack] -> Maybe (Int, Double)
    go _ _         []  = error "Non-empty tableau supplied to `nextRow`."
    go idx Nothing [x] = (idx,) <$> coeffRatio x col
    go idx (Just (aidx, acc)) (x:xs) = case coeffRatio x col of
      Nothing -> Just (aidx, acc)
      Just acc' | acc' > acc -> go (idx+1) (Just (idx, acc')) xs
                | otherwise  -> go (idx+1) (Just (aidx, acc)) xs


-- | Computes coefficient ratio to constant, based on a column index
coeffRatio :: IneqSlack -> Int -> Maybe Double
coeffRatio x n =
  let xs = getStdVars $ slackIneq x
      xc = getStdCoeff $ slackIneq x
  in
  if varCoeff (xs !! n) /= 0
  then
      let ratio = varCoeff (xs !! n) / xc in
      if ratio < 0
      then Nothing -- negative ratio
      else Just ratio
  else Nothing -- undefined ratio

-- | flattens targeted row to form the identity at it's column coefficient, then
-- reduces each non-zero row at this column, via a multiple of this flattened row.
-- Heart of the simplex method.
pivot :: (Int, Int) -> Objective -> [IneqSlack] -> [IneqSlack]
pivot (row,col) objective constrs =
  let
    focalRow = flatten (constrs !! row) col
    initConstrs = take row constrs
    tailConstrs = drop (row+1) constrs
  in
  undefined

-- | "Flattens" a row for further processing.
flatten :: IneqSlack -> Int -> IneqSlack
flatten (IneqSlack (EquStd xs xc) ys) n =
  let
    coeffRecip = recip $ varCoeff $ xs !! n
    mapRecip = map (mapCoeff $ (*) coeffRecip)
  in
  IneqSlack (EquStd (mapRecip xs) $ xc * coeffRecip) $ mapRecip ys

-- | Takes the focal row, the row to affect, and the column in question to facilitate
-- the sum-oriented part of the pivot.
compensate :: IneqSlack -> IneqSlack -> Int -> IneqSlack
compensate focal target col =
  let
    coeff = varCoeff $ getStdVars (slackIneq target) !! col
    -- multiply all literals by @coeff@
    newFocal = focal { slackIneq = mapStdVars (map $ mapCoeff (coeff *)) $
                                   mapStdCoeff (coeff *) $ slackIneq focal
                     , slackVars = map (mapCoeff (coeff *)) $ slackVars focal
                     }
  in
  undefined
  where
    -- Note: Must have identical occurrances of variables
    diffZip :: IneqSlack -> IneqSlack -> IneqSlack
    diffZip = undefined

-- | Extracts resulting data from tableau, excluding junk data
getSubst :: [IneqSlack] -> [(LinVar, Double)]
getSubst = undefined


-- | Standard-form inequality populated with arbitrary slack variables.
data IneqSlack = IneqSlack
  { slackIneq :: IneqStdForm
  , slackVars :: [LinVar]
  } deriving (Show, Eq)

-- | Also translates @Ax >= Q@ to @-Ax <= -Q@. Ie; result will __exclude__ @GteStd@.
makeSlackVars :: MonadState Integer m => IneqStdForm -> m IneqSlack
makeSlackVars a@(EquStd _ _) = return $ IneqSlack a []
makeSlackVars (LteStd xs xc) = do
  suffix <- get
  put $ suffix + 1
  return $ IneqSlack (EquStd xs xc) [LinVar ("s" ++ show suffix) 1]
makeSlackVars (GteStd xs xc) = -- invert equation to <= form
  makeSlackVars $ LteStd (map (mapCoeff $ (*) (-1)) xs)
                         ((-1) * xc)

-- | Fills missing variables. List of inequalities includes objective function.
populate :: [IneqSlack] -> [IneqSlack]
populate xs =
  let
    exauhstive :: ([[String]], [[String]])
    exauhstive = unzip $ map linVarNames xs

    allnames :: ([String], [String])
    allnames = bimap (nub . concat) (nub . concat) exauhstive
  in
  map (fill allnames) xs
  where
    -- left is user-level vars, right are slack vars
    linVarNames :: IneqSlack -> ([String], [String])
    linVarNames x = ( map varName $ getStdVars $ slackIneq x
                    , map varName $ slackVars x
                    )

    -- populates missing variables with @0@ as coefficients, and sorts the result.
    fill :: ([String], [String]) -> IneqSlack -> IneqSlack
    fill (rs,ss) x =
      let
        (rs',ss') = linVarNames x
      in
      case (rs \\ rs', ss \\ ss') of
        (names,slacks) ->
          x { slackIneq = -- instantiate empty user-level vars
                          mapStdVars (\xs -> sort $ xs ++ map (flip LinVar 0) names) $
                          slackIneq x
            , slackVars = -- instantiate empty slack vars
                          sort $ slackVars x ++ map (flip LinVar 0) slacks
            }
