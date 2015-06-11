{-# LANGUAGE
    FlexibleContexts
  , TupleSections
  #-}

module Linear.Simplex.Basic where

import Linear.Grammar
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Bifunctor
import Control.Monad
import Control.Monad.State

import Test.QuickCheck


data Optimize = Max | Min
  deriving (Show, Eq)

type Objective = IneqSlack

-- | Takes an objective function, a set of constraints, and an operation mode,
-- then returns a substitution.
-- .
-- Objective function should be in the form of @Ax + By + Cz + P = 0@
simplex :: IneqStdForm -> [IneqStdForm] -> Optimize -> [(String, Double)]
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


-- | Finds next pivot row by the smallest ratio in each row.
-- Note: row list should be non-empty
nextRow :: [IneqSlack] -> Int -> Maybe Int
nextRow xs col = if null xs
  then error "Non-empty tableau supplied to `nextRow`."
  else minIdxMaybe $ map (`coeffRatio` col) xs
  where
    minIdxMaybe :: Ord a => [Maybe a] -> Maybe Int
    minIdxMaybe xs =
      fst <$> foldl go Nothing (catMaybes $ mapIdxs xs)
      where
        go Nothing  x = Just x
        go (Just n) x | snd x < snd n = Just x
                      | otherwise     = Just n

    mapIdxs :: Functor f => [f a] -> [f (Int, a)]
    mapIdxs = go 0
      where
        go n [] = []
        go n (fx:xs) = ((n,) <$> fx):go (n+1) xs


-- | Computes coefficient ratio to constant, based on a column index
coeffRatio :: IneqSlack -> Int -> Maybe Double
coeffRatio x n =
  let xs = getStdVars $ slackIneq x
      xc = getStdConst $ slackIneq x
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
-- Heart of the simplex method. Also prepends @objective@ back on @constrs@.
pivot :: (Int, Int) -> Objective -> [IneqSlack] -> [IneqSlack]
pivot (row,col) objective constrs =
  let
    focalRow = flatten (constrs !! row) col
    initConstrs = map (\x -> compensate focalRow x col) $ take row constrs
    tailConstrs = map (\x -> compensate focalRow x col) $ drop (row+1) constrs
  in
  objective:(initConstrs ++ (focalRow:tailConstrs))

-- | "Flattens" a row for further processing.
flatten :: IneqSlack -> Int -> IneqSlack
flatten (IneqSlack x ys) n =
  let coeffRecip = recip $ varCoeff $ getStdVars x !! n
      mapRecip = map $ mapCoeff (coeffRecip *)
  in
  IneqSlack (mapStdVars mapRecip $ mapStdConst (coeffRecip *) x) $ mapRecip ys

-- | Takes the focal row, the row to affect, and the column in question to facilitate
-- the sum-oriented part of the pivot.
compensate :: IneqSlack -> IneqSlack -> Int -> IneqSlack
compensate focal target col =
  let
    coeff = varCoeff $ getStdVars (slackIneq target) !! col
    -- multiply all literals by @coeff@
    newFocal = focal { slackIneq = mapStdVars (map $ mapCoeff (coeff *)) $
                                   mapStdConst (coeff *) $ slackIneq focal
                     , slackVars = map (mapCoeff (coeff *)) $ slackVars focal
                     }
  in
  diffZip target newFocal


-- | Note: Must have identical occurrances of variables, and must be @EquStd@.
-- subtracts rhs from lhs.
diffZip :: IneqSlack -> IneqSlack -> IneqSlack
diffZip (IneqSlack (EquStd xs xc) xvs) (IneqSlack (EquStd ys yc) yvs) =
  IneqSlack (EquStd (zipDiff xs ys) $ xc - yc) $ zipDiff xvs yvs
  where
    zipDiff = zipWith (\x y -> LinVar (varName x) $ varCoeff x - varCoeff y)
diffZip _ _ = error "`diffZip` called with non `EquStd` input."

-- | Extracts resulting data from tableau, excluding junk data
getSubst :: [IneqSlack] -> [(String, Double)]
getSubst xs =
  let (vars, solutions) = transposeTableau xs
      solutionIdxs = getSolutionIdxs vars
  in
  map (`getSolutionIdx` solutions) solutionIdxs
  where
    getSolutionIdx :: (String, Maybe Int) -> [Double] -> (String, Double)
    getSolutionIdx (n, Nothing) _ = (n, 0)
    getSolutionIdx (n, Just i) xs = (n, xs !! i)

    getSolutionIdxs :: [(String,[Double])] -> [(String, Maybe Int)]
    getSolutionIdxs [] = []
    getSolutionIdxs ((v,ds):xs) = (v,findIdx ds):getSolutionIdxs xs
      where
        findIdx :: [Double] -> Maybe Int
        findIdx ds | maximum ds == 1
                  && length (filter (== 1) ds) == 1 = elemIndex 1 ds
                   | otherwise = Nothing

    transposeTableau :: [IneqSlack] -> ([(String, [Double])], [Double])
    transposeTableau = foldl go ([],[])
      where
        go :: ([(String,[Double])], [Double]) -> IneqSlack -> ([(String,[Double])], [Double])
        go (vars,solutions) (IneqSlack x ys) =
          let
            newvars = getStdVars x ++ ys
            newvarsmap :: [(String,[Double])]
            newvarsmap = map (\z -> (varName z,[varCoeff z])) newvars
            newvarsvals :: [[Double]]
            newvarsvals = if null vars
                          then snd $ unzip newvarsmap
                          else zipWith (++) (snd $ unzip vars) (snd $ unzip newvarsmap)
          in
          ( if null vars
            then newvarsmap
            else zip (fst $ unzip vars) newvarsvals
          , solutions ++ [getStdConst x]
          )


-- | Standard-form inequality populated with arbitrary slack variables.
data IneqSlack = IneqSlack
  { slackIneq :: IneqStdForm
  , slackVars :: [LinVar]
  } deriving (Show, Eq)

instance Arbitrary IneqSlack where
  arbitrary = liftM2 IneqSlack arbitrary arbitrary

-- | Also translates @Ax >= Q@ to @-Ax <= -Q@. Ie; result will __exclude__ @GteStd@.
makeSlackVars :: MonadState Integer m => IneqStdForm -> m IneqSlack
makeSlackVars a@(EquStd _ _) = return $ IneqSlack a []
makeSlackVars (LteStd xs xc) = do
  suffix <- get
  put $ suffix + 1
  return $ IneqSlack (EquStd xs xc) [LinVar ("s" ++ show suffix) 1]
makeSlackVars (GteStd xs xc) = -- invert equation to <= form
  makeSlackVars $ LteStd (map (mapCoeff ((-1) *)) xs)
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
