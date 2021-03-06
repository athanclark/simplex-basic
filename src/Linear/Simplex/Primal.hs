{-# LANGUAGE
    FlexibleContexts
  , TupleSections
  , MultiWayIf
  #-}

module Linear.Simplex.Primal where

import Linear.Simplex.Primal.Types
import Linear.Grammar

import Data.List
import Data.Maybe
import Data.Bifunctor
import Control.Monad.State
import Control.Applicative


-- | Takes an objective function, a set of constraints, and an operation mode,
-- then returns a substitution.
-- .
-- Objective function should be in the form of @Ax + By + Cz + P = 0@, where @P@ is the
-- resule, and free in the constraint set.
simplexPrimal :: IneqStdForm -> [IneqStdForm] -> [(String, Rational)]
simplexPrimal (LteStd _ _) _ = error "Can't run simplex over an inequality - objective function must be ==."
simplexPrimal (GteStd _ _) _ = error "Can't run simplex over an inequality - objective function must be ==."
simplexPrimal f cs =
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
          mRow = nextRow constrs =<< mCol
      in
      if isNothing mCol || isNothing mRow
      then objective:constrs -- solved
      else run $ pivot (fromJust mRow, fromJust mCol) objective constrs

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
  then error "Empty tableau supplied to `nextRow`."
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


-- | Computes coefficient ratio to constant, based on a column index. Warning:
-- @Int@ parameter must be less than the length of the primal variables.
coeffRatio :: IneqSlack -> Int -> Maybe Rational
coeffRatio x col =
  let xs = getStdVars $ slackIneq x
      xc = getStdConst $ slackIneq x
  in
  if | col >= length xs -> error "`coeffRatio` called with a column index larger than the length of variables."
     | varCoeff (xs !! col) /= 0 ->
        let ratio = xc / varCoeff (xs !! col) in
        if ratio < 0
        then Nothing -- negative ratio
        else Just ratio
     | otherwise -> Nothing -- undefined ratio

-- | flattens targeted row to form the identity at it's column coefficient, then
-- reduces each non-zero row at this column, via a multiple of this flattened row.
-- Heart of the simplex method. Also prepends @objective@ back on @constrs@.
pivot :: (Int, Int) -> Objective -> [IneqSlack] -> [IneqSlack]
pivot (row,col) objective constrs =
  let
    focal = flatten (constrs !! row) col
    initConstrs = map (\x -> compensate focal x col) $ take row constrs
    tailConstrs = map (\x -> compensate focal x col) $ drop (row+1) constrs
    objective' = compensate focal objective col
  in
  objective':(initConstrs ++ (focal:tailConstrs))

-- | "Flattens" a row for further processing.
flatten :: IneqSlack -> Int -> IneqSlack
flatten (IneqSlack x ys) n =
  let invertedCoeff = recip $ varCoeff $ getStdVars x !! n
      mapRecip = map $ mapCoeff (invertedCoeff *)
      newStdIneq = mapStdVars mapRecip $ mapStdConst (invertedCoeff *) x
      newStdIneq' = mapStdVars (\xs -> replaceNth n (LinVar (varName (xs !! n)) 1) xs) newStdIneq
  in
  IneqSlack newStdIneq' $ mapRecip ys

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
  target `diffZip` newFocal


-- | Note: Must have identical occurrances of variables, and must be @EquStd@.
-- subtracts rhs from lhs.
diffZip :: IneqSlack -> IneqSlack -> IneqSlack
diffZip (IneqSlack (EquStd xs xc) xvs) (IneqSlack (EquStd ys yc) yvs) =
  IneqSlack (EquStd (zipDiff xs ys) $ xc - yc) $ zipDiff xvs yvs
  where
    zipDiff = zipWith (\x y -> LinVar (varName x) $ varCoeff x - varCoeff y)
diffZip _ _ = error "`diffZip` called with non `EquStd` input."


-- | Extracts resulting data from tableau, excluding junk data
getSubst :: [IneqSlack] -> [(String, Rational)]
getSubst xs =
  let (vars, solutions) = transposeTableau xs
      solutionIdxs = getSolutionIdxs vars
  in
  map (`getSolution` solutions) solutionIdxs
  where
    -- Takes the list of constants as a paramter
    getSolution :: (String, Maybe Int) -> [Rational] -> (String, Rational)
    getSolution (n, Nothing) _ = (n, 0)
    getSolution (n, Just i) ss = (n, ss !! i) -- dependent on rightward bias

    getSolutionIdxs :: [(String, [Rational])] -> [(String, Maybe Int)]
    getSolutionIdxs [] = []
    getSolutionIdxs ((v,ds):vs) = (v,findIdx ds):getSolutionIdxs vs
      where
        findIdx :: [Rational] -> Maybe Int
        findIdx ds | maximum ds == 1 -- the index of the only `1` element
                  && length (filter (== 1) ds) == 1 = elemIndex 1 ds
                   | otherwise = Nothing

    transposeTableau :: [IneqSlack] -> ([(String, [Rational])], [Rational])
    transposeTableau = foldl go ([],[])
      where
        go :: ([(String, [Rational])], [Rational])
           -> IneqSlack
           -> ([(String, [Rational])], [Rational])
        go (vars,solutions) (IneqSlack x ys) =
          let
            newvarsmap :: [(String, [Rational])]
            newvarsmap = map (\z -> (varName z,[varCoeff z])) $ getStdVars x ++ ys
            -- result after combining acc & current
            varsvals :: [[Rational]]
            varsvals = if null vars
                       then snd $ unzip newvarsmap -- pointwise combine acc vars & current vars
                       else zipWith (++) (snd $ unzip vars) (snd $ unzip newvarsmap)
          in
          ( if null vars
            then newvarsmap
            else zip (fst $ unzip vars) varsvals
          , solutions ++ [getStdConst x]
          )

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
    allnames :: ([String], [String])
    allnames = bimap (nub . concat) (nub . concat) $ unzip $ map varNames xs
  in
  map (fill allnames) xs
  where
    -- left is user-level vars, right are slack vars
    varNames :: IneqSlack -> ([String], [String])
    varNames x = ( map varName $ getStdVars $ slackIneq x
                 , map varName $ slackVars x
                 )

    -- populates missing variables with @0@ as coefficients, and sorts the result.
    fill :: ([String], [String]) -> IneqSlack -> IneqSlack
    fill (allns,allss) x =
      let (oldns,oldss) = varNames x in
      case (allns \\ oldns, allss \\ oldss) of
        (names,slacks) ->
          x { slackIneq = -- instantiate empty user-level vars
                          mapStdVars (\xs -> sort $ xs ++ map (flip LinVar 0) names) $
                          slackIneq x
            , slackVars = -- instantiate empty slack vars
                          sort $ slackVars x ++ map (flip LinVar 0) slacks
            }


replaceNth :: Int -> a -> [a] -> [a]
replaceNth n newVal (x:xs)
  | n == 0 = newVal:xs
  | otherwise = x:replaceNth (n-1) newVal xs
