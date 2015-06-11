{-# LANGUAGE
    FlexibleContexts
  #-}

module Linear.Simplex.Basic where

import Linear.Grammar
import Data.List
import Data.Bifunctor

import Control.Monad
import Control.Monad.State


data Optimize = Max | Min
  deriving (Show, Eq)

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
    run :: [IneqSlack] -> [IneqSlack]
    run = undefined

    -- finds next column index from objective function
    nextColumn :: IneqSlack -> Maybe Int
    nextColumn (IneqSlack (EquStd xs _) _)
      | minimum (map varCoeff xs) < 0 = findIndex (hasCoeff $ minimum (map varCoeff xs)) xs
      | otherwise = Nothing -- simplex is finished
    nextColumn _ = error "`nextColumn` called on an inequality."

    coeffRatio :: IneqSlack -> Int -> Maybe Double
    coeffRatio (IneqSlack (EquStd xs xc) _) n
      | varCoeff (xs !! n) /= 0 = let ratio = varCoeff (xs !! n) / xc in
          if ratio < 0
          then Nothing -- negative ratio
          else Just ratio
      | otherwise = Nothing -- undefined ratio
    coeffRatio (IneqSlack (LteStd xs xc) _) n
      | varCoeff (xs !! n) /= 0 = let ratio = varCoeff (xs !! n) / xc in
          if ratio < 0
          then Nothing -- negative ratio
          else Just ratio
      | otherwise = Nothing -- undefined ratio
    coeffRatio (IneqSlack (GteStd xs xc) _) n
      | varCoeff (xs !! n) /= 0 = let ratio = varCoeff (xs !! n) / xc in
          if ratio < 0
          then Nothing -- negative ratio
          else Just ratio
      | otherwise = Nothing -- undefined ratio

    -- Extracts resulting data from tableau, excluding junk data
    getSubst :: [IneqSlack] -> [(LinVar, Double)]
    getSubst = undefined

-- | Standard-form inequality populated with arbitrary slack variables.
data IneqSlack = IneqSlack IneqStdForm [LinVar]
  deriving (Show, Eq)

-- | Also translates @Ax >= Q@ to @-Ax <= -Q@. Ie; result will __exclude__ @GteStd@.
makeSlackVars :: MonadState Integer m => IneqStdForm -> m IneqSlack
makeSlackVars a@(EquStd _ _) = return $ IneqSlack a []
makeSlackVars (LteStd xs xc) = do
  suffix <- get
  put $ suffix + 1
  return $ IneqSlack (EquStd xs xc) [LinVar ("s" ++ show suffix) 1]
makeSlackVars (GteStd xs xc) = -- invert equation, for <= form
  makeSlackVars $ LteStd (map (\v -> v {varCoeff = varCoeff v * (-1)}) xs)
                         ((-1) * xc)

-- | Fills missing variables
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
    linVarNames (IneqSlack (EquStd xs _) ys) = (map varName xs, map varName ys)
    linVarNames (IneqSlack (LteStd xs _) ys) = (map varName xs, map varName ys)
    linVarNames (IneqSlack (GteStd xs _) ys) = (map varName xs, map varName ys)

    -- populates missing variables with @0@ as coefficients, and sorts the result.
    fill :: ([String], [String]) -> IneqSlack -> IneqSlack
    fill (rs,ss) x@(IneqSlack (EquStd xs xc) ys) =
      let (rs',ss') = linVarNames x in
      case (rs \\ rs', ss \\ ss') of
        (names,slacks) -> IneqSlack
          -- instantiate empty user-level vars
          (EquStd (sort $ xs ++ map (flip LinVar 0) names) xc)
          -- instantiate empty slack vars
          (sort $ ys ++ map (flip LinVar 0) slacks)

    fill (rs,ss) x@(IneqSlack (LteStd xs xc) ys) =
      let (rs',ss') = linVarNames x in
      case (rs \\ rs', ss \\ ss') of
        (names,slacks) -> IneqSlack (LteStd (sort $ xs ++ map (flip LinVar 0) names) xc) $
                                    sort $ ys ++ map (flip LinVar 0) slacks

    fill (rs,ss) x@(IneqSlack (GteStd xs xc) ys) =
      let (rs',ss') = linVarNames x in
      case (rs \\ rs', ss \\ ss') of
        (names,slacks) -> IneqSlack (GteStd (sort $ xs ++ map (flip LinVar 0) names) xc) $
                                    sort $ ys ++ map (flip LinVar 0) slacks
