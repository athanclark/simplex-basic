{-# LANGUAGE
    FlexibleContexts
  #-}

module Linear.Simplex.Basic where

import Linear.Grammar
import Data.List

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
simplex f cs Max =
  let
    cs' = evalState (mapM makeSlackVars cs) 0
    tableau = populate (f:cs')
  in
  findSubsts $ run tableau
  where
    run :: [IneqStdForm] -> [IneqStdForm]
    run = undefined

-- | Also translates @Ax >= Q@ to @-Ax <= -Q@.
makeSlackVars :: MonadState Integer m => IneqStdForm -> m IneqStdForm
makeSlackVars a@(EquStd _ _) = return a
makeSlackVars (LteStd xs xc) = do
  suffix <- get
  put $ suffix + 1
  return $ EquStd (LinVar ("s" ++ show suffix) 1 : xs) xc
makeSlackVars (GteStd xs xc) =
  makeSlackVars $ LteStd (map (\v -> v {varCoeff = varCoeff v * (-1)}) xs) ((-1) * xc)

-- | Fills missing variables
populate :: [IneqStdForm] -> [IneqStdForm]
populate [] = []
populate xs = let names = nub $ concatMap linVarNames xs in
  map (fill names) xs
  where
    linVarNames :: IneqStdForm -> [String]
    linVarNames (EquStd xs _) = map varName xs
    linVarNames (LteStd xs _) = map varName xs

    -- populates missing variables with 0 coefficients, and sorts the result.
    fill :: [String] -> IneqStdForm -> IneqStdForm
    fill names x@(EquStd xs xc) = let xnames = linVarNames x in
      case names \\ xnames of
        [] -> EquStd (sort xs) xc
        ns -> EquStd (sort $ xs ++ map (flip LinVar 0) ns) xc
    fill names x@(LteStd xs xc) = let xnames = linVarNames x in
      case names \\ xnames of
        [] -> LteStd (sort xs) xc
        ns -> LteStd (sort $ xs ++ map (flip LinVar 0) ns) xc
    fill names x@(GteStd xs xc) = let xnames = linVarNames x in
      case names \\ xnames of
        [] -> GteStd (sort xs) xc
        ns -> GteStd (sort $ xs ++ map (flip LinVar 0) ns) xc
