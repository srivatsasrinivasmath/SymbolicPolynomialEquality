module Utils where

import Control.Monad
import Control.Monad.Loops
import Data.List as L
import Data.SBV
import Data.SBV.Control

proveOp :: [SBool] -> (a -> a -> SBool) -> a -> a -> Query Bool
proveOp ls op x y =
  do
    push 1
    forM_ ls constrain
    constrain $ sNot (op x y)
    cs <- checkSat
    pop 1
    return $ case cs of
      Sat -> False
      Unsat -> True

partitionM :: (Monad m) => (a -> m Bool) -> [a] -> m ([a], [a])
partitionM _ [] = return ([], [])
partitionM p (x : xs) = do
  res <- p x
  (lsTrue, lsFalse) <- partitionM p xs
  if res
    then return (x : lsTrue, lsFalse)
    else return (lsTrue, x : lsFalse)

isMaximal :: (a -> a -> SBool) -> [SBool] -> a -> [a] -> Query Bool
isMaximal op ctx l ls = liftM not $ anyM (proveOp ctx op l) ls

maximalAndRest :: (a -> a -> SBool) -> [SBool] -> [a] -> Query ([a], [a])
maximalAndRest op ctx ls = partitionM (\l -> isMaximal op ctx l ls) ls

partitionAgainst :: (b -> Bool) -> [(a, b)] -> ([a], [a])
partitionAgainst p ls = (fst <$> pass', fst <$> fail')
  where
    (pass', fail') = L.partition (\(_, y) -> p y) ls

numToList :: Int -> Int -> [Bool]
numToList 0 _ = []
numToList k n = phi b : numToList (k - 1) a
  where
    (a, b) = (n `div` 2, n `rem` 2)
    phi l = case l of
      0 -> False
      _ -> True

nonEmptySublistsAndRest :: [a] -> [([a], [a])]
nonEmptySublistsAndRest ls = partitionAgainst id <$> a0
  where
    nonEmptyBinaryLists = numToList (length ls) <$> [1 .. 2 ^ (length ls) - 1]
    a0 = [zip ls u | u <- nonEmptyBinaryLists]

pairs :: [a] -> [(a, a)]
pairs [] = []
pairs [_] = []
pairs (x : y : xs) = (x, y) : pairs (y : xs)

collapseEquals :: [SBool] -> (a -> a -> a) -> (a -> a -> SBool) -> [a] -> Query [a]
collapseEquals ctx cmbn op = foldM phi []
  where
    phi [] x = pure [x]
    phi (y : xs) x = do
      res <- proveOp ctx op x y
      if res
        then pure $ cmbn x y : xs
        else do
          rest <- phi xs x
          pure $ y : rest
