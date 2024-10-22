module MSearchTree where

import Control.Monad (join)
import Data.List.NonEmpty
import Data.Maybe (isJust)
import Data.Tree (Tree, unfoldTreeM)

--- Error in the definition ot be revised later, children should be of type m (NonEmpty (MSearchTree m a b)). This is beacuse you dont necessarily want to calculate th children of the node when you access it's value
data MStep m a b = Node {val :: a, children :: NonEmpty (MSearchTree m a b)} | Leaf b

newtype MSearchTree m a b = MSearchTree (m (MStep m a b))

getVal :: (Monad m) => MSearchTree m a b -> m (Either b a)
getVal (MSearchTree t) = do
  t' <- t
  pure $ case t' of
    Leaf lf -> Left lf
    Node {val = v} -> Right v

ana :: (Monad m) => (s -> m (Either b (a, NonEmpty s))) -> s -> MSearchTree m a b
ana phi seed = MSearchTree step
  where
    step = do
      res <- phi seed
      pure $ case res of
        Left leaf -> Leaf leaf
        Right (x, ls) -> Node {val = x, children = ana phi <$> ls}

findM :: (Monad m) => (a -> m Bool) -> [m a] -> m (Maybe a)
findM _ [] = pure Nothing
findM p (c : cs) = do
  out <- c
  res <- p out
  if res then pure $ Just out else findM p cs

findLeaf :: (Monad m) => (b -> Bool) -> MSearchTree m a b -> m (Maybe b)
findLeaf p (MSearchTree t) = do
  node <- t
  let x = case node of
        Leaf l ->
          pure $
            if p l
              then Just l
              else Nothing
        Node {children = c} ->
          let phi = toList (findLeaf p <$> c)
           in do
                res <- findM (pure . isJust) phi
                pure (join res)
  x

toTree :: (Monad m) => MSearchTree m a b -> m (Tree (Either b a))
toTree = unfoldTreeM go
  where
    go (MSearchTree t) = do
      t' <- t
      let next = case t' of
            Leaf lf -> (Left lf, [])
            Node {val = v, children = c} -> (Right v, toList c)
      pure next

filterMSearchTree :: (Monad m) => (a -> m Bool) -> NonEmpty (MSearchTree m a b) -> m (NonEmpty (MSearchTree m a b))
filterMSearchTree p ls = do
  init_ls <- validBoundary p ls
  let phi = ana builder
  pure (phi <$> init_ls)
  where
    builder (MSearchTree t) = do
      t' <- t
      case t' of
        Leaf lf -> pure $ Left lf
        Node {val = v, children = c} -> do
          c' <- validBoundary p c
          pure $ Right (v, c')

validBoundary :: (Monad m) => (a -> m Bool) -> NonEmpty (MSearchTree m a b) -> m (NonEmpty (MSearchTree m a b))
validBoundary p (MSearchTree t :| ts) =
  do
    t' <- t
    let validRest = case nonEmpty ts of
          Nothing -> pure []
          Just ts' -> (validBoundary p ts') >>= pure . toList
    let o1 = validRest >>= pure . (MSearchTree t :|)
    case t' of
      Leaf _ -> o1
      Node {val = v, children = c} -> do
        let o2 = validRest >>= pure . (c `appendList`)
        res <- p v
        if res
          then o1
          else validBoundary p =<< o2
