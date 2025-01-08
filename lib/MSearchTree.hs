module MSearchTree where

import Control.Monad (join)
import Data.List.NonEmpty
import Data.Maybe (isJust)
import Data.Tree (Tree, unfoldTreeM)
import Utils (findM)

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

findLeaf :: (Monad m) => (b -> Bool) -> MSearchTree m a b -> m (Maybe b)
findLeaf p (MSearchTree t) = do
  node <- t
  case node of
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

toTree :: (Monad m) => MSearchTree m a b -> m (Tree (Either b a))
toTree = unfoldTreeM go
  where
    go (MSearchTree t) = do
      t' <- t
      let next = case t' of
            Leaf lf -> (Left lf, [])
            Node {val = v, children = c} -> (Right v, toList c)
      pure next
