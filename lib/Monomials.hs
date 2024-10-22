module Monomials where

import Control.Monad
import qualified Data.List.NonEmpty as N
import Data.Maybe
import Data.SBV
import Data.SBV.Control
import Data.SBV.Internals (SMTModel)
import Data.Tree (Tree, drawForest)
import qualified MSearchTree as T
import qualified Utils as U

type Monomial = (Integer, SInteger)

data Leaf = Success [SBool] | Fail
  deriving (Show)

isSuccess :: Leaf -> Bool
isSuccess (Success _) = True
isSuccess Fail = False

type SymPoly = ([Monomial], [SBool])

canBeNextMonomial :: (Maybe Monomial, [SBool]) -> N.NonEmpty Monomial -> Query (Maybe (Monomial, [SBool]))
canBeNextMonomial (prev, ctx) candidate =
  do
    push 1
    forM_ new_ctx constrain
    cs <- checkSat
    pop 1
    return $ case cs of
      Sat -> Just ((c, k), new_ctx)
      Unsat -> Nothing
  where
    k = snd $ N.head candidate
    c = sum $ fst <$> candidate
    eq_ctx = uncurry (.==) <$> U.pairs (N.toList (snd <$> candidate))
    prev_ctx = case prev of
      Nothing -> []
      Just m -> [snd m .> k]
    new_ctx = prev_ctx ++ eq_ctx ++ ctx

makeSeedList :: (Maybe Monomial, SymPoly) -> Query [(Monomial, SymPoly)]
makeSeedList (prev, (rest, ctx)) = do
  (maxls, rest0) <- U.maximalAndRest (\(_, k) (_, k') -> k .< k') ctx rest
  let maxls' = U.nonEmptySublistsAndRest maxls
  nextSeedList <- mapM (nextSeedFromMaxList (prev, ctx) rest0) maxls'
  pure $ catMaybes nextSeedList

nextSeedFromMaxList :: (Maybe Monomial, [SBool]) -> [Monomial] -> ([Monomial], [Monomial]) -> Query (Maybe (Monomial, SymPoly))
nextSeedFromMaxList x rest0 (maxls, rest1) = r0
  where
    maxls' = N.nonEmpty maxls
    r0 =
      let op m m' = snd m .== snd m'
          cmbn m m' = (fst m + fst m', snd m)
       in do
            case maxls' of
              Nothing -> pure Nothing
              Just maxls'' -> do
                r1 <- canBeNextMonomial x maxls''
                case r1 of
                  Nothing -> pure Nothing
                  Just (m, new_ctx) ->
                    let rest = U.collapseEquals new_ctx cmbn op (rest1 ++ rest0)
                     in do
                          rest' <- rest
                          pure $ Just (m, (rest', new_ctx))

type NormalSeed = Either (Monomial, SymPoly) [SBool]

type NormalNode = (Monomial, [SBool])

normalTreeStep :: NormalSeed -> Query (Either Leaf (NormalNode, N.NonEmpty NormalSeed))
normalTreeStep (Right ctx) = pure (Left (Success ctx))
normalTreeStep (Left (prev, (rest, ctx))) = case rest of
  [] -> pure (Right ((prev, ctx), N.singleton (Right ctx)))
  _ ->
    do
      nextSeedList <- makeSeedList (Just prev, (rest, ctx))
      case N.nonEmpty nextSeedList of
        Nothing -> pure (Left Fail)
        Just seed_list -> pure (Right ((prev, ctx), Left <$> seed_list))

normalForestBuilder :: SymPoly -> Query [T.MSearchTree Query NormalNode Leaf]
normalForestBuilder p = init_ls >>= pure . phi
  where
    init_ls = (Left <$>) <$> makeSeedList (Nothing, p) :: Query [NormalSeed]
    phi ls = T.ana normalTreeStep <$> ls :: [T.MSearchTree Query NormalNode Leaf]

type NormalTree = T.MSearchTree Query NormalNode Leaf

mkEqualTree :: [SBool] -> SymPoly -> SymPoly -> Query [T.MSearchTree Query (Maybe Monomial) Leaf]
mkEqualTree init_ctx p q = init_ls >>= (pure . phi)
  where
    pTree = normalForestBuilder p
    qTree = normalForestBuilder q
    init_ls = do
      pTree' <- pTree
      qTree' <- qTree
      pure $ [((p', q'), init_ctx) | p' <- pTree', q' <- qTree']
    phi ls = T.ana equalTreeBuilder <$> ls

equalTreeBuilder :: ((NormalTree, NormalTree), [SBool]) -> Query (Either Leaf (Maybe Monomial, N.NonEmpty ((NormalTree, NormalTree), [SBool])))
equalTreeBuilder ((T.MSearchTree t_l, T.MSearchTree t_r), ctx) = do
  t_l' <- t_l
  t_r' <- t_r
  case (t_l', t_r') of
    (T.Leaf Fail, _) -> pure (Left Fail)
    (_, T.Leaf Fail) -> pure (Left Fail)
    (T.Leaf (Success ctx_l), T.Leaf (Success ctx_r)) -> pure (Left (Success (ctx ++ ctx_l ++ ctx_r)))
    (T.Leaf (Success _), _) -> pure (Left Fail)
    (_, T.Leaf (Success _)) -> pure (Left Fail)
    (T.Node {T.val = ((c_l, k_l), ctx_l), T.children = n_l}, T.Node {T.val = ((c_r, k_r), ctx_r), T.children = n_r}) ->
      case (c_l, c_r) of
        (_, 0) -> pure (Right (Nothing, makeNextSeeds (N.singleton (T.MSearchTree t_l)) n_r ctx))
        (0, _) -> pure (Right (Nothing, makeNextSeeds n_l (N.singleton (T.MSearchTree t_r)) ctx))
        _ ->
          ( if c_l == c_r
              then
                ( do
                    push 1
                    forM_ ((k_l .== k_r) : (ctx ++ ctx_l ++ ctx_r)) constrain
                    cs <- checkSat
                    pop 1
                    case cs of
                      Sat ->
                        pure (Right (Just (c_l, k_l), makeNextSeeds n_l n_r ((k_l .== k_r) : ctx)))
                      Unsat -> pure (Left Fail)
                )
              else (pure (Left Fail))
          )
  where
    pairs0 ls r = (\l -> (l, r)) <$> ls
    pairs1 ls rs = join (pairs0 ls <$> rs)
    addCtx ls ctx' = (\x -> (x, ctx')) <$> ls
    makeNextSeeds ls rs = addCtx (pairs1 ls rs)

mkSymPoly :: String -> [Integer] -> Symbolic SymPoly
mkSymPoly name ls = do
  let l = length ls
  let names = (name ++) <$> (show <$> [0 .. (l - 1)])
  ks <- sIntegers names
  let p_body = zip ls ks
  let gt0 = case ks of
        [] -> []
        (k : _) -> [k .== 0]
  let strct = (\(x, y) -> x .< y) <$> U.pairs ks
  pure (p_body, gt0 ++ strct)

pCross :: SymPoly -> SymPoly
pCross (body, ctx) = ((\(x, y) -> (x, deg - y)) <$> body, ctx)
  where
    deg = case body of
      [] -> 0
      _ -> snd (last body)

pMult :: SymPoly -> SymPoly -> SymPoly
pMult (p_body, p_ctx) (q_body, q_ctx) = (pq_body, pq_ctx)
  where
    pq_body = [(u_p * u_q, v_p + v_q) | (u_p, v_p) <- p_body, (u_q, v_q) <- q_body]
    pq_ctx = p_ctx ++ q_ctx

test = runSMT . mkTest1
  where
    mkTest0 = do
      p <- mkSymPoly "k" [1, 1, 1, 1, 1, 1]
      let ls = normalForestBuilder (p `pMult` (pCross p))
      let qu = do
            ls' <- ls
            let res_ls = ((T.findLeaf isSuccess) <$> ls')
            res0 <- T.findM (pure . isJust) res_ls
            let res1 = join res0
            let res2 = case res1 of
                  Nothing -> do
                    msg <- io (print "Failure")
                    pure $ Left msg
                  Just lf -> case lf of
                    Success ctx -> do
                      push 1
                      forM_ ctx constrain
                      cs <- checkSat
                      mdl <- getModel
                      pop 1
                      pure $ Right mdl
            res2
      query qu
    mkTest1 ls = do
      p <- mkSymPoly "k" ls
      q <- mkSymPoly "l" [1, -2, 1]
      let m = snd ((fst q) !! 1)
      let n = snd ((fst q) !! 2)
      let ls = mkEqualTree [5 * n ./= 7 * m] (p `pMult` pCross p) (q `pMult` pCross q)
      let qu = do
            ls' <- ls
            let res_ls = ((T.findLeaf isSuccess) <$> ls')
            res0 <- T.findM (pure . isJust) res_ls
            let res1 = join res0
            let res2 = case res1 of
                  Nothing -> do
                    msg <- io (print "Failure")
                    pure $ Left msg
                  Just lf -> case lf of
                    Success ctx -> do
                      push 1
                      forM_ ctx constrain
                      cs <- checkSat
                      mdl <- getModel
                      pop 1
                      pure $ Right mdl
            res2
      query qu
    mkTest2 ls = do
      p <- mkSymPoly "l" ls
      query $ do
        pTree <- normalForestBuilder (p `pMult` pCross p)
        let (T.MSearchTree t) = head pTree
        t' <- t
        mapM T.getVal (T.children t')

-- printTillDepth :: (Monad m) => m [T.MSearchTree m a b] -> m [Tree String]
