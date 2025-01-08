module Blog where

import Control.Monad (forM_, join, void)
import qualified Data.List.NonEmpty as N
import Data.Maybe (catMaybes, isJust)
import Data.SBV
import Data.SBV.Control
import Data.SBV.Internals (SMTModel)
import qualified MSearchTree as T
import qualified Utils as U

type Monomial = (SInteger, SInteger)

type SymPoly = ([Monomial], [SBool])

data Leaf = Success [SBool] | Fail
  deriving (Show)

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

type NormalSeed = (Monomial, SymPoly)

type NormalNode = (Monomial, [SBool])

normalTreeStep :: NormalSeed -> Query (Either Leaf (NormalNode, N.NonEmpty NormalSeed))
normalTreeStep (prev, (rest, ctx)) = case rest of
  [] -> pure (Left (Success ctx))
  _ ->
    do
      nextSeedList <- makeSeedList (Just prev, (rest, ctx))
      case N.nonEmpty nextSeedList of
        Nothing -> pure (Left Fail)
        Just seed_list -> pure (Right ((prev, ctx), seed_list))

normalForestBuilder :: SymPoly -> Query [T.MSearchTree Query NormalNode Leaf]
normalForestBuilder p = init_ls >>= pure . phi
  where
    init_ls = makeSeedList (Nothing, p) :: Query [NormalSeed]
    phi ls = T.ana normalTreeStep <$> ls :: [T.MSearchTree Query NormalNode Leaf]

type NormalTree = T.MSearchTree Query NormalNode Leaf

zeroTreeBuilder :: (NormalTree, [SBool]) -> Query (Either Leaf ((), N.NonEmpty (NormalTree, [SBool])))
zeroTreeBuilder (T.MSearchTree t, ctx_acc) =
  do
    t' <- t
    case t' of
      T.Leaf Fail -> pure (Left Fail)
      T.Leaf (Success nrm_ctx) -> pure (Left (Success (nrm_ctx ++ ctx_acc)))
      T.Node {T.val = ((c, _), nrm_ctx), T.children = n} ->
        let curr_ctx = ((c .== 0) : ctx_acc)
         in do
              push 1
              forM_ (curr_ctx ++ nrm_ctx) constrain
              cs <- checkSat
              pop 1
              case cs of
                Sat -> pure (Right ((), (\x -> (x, curr_ctx)) <$> n))
                _ -> pure (Left Fail)

mkZeroForest :: SymPoly -> Query [T.MSearchTree Query () Leaf]
mkZeroForest p = init_ls >>= (pure . phi)
  where
    pNormalForest = normalForestBuilder p
    init_ls = ((\x -> (x, [])) <$>) <$> pNormalForest
    phi ls = T.ana zeroTreeBuilder <$> ls

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

mkSymPoly :: String -> [SInteger] -> Symbolic SymPoly
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

pAdd :: SymPoly -> SymPoly -> SymPoly
pAdd (p_body, p_ctx) (q_body, q_ctx) = (p_body ++ q_body, p_ctx ++ q_ctx)

pScalarMult :: SInteger -> SymPoly -> SymPoly
pScalarMult lambda (p_body, p_ctx) = ((\(x, y) -> (lambda * x, y)) <$> p_body, p_ctx)

isSuccess :: Leaf -> Bool
isSuccess (Success _) = True
isSuccess Fail = False

checkZeroSat :: SymPoly -> Symbolic ()
checkZeroSat p =
  let ls = mkZeroForest p
   in query $ do
        ls' <- ls
        let res_ls = T.findLeaf isSuccess <$> ls'
        res0 <- U.findM (pure . isJust) res_ls
        let res1 = join res0
        let res2 = case res1 of
              Nothing -> do
                io (print "Failure")
              Just lf -> case lf of
                Success ctx -> do
                  push 1
                  forM_ ctx constrain
                  cs <- checkSat
                  mdl <- getModel
                  pop 1
                  io $ print mdl
        void res2

rMinusWithConstraint :: Symbolic SymPoly
rMinusWithConstraint = do
  qs <- sIntegers ((\x -> "a" ++ show x) <$> [0 .. 5])
  (q'_body, q'_ctx) <- mkSymPoly "k" qs
  (p'_body, p'_ctx) <- mkSymPoly "p" [1, -2, 1]
  let m = snd (p'_body !! 1)
  let n = snd (p'_body !! 2)
  let q = (q'_body, ((\x -> ((fst x) .== 1) .|| ((fst x) .== -1)) <$> q'_body) ++ [snd (q'_body !! 5) .== n] ++ q'_ctx)
  let p = (p'_body, [n .> 2 * m, 2 * n ./= 7 * m] ++ p'_ctx)
  pure (pAdd (p `pMult` pCross p) (pScalarMult (-1) (q `pMult` pCross q)))

rMinus :: Symbolic SymPoly
rMinus = do
  qs <- sIntegers ((\x -> "a" ++ show x) <$> [0 .. 5])
  (q'_body, q'_ctx) <- mkSymPoly "k" qs
  (p'_body, p'_ctx) <- mkSymPoly "p" [1, -2, 1]
  let m = snd (p'_body !! 1)
  let n = snd (p'_body !! 2)
  let q = (q'_body, ((\x -> ((fst x) .== 1) .|| ((fst x) .== -1)) <$> q'_body) ++ [snd (q'_body !! 5) .== n] ++ q'_ctx)
  let p = (p'_body, [n .> 2 * m] ++ p'_ctx)
  pure (pAdd (p `pMult` pCross p) (pScalarMult (-1) (q `pMult` pCross q)))

rPlus :: Symbolic SymPoly
rPlus = do
  qs <- sIntegers ((\x -> "a" ++ show x) <$> [0 .. 5])
  (q'_body, q'_ctx) <- mkSymPoly "k" qs
  (p'_body, p'_ctx) <- mkSymPoly "p" [1, -2, 1]
  let m = snd (p'_body !! 1)
  let n = snd (p'_body !! 2)
  let q = (q'_body, ((\x -> ((fst x) .== 1) .|| ((fst x) .== -1)) <$> q'_body) ++ [snd (q'_body !! 5) .== n] ++ q'_ctx)
  let p = (p'_body, [n .> 2 * m, 2 * n ./= 7 * m] ++ p'_ctx)
  pure (pAdd (p `pMult` pCross p) (q `pMult` pCross q))

distinctAlpha :: Symbolic SymPoly
distinctAlpha = do
  [a_1, b_1, a_2, b_2, k_1, k_2] <- sIntegers (["a_1", "b_1", "a_2", "b_2", "k_1", "k_2"])
  let p_1 = ([(1, a_1 * k_1), (-2, b_1 * k_1), (1, 0)], [a_1 .> b_1, b_1 .> 0, k_1 .> 0]) :: SymPoly
  let p_2 = ([(1, a_2 * k_2), (-2, b_2 * k_2), (1, 0)], [a_2 .> b_2, b_2 .> 0, k_2 .> 0]) :: SymPoly
  let q_1 = ([(1, k_1), (-1, 0)], []) :: SymPoly
  let q_2 = ([(1, k_2), (-1, 0)], [k_2 ./= k_1]) :: SymPoly
  pure $ (pAdd (pMult q_2 p_1) (pScalarMult (-1) (pMult q_1 p_2)))

distinctBeta :: Symbolic SymPoly
distinctBeta = do
  [a_1, b_1, a_2, b_2, k_1, k_2] <- sIntegers (["a_1", "b_1", "a_2", "b_2", "k_1", "k_2"])
  let p_1 = ([(-2, a_1 * k_1), (1, b_1 * k_1), (1, 0)], [a_1 .> b_1, b_1 .> 0, k_1 .> 0]) :: SymPoly
  let p_2 = ([(-2, a_2 * k_2), (1, b_2 * k_2), (1, 0)], [a_2 .> b_2, b_2 .> 0, k_2 .> 0]) :: SymPoly
  let q_1 = ([(1, k_1), (-1, 0)], []) :: SymPoly
  let q_2 = ([(1, k_2), (-1, 0)], [k_2 ./= k_1]) :: SymPoly
  pure $ (pAdd (pMult q_2 p_1) (pScalarMult (-1) (pMult q_1 p_2)))

distinctAlphaMuK :: Symbolic SymPoly
distinctAlphaMuK = do
  [a_1, b_1, k_1, k_2] <- sIntegers (["a_1", "b_1", "k_1", "k_2"])
  let p_1 = ([(1, a_1 * k_1), (-2, b_1 * k_1), (1, 0)], [a_1 .> b_1, b_1 .> 0, k_1 .> 0]) :: SymPoly
  let q_1 = ([(1, k_1), (-1, 0)], []) :: SymPoly
  let mu = ([(1, 3 * k_2), (1, k_2), (1, 0)], [k_2 .> 0]) :: SymPoly
  pure $ pAdd p_1 (pScalarMult (-1) (pMult mu q_1))

distinctAlphaNuK :: Symbolic SymPoly
distinctAlphaNuK = do
  [a_1, b_1, k_1, k_2] <- sIntegers (["a_1", "b_1", "k_1", "k_2"])
  let p_1 = ([(1, a_1 * k_1), (-2, b_1 * k_1), (1, 0)], [a_1 .> b_1, b_1 .> 0, k_1 .> 0]) :: SymPoly
  let q_1 = ([(1, k_1), (-1, 0)], []) :: SymPoly
  let mu = ([(1, 3 * k_2), (1, 2 * k_2), (-1, 0)], [k_2 .> 0]) :: SymPoly
  pure $ pAdd p_1 (pScalarMult (-1) (pMult mu q_1))
