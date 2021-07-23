{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE MultiWayIf   #-}
{-# LANGUAGE ViewPatterns #-}
module Floor1.Backward where

import           Data.Bool          (bool)
import           Data.Either        (fromRight)
import           Data.Proxy         (Proxy (Proxy))
import           Data.Type.Equality
import           Data.Vector.Sized  (Vector)
import qualified Data.Vector.Sized  as Vector
import           Floor1.Ast
import           Floor1.Util
import           GHC.Tuple          (Unit (..))
import           GHC.TypeLits
import Data.Finite (packFinite)

type InferenceRule n extras newGoals = ProofGoal n -> extras -> Maybe newGoals

intro :: (KnownNat n) => InferenceRule n () ()
intro (ctx, g) _ = bool Nothing (Just ()) (g `inProofContext` ctx)

topI :: (KnownNat n) => InferenceRule n () ()
topI (_, f) _ =
  case runExp f (Vector.replicate ()) of
    Top -> Just ()
    _   -> Nothing

botE :: (KnownNat n) => InferenceRule n (Unit (Exp n)) (Unit (ProofGoal n))
botE (ctx, f) (Unit c) =
  case runExp f (Vector.replicate ()) of
    Bot -> Just $ Unit (ctx, c)
    _   -> Nothing

impI :: (KnownNat n) => InferenceRule n () (Unit (ProofGoal n))
impI (ctx, f) _ =
  case runExp f (Vector.replicate ()) of
    Imp _ _ -> Just $ Unit (Exp (impAntecedent . runExp f) : ctx, Exp (impConsequent . runExp f))
    _ -> Nothing
  where
    impAntecedent :: Exp_ a -> Exp_ a
    impAntecedent (Imp a _) = a
    impAntecedent _         = error "impI: impossible"

    impConsequent :: Exp_ a -> Exp_ a
    impConsequent (Imp _ b) = b
    impConsequent _         = error "impI: impossible"

impE :: InferenceRule n (Unit (Exp n)) (ProofGoal n, ProofGoal n)
impE (ctx, g) (Unit f) = Just ((ctx, Exp $ \vs -> Imp (runExp f vs) (runExp g vs)) , (ctx, f))

conjI :: (KnownNat n) => InferenceRule n () (ProofGoal n, ProofGoal n)
conjI (ctx, f) _ =
  case runExp f (Vector.replicate ()) of
    Conj _ _ -> Just ((ctx, Exp (conjLeftArg . runExp f)), (ctx, Exp (conjRightArg . runExp f)))
    _ -> Nothing
  where
    conjLeftArg :: Exp_ a -> Exp_ a
    conjLeftArg (Conj a _) = a
    conjLeftArg _          = error "conjI: impossible"

    conjRightArg :: Exp_ a -> Exp_ a
    conjRightArg (Conj _ b) = b
    conjRightArg _          = error "conjI: impossible"

conjE1 :: InferenceRule n (Unit (Exp n)) (Unit (ProofGoal n))
conjE1 (ctx, f) (Unit g) = Just $ Unit (ctx, Exp $ \vs -> Conj (runExp f vs) (runExp g vs))

conjE2 :: InferenceRule n (Unit (Exp n)) (Unit (ProofGoal n))
conjE2 (ctx, f) (Unit g) = Just $ Unit (ctx, Exp $ \vs -> Conj (runExp g vs) (runExp f vs))

disjI1 :: (KnownNat n) => InferenceRule n () (Unit (ProofGoal n))
disjI1 (ctx, f) _ =
  case runExp f (Vector.replicate ()) of
    Disj _ _ -> Just $ Unit (ctx, Exp (disjLeftArg . runExp f))
    _        -> Nothing
  where
    disjLeftArg :: Exp_ a -> Exp_ a
    disjLeftArg (Conj a _) = a
    disjLeftArg _          = error "disjI2: impossible"

disjI2 :: (KnownNat n) => InferenceRule n () (Unit (ProofGoal n))
disjI2 (ctx, f) _ =
  case runExp f (Vector.replicate ()) of
    Disj _ _ -> Just $ Unit (ctx, Exp (disjRightArg . runExp f))
    _        -> Nothing
  where
    disjRightArg :: Exp_ a -> Exp_ a
    disjRightArg (Conj _ b) = b
    disjRightArg _          = error "disj2: impossible"

disjE :: InferenceRule n (Exp n, Exp n) (ProofGoal n, ProofGoal n, ProofGoal n)
disjE (ctx, f) (g, h) = Just ((ctx, Exp $ \vs -> Disj (runExp g vs) (runExp h vs)) , (g : ctx, f) , (h : ctx, f))

negI :: (KnownNat n) => InferenceRule n () (Unit (ProofGoal n))
negI (ctx, f) () =
  case runExp f (Vector.replicate ()) of
    Neg _ -> Just $ Unit (ctx, Exp (negArg . runExp f))
    _     -> Nothing
  where
    negArg :: Exp_ a -> Exp_ a
    negArg (Neg a) = a
    negArg _       = error "negI: impossible"

negE :: InferenceRule n (Unit (Exp n)) (ProofGoal n, ProofGoal n)
negE (ctx, _) (Unit g) = Just ((ctx, Exp $ \vs -> Neg (runExp g vs)) , (ctx, g))

uniQI :: (KnownNat n) => InferenceRule n () (Unit (ProofGoal (1 + n)))
uniQI (ctx, f) _ =
  case runExp f (Vector.replicate ()) of
    UniQ _ -> Just $ Unit (expLifting <$> ctx, Exp $ \vs -> uniQArg (runExp f (Vector.tail vs)) (Vector.head vs))
    _      -> Nothing
  where
    uniQArg :: Exp_ var -> (var -> Exp_ var)
    uniQArg (UniQ g) = g
    uniQArg _        = error "uniQI: impossible"

-- | To eliminate universal quantifier, the variable of @n+1@-th
-- position should not appears in the proof context.
uniQE :: forall proxy n m. (KnownNat n, KnownNat (n + (1 + m))) => proxy n -> InferenceRule (n + (1 + m)) () (Unit (ProofGoal (n + m)))
uniQE pn (ctx, f) _
  | Just ctx' <- traverse unlift ctx
  = Just $ Unit (ctx', Exp $ UniQ . (runExp f .) . insertAt' pn)
  | otherwise = Nothing
  where
    unlift :: Exp (n + (1 + m)) -> Maybe (Exp (n + m))
    unlift g =
      Vector.withSizedList (fmap Right fvNames :: [Either Integer Integer]) $ \rfvs ->
        Vector.withSizedList (fvNNames ++ Left fv1 : fvMNames) $ \lfvs ->
          if
            | Just Refl <- sameNat pn1m $ Vector.length' lfvs
            , Just Refl <- sameNat pn1m $ Vector.length' rfvs ->
              if exp_EqWithNames (fmap Left bvNames) (runExp g rfvs) (runExp g lfvs)
              then
                -- @fv1@ (i.e. the variable of n+1-th position) does not
                -- appear in @g@, as both @Right@/@Left@ @fv1@ versions
                -- give the same 'Exp_'.
                Just
                $ Exp
                $ exp_varMap fromRightForce Right
                . runExp g
                . flip (insertAt' pn) (Left ())
                . fmap Right
              else
                Nothing
            | otherwise ->
                error
                $ "uniQE: impossible length of fvNames: "
                <> show (length fvNames)
                <> " for Exp "
                <> show (natVal pn1m)
      where
        pn1m = Proxy @(n + (1 + m))
        (fmap Right -> fvNNames, fv1MNames) = splitAt (fromIntegral (natVal pn)) fvNames
        fv1 = head fv1MNames
        (fmap Right -> fvMNames) = tail fv1MNames
        (fvNames, bvNames) = splitAt (fromIntegral (natVal pn1m)) [(0 :: Integer)..]

        fromRightForce = fromRight (error "uniQE: impossible dependency on irrelevant variables")

extQI :: (KnownNat n, KnownNat m) => InferenceRule n (Unit (Proxy m)) (Unit (ProofGoal n))
extQI (ctx, f) (Unit pm)
  | Just m <- packFinite (natVal pm)
  = case runExp f (Vector.replicate ()) of
      ExtQ _ -> Just $ Unit (ctx, Exp $ \vs -> extQArg (runExp f vs) (Vector.index vs m))
      _      -> Nothing
  | otherwise = Nothing
  where
    extQArg :: Exp_ var -> (var -> Exp_ var)
    extQArg (ExtQ g) = g
    extQArg _        = error "extQI: impossible"

extQE :: InferenceRule n (Unit (Exp (1 + n))) (ProofGoal n, ProofGoal (1 + n))
extQE (ctx, f) (Unit g) = Just ((ctx, Exp $ ExtQ . (runExp g .) . flip Vector.cons), (g : fmap expLifting ctx, expLifting f))
