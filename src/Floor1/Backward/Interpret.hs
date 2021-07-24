{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE MultiWayIf   #-}
{-# LANGUAGE ViewPatterns #-}
module Floor1.Backward.Interpret where

import           Data.Bool                (bool)
import           Data.Either              (fromRight)
import           Data.Finite              (packFinite)
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.TypeLits
import qualified Data.Vector.Sized        as Vector
import           Floor1.Ast
import           Floor1.Backward.Command
import           Floor1.Backward.State
import           Floor1.Util
import           GHC.Tuple                (Unit (..))

interpretCommand :: Command n -> ProofState n -> Either String (Maybe SomeProofState)
interpretCommand CmdIntro (ProofState fg osgs)
  = interpretFailableNullaryCommand intro fg () osgs
    "Error: the focused goal is not in the context"
interpretCommand CmdTopI (ProofState fg osgs)
  = interpretFailableNullaryCommand intro fg () osgs
    "Error: the focused goal is not a truth proposition (Top)"
interpretCommand CmdBotE (ProofState fg osgs)
  | Unit fg' <- botE fg () = Right $ Just $ SomeProofState $ ProofState fg' osgs
interpretCommand CmdImpI (ProofState fg osgs)
  = interpretFailableUnaryCommand impI fg () osgs
    "Error: the focused goal is not an implication (Imp)"
interpretCommand (CmdImpE g) (ProofState fg osgs)
  | (fg0, fg1) <- impE fg (Unit g) = Right $ Just $ SomeProofState $ ProofState fg0 (SomeProofGoal fg1 : osgs)
interpretCommand CmdConjI (ProofState fg osgs)
  = interpretFailableBinaryCommand conjI fg () osgs
    "Error: the focused goal is not a conjunction (Conj)"
interpretCommand (CmdConjE1 g) (ProofState fg osgs)
  | Unit fg' <- conjE1 fg (Unit g) = Right $ Just $ SomeProofState $ ProofState fg' osgs
interpretCommand (CmdConjE2 g) (ProofState fg osgs)
  | Unit fg' <- conjE2 fg (Unit g) = Right $ Just $ SomeProofState $ ProofState fg' osgs
interpretCommand CmdDisjI1 (ProofState fg osgs)
  = interpretFailableUnaryCommand disjI1 fg () osgs
    "Error: the focused goal is not a disjunction (Disj)"
interpretCommand CmdDisjI2 (ProofState fg osgs)
  = interpretFailableUnaryCommand disjI1 fg () osgs
    "Error: the focused goal is not a disjunction (Disj)"
interpretCommand (CmdDisjE g h) (ProofState fg osgs)
  | (fg0, fg1, fg2) <- disjE fg (g, h) = Right $ Just $ SomeProofState $ ProofState fg0 (SomeProofGoal fg1 : SomeProofGoal fg2 : osgs)
interpretCommand CmdNegI (ProofState fg osgs)
  = interpretFailableUnaryCommand negI fg () osgs
    "Error: the focused goal is not a negation (Neg)"
interpretCommand CmdNegE (ProofState fg osgs)
  = interpretFailableUnaryCommand negI fg () osgs
    "Error: the focused goal is not an implication with false consequent (Imp _ Bot)"
interpretCommand CmdUniQI (ProofState fg osgs)
  = interpretFailableUnaryCommand uniQI fg () osgs
    "Error: the focused goal is not an universally quantified proposition (UniQ)"
interpretCommand (CmdUniQE n) (ProofState fg@(expNum . snd -> pn1m@SNat) osgs)
  | n >= 0
  , m >= 0
  , SomeSing pn <- toSing (fromInteger n)
  , SomeSing pm <- toSing (fromInteger m)
  = go pn pm
  | otherwise
  = Left "Error: the variable index for the generalization is not valid"
  where
    m = n1m - n - 1
    n1m = fromIntegral (natVal pn1m)

    go :: SNat n
       -> SNat m
       -> Either String (Maybe SomeProofState)
    go pn@SNat pm@SNat
      | Proved Refl <- pn %+ (SNat @1 %+ pm) %~ pn1m
      = interpretFailableUnaryCommand (uniQE pn) fg () osgs
        "Error: the context of the focused goal contains the target variable of the generalization"
      | otherwise
      = error "interpretCommand: impossible"
interpretCommand (CmdExtQI m) (ProofState fg osgs)
  | m >= 0
  , SomeSing pm <- toSing (fromInteger m)
  = go pm
  | otherwise
  = Left "Error: the variable index for the existential instantiation is not valid"
  where
    go :: SNat m -> Either String (Maybe SomeProofState)
    go pm@SNat
      | Just (Unit fg') <- extQI fg (Unit pm)
      = Right $ Just $ SomeProofState $ ProofState fg' osgs
      | otherwise
      = undefined
interpretCommand (CmdExtQE g) (ProofState fg osgs)
  | (fg0, fg1) <- extQE fg (Unit g) = Right $ Just $ SomeProofState $ ProofState fg0 (SomeProofGoal fg1 : osgs)

type AlwaysPassInferenceRule n extras newGoals = ProofGoal n -> extras -> newGoals
type FailableInferenceRule n extras newGoals = ProofGoal n -> extras -> Maybe newGoals

interpretFailableNullaryCommand :: FailableInferenceRule n extras () -> ProofGoal n -> extras -> [SomeProofGoal] -> String -> Either String (Maybe SomeProofState)
interpretFailableNullaryCommand r fg e osgs errMsg
  | Just _ <- r fg e = Right $ nextGoal osgs
  | otherwise = Left errMsg

interpretFailableUnaryCommand :: FailableInferenceRule n extras (Unit (ProofGoal m)) -> ProofGoal n -> extras -> [SomeProofGoal] -> String -> Either String (Maybe SomeProofState)
interpretFailableUnaryCommand r fg e osgs errMsg
  | Just (Unit fg') <- r fg e = Right $ Just $ SomeProofState $ ProofState fg' osgs
  | otherwise = Left errMsg

interpretFailableBinaryCommand :: FailableInferenceRule n extras (ProofGoal m, ProofGoal l) -> ProofGoal n -> extras -> [SomeProofGoal] -> String -> Either String (Maybe SomeProofState)
interpretFailableBinaryCommand r fg e osgs errMsg
  | Just (fg0, fg1) <- r fg e = Right $ Just $ SomeProofState $ ProofState fg0 (SomeProofGoal fg1 : osgs)
  | otherwise = Left errMsg

intro :: FailableInferenceRule n () ()
intro (ctx, g) _ = bool Nothing (Just ()) (g `inProofContext` ctx)

topI :: FailableInferenceRule n () ()
topI (_, f@Exp{expNum = SNat}) _
  | Top <- runExp f (Vector.replicate ()) = Just ()
  | otherwise = Nothing

botE :: AlwaysPassInferenceRule n () (Unit (ProofGoal n))
botE (ctx, f) _ = Unit (ctx, f{ runExp = const Bot })

impI :: FailableInferenceRule n () (Unit (ProofGoal n))
impI (ctx, f@Exp{expNum = SNat}) _
  | Imp _ _ <- runExp f (Vector.replicate ()) = Just $ Unit (f{ runExp = impAntecedent . runExp f } : ctx, f{ runExp = impConsequent . runExp f })
  | otherwise = Nothing
  where
    impAntecedent :: Exp_ a -> Exp_ a
    impAntecedent (Imp a _) = a
    impAntecedent _         = error "impI: impossible"

    impConsequent :: Exp_ a -> Exp_ a
    impConsequent (Imp _ b) = b
    impConsequent _         = error "impI: impossible"

-- | precondition: In @impE (ctx, f) (Unit g)@, @f@ and @g@ should share
-- free variable names in exp context.
impE :: AlwaysPassInferenceRule n (Unit (Exp n)) (ProofGoal n, ProofGoal n)
impE (ctx, f) (Unit g) = ((ctx, f{ runExp = Imp <$> runExp g <*> runExp f }) , (ctx, g))

conjI :: FailableInferenceRule n () (ProofGoal n, ProofGoal n)
conjI (ctx, f@Exp{expNum = SNat}) _
  | Conj _ _ <- runExp f (Vector.replicate ()) = Just ((ctx, f{ runExp = conjLeftArg . runExp f }), (ctx, f{ runExp = conjRightArg . runExp f }))
  | otherwise = Nothing
  where
    conjLeftArg :: Exp_ a -> Exp_ a
    conjLeftArg (Conj a _) = a
    conjLeftArg _          = error "conjI: impossible"

    conjRightArg :: Exp_ a -> Exp_ a
    conjRightArg (Conj _ b) = b
    conjRightArg _          = error "conjI: impossible"

-- | precondition: In @conjE1 (ctx, f) (Unit g)@, @f@ and @g@ should share
-- free variable names in exp context.
conjE1 :: AlwaysPassInferenceRule n (Unit (Exp n)) (Unit (ProofGoal n))
conjE1 (ctx, f) (Unit g) = Unit (ctx, f{ runExp = Conj <$> runExp f <*> runExp g })

-- | precondition: In @conjE2 (ctx, f) (Unit g)@, @f@ and @g@ should share
-- free variable names in exp context.
conjE2 :: AlwaysPassInferenceRule n (Unit (Exp n)) (Unit (ProofGoal n))
conjE2 (ctx, f) (Unit g) = Unit (ctx, f{ runExp = Conj <$> runExp g <*> runExp f })

disjI1 :: FailableInferenceRule n () (Unit (ProofGoal n))
disjI1 (ctx, f@Exp{expNum = SNat}) _
  | Disj _ _ <- runExp f (Vector.replicate ()) = Just $ Unit (ctx, f{ runExp = disjLeftArg . runExp f })
  | otherwise = Nothing
  where
    disjLeftArg :: Exp_ a -> Exp_ a
    disjLeftArg (Conj a _) = a
    disjLeftArg _          = error "disjI2: impossible"

disjI2 :: FailableInferenceRule n () (Unit (ProofGoal n))
disjI2 (ctx, f@Exp{expNum = SNat}) _
  | Disj _ _ <- runExp f (Vector.replicate ()) = Just $ Unit (ctx, f{ runExp = disjRightArg . runExp f })
  | otherwise = Nothing
  where
    disjRightArg :: Exp_ a -> Exp_ a
    disjRightArg (Conj _ b) = b
    disjRightArg _          = error "disj2: impossible"

-- | precondition: In @conjE2 (ctx, f) (g, h)@, @g@ and @h@ should share
-- free variable names in exp context.
disjE :: AlwaysPassInferenceRule n (Exp n, Exp n) (ProofGoal n, ProofGoal n, ProofGoal n)
disjE (ctx, f) (g, h) = ((ctx, g{ runExp = Disj <$> runExp g <*> runExp h }) , (g : ctx, f) , (h : ctx, f))

negI :: FailableInferenceRule n () (Unit (ProofGoal n))
negI (ctx, f@Exp{expNum = SNat}) ()
  | Neg _ <- runExp f (Vector.replicate ()) = Just $ Unit (ctx, f{ runExp = flip Imp Bot . negArg . runExp f })
  | otherwise = Nothing
  where
    negArg :: Exp_ a -> Exp_ a
    negArg (Neg a) = a
    negArg _       = error "negI: impossible"

negE :: FailableInferenceRule n () (Unit (ProofGoal n))
negE (ctx, f@Exp{expNum = SNat}) _
  | Imp _ Bot <- runExp f (Vector.replicate ()) = Just $ Unit (ctx, f{ runExp = Neg . impAntecedent . runExp f })
  | otherwise = Nothing
  where
    impAntecedent :: Exp_ a -> Exp_ a
    impAntecedent (Imp a _) = a
    impAntecedent _         = error "impI: impossible"

uniQI :: FailableInferenceRule n () (Unit (ProofGoal (1 + n)))
uniQI (ctx, f@Exp{expNum = pn@SNat}) _
  | UniQ ms _ <- runExp f (Vector.replicate ())
  = Just $ Unit (expLifting <$> ctx, Exp (SNat %+ pn) (Vector.cons ms (expContext f)) $ uniQArg <$> runExp f . Vector.tail <*> Vector.head)
  | otherwise
  = Nothing
  where
    uniQArg :: Exp_ var -> (var -> Exp_ var)
    uniQArg (UniQ _ g) = g
    uniQArg _          = error "uniQI: impossible"

-- | To eliminate universal quantifier, the variable of @n+1@-th
-- position should not appears in the proof context.
uniQE :: forall n m. (KnownNat m) => SNat n -> FailableInferenceRule (n + (1 + m)) () (Unit (ProofGoal (n + m)))
uniQE pn@SNat (ctx, f@Exp{expNum = pn1m@SNat}) _
  | Just ctx' <- traverse unlift ctx
  = Just $ Unit (ctx', Exp pnm (deleteAt' pn (expContext f)) $ UniQ Nothing . (runExp f .) . insertAt' pn)
  | otherwise = Nothing
  where
    pnm :: SNat (n + m)
    pnm = pn %+ SNat @m

    unlift :: Exp (n + (1 + m)) -> Maybe (Exp (n + m))
    unlift g =
      Vector.withSizedList (fmap Right fvNames :: [Either Integer Integer]) $ \rfvs ->
        Vector.withSizedList (fvNNames ++ Left fv1 : fvMNames) $ \lfvs ->
          if
            | Proved Refl <- pn1m %~ singByProxy (Vector.length' lfvs)
            , Proved Refl <- pn1m %~ singByProxy (Vector.length' rfvs) ->
              if exp_EqWithNames (fmap Left bvNames) (runExp g rfvs) (runExp g lfvs)
              then
                -- @fv1@ (i.e. the variable of n+1-th position) does not
                -- appear in @g@, as both @Right@/@Left@ @fv1@ versions
                -- give the same 'Exp_'.
                Just
                $ Exp pnm (deleteAt' pn (expContext g))
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
        (fmap Right -> fvNNames, fv1MNames) = splitAt (fromIntegral (natVal pn)) fvNames
        fv1 = head fv1MNames
        (fmap Right -> fvMNames) = tail fv1MNames
        (fvNames, bvNames) = splitAt (fromIntegral (natVal pn1m)) [(0 :: Integer)..]

        fromRightForce = fromRight (error "uniQE: impossible dependency on irrelevant variables")

extQI :: FailableInferenceRule n (Unit (SNat m)) (Unit (ProofGoal n))
extQI (ctx, f@Exp{expNum = SNat}) (Unit pm@SNat)
  | Just m <- packFinite (fromIntegral (natVal pm))
  = case runExp f (Vector.replicate ()) of
      ExtQ _ _ -> Just $ Unit (ctx, f{ runExp = extQArg <$> runExp f <*> (`Vector.index` m) })
      _      -> Nothing
  | otherwise = Nothing
  where
    extQArg :: Exp_ var -> (var -> Exp_ var)
    extQArg (ExtQ _ g) = g
    extQArg _          = error "extQI: impossible"

extQE :: AlwaysPassInferenceRule n (Unit (Exp (1 + n))) (ProofGoal n, ProofGoal (1 + n))
extQE (ctx, f) (Unit g) = ((ctx, f{ runExp = ExtQ Nothing . (runExp g .) . flip Vector.cons }), (g : fmap expLifting ctx, expLifting f))

inProofContext :: Exp n -> ProofContext n -> Bool
inProofContext = any . expEq

inProofContextHetro :: forall n m. (KnownNat m) => Exp n -> ProofContext m -> Bool
inProofContextHetro f@Exp{expNum = pn@SNat} ctx
  | Proved Refl <- pn %~ SNat @m = inProofContext f ctx
  | otherwise = False
