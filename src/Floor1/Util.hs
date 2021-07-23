{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE MultiWayIf   #-}
{-# LANGUAGE ViewPatterns #-}
module Floor1.Util where

import           Data.Proxy         (Proxy (Proxy))
import           Data.Type.Equality
import           Data.Vector.Sized  (Vector)
import qualified Data.Vector.Sized  as Vector
import           Floor1.Ast
import           GHC.TypeLits

{-# ANN exp_EqWithNames "HLint: ignore Use camelCase" #-}
exp_EqWithNames :: (Eq a) => [a] -> Exp_ a -> Exp_ a -> Bool
exp_EqWithNames _ (Prop ah avs) (Prop bh bvs) = ah == bh && avs == bvs
exp_EqWithNames _ Top Top = True
exp_EqWithNames _ Bot Bot = True
exp_EqWithNames ctx (Imp aa ab) (Imp ba bb) = exp_EqWithNames ctx aa ba && exp_EqWithNames ctx ab bb
exp_EqWithNames ctx (Conj aa ab) (Conj ba bb) = exp_EqWithNames ctx aa ba && exp_EqWithNames ctx ab bb
exp_EqWithNames ctx (Disj aa ab) (Disj ba bb) = exp_EqWithNames ctx aa ba && exp_EqWithNames ctx ab bb
exp_EqWithNames ctx (Neg a) (Neg b) = exp_EqWithNames ctx a b
exp_EqWithNames ctx (UniQ ag) (UniQ bg) = exp_EqWithNames (tail ctx) (ag (head ctx)) (bg (head ctx))
exp_EqWithNames ctx (ExtQ ag) (ExtQ bg) = exp_EqWithNames (tail ctx) (ag (head ctx)) (bg (head ctx))
exp_EqWithNames _ _ _ = False

expEq :: forall n. (KnownNat n) => Exp n -> Exp n -> Bool
expEq f g =
  Vector.withSizedList fvNames $ \case
    fvs@(sameNat pn . Vector.length' -> Just Refl) ->
      exp_EqWithNames bvNames (runExp f fvs) (runExp g fvs)
    _ -> error $ "intro: impossible length of fvNames: " <> show (length fvNames) <> " for Exp " <> show (natVal pn)
  where
    pn = Proxy @n

    (fvNames, bvNames) = splitAt (fromIntegral (natVal pn)) [(0 :: Integer)..]

expHetroEq :: forall n m. (KnownNat n, KnownNat m) => Exp n -> Exp m -> Bool
expHetroEq f g
  | Just Refl <- sameNat pn pm = expEq f g
  | otherwise = False
  where
    pn = Proxy @n
    pm = Proxy @m

inProofContext :: forall n. (KnownNat n) => Exp n -> ProofContext n -> Bool
inProofContext = any . expEq

inProofContextHetro :: forall n m. (KnownNat n, KnownNat m) => Exp n -> ProofContext m -> Bool
inProofContextHetro f ctx
  | Just Refl <- sameNat pn pm = inProofContext f ctx
  | otherwise = False
  where
    pn = Proxy @n
    pm = Proxy @m

expLifting :: Exp n -> Exp (1 + n)
expLifting f = Exp $ runExp f . Vector.tail

{-# ANN exp_varMap "HLint: ignore Use camelCase" #-}
exp_varMap :: (v -> u) -> (u -> v) -> Exp_ v -> Exp_ u
exp_varMap fvu _ (Prop h vs) = Prop h (fmap fvu vs)
exp_varMap _ _ Top = Top
exp_varMap _ _ Bot = Bot
exp_varMap fvu fuv (Imp a b) = Imp (exp_varMap fvu fuv a) (exp_varMap fvu fuv b)
exp_varMap fvu fuv (Conj a b) = Conj (exp_varMap fvu fuv a) (exp_varMap fvu fuv b)
exp_varMap fvu fuv (Disj a b) = Disj (exp_varMap fvu fuv a) (exp_varMap fvu fuv b)
exp_varMap fvu fuv (Neg a) = Neg (exp_varMap fvu fuv a)
exp_varMap fvu fuv (UniQ g) = UniQ (exp_varMap fvu fuv . g . fuv)
exp_varMap fvu fuv (ExtQ g) = ExtQ (exp_varMap fvu fuv . g . fuv)

insertAt' :: (KnownNat n) => proxy n -> Vector (n + m) a -> a -> Vector (n + (1 + m)) a
insertAt' pn (Vector.splitAt' pn -> (vs1, vs2)) v = vs1 Vector.++ Vector.cons v vs2
