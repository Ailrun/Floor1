{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE ViewPatterns #-}
module Floor1.Ast where

import           Control.Monad.State.Strict (State, evalState, state)
import           Data.Finite                (Finite)
import           Data.Kind
import qualified Data.List                  as List
import           Data.Proxy                 (Proxy (..))
import           Data.Type.Equality
import           Data.Vector.Sized          (Vector)
import qualified Data.Vector.Sized          as Vector
import           GHC.TypeNats
import           Text.Show.Functions        ()

type VarContext = Vector

varCtxAccess :: Vector n a -> Finite n -> a
varCtxAccess = Vector.index

type ProofContext n = [Exp n]
type ProofGoal n = (ProofContext n, Exp n)

data Exp_ var where
  Prop :: String -> [var] -> Exp_ var
  Top :: Exp_ var
  Bot :: Exp_ var
  Imp :: Exp_ var -> Exp_ var -> Exp_ var
  Conj :: Exp_ var -> Exp_ var -> Exp_ var
  Disj :: Exp_ var -> Exp_ var -> Exp_ var
  Neg :: Exp_ var -> Exp_ var
  UniQ :: (var -> Exp_ var) -> Exp_ var
  ExtQ :: (var -> Exp_ var) -> Exp_ var

deriving stock instance (Show var) => Show (Exp_ var)

-- | Note: 'Exp' @0@ is a closed expression
newtype Exp n = Exp { runExp :: forall var. VarContext n var -> Exp_ var }

data family ExpArgPos :: forall k. k -> Type
data instance ExpArgPos 'Prop
data instance ExpArgPos 'Top
data instance ExpArgPos 'Bot
data instance ExpArgPos 'Imp = ImpAntecedent | ImpConsequent
data instance ExpArgPos 'Conj = ConjLeftArg | ConjRightArg
data instance ExpArgPos 'Disj = DisjLeftArg | DisjRightArg
data instance ExpArgPos 'Neg = NegArg
data instance ExpArgPos 'UniQ = UniQArg
data instance ExpArgPos 'ExtQ = ExtQArg

type ExpPrec :: forall k. k -> Constraint
class ExpPrec a where
  expPrec :: proxy a -> Int

  argPrec :: ExpArgPos a -> Int
  argPrec _ = 1 + expPrec (Proxy :: Proxy a)
  {-# INLINEABLE argPrec #-}
  {-# MINIMAL expPrec #-}

instance ExpPrec 'Prop where
  expPrec _ = 3
  {-# INLINEABLE expPrec #-}

instance ExpPrec 'Imp where
  expPrec _ = 1
  {-# INLINEABLE expPrec #-}
  argPrec ImpAntecedent = 2
  argPrec ImpConsequent = 1
  {-# INLINEABLE argPrec #-}

instance ExpPrec 'Conj where
  expPrec _ = 2

instance ExpPrec 'Disj where
  expPrec _ = 2

instance ExpPrec 'Neg where
  expPrec _ = 2

instance ExpPrec 'UniQ where
  expPrec _ = 0
  argPrec _ = 0

instance ExpPrec 'ExtQ where
  expPrec _ = 0
  argPrec _ = 0

toHaskellCode :: forall n. (KnownNat n) => Exp n -> String
toHaskellCode (Exp f) =
  Vector.withSizedList fvNames $ \case
    v@(sameNat pn . Vector.length' -> Just Refl) ->
      bindFvNames fvNames <> "\n  " <> evalState (go (f v) 0) bvNames ""
    _ -> error $ "toHaskellCode: impossible length of fvNames: " <> show (length fvNames) <> " for Exp " <> show (natVal pn)
  where
    pn = Proxy @n
    bvNames = flip (:) <$> "" : fmap show [(0 :: Integer)..] <*> ['a'..'z']
    (fvNames, _) = splitAt (fromIntegral (natVal pn)) $ fmap ("fv_" <>) bvNames

    bindFvNames fvs =
      List.intercalate "\n"
        [ "\\ctx ->"
        , "  let"
        , List.intercalate "\n" $ zipWith (\fv n -> "    " <> fv <> " = ctx `varCtxAccess` " <> show n) fvs [(0 :: Integer)..]
        , "  in"
        ]

    goBinary a b con prec = showParen (prec > 10) . (showString con .) <$> ((.) . (. showString " ") <$> go a 11 <*> go b 11)

    goQuantifier g con prec = do
      n <- state ((,) <$> head <*> tail)
      showParen (prec > 10) . (showString con .) . showParen True . (showString ("\\" <> n <> " -> ") .) <$> go (g n) 0

    go :: Exp_ String -> Int -> State [String] ShowS
    go (Prop h vs) prec = pure . showParen (prec > 10) $ showString "Prec " . showsPrec prec h . showString (" [" <> List.intercalate ", " vs <> "]")
    go e@Top prec = pure $ showsPrec prec e
    go e@Bot prec = pure $ showsPrec prec e
    go (Imp a b) prec = goBinary a b "Imp " prec
    go (Conj a b) prec = goBinary a b "Conj " prec
    go (Disj a b) prec = goBinary a b "Disj " prec
    go (Neg a) prec = showParen (prec > 10) . (showString "Neg " .) <$> go a 11
    go (UniQ g) prec = goQuantifier g "UniQ " prec
    go (ExtQ g) prec = goQuantifier g "ExtQ " prec

toFormatted :: forall n. (KnownNat n) => Exp n -> String
toFormatted (Exp f) =
  Vector.withSizedList fvNames $ \case
    v@(sameNat pn . Vector.length' -> Just Refl) -> evalState (go (f v) 0) bvNames
    _ -> error $ "toFormatted: impossible length of fvNames: " <> show (length fvNames) <> " for Exp " <> show (natVal pn)
  where
    pn = Proxy @n
    bvNames = flip (:) <$> "" : fmap show [(0 :: Integer)..] <*> ['a'..'z']
    (fvNames, _) = splitAt (fromIntegral (natVal pn)) $ fmap ("?fv_" <>) bvNames

    wrap = ("(" <>) . (<> ")")
    wrapPrec prec pc = if prec > expPrec pc then wrap else id

    goBinary :: Exp_ String -> Exp_ String -> String -> Int -> (forall c. (ExpPrec c) => ExpArgPos c -> ExpArgPos c -> State [String] String)
    goBinary a b con prec = helper
      where
        helper :: forall c. (ExpPrec c) => ExpArgPos c -> ExpArgPos c -> State [String] String
        helper l r = wrapPrec prec (Proxy @c) . List.intercalate con <$> sequenceA [go a (argPrec l), go b (argPrec r)]

    goQuantifier :: (String -> Exp_ String) -> String -> Int -> (forall c. (ExpPrec c) => ExpArgPos c -> State [String] String)
    goQuantifier g q prec = helper
      where
        helper :: forall c. (ExpPrec c) => ExpArgPos c -> State [String] String
        helper u = do
          n <- state ((,) <$> head <*> tail)
          wrapPrec prec (Proxy @c) . ((q <> n <> ". ") <>) <$> go (g n) (argPrec u)

    go (Prop h vs) prec = pure . wrapPrec prec (Proxy @'Prop) . unwords $ h : vs
    go Top _ = pure "^|^"
    go Bot _ = pure "_|_"
    go (Imp a b) prec = goBinary a b " -> " prec @'Imp ImpAntecedent ImpConsequent
    go (Conj a b) prec = goBinary a b " /\\ " prec @'Conj ConjLeftArg ConjRightArg
    go (Disj a b) prec = goBinary a b " \\/ " prec @'Disj DisjLeftArg DisjRightArg
    go (Neg a) prec = wrapPrec prec (Proxy @'Neg) . ("~ " <>) <$> go a (argPrec NegArg)
    go (UniQ g) prec = goQuantifier g "forall " prec @'UniQ UniQArg
    go (ExtQ g) prec = goQuantifier g "exists " prec @'ExtQ ExtQArg
