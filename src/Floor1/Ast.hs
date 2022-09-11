{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
module Floor1.Ast where

import           Control.Applicative
import           Control.Monad.State.Strict (State, evalState, state)
import           Data.Finite                (Finite)
import           Data.Kind
import           Data.Maybe                 (fromMaybe)
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.TypeLits
import           Data.Text                  (Text)
import qualified Data.Text                  as Text
import           Data.Vector.Sized          (Vector)
import qualified Data.Vector.Sized          as Vector
import           Text.Show.Functions        ()

type VarContext = Vector

varCtxAccess :: Vector n a -> Finite n -> a
varCtxAccess = Vector.index

data Exp_ var where
  Prop :: Text -> [var] -> Exp_ var
  Top :: Exp_ var
  Bot :: Exp_ var
  Imp :: Exp_ var -> Exp_ var -> Exp_ var
  Conj :: Exp_ var -> Exp_ var -> Exp_ var
  Disj :: Exp_ var -> Exp_ var -> Exp_ var
  Neg :: Exp_ var -> Exp_ var
  UniQ :: Maybe Text -> (var -> Exp_ var) -> Exp_ var
  ExtQ :: Maybe Text -> (var -> Exp_ var) -> Exp_ var

deriving stock instance (Show var) => Show (Exp_ var)

type ExpContext n = Vector n (Maybe Text)

-- | Note: 'Exp' @0@ is a closed expression
data Exp n
  = Exp
    { expNum     :: SNat n
    , expContext :: ExpContext n
    , runExp     :: forall var. VarContext n var -> Exp_ var
    }

data SomeExp = forall n. SomeExp (Exp n)

emptyExpContext :: (KnownNat n) => ExpContext n
emptyExpContext = Vector.replicate Nothing

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
  {-# INLINEABLE expPrec #-}

instance ExpPrec 'Disj where
  expPrec _ = 2
  {-# INLINEABLE expPrec #-}

instance ExpPrec 'Neg where
  expPrec _ = 2
  {-# INLINEABLE expPrec #-}

instance ExpPrec 'UniQ where
  expPrec _ = 0
  {-# INLINEABLE expPrec #-}
  argPrec _ = 0
  {-# INLINEABLE argPrec #-}

instance ExpPrec 'ExtQ where
  expPrec _ = 0
  {-# INLINEABLE expPrec #-}
  argPrec _ = 0
  {-# INLINEABLE argPrec #-}

toHaskellCode :: forall n. Exp n -> Text
toHaskellCode f@Exp{expNum = SNat} =
  Vector.withSizedList fvBasis $ \case
    v@((pn %~) . singByProxy . Vector.length' -> Proved Refl) ->
      let
        fvNames = liftA2 ((("fv_" <>) .) . fromMaybe) v (expContext f)
      in
        bindFvNames (Vector.toList fvNames)
        <> "\n  "
        <> evalState (go (runExp f fvNames) 0) bvNames
    _ ->
      error
      $ "toHaskellCode: impossible length of fvBasis: "
      <> show (length fvBasis)
      <> " for Exp "
      <> show (natVal pn)
  where
    pn = SNat @n
    (fvBasis, bvNames) = splitAt (fromIntegral (natVal pn)) $ flip Text.cons <$> "" : fmap (Text.pack . show) [(0 :: Integer)..] <*> ['a'..'z']

    bindFvNames fvs =
      Text.intercalate "\n"
        [ "\\ctx ->"
        , "  let"
        , Text.intercalate "\n" $ zipWith (\fv n -> "    " <> fv <> " = ctx `varCtxAccess` " <> Text.pack (show n)) fvs [(0 :: Integer)..]
        , "  in"
        ]

    wrap :: Text -> Text
    wrap = ("(" <>) . (<> ")")
    wrapPrec prec ePrec = if prec > ePrec then wrap else id

    goBinary a b con prec = wrapPrec prec 10 . (con <>) <$> (Text.intercalate " " <$> sequenceA [go a 11, go b 11])

    goQuantifier ms g con prec = do
      n <- state ((,) <$> head <*> tail)
      wrapPrec prec 10
        . (con <>)
        . (Text.pack (showsPrec 11 ms "") <>)
        . (" " <>)
        . wrap
        . (("\\" <> n <> " -> ") <>) <$> go (g n) 0

    go :: Exp_ Text -> Int -> State [Text] Text
    go (Prop h vs) prec = pure . wrapPrec prec 10 . ("Prec " <>) . (Text.pack (showsPrec 11 h "") <>) $ " [" <> Text.intercalate ", " vs <> "]"
    go e@Top prec = pure . Text.pack $ showsPrec prec e ""
    go e@Bot prec = pure . Text.pack $ showsPrec prec e ""
    go (Imp a b) prec = goBinary a b "Imp " prec
    go (Conj a b) prec = goBinary a b "Conj " prec
    go (Disj a b) prec = goBinary a b "Disj " prec
    go (Neg a) prec = wrapPrec prec 10 . ("Neg " <>) <$> go a 11
    go (UniQ ms g) prec = goQuantifier ms g "UniQ " prec
    go (ExtQ ms g) prec = goQuantifier ms g "ExtQ " prec

toFormatted :: forall n. Exp n -> Text
toFormatted f@Exp{expNum = SNat} =
  Vector.withSizedList fvBasis $ \case
    v@((pn %~) . singByProxy . Vector.length' -> Proved Refl) ->
      let
        fvNames = liftA2 ((("?fv_" <>) .) . fromMaybe) v (expContext f)
      in
        evalState (go (runExp f fvNames) 0) bvNames
    _ ->
      error
      $ "toFormatted: impossible length of fvBasis: "
      <> show (length fvBasis)
      <> " for Exp "
      <> show (natVal pn)
  where
    pn = SNat @n
    (fvBasis, bvNames) = splitAt (fromIntegral (natVal pn)) $ flip Text.cons <$> "" : fmap (Text.pack . show) [(0 :: Integer)..] <*> ['a'..'z']

    wrap :: Text -> Text
    wrap = ("(" <>) . (<> ")")
    wrapPrec prec pc = if prec > expPrec pc then wrap else id

    goBinary :: Exp_ Text -> Exp_ Text -> Text -> Int -> (forall c. (ExpPrec c) => ExpArgPos c -> ExpArgPos c -> State [Text] Text)
    goBinary a b con prec = helper
      where
        helper :: forall c. (ExpPrec c) => ExpArgPos c -> ExpArgPos c -> State [Text] Text
        helper l r = wrapPrec prec (Proxy @c) . Text.intercalate con <$> sequenceA [go a (argPrec l), go b (argPrec r)]

    goQuantifier :: Maybe Text -> (Text -> Exp_ Text) -> Text -> Int -> (forall c. (ExpPrec c) => ExpArgPos c -> State [Text] Text)
    goQuantifier ms g q prec = helper
      where
        helper :: forall c. (ExpPrec c) => ExpArgPos c -> State [Text] Text
        helper u = do
          n <- getName
          wrapPrec prec (Proxy @c) . ((q <> n <> ". ") <>) <$> go (g n) (argPrec u)

        getName
          | Just s <- ms = pure s
          | otherwise = state ((,) <$> head <*> tail)

    go (Prop h vs) prec = pure . wrapPrec prec (Proxy @'Prop) . Text.unwords $ h : vs
    go Top _ = pure "^|^"
    go Bot _ = pure "_|_"
    go (Imp a b) prec = goBinary a b " -> " prec @'Imp ImpAntecedent ImpConsequent
    go (Conj a b) prec = goBinary a b " /\\ " prec @'Conj ConjLeftArg ConjRightArg
    go (Disj a b) prec = goBinary a b " \\/ " prec @'Disj DisjLeftArg DisjRightArg
    go (Neg a) prec = wrapPrec prec (Proxy @'Neg) . ("~ " <>) <$> go a (argPrec NegArg)
    go (UniQ ms g) prec = goQuantifier ms g "forall " prec @'UniQ UniQArg
    go (ExtQ ms g) prec = goQuantifier ms g "exists " prec @'ExtQ ExtQArg
