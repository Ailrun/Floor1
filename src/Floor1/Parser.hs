{-# LANGUAGE OverloadedLists #-}
module Floor1.Parser where

import           Data.IntMap       (IntMap)
import qualified Data.IntMap       as IntMap
import           Data.Set          (Set)
import qualified Data.Set          as Set
import           Data.Text         (Text)
import           Data.Vector.Sized (Vector)
import qualified Data.Vector.Sized as Vector
import           Data.Void
import           Floor1.Ast
import           Text.Megaparsec

type Parser a = Parsec Void Text a

data ExtExp var where
  ExtProp :: Text -> [var] -> ExtExp var
  ExtTop :: ExtExp var
  ExtBot :: ExtExp var
  ExtImp :: ExtExp var -> ExtExp var -> ExtExp var
  ExtConj :: ExtExp var -> ExtExp var -> ExtExp var
  ExtDisj :: ExtExp var -> ExtExp var -> ExtExp var
  ExtNeg :: ExtExp var -> ExtExp var
  ExtUniQ :: Text -> var -> ExtExp var -> ExtExp var
  ExtExtQ :: Text -> var -> ExtExp var -> ExtExp var
  deriving stock (Functor)

theorem :: Parser SomeExp
theorem = undefined

extexp :: Parser (ExtExp Text)
extexp = undefined

elaborate :: ExtExp Text -> SomeExp
elaborate ee = SomeExp $ Exp undefined undefined $ go (to ee) IntMap.empty
  where
    to :: ExtExp Text -> ExtExp Int
    to = undefined

    go :: ExtExp Int -> IntMap var -> Vector n var -> Exp_ var
    go (ExtProp h vs) im = Prop h . convs vs im
    go ExtTop _ = const Top
    go ExtBot _ = const Bot
    go (ExtImp a b) im = Imp <$> go a im <*> go b im
    go (ExtConj a b) im = Conj <$> go a im <*> go b im
    go (ExtDisj a b) im = Disj <$> go a im <*> go b im
    go (ExtNeg a) im = Neg <$> go a im
    go (ExtUniQ n i a) im = UniQ (Just n) <$> \var v -> go a (IntMap.insert i v im) var
    go (ExtExtQ n i a) im = ExtQ (Just n) <$> \var v -> go a (IntMap.insert i v im) var

    convs vs im = traverse (conv . (\v -> (v, v `IntMap.lookup` im))) vs

    conv (_, Just x)  = const x
    conv (i, Nothing) = (`Vector.unsafeIndex` i)

varsInExtexp :: ExtExp Text -> Set Text
varsInExtexp (ExtProp _ vs)  = Set.fromList vs
varsInExtexp ExtTop          = []
varsInExtexp ExtBot          = []
varsInExtexp (ExtImp a b)    = varsInExtexp a `Set.union` varsInExtexp b
varsInExtexp (ExtConj a b)   = varsInExtexp a `Set.union` varsInExtexp b
varsInExtexp (ExtDisj a b)   = varsInExtexp a `Set.union` varsInExtexp b
varsInExtexp (ExtNeg a)      = varsInExtexp a
varsInExtexp (ExtUniQ _ v a) = v `Set.insert` varsInExtexp a
varsInExtexp (ExtExtQ _ v a) = v `Set.insert` varsInExtexp a
