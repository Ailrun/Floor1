{-# LANGUAGE ViewPatterns #-}
module Floor1.Backward.State where

import           Data.Singletons.TypeLits
import           Floor1.Ast

type ProofContext n = [Exp n]
type ProofGoal n = (ProofContext n, Exp n)
data SomeProofGoal = forall n. SomeProofGoal (ProofGoal n)

fvNumOfProofGoal :: ProofGoal n -> SNat n
fvNumOfProofGoal (expNum . snd -> SNat) = SNat

data ProofState n
  = ProofState
    { focusedGoal :: ProofGoal n
    , otherGoals  :: [SomeProofGoal]
    }
data SomeProofState = forall n. SomeProofState (ProofState n)

nextGoal :: [SomeProofGoal] -> Maybe SomeProofState
nextGoal []                         = Nothing
nextGoal (SomeProofGoal fsg : osgs) = Just $ SomeProofState $ ProofState fsg osgs
