{-# LANGUAGE DataKinds #-}
module Floor1.Backward.Command where

import           Floor1.Ast
import           GHC.TypeLits

data Command n
  = CmdIntro
  | CmdTopI
  | CmdBotE
  | CmdImpI
  | CmdImpE (Exp n)
  | CmdConjI
  | CmdConjE1 (Exp n)
  | CmdConjE2 (Exp n)
  | CmdDisjI1
  | CmdDisjI2
  | CmdDisjE (Exp n) (Exp n)
  | CmdNegI
  | CmdNegE
  | CmdUniQI
  | CmdUniQE Integer
  | CmdExtQI Integer
  | CmdExtQE (Exp (1 + n))
