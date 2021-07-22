{-# LANGUAGE DataKinds #-}
module Floor1.Example where

import           Floor1.Ast

-- | Example expression 1
exp1 :: Exp 2
exp1 = Exp $ \ctx ->
  let
    x = ctx `varCtxAccess` 0
    y = ctx `varCtxAccess` 1
  in
    Prop "P" [x, y]

-- | Example expression 2
exp2 :: Exp 2
exp2 = Exp $ \ctx ->
  let
    a = ctx `varCtxAccess` 0
    b = ctx `varCtxAccess` 1
  in
    UniQ $ \x -> ExtQ $ \y ->
      Neg (Prop "P" [a, x]) `Conj` (Prop "Q" [y] `Disj` Prop "R" [b])
