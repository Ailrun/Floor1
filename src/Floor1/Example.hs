{-# LANGUAGE DataKinds #-}
module Floor1.Example where

import qualified Data.Vector.Sized as Vector
import           Floor1.Ast

-- | Example expression 1
exp1 :: Exp 2
exp1 = Exp emptyExpContext $ \ctx ->
  let
    x = ctx `varCtxAccess` 0
    y = ctx `varCtxAccess` 1
  in
    Prop "P" [x, y]

-- | Example expression 2
exp2 :: Exp 2
exp2 = Exp (Vector.cons (Just "name") emptyExpContext) $ \ctx ->
  let
    a = ctx `varCtxAccess` 0
    b = ctx `varCtxAccess` 1
  in
    UniQ Nothing $ \x -> ExtQ Nothing $ \y ->
      Neg (Prop "P" [a, x]) `Conj` (Prop "Q" [y] `Disj` Prop "R" [b])
