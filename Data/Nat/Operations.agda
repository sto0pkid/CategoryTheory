module Data.Nat.Operations where

open import Data.Nat
open import Data.Nat.BinPreds

plus : Nat → Nat → Nat
plus zero y = y
plus (suc x) y = suc (plus x y)

infixr 4 _+_
_+_ : Nat → Nat → Nat
x + y = plus x y

mult : Nat → Nat → Nat
mult zero y = zero
mult (suc x) y = plus y (mult x y)

infixr 5 _*_
_*_ : Nat → Nat → Nat
x * y = mult x y

prev : Nat → Nat
prev zero = zero
prev (suc x) = x

pred : Nat → Nat
pred x = prev x

_minus_ : Nat → Nat → Nat
zero minus y = zero
(suc x) minus zero = suc x
(suc x) minus (suc y) = x minus y
