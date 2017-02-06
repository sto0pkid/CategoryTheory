module Data.Nat.BinPreds where

open import Data.Bool
open import Data.Nat

_eq_ : Nat → Nat → Bool
zero eq zero = true
zero eq (suc y) = false
(suc x) eq zero = false
(suc x) eq (suc y) = x eq y

_gte_ : Nat → Nat → Bool
zero gte zero = true
zero gte (suc y) = false
(suc x) gte zero = true
(suc x) gte (suc y) = x gte y

_gt_ : Nat → Nat → Bool
zero gt y = false
(suc x) gt zero = true
(suc x) gt (suc y) = x gt y

_lte_ : Nat → Nat → Bool
x lte y = y gte x

_lt_ : Nat → Nat → Bool
x lt y = y gt x

isZero : Nat → Bool
isZero zero = true
isZero (suc x) = false

isEven : Nat → Bool
isEven zero = true
isEven (suc zero) = false
isEven (suc (suc x)) = isEven x

isOdd : Nat → Bool
isOdd zero = false
isOdd (suc zero) = true
isOdd (suc (suc x)) = isOdd x

isEven₂ : Nat → Bool
isEven₂ x = not (isOdd x)

isOdd₂ : Nat → Bool
isOdd₂ x = not (isEven x)
