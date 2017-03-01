module Data.Nat.Properties where

open import Agda.Primitive
open import BaseLogic
open import Data.Nat
open import Data.Bool
open import Data.Bool.Operations

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
