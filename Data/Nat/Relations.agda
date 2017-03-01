module Data.Nat.Relations where

open import BaseLogic
open import Data.Nat
open import Data.Nat.Operations
open import Data.Product
open import Data.PropositionalEquality

-- could irrelefy π₂
infixr 3 _≥_
_≥_ : Nat → Nat → Set
x ≥ y = ∃ n ∈ Nat , (plus y n ≡ x)

infixr 3 _≤_ 
_≤_ : Nat → Nat → Set
x ≤ y = y ≥ x

infixr 3 _>_
-- could irrelefy π₂
_>_ : Nat → Nat → Set
x > y = ∃ n ∈ Nat , (plus y (suc n) ≡ x)

infixr 3 _<_
_<_ : Nat → Nat → Set
x < y = y > x
