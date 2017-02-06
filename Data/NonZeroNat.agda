module Data.NonZeroNat where

open import BaseLogic using (_≠_)
open import Data.Nat
open import Data.Nat.Relations
open import Data.Product

-- need to irrelefy π₂
NonZeroNat : Set
NonZeroNat = ∃ x ∈ Nat , (x ≠ 0)

-- need to irrelefy π₂
NonZeroNat₂ : Set
NonZeroNat₂ = ∃ x ∈ Nat , (x > 0)
