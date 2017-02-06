module Data.PositiveNat where

--open import BaseLogic
open import Data.Nat
open import Data.Nat.Relations
open import Data.Product

PositiveNat : Set
PositiveNat = ∃ n ∈ Nat , (n > 0)
