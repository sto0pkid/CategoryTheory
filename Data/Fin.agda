module Data.Fin where

open import Data.Nat

-- Fin n is a set with n elements.
data Fin : Nat → Set where
 zero : {n : Nat} → Fin (suc n)
 suc : {n : Nat} → (i : Fin n) → Fin (suc n)
