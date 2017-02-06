module Data.Fin where

open import Data.Nat
open import Data.Nat.Operations

-- Fin n is a set with n elements.
data Fin : Nat → Set where
 zero : {n : Nat} → Fin (suc n)
 suc : {n : Nat} → (i : Fin n) → Fin (suc n)

fromℕ : (n : Nat) → Fin (suc n)
fromℕ zero = zero
fromℕ (suc n) = suc (fromℕ n)

raise : ∀ {m : Nat} (n : Nat) → Fin m → Fin (n + m)
raise zero i = i
raise (suc n) i = suc (raise n i)
