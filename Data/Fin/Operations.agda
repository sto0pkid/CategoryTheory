module Data.Fin.Operations where

open import Data.Fin
open import Data.Nat
open import Data.Nat.Operations
open import Data.Nat.Relations

toNat : ∀ {n : Nat} → Fin n → Nat
toNat zero = zero
toNat (suc i) = suc (toNat i)

fromNat : (n : Nat) → Fin (suc n)
fromNat zero = zero
fromNat (suc n) = suc (fromNat n)

raise : {m : Nat} → (n : Nat) → Fin m → Fin (n + m)
raise zero i = i
raise (suc n) i = suc (raise n i)
