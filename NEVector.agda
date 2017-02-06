module NEVector where

open import Data.Nat
open import Data.Nat.Operations
open import Data.Nat.Relations
open import Data.Product

data NEVec (A : Set) : Nat → Set where
 end : A → NEVec A (suc zero)
 _∷_ : {n : Nat} → A → NEVec A n → NEVec A (suc n)
