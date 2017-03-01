module ListVector where

open import Data.Nat
open import Data.List
open import Data.List.Operations
open import Data.Vector

vector2list : ∀ {i} {A : Set i} {n : Nat} → Vector A n → List A
vector2list {i} {A} {zero} [] = []
vector2list {i} {A} {suc n} (a ∷ as) = a ∷ (vector2list as)

list2vector : ∀ {i} {A : Set i} → (l : List A) → Vector A (length l)
list2vector {i} {A} [] = []
list2vector {i} {A} (a ∷ as) = a ∷ (list2vector as)
