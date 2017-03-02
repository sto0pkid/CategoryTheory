module ListVector where

open import Data.Nat
open import Data.List
open import Data.List.Operations
open import Data.Vector

vector2list : ∀ {i} {A : Set i} {n : Nat} → Vector A n → List A
vector2list {i} {A} {zero} [] = []
vector2list {i} {A} {suc n} (Data.Vector._∷_ a as) = Data.List._∷_ a (vector2list as)

list2vector : ∀ {i} {A : Set i} → (l : List A) → Vector A (length l)
list2vector {i} {A} [] = []
list2vector {i} {A} (Data.List._∷_ a as) = Data.Vector._∷_ a (list2vector as)
