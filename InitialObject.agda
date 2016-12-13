module InitialObject where

open import Agda.Primitive
open import BaseLogic
open import Category

record InitialObject {i j} (C : Category {i} {j}) : Set (i ⊔ j) where
 field
  initial-obj : Category.obj C
  initiality : (x : Category.obj C) → ∃ f ∈ ((Category.hom C) initial-obj x) , ((g : ((Category.hom C) initial-obj x)) → f ≡ g)
