module NaturalTransformations where

open import Agda.Primitive
open import BaseLogic
open import Category
open import Functor

record NaturalTransformation {i j k l} {C : Category {i} {j}} {D : Category {k} {l}} (F G : Functor C D) : Set ((i ⊔ j) ⊔ (k ⊔ l)) where
 field
  η : (x : Category.obj C) → ((Category.hom D) ((Functor.omap F) x) ((Functor.omap G) x))
  η-comm : (x y : Category.obj C) → (f : (Category.hom C) x y) → ((Category.comp D) (η y) ((Functor.fmap F) f)) ≡ ((Category.comp D) ((Functor.fmap G) f) (η x))

{-
record NaturalIsomorphism {i j k l} {C : Category {i} {j}} {D : Category {k} {l}} (F G : Functor C D) : Set ((i ⊔ j) ⊔ (k ⊔ l)) where
 field
  η : NaturalTransformation {i} {j} {k} {l} {C} {D} F G
  η-iso : (x : Category.obj C) → (
-}

