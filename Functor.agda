module Functor where

open import Agda.Primitive
open import BaseLogic
open import Category

record Functor₀ {i j k l} (C : Category {i} {j}) (D : Category {k} {l}) : Set ((lsuc (i ⊔ j)) ⊔ (lsuc (k ⊔ l))) where
 field
  omap : (Category.obj C) → (Category.obj D)
  fmap : {x y : (Category.obj C)} → ((Category.hom C) x y) → ((Category.hom D) (omap x) (omap y))
  

record Functor {i j k l} (C : Category {i} {j}) (D : Category {k} {l}) : Set ((lsuc (i ⊔ j)) ⊔ (lsuc (k ⊔ l))) where
 field
  omap : (Category.obj C) → (Category.obj D)
  fmap : {x y : (Category.obj C)} → ((Category.hom C) x y) → ((Category.hom D) (omap x) (omap y)) 

  preserves-id : (x : (Category.obj C)) → (fmap ((Category.id C) x)) ≡ ((Category.id D) (omap x))
  preserves-comp : {x y z : (Category.obj C)} → (f : (Category.hom C) x y) → (g : (Category.hom C) y z) → (fmap ((Category.comp C) g f)) ≡ ((Category.comp D) (fmap g) (fmap f))
