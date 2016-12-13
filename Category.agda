module Category where

open import Agda.Primitive
open import BaseLogic

record Category₀ {i j} : Set (lsuc (i ⊔ j))  where
 field
  obj : Set i
  hom : obj → obj → Set j
  id : (x : obj) → hom x x
  comp : {x y z : obj} → hom y z → hom x y → hom x z


record Category {i j } : Set (lsuc (i ⊔ j)) where
 field
  obj : Set i
  hom : obj → obj → Set j
  id : (x : obj) → hom x x
  comp : {x y z : obj} → hom y z → hom x y → hom x z

  left-id : {x y : obj} → (f : hom x y) → (comp (id y) f) ≡ f
  right-id : {x y : obj} → (f : hom x y) → (comp f (id x)) ≡ f
  assoc : {x y z w : obj} → (f : hom z w) (g : hom y z) (h : hom x y)
     → (comp (comp f g) h) ≡ (comp f (comp g h))

category-comp-rev : ∀ {i j} → (C : Category {i} {j}) → {x y z : (Category.obj C)} → (f : (Category.hom C) x y) → (g : (Category.hom C) y z) → (Category.hom C) x z
category-comp-rev {i} {j} C {x} {y} {z} f g = g ∘ f
 where
  _∘_ : {x y z : Category.obj C} → (Category.hom C y z) → (Category.hom C x y) → (Category.hom C x z)
  _∘_ = Category.comp C 
