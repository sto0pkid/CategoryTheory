module Morphisms where

open import Agda.Primitive
--open import BaseLogic
open import Category
open import Data.Product
open import Data.PropositionalEquality

iso : ∀ {i j} {C : Category {i} {j}} → {x y : Category.obj C} → ((Category.hom C) x y) → Set j
iso {i} {j} {C} {x} {y} f = ∃ f⁻¹ ∈ (hom y x) , (((f ∘ f⁻¹) ≡ (id y)) ∧ ((f⁻¹ ∘ f) ≡ (id x)))
 where
  obj = Category.obj C
  hom = Category.hom C
  _∘_ = Category.comp C
  id = Category.id C

mono : ∀ {i j} {C : Category {i} {j}} → {x y : Category.obj C} → ((Category.hom C) x y) → Set (j ⊔ i)
mono {i} {j} {C} {x} {y} f = (z : obj) → (g₁ g₂ : hom z x) → (f ∘ g₁) ≡ (f ∘ g₂) → g₁ ≡ g₂
 where
  obj = Category.obj C
  hom = Category.hom C
  _∘_ = Category.comp C
  id = Category.id C

epi : ∀ {i} {j} {C : Category {i} {j}} → {x y : Category.obj C} → ((Category.hom C) x y) → Set (j ⊔ i)
epi {i} {j} {C} {x} {y} f = (z : obj) → (g₁ g₂ : hom y z) → (g₁ ∘ f) ≡ (g₂ ∘ f) → g₁ ≡ g₂
 where
  obj = Category.obj C
  hom = Category.hom C
  _∘_ = Category.comp C
  id = Category.id C
