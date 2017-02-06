module Decidability where

open import Agda.Primitive
open import BaseLogic
open import Data.Bool
open import Data.False
open import Data.Product
open import Data.PropositionalEquality

Decidable : ∀ {i j} → {A : Set i} → (P : A → Set j) → Set (j ⊔ i)
Decidable {i} {j} {A} P = ∃ f ∈ (A → Bool) , ((x : A) → ((((f x) ≡ true) → P x) ∧ (((f x) ≡ false) → (P x → ⊥))))

Decidable' : ∀ {i j} → {A : Set i} → (P : A → Set j) → Set (j ⊔ i)
Decidable' {i} {j} {A} P = ∃ f ∈ (A → Bool) , ((x : A) → ((((f x) ≡ true) ↔ P x) ∧ (((f x) ≡ false) ↔ (P x → ⊥))))

Decidable₂ : ∀ {i j k} → {A : Set i} → {B : Set j} → (P : A → B → Set k) → Set (k ⊔ (j ⊔ i))
Decidable₂ {i} {j} {k} {A} {B} P = ∃ f ∈ (A → B → Bool) , ((x : A) → (y : B) → ((((f x y) ≡ true) → P x y) ∧ (((f x y) ≡ false) → (P x y → ⊥))))

Decidable₂' : ∀ {i j k} → {A : Set i} → {B : Set j} → (P : A → B → Set k) → Set (k ⊔ (j ⊔ i))
Decidable₂' {i} {j} {k} {A} {B} P = ∃ f ∈ (A → B → Bool) , ((x : A) → (y : B) → ((((f x y) ≡ true) ↔ P x y) ∧ (((f x y) ≡ false) ↔ (P x y → ⊥))))
