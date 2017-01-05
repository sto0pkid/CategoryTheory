module Relations where

open import BaseLogic
open import Data.Bool

isReflexive : ∀ {i} {A : Set i} (r : A → A → Bool) → Set i
isReflexive {i} {A} r = (x : A) → (r x x ≡ true)

isSymmetric : ∀ {i} {A : Set i} (r : A → A → Bool) → Set i
isSymmetric {i} {A} r = (x y : A) → (r x y ≡ true) → (r y x ≡ true)

isSymmetric' : ∀ {i} {A : Set i} (r : A → A → Bool) → Set i
isSymmetric' {i} {A} r = (x y : A) (z : Bool) → (r x y ≡ z) → (r y x ≡ z)

isTransitive : ∀ {i} {A : Set i} (r : A → A → Bool) → Set i
isTransitive {i} {A} r = (x y z : A) → (r x y ≡ true) → (r y z ≡ true) → (r x z ≡ true)

isEquivalenceRelation : ∀ {i} {A : Set i} (r : A → A → Bool) → Set i
isEquivalenceRelation {i} {A} r = (isReflexive r) ∧ ((isSymmetric r) ∧ (isTransitive r))
