module SetTheory where

open import Agda.Primitive
open import BaseLogic
open import Data.Bool

-- Subsets:
-- Can't switch over set-membership with definition
Powerset : ∀ {α} (A : Set α) → Set (lsuc lzero ⊔ α)
Powerset {α} A = A → Set

-- A subset S ⊂ A is given by S : Powerset A
-- An object a : A is an element of the subset if (S a) has a proof
-- The set of elements of the subset is given by:
-- ∃ a ∈ A , ∥ S a ∥

[_||_⊆_] : ∀ {α} (X : Set α) (A B : Powerset X) → Set α
[ X || A ⊆ B ] = (x : X) → A x → B x

[_||_⊂_] : ∀ {α} (X : Set α) (A B : Powerset X) → Set α
[ X || A ⊂ B ] = ((x : X) → A x → B x) ∧ (∃ x ∈ X , ((A x → ⊥) ∧ B x))

-- Subsets with decidable set-membership.
Powerset' : ∀ {α} (A : Set α) → Set α
Powerset' {α} A = A → Bool

FullSet' : ∀ {α} (A : Set α) → Powerset' A
FullSet' A = λ x → true

EmptySet' : ∀ {α} (A : Set α) → Powerset' A
EmptySet' A = λ x → false


[_||_⊆_]' : ∀ {α} (X : Set α) (A B : Powerset' X) → Set α
[ X || A ⊆ B ]' = (x : X) → (A x ≡ true) → (B x ≡ true)
 
[_||_⊂_]' : ∀ {α} (X : Set α) (A B : Powerset' X) → Set α
[ X || A ⊂ B ]' = ((x : X) → (A x ≡ true) → (B x ≡ true)) ∧ (∃ x ∈ X , ((A x ≡ false) ∧ (B x ≡ true)))

-- A subset S ⊂ A is given by S : Powerset' A
-- An object a : A is an element of the subset if (S a) ≡ true has a proof
-- The set of elements of the subset is given by:
-- ∃ a ∈ A , ∥ Sa ≡ true ∥
-- You can use this version in if-statements, like:
-- if (S a) then .. else ...
-- And you can differentiate between the interior and exterior of the subset:
Interior : ∀ {α} {A : Set α} → Powerset' A → Set α
Interior {α} {A} S = ∃ a ∈ A , ∥ S a ≡ true ∥

Exterior : ∀ {α} {A : Set α} → Powerset' A → Set α
Exterior {α} {A} S = ∃ a ∈ A , ∥ S a ≡ false ∥
