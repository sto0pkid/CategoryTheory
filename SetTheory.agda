module SetTheory where

open import Agda.Primitive
open import BaseLogic
open import Data.Bool

{-
   Subsets:
   Can't switch over set-membership with this definition. What we can do with this definition
   though is define a subset by a proposition that it's elements must satisfy in order to be
   called members of the subset.
-}
Powerset : ∀ {α} (A : Set α) → Set (lsuc lzero ⊔ α)
Powerset {α} A = A → Set

{-
   A subset S ⊂ A is given by S : Powerset A
   An object a : A is an element of the subset if (S a) has a proof
   The set of elements of the subset is given by:
   ∃ a ∈ A , ∥ S a ∥
-}

[_||_⊆_] : ∀ {α} (X : Set α) (A B : Powerset X) → Set α
[ X || A ⊆ B ] = (x : X) → A x → B x

[_||_⊂_] : ∀ {α} (X : Set α) (A B : Powerset X) → Set α
[ X || A ⊂ B ] = ((x : X) → A x → B x) ∧ (∃ x ∈ X , ((A x → ⊥) ∧ B x))


⊆-trans : ∀ {α} {X : Set α} {A B C : Powerset X} → [ X || A ⊆ B ] → [ X || B ⊆ C ] → [ X || A ⊆ C ]
⊆-trans {α} {X} A⊆B B⊆C x Ax = B⊆C x (A⊆B x Ax)

{- 
   We can switch over set-membership with this definition. This defines a subset of A by a function
   A → Bool which returns "true" for elements in the subset and "false" for elements in the complement
   of the subset. Whereas `Powerset` defines subsets propositionally, `Powerset'` defines subsets
   algorithmically.
-} 
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


⊆'-trans : ∀ {α} {X : Set α} {A B C : Powerset' X} → [ X || A ⊆ B ]' → [ X || B ⊆ C ]' → [ X || A ⊆ C ]'
⊆'-trans {α} {X} {A} {B} {C} A⊆B B⊆C x Ax≡true = B⊆C x (A⊆B x Ax≡true)

subsetUnion' : ∀ {α} {X : Set α} (A B : Powerset' X) → Powerset' X
subsetUnion' {α} {X} A B = λ x → (A x) or (B x)

subsetIntersection' : ∀ {α} {X : Set α} (A B : Powerset' X) → Powerset' X
subsetIntersection' {α} {X} A B = λ x → (A x) and (B x)

subsetComplement' : ∀ {α} {X : Set α} (A : Powerset' X) → Powerset' X
subsetComplement' {α} {X} A = λ x → not (A x)

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


