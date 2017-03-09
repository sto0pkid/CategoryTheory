module SetTheory where

open import Agda.Primitive
open import BaseLogic
open import Data.False
open import Data.True
open import Data.Disjunction
open import Data.Product
open import Data.PropositionalEquality
open import Data.Bool
open import Data.Bool.Operations
open import Data.Bool.Proofs
open import Data.Irrelevance
open import Level

Powerset : ∀ {α β} (A : Set α) → Set (lsuc β ⊔ α)
Powerset {α} {β} A = A → Set β

Subset : ∀ {α β} (A : Set α) → Set (lsuc β ⊔ α)
Subset {α} {β} A = A → Set β

FullSet : ∀ {α} (A : Set α) → Subset {α} {lzero} A
FullSet {α} A = λ x → ⊤

EmptySet : ∀ {α} (A : Set α) → Subset {α} {lzero} A
EmptySet {α} A = λ x → ⊥

Subset' : ∀ {α} (A : Set α) → Set α
Subset' {α} A = A → Bool

FullSet' : ∀ {α} (A : Set α) → Subset' A
FullSet' {α} A = λ x → true


EmptySet' : ∀ {α} (A : Set α) → Subset' A
EmptySet' {α} A = λ x → false

[_∈_] : ∀ {α β} {A : Set α} (x : A) → Subset {α} {β} A → Set β
[ x ∈ S ] = S x

[_∈_]' : ∀ {α} {A : Set α} (x : A) → Subset' A → Bool
[ x ∈ S ]' = S x

{-
   A subset S ⊂ A is given by S : Powerset A
   An object a : A is an element of the subset if (S a) has a proof
   The set of elements of the subset is given by:
   ∃ a ∈ A , ∥ S a ∥
-}

[_||_⊆_] : ∀ {α β} (X : Set α) (A B : Powerset {α} {β} X) → Set (β ⊔ α)
[ X || A ⊆ B ] = (x : X) → A x → B x

[_||_⊆_]₁ : ∀ {α β} (X : Set α) (A B : Subset {α} {β} X) → Set (β ⊔ α)
[ X || A ⊆ B ]₁ = (x : X) → A x → B x

[_||_⊂_] : ∀ {α β} (X : Set α) (A B : Powerset {α} {β} X) → Set (β ⊔ α)
[ X || A ⊂ B ] = ((x : X) → A x → B x) ∧ (∃ x ∈ X , ((A x → ⊥) ∧ B x))

[_||_⊂_]₁ : ∀ {α β} (X : Set α) (A B : Subset {α} {β} X) → Set (β ⊔ α)
[ X || A ⊂ B ]₁ = ((x : X) → A x → B x) ∧ (∃ x ∈ X , ((A x → ⊥) ∧ B x))


⊆-trans : ∀ {α β} {X : Set α} {A B C : Powerset {α} {β} X} → [ X || A ⊆ B ] → [ X || B ⊆ C ] → [ X || A ⊆ C ]
⊆-trans {α} {X} A⊆B B⊆C x Ax = B⊆C x (A⊆B x Ax)

{- 
   We can switch over set-membership with this definition. This defines a subset of A by a function
   A → Bool which returns "true" for elements in the subset and "false" for elements in the complement
   of the subset. Whereas `Powerset` defines subsets propositionally, `Powerset'` defines subsets
   algorithmically.
-} 
Powerset' : ∀ {α} (A : Set α) → Set α
Powerset' {α} A = A → Bool



{-
FullSet : ∀ {α} (A : Set α) → Subset A
FullSet A = λ x → true
-}

{-
FullSet' : ∀ {α} (A : Set α) → Powerset' A
FullSet' A = λ x → true

EmptySet' : ∀ {α} (A : Set α) → Powerset' A
EmptySet' A = λ x → false
-}

[_||_⊆_]' : ∀ {α} (X : Set α) (A B : Powerset' X) → Set α
[ X || A ⊆ B ]' = (x : X) → (A x ≡ true) → (B x ≡ true)
 
[_||_⊂_]' : ∀ {α} (X : Set α) (A B : Powerset' X) → Set α
[ X || A ⊂ B ]' = ((x : X) → (A x ≡ true) → (B x ≡ true)) ∧ (∃ x ∈ X , ((A x ≡ false) ∧ (B x ≡ true)))


⊆'-trans : ∀ {α} {X : Set α} {A B C : Powerset' X} → [ X || A ⊆ B ]' → [ X || B ⊆ C ]' → [ X || A ⊆ C ]'
⊆'-trans {α} {X} {A} {B} {C} A⊆B B⊆C x Ax≡true = B⊆C x (A⊆B x Ax≡true)



subsetUnion : ∀ {α β} {X : Set α} (A B : Subset {α} {β} X) → Subset X
subsetUnion {α} {β} {X} A B = λ x → (A x) ∨ (B x)

subsetUnion' : ∀ {α} {X : Set α} (A B : Powerset' X) → Powerset' X
subsetUnion' {α} {X} A B = λ x → (A x) or (B x)

subsetUnion₂ : ∀ {i j k l} {X : Set i} {Y : Set k} (A : Subset {i} {j} X) (B : Subset {k} {l} Y) → Subset {i ⊔ k} {j ⊔ l} (X ⊹ Y)
subsetUnion₂ {i} {j} {k} {l} {X} {Y} A B (inl x) = Lift {j} {j ⊔ l} (A x)
subsetUnion₂ {i} {j} {k} {l} {X} {Y} A B (inr y) = Lift {l} {j ⊔ l} (B y)




A⊆A∪B : ∀ {i} {X : Set i} (A B : Subset' X) → [ X || A ⊆ (subsetUnion' A B) ]'
A⊆A∪B {i} {X} A B x Ax = proof
 where
  or-Bx : Bool → Bool
  or-Bx b = b or (B x)

  [Ax-or-Bx≡true-or-Bx] : (A x) or (B x) ≡ true or (B x)
  [Ax-or-Bx≡true-or-Bx] = [x≡y]→[fx≡fy] or-Bx (A x) true Ax

  [true-or-Bx≡true] : true or (B x) ≡ true
  [true-or-Bx≡true] = true-or-x≡true (B x)

  proof : (A x) or (B x) ≡ true
  proof = ≡-trans [Ax-or-Bx≡true-or-Bx] [true-or-Bx≡true]
   

B⊆A∪B : ∀ {i} {X : Set i} (A B : Subset' X) → [ X || B ⊆ (subsetUnion' A B) ]'
B⊆A∪B {i} {X} A B x Bx = proof
 where
  Ax-or : Bool → Bool
  Ax-or b = (A x) or b

  [Ax-or-Bx≡Ax-or-true] : (A x) or (B x) ≡ (A x) or true
  [Ax-or-Bx≡Ax-or-true] = [x≡y]→[fx≡fy] Ax-or (B x) true Bx

  [Ax-or-true≡true] : (A x) or true ≡ true
  [Ax-or-true≡true] = x-or-true≡true (A x)

  proof : (A x) or (B x) ≡ true
  proof = ≡-trans [Ax-or-Bx≡Ax-or-true] [Ax-or-true≡true]

subsetIntersection : ∀ {α β} {X : Set α} (A B : Subset {α} {β} X) → Subset X
subsetIntersection {α} {β} {X} A B = λ x → (A x) ∧ (B x)

subsetIntersection' : ∀ {α} {X : Set α} (A B : Powerset' X) → Powerset' X
subsetIntersection' {α} {X} A B = λ x → (A x) and (B x)

subsetProduct : ∀ {i j k l} {X : Set i} {Y : Set k} (A : Subset {i} {j} X) (B : Subset {k} {l} Y) → Subset (X × Y)
subsetProduct {i} {j} {k} {l} {X} {Y} A B (x , y) = (A x) × (B y)

{-
A∩B⊆A : ∀ {i} {X : Set i} (A B : Subset' X) → [ X || (subsetIntersection' A B) ⊆ A ]'
A∩B⊆A {i} {X} A B x A∩Bx = 

A∩B⊆B 
-}


subsetComplement : ∀ {α β} {X : Set α} (A : Subset {α} {β} X) → Subset X
subsetComplement {α} {β} {X} A = λ x → (A x → ⊥)

subsetComplement' : ∀ {α} {X : Set α} (A : Powerset' X) → Powerset' X
subsetComplement' {α} {X} A = λ x → not (A x)

-- A subset S ⊂ A is given by S : Powerset' A
-- An object a : A is an element of the subset if (S a) ≡ true has a proof
-- The set of elements of the subset is given by:
-- ∃ a ∈ A , ∥ Sa ≡ true ∥
-- You can use this version in if-statements, like:
-- if (S a) then .. else ...
-- And you can differentiate between the interior and exterior of the subset:

Interior : ∀ {α β} {A : Set α} → Subset {α} {β} A → Set (β ⊔ α)
Interior {α} {β} {A} S = ∃ a ∈ A , ∥ S a ∥ 

Interior' : ∀ {α} {A : Set α} → Powerset' A → Set α
Interior' {α} {A} S = ∃ a ∈ A , ∥ S a ≡ true ∥

Exterior : ∀ {α β} {A : Set α} → Subset {α} {β} A → Set (β ⊔ α)
Exterior {α} {β} {A} S = ∃ a ∈ A , ∥ (S a → ⊥) ∥

Exterior' : ∀ {α} {A : Set α} → Powerset' A → Set α
Exterior' {α} {A} S = ∃ a ∈ A , ∥ S a ≡ false ∥
