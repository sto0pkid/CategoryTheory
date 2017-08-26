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

Set[_] : ∀ {α} (A : Set α) → Subset {α} {lzero} A
Set[ A ] = λ x → ⊤

EmptySet : ∀ {α} (A : Set α) → Subset {α} {lzero} A
EmptySet {α} A = λ x → ⊥

Subset' : ∀ {α} (A : Set α) → Set α
Subset' {α} A = A → Bool

FullSet' : ∀ {α} (A : Set α) → Subset' A
FullSet' {α} A = λ x → true

Set'[_] : ∀ {α} (A : Set α) → Subset' A
Set'[ A ] = λ x → true 

EmptySet' : ∀ {α} (A : Set α) → Subset' A
EmptySet' {α} A = λ x → false

[_∈_] : ∀ {α β} {A : Set α} (x : A) → Subset {α} {β} A → Set β
[ x ∈ S ] = S x

[_∉_] : ∀ {i j} {A : Set i} (a : A) → Subset {i} {j} A → Set j
[ a ∉ S ] = ¬ (S a)

[_∈_]' : ∀ {i} {A : Set i} (x : A) → Subset' A → Set
[ x ∈ S ]' = S x ≡ true

[_∉_]' : ∀ {i} {A : Set i} (a : A) → Subset' A → Set
[ a ∉ S ]' = S a ≡ false

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

SetEquiv : ∀ {i j} {A : Set i} → (X Y : Subset {i} {j} A) → Set (i ⊔ j)
SetEquiv {i} {j} {A} X Y = [ A || X ⊆ Y ] ∧ [ A || Y ⊆ X ]



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

SetEquiv' : ∀ {i} (A : Set i) (X Y : Subset' A) → Set i
SetEquiv' {i} A X Y = [ A || X ⊆ Y ]' ∧ [ A || Y ⊆ X ]'

{-
only works on subsets of (types with decidable equality)

[_||_;_]' : ∀ {i} (A : Set i) (X : Subset' A) (t : A) → Subset' A
[ A || X ; t ]' = λ x → 
-}

{-
Here's how we can define it for arbitrary subsets without decidable equality. Without decidable equality of A we
can't necessarily take an arbitrary subset X and object t : A and give back a subset Y that includes only the
objects of X along with t. On the other hand, we can describe the conditions that must be satisfied by the subset
Y in order to be the required extension of X by the object t. It must be the smallest subset of A containing
both X and t.
-}
data AddSetMember {i} {j} (A : Set i) (X : Subset {i} {j} A) (t : A) (Y : Subset {i} {j} A) : Set (lsuc (i ⊔ j)) where
 cons : ([ A || X ⊆ Y ] ∧ [ t ∈ Y ]) ∧ ((Z : Subset A) → ([ A || X ⊆ Z ] ∧ [ t ∈ Z ]) → [ A || Y ⊆ Z ]) → AddSetMember {i} {j} A X t Y


⊆'-trans : ∀ {α} {X : Set α} {A B C : Powerset' X} → [ X || A ⊆ B ]' → [ X || B ⊆ C ]' → [ X || A ⊆ C ]'
⊆'-trans {α} {X} {A} {B} {C} A⊆B B⊆C x Ax≡true = B⊆C x (A⊆B x Ax≡true)

⊂'-trans : ∀ {i} {X : Set i} {A B C : Powerset'  X} → [ X || A ⊂ B ]' → [ X || B ⊂ C ]' → [ X || A ⊂ C ]'
⊂'-trans {i} {X} {A} {B} {C} A⊂B B⊂C = (A⊆C , ∃x,¬Ax∧Cx)
 where
  A⊆C : [ X || A ⊆ C ]'
  A⊆C x Ax = (first B⊂C) x ((first A⊂B) x Ax)

  x : X
  x = π₁ (second (A⊂B))

  Ax≡false : A x ≡ false
  Ax≡false = first (π₂ (second A⊂B))

  Bx≡true : B x ≡ true
  Bx≡true = second (π₂ (second A⊂B))

  Cx≡true : C x ≡ true
  Cx≡true = (first B⊂C) x Bx≡true

  ∃x,¬Ax∧Cx : ∃ x ∈ X , ((A x ≡ false) ∧ (C x ≡ true)) 
  ∃x,¬Ax∧Cx = (x , (Ax≡false , Cx≡true))



subsetUnion : ∀ {α β} {X : Set α} (A B : Subset {α} {β} X) → Subset X
subsetUnion {α} {β} {X} A B = λ x → (A x) ∨ (B x)

subsetUnion' : ∀ {α} {X : Set α} (A B : Powerset' X) → Powerset' X
subsetUnion' {α} {X} A B = λ x → (A x) or (B x)

subsetUnion₂ : ∀ {i j k l} {X : Set i} {Y : Set k} (A : Subset {i} {j} X) (B : Subset {k} {l} Y) → Subset {i ⊔ k} {j ⊔ l} (X ⊹ Y)
subsetUnion₂ {i} {j} {k} {l} {X} {Y} A B (inl x) = Lift {j} {j ⊔ l} (A x)
subsetUnion₂ {i} {j} {k} {l} {X} {Y} A B (inr y) = Lift {l} {j ⊔ l} (B y)



A⊆A : ∀ {i} {X : Set i} (A : Subset' X) → [ X || A ⊆ A ]'
A⊆A A x Ax = Ax

A⊄A : ∀ {i} {X : Set i} (A : Subset' X) → ¬ [ X || A ⊂ A ]'
A⊄A A [A⊂A] = true≠false (≡-trans (≡-sym (second (π₂ (second [A⊂A])))) (first (π₂ (second [A⊂A]))))

∅⊆A : ∀ {i} {X : Set i} (A : Subset' X) → [ X || (EmptySet' X) ⊆ A ]'
∅⊆A A x ∅x = ω (true≠false (≡-sym ∅x))


{-
{x,y} = {y,x}
requires decidable equality to even form these sets generally and requires extensionality for the symmetry


-}
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

Interior-set' : ∀ {i} (A : Set i) → Subset' A → Subset' A
Interior-set' {i} A X = X


Exterior : ∀ {α β} {A : Set α} → Subset {α} {β} A → Set (β ⊔ α)
Exterior {α} {β} {A} S = ∃ a ∈ A , ∥ (S a → ⊥) ∥

Exterior' : ∀ {α} {A : Set α} → Powerset' A → Set α
Exterior' {α} {A} S = ∃ a ∈ A , ∥ S a ≡ false ∥

Exterior-set' : ∀ {i} (A : Set i) → Subset' A → Subset' A
Exterior-set' {i} A X = λ x → not (X x)

member : ∀ {i j} {A : Set i} → Subset {i} {j} A → Set (i ⊔ j)
member {i} {j} {A} S = ∃ a ∈ A , (S a)

has-decidable-equality : ∀ {i} (A : Set i) → Set i
has-decidable-equality A = ∃ f ∈ (A → A → Bool) , ((x y : A) → (f x y ≡ true → x ≡ y) ∧ (x ≡ y → f x y ≡ true))

{-
with decidable equality you can talk about the set {x} containing just a specific object x : A.
-}

singleton : ∀ {i} {A : Set i} → (d : has-decidable-equality A) → (x : A) → ∃ S ∈ Subset' A , (S x ≡ true ∧ ((S' : Subset' A) →  S' x ≡ true → [ A || S ⊆ S' ]'))
singleton {i} {A} d x = (S , (Sx , S-minimal))
 where
  S : Subset' A
  S y = (π₁ d) x y

  Sx : S x ≡ true
  Sx = (second ((π₂ d) x x)) refl

  S-minimal : (S' : Subset' A) → S' x ≡ true → [ A || S ⊆ S' ]'
  S-minimal S' S'x y Sy = S'y
   where
    x≡y : x ≡ y
    x≡y = (first ((π₂ d) x y)) Sy

    S'x≡S'y : S' x ≡ S' y
    S'x≡S'y = [x≡y]→[fx≡fy] S' x y x≡y

    S'y : S' y ≡ true
    S'y = ≡-trans (≡-sym S'x≡S'y) S'x
