module Relations where

open import Agda.Primitive
open import BaseLogic
open import Data.Bool
open import Data.Nat
open import Data.Vector

data N-ary-relation {α} (A : Set α) : Nat → Set α where
 [in=_,out=_] : {n : Nat} → Vector A n → A → N-ary-relation A (suc n)

-- Note that we could just define Vectors of length n as n-ary relations.

data N-ary-relation₂ {α} (A : Set α) (n : Nat) (P : Vector A n → Set) : Set α where
 [components=_,proof=_] : (vec : Vector A n) → P vec → N-ary-relation₂ A n P

data N-ary-relation₃ {α} (A : Set α) (n : Nat) : Set (lsuc α) where
 rel : (Vector A n → Set α) → N-ary-relation₃ A n

data Relation {α} {β} (A : Set α) (n : Nat) : Set (lsuc β ⊔ α) where
 rel : (Vector A n → Set β) → Relation A n

Relation₁ : ∀ {α β} (A : Set α) (n : Nat) → Set (lsuc β ⊔ α)
Relation₁ {α} {β} A n = Vector A n → Set β



{-
≡-⟲ : ∀ {α} {A : Set α} (x : A) → x ≡ x
≡-⟲ {α} {A} x = refl x
-}
isReflexive-Set : ∀ {i j} {A : Set i} (R : A → A → Set j) → Set (i ⊔ j)
isReflexive-Set {i} {j} {A} R = (x : A) → R x x

isReflexive : ∀ {i} {A : Set i} (R : A → A → Bool) → Set i
isReflexive {i} {A} R = (x : A) → (R x x ≡ true)

{-
≡-↑↓ : ∀ {α} {A : Set α} {x y : A} → x ≡ y → y ≡ x
≡-↑↓ {α} {A} {x} {.x} (refl .x) = refl x
-}
isSymmetric-Set : ∀ {i j} {A : Set i} (R : A → A → Set j) → Set (i ⊔ j)
isSymmetric-Set {i} {j} {A} R = {x y : A} → R x y → R y x

isSymmetric : ∀ {i} {A : Set i} (R : A → A → Bool) → Set i
isSymmetric {i} {A} R = (x y : A) → (R x y ≡ true) → (R y x ≡ true)

isSymmetric' : ∀ {i} {A : Set i} (r : A → A → Bool) → Set i
isSymmetric' {i} {A} r = (x y : A) (z : Bool) → (r x y ≡ z) → (r y x ≡ z)

{-
≡-⇶ : ∀ {α} {A : Set α} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-⇶ {α} {A} {x} {.x} {.x} (refl .x) (refl .x) = refl x

-}
isTransitive-Set : ∀ {i j} {A : Set i} (R : A → A → Set j) → Set (i ⊔ j)
isTransitive-Set {i} {j} {A} R = {x y z : A} → R x y → R y z → R x z

isTransitive : ∀ {i} {A : Set i} (r : A → A → Bool) → Set i
isTransitive {i} {A} r = (x y z : A) → (r x y ≡ true) → (r y z ≡ true) → (r x z ≡ true)

isEquivalence-Set : ∀ {i j} {A : Set i} (R : A → A → Set j) → Set (i ⊔ j)
isEquivalence-Set {i} {j} {A} R = (isReflexive-Set R) ∧ ((isSymmetric-Set R) ∧ (isTransitive-Set R))

isEquivalenceRelation : ∀ {i} {A : Set i} (r : A → A → Bool) → Set i
isEquivalenceRelation {i} {A} r = (isReflexive r) ∧ ((isSymmetric r) ∧ (isTransitive r))


isEqDec : ∀ {α} {A : Set α} → (R : A → A → Bool) → Set α
isEqDec {α} {A} R = (x y : A) → (R x y ≡ true → x ≡ y) ∧ (x ≡ y → R x y ≡ true)


≡-equiv : ∀ {α} {A : Set α} → isEquivalence-Set (_≡_ {α} {A})
≡-equiv = (≡-⟲ , (≡-↑↓ , ≡-⇶))


isEqDec-R→isEquiv-R : ∀ {α} {A : Set α} (R : A → A → Bool) → isEqDec R → isEquivalenceRelation R
isEqDec-R→isEquiv-R {α} {A} R isEqDec-R = (isRefl-R , (isSym-R , isTrans-R))
 where
  isRefl-R : isReflexive R
  isRefl-R x = Rxx
   where
    x≡x : x ≡ x
    x≡x = refl x

    x≡x→Rxx : x ≡ x → R x x ≡ true
    x≡x→Rxx = second (isEqDec-R x x)

    Rxx : R x x ≡ true
    Rxx = x≡x→Rxx x≡x

  isSym-R : isSymmetric R
  isSym-R x y Rxy = Ryx
   where
    Rxy→x≡y : R x y ≡ true → x ≡ y
    Rxy→x≡y = first (isEqDec-R x y)

    x≡y : x ≡ y
    x≡y = Rxy→x≡y Rxy

    y≡x : y ≡ x
    y≡x = ≡-↑↓ x≡y
    
    y≡x→Ryx : y ≡ x → R y x ≡ true
    y≡x→Ryx = second (isEqDec-R y x)
  
    Ryx : R y x ≡ true
    Ryx = y≡x→Ryx y≡x

  isTrans-R : isTransitive R
  isTrans-R x y z Rxy Ryz = Rxz
   where
    Rxy→x≡y : R x y ≡ true → x ≡ y
    Rxy→x≡y = first (isEqDec-R x y)

    Ryz→y≡z : R y z ≡ true → y ≡ z
    Ryz→y≡z = first (isEqDec-R y z)

    x≡y : x ≡ y
    x≡y = Rxy→x≡y Rxy

    y≡z : y ≡ z
    y≡z = Ryz→y≡z Ryz

    x≡z : x ≡ z
    x≡z = ≡-⇶ x≡y y≡z

    Rxz : R x z ≡ true
    Rxz = (second (isEqDec-R x z)) x≡z


{-
DecEq-R→isRefl-R : ∀ {α} {A : Set α} → (R : A → A → Bool) → isEqDec R → isReflexive R
DecEq-R→isRefl-R {α} {A} R [isEqDec] x = [Rxx≡𝕥]
 where
  
  [Rxx≡𝕥] 
-}

{-
DecEq-R→isEquiv-R : ∀ {α} {A : Set α} → (R : A → A → Bool) → isEqDec R → isEquivalence R
DecEq-R→isEquiv-R {α} {A} R isEqDec-R =
-}

{-
Alright now we want to have general proofs for N-ary relations.
We have to build up our own theory of N-ary relations, because Agda doesn't give any
direct mechanism for talking about arity.
-}

get-rel : {k : Nat} → Relation Nat (suc (suc k)) → Vector Nat (suc (suc k)) → Set
get-rel {k} (rel R) = R

get-inputs : (k : Nat) → Vector Nat (suc (suc k)) → Vector Nat (suc k)
get-inputs zero (x₁ ∷ x₂ ∷ []) = x₁ ∷ []
get-inputs (suc n) (x₁ ∷ x₂ ∷ xs) = x₁ ∷ (get-inputs n (x₂ ∷ xs))

get-output : (k : Nat) → Vector Nat (suc (suc k)) → Nat
get-output zero (x₁ ∷ x₂ ∷ []) = x₂
get-output (suc n) (x₁ ∷ x₂ ∷ xs) = get-output n (x₂ ∷ xs)

-- Relation A n
-- could have A ≡ B and n ≡ m, and a function that takes a Relation B m
-- Relation (A ∷ n ∷ []) → Relation (B ∷ n ∷ [])
-- It's a vector with a potentially different type at every index, and the types are
-- potentially dependent
-- So it's more like a record type for the arguments
-- A particular set of arguments will be a record
-- The problem with records is that we lose the ability to access them at a numeric index
-- Each record type needs to be equipped with a function that lets you access it with a numeric index
-- so that we can use homogeneous record-independent indices
-- And each record type needs an associated record type that holds equalities
-- Then we can coerce between extensionally equal record types


{-
 What is decidable equality? A proposition P : A → Set is decidable if
 there is a total computable function f : A → Bool that decides inhabitation
 in P.

 Is generalized by decidable relations.
-}


Decidable : ∀ {i j} → {A : Set i} → (P : A → Set j) → Set (j ⊔ i)
Decidable {i} {j} {A} P = ∃ f ∈ (A → Bool) , ((x : A) → ((((f x) ≡ true) → P x) ∧ (((f x) ≡ false) → (P x → ⊥))))

Decidable' : ∀ {i j} → {A : Set i} → (P : A → Set j) → Set (j ⊔ i)
Decidable' {i} {j} {A} P = ∃ f ∈ (A → Bool) , ((x : A) → ((((f x) ≡ true) ↔ P x) ∧ (((f x) ≡ false) ↔ (P x → ⊥))))

Decidable₂ : ∀ {i j k} → {A : Set i} → {B : Set j} → (P : A → B → Set k) → Set (k ⊔ (j ⊔ i))
Decidable₂ {i} {j} {k} {A} {B} P = ∃ f ∈ (A → B → Bool) , ((x : A) → (y : B) → ((((f x y) ≡ true) → P x y) ∧ (((f x y) ≡ false) → (P x y → ⊥))))

Decidable₂' : ∀ {i j k} → {A : Set i} → {B : Set j} → (P : A → B → Set k) → Set (k ⊔ (j ⊔ i))
Decidable₂' {i} {j} {k} {A} {B} P = ∃ f ∈ (A → B → Bool) , ((x : A) → (y : B) → ((((f x y) ≡ true) ↔ P x y) ∧ (((f x y) ≡ false) ↔ (P x y → ⊥))))

{-
Need to generalize this to N-ary relations.
-}
