module TuringMachine where

open import Agda.Primitive

data ⊥ : Set where
ω : ∀ {α} {A : Set α} → ⊥ → A
ω ()


¬ : ∀ {i} → Set i → Set i
¬ A = A → ⊥

data Bool : Set where
 true : Bool
 false : Bool

data Nat : Set where
 zero : Nat
 suc : Nat → Nat

data Fin : Nat → Set where
 zero : {n : Nat} → Fin (suc n)
 suc : {n : Nat} → Fin n → Fin (suc n)

infixr 2 _×_
data _×_ {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where
 _,_ : A → B → A × B

infixr 2 _∧_
_∧_ : ∀ {α β} (A : Set α) (B : Set β) → Set (α ⊔ β)
_∧_ = _×_

×-cons' : ∀ {α β} {A : Set α} {B : Set β} → B → A → A × B
×-cons' {α} {β} {A} {B} b a = (a , b)

∧-cons' : ∀ {α β} {A : Set α} {B : Set β} → B → A → A ∧ B
∧-cons' = ×-cons'


first : ∀ {α β} {A : Set α} {B : Set β} (P : A × B) → A
first (a , b) = a

second : ∀ {α β} {A : Set α} {B : Set β} (P : A × B) → B
second (a , b) = b


data ∃ {α β} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
 _,_ : (x : A) → B x → ∃ A B

syntax ∃ A (λ x → e) = ∃ x ∈ A , e

proj₁ : ∀ {α β} {A : Set α} {B : A → Set β} (P : ∃ x ∈ A , (B x)) → A
proj₁ (a , b) = a

π₁ : ∀ {α β} {A : Set α} {B : A → Set β} (P : ∃ x ∈ A , (B x)) → A
π₁ = proj₁

proj₂ : ∀ {α β} {A : Set α} {B : A →  Set β} (P : ∃ x ∈ A , (B x)) → B (proj₁ P)
proj₂ (a , b) = b 

π₂ : ∀ {α β} {A : Set α} {B : A →  Set β} (P : ∃ x ∈ A , (B x)) → B (proj₁ P)
π₂ = proj₂

data _≡_ {i} {A : Set i} (x : A) : A → Set i where
 refl : x ≡ x


record TM : Set where
 field
  states : Nat
  final-states : Fin states → Bool
  initial-state : Fin states
  alphabet : Nat
  blank-symbol : Fin alphabet
  input-symbols : ∃ s ∈ (Fin alphabet → Bool) , (s blank-symbol ≡ false)
  transition-function : ((∃ s ∈ (Fin states → Bool) , ((x : Fin states) → (final-states x ≡ true) → (s x ≡ false))) × (Fin alphabet)) → (Fin states) × (Fin alphabet) × Bool
 
