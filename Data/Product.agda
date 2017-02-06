module Data.Product where

open import Agda.Primitive

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
