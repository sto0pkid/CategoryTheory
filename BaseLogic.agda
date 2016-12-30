module BaseLogic where

open import Agda.Primitive

data ⊥ : Set where
ω : ∀ {α} {A : Set α} → ⊥ → A
ω ()

data ⊤ : Set where
 ● : ⊤

infixr 2 _⊹_
data _⊹_ {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where
 inl : A → A ⊹ B
 inr : B → A ⊹ B

infixr 2 _∨_
_∨_ : ∀ {α β} (A : Set α) (B : Set β) → Set (α ⊔ β)
_∨_ = _⊹_

infixr 2 _∪_ 
_∪_ : ∀ {α β} (A : Set α) (B : Set β) → Set (α ⊔ β)
_∪_ = _⊹_

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

proj₂ : ∀ {α β} {A : Set α} {B : A →  Set β} (P : ∃ x ∈ A , (B x)) → B (proj₁ P)
proj₂ (a , b) = b 

infixr 3 _≡_
data _≡_ {α} {A : Set α} : A → A → Set α where
 refl : (x : A) → x ≡ x

≡-↑↓ : ∀ {α} {A : Set α} {x y : A} → x ≡ y → y ≡ x
≡-↑↓ {α} {A} {x} {.x} (refl .x) = refl x

≡-⇶ : ∀ {α} {A : Set α} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-⇶ {α} {A} {x} {.x} {.x} (refl .x) (refl .x) = refl x

[x≡y]→[fx≡fy] : ∀ {α β} {A : Set α} {B : Set β} (f : A → B) → (x y : A) → x ≡ y → (f x) ≡ (f y)
[x≡y]→[fx≡fy] {α} {β} {A} {B} f x .x (refl .x) = refl (f x)

[x≡y]→[Px→Py] : ∀ {α β} {A : Set α} (P : A → Set β) → (x y : A) → x ≡ y → P x → P y
[x≡y]→[Px→Py] {α} {β} {A} P x .x (refl .x) Px = Px

p≡[π₁-p,π₂-p] : ∀ {α β} {A : Set α} {B : Set β} (p : A × B) → p ≡ (first p , second p)
p≡[π₁-p,π₂-p] {α} {β} {A} {B} (p1 , p2) = refl (p1 , p2)


infixr 3 _∷_
data EqChain {α} {A : Set α} : A → A → Set α where
 end : {x y : A} → x ≡ y → EqChain x y
 _∷_ : {x y z : A} → x ≡ y → EqChain y z → EqChain x z
 

EqChainExtract : ∀ {α} {A : Set α} {x y : A} → EqChain x y → x ≡ y
EqChainExtract {α} {A} {x} {y} (end p) = p
EqChainExtract {α} {A} {x} {y} (p ∷ (end q)) = ≡-⇶ p q
EqChainExtract {α} {A} {x} {y} (p ∷ (q ∷ rest)) = ≡-⇶ p (≡-⇶ q (EqChainExtract rest))


