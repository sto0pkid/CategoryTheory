module BaseLogic where

open import Agda.Primitive
open import Data.False
open import Data.True
open import Data.Disjunction
open import Data.Product
open import Data.PropositionalEquality
open import Data.Irrelevance

~ : ∀ {α} (A : Set α) → Set α
~ A = A → ⊥

¬ : ∀ {α} (A : Set α) → Set α
¬ = ~

_↔_ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
A ↔ B = (A → B) ∧ (B → A)

[x≡y]→[fx≡fy] : ∀ {α β} {A : Set α} {B : Set β} (f : A → B) → (x y : A) → x ≡ y → (f x) ≡ (f y)
[x≡y]→[fx≡fy] {α} {β} {A} {B} f x .x refl = refl

[x≡y]→[Px→Py] : ∀ {α β} {A : Set α} (P : A → Set β) → (x y : A) → x ≡ y → P x → P y
[x≡y]→[Px→Py] {α} {β} {A} P x .x refl Px = Px

p≡[π₁-p,π₂-p] : ∀ {α β} {A : Set α} {B : Set β} (p : A × B) → p ≡ (first p , second p)
p≡[π₁-p,π₂-p] {α} {β} {A} {B} (p1 , p2) = refl

_≠_ : ∀ {α} {A : Set α} (x y : A) → Set α
x ≠ y = (x ≡ y) → ⊥

≠-↑↓ : ∀ {α} {A : Set α} {x y : A} → x ≠ y → y ≠ x
≠-↑↓ [x≠y] [y≡x] = ☢
 where
  ☢ : ⊥
  ☢ = [x≠y] (≡-↑↓ [y≡x])

[A≡B]→[A→B] : ∀ {α} {A B : Set α} → A ≡ B → A → B
[A≡B]→[A→B] refl a = a

⊤≠⊥ : ⊤ ≠ ⊥
⊤≠⊥ [⊤≡⊥] = ☢ 
 where
  [⊤→⊥] : ⊤ → ⊥
  [⊤→⊥] = [A≡B]→[A→B] [⊤≡⊥]

  ☢ : ⊥
  ☢ = [⊤→⊥] ●

_<=>_ : ∀ {α β} (A : Set α) (B : Set β) → Set (α ⊔ β)
A <=> B = (A → B) ∧ (B → A)
