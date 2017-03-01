module Data.PropositionalEquality where

infixr 3 _≡_
data _≡_ {α} {A : Set α} (x : A) : A → Set α where
 refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}


≡-⟲ : ∀ {α} {A : Set α} (x : A) → x ≡ x
≡-⟲ x = refl

≡-refl : ∀ {α} {A : Set α} (x : A) → x ≡ x
≡-refl = ≡-⟲

equiv-refl : ∀ {α} {A : Set α} (x : A) → x ≡ x
equiv-refl = ≡-refl

≡-↑↓ : ∀ {α} {A : Set α} {x y : A} → x ≡ y → y ≡ x
≡-↑↓ refl = refl

≡-sym : ∀ {α} {A : Set α} {x y : A} → x ≡ y → y ≡ x
≡-sym = ≡-↑↓

equiv-sym : ∀ {α} {A : Set α} {x y : A} → x ≡ y → y ≡ x
equiv-sym = ≡-sym

≡-⇶ : ∀ {α} {A : Set α} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-⇶ refl refl = refl

≡-trans : ∀ {α} {A : Set α} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans = ≡-⇶

equiv-trans : ∀ {α} {A : Set α} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
equiv-trans = ≡-trans
