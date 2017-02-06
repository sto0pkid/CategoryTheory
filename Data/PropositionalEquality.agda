module Data.PropositionalEquality where

infixr 3 _≡_
data _≡_ {α} {A : Set α} (x : A) : A → Set α where
 refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}


≡-⟲ : ∀ {α} {A : Set α} (x : A) → x ≡ x
≡-⟲ x = refl

≡-↑↓ : ∀ {α} {A : Set α} {x y : A} → x ≡ y → y ≡ x
≡-↑↓ refl = refl

≡-⇶ : ∀ {α} {A : Set α} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-⇶ refl refl = refl
