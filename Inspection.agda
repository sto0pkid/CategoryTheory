module Inspection where

open import Data.PropositionalEquality

data Singleton {α} {A : Set α} (x : A) : Set α where
 _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {α} {A : Set α} (x : A) → Singleton x
inspect x = x with≡ refl
