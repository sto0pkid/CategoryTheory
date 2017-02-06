module FixedPoint where

--open import BaseLogic
open import Data.PropositionalEquality

record FixedPoint {α} {A : Set} (f : A → A) : Set α where
 field
  x : A
  isFixed : x ≡ f x
