module Data.Maybe.Operations where

open import Data.Maybe

maybe-map : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → Maybe A → Maybe B
maybe-map {i} {j} {A} {B} f Nothing = Nothing
maybe-map {i} {j} {A} {B} f (Just a) = Just (f a)
