module Data.False where

data ⊥ : Set where
ω : ∀ {α} {A : Set α} → ⊥ → A
ω ()
