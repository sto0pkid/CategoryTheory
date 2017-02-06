module Data.Disjunction where

open import Agda.Primitive

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
