module PolynomialFunctor where

open import BaseLogic

infixl 6 _⊕_
infixr 7 _⊗_

data PolynomialFunctor : Set₁ where
 Id : PolynomialFunctor
 Const : Set → PolynomialFunctor
 _⊕_ : PolynomialFunctor → PolynomialFunctor → PolynomialFunctor
 _⊗_ : PolynomialFunctor → PolynomialFunctor → PolynomialFunctor

[_] : PolynomialFunctor → Set → Set
[ Id ] B = B
[ Const C ] B = C
[ F ⊕ G ] B = ([ F ] B) ⊹ ([ G ] B)
[ F ⊗ G ] B = ([ F ] B) × ([ G ] B)

data LFP (F : PolynomialFunctor) : Set where
 inn : [ F ] (LFP F) → (LFP F)

ListFunctor : Set → PolynomialFunctor
ListFunctor A = (Const ⊤) ⊕ ((Const A) ⊗ Id)

List : Set → Set
List A = LFP (ListFunctor A)

