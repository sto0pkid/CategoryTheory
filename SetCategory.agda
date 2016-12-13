module SetCategory where

open import Agda.Primitive
open import BaseLogic
open import Category

SetCategory₀ : ∀ {α} → Category₀ {lsuc α} {α}
SetCategory₀ {α} =
 record {
  obj = Set α ;
  hom = λ A B → (A → B) ;
  id = λ A → (λ x → x) ;
  comp = λ g f → (λ x → g (f x))

 }


SetCategory : ∀ {α} → Category {lsuc α} {α}
SetCategory {α} = 
 record {
  obj = Set α ;
  hom = λ A B → (A → B) ;
  id = λ A → (λ x → x) ;
  comp = λ g f → (λ x → g (f x)) ;

  left-id = λ f → refl f ;
  right-id = λ f → refl f ;
  assoc = λ f g h → refl (λ x → (f (g (h x))))
 }
