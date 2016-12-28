module Data.List where

open import Agda.Primitive
open import BaseLogic
open import Data.Bool

infixr 3 _∷_
data List {α} (A : Set α) : Set α where
 [] : List A
 _∷_ : A → List A → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL []    #-}
{-# BUILTIN CONS _∷_  #-}

isEmpty : ∀ {α} {A : Set α} → List A → Bool
isEmpty [] = true
isEmpty (x ∷ xs) = false

infixr 3 _++_
_++_ : ∀ {α} {A : Set α} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

[]++xs≡xs : ∀ {α} {A : Set α} → (x : List A) → ([] ++ x) ≡ x
[]++xs≡xs x = refl x


[xs++[]≡xs]-ind : ∀ {α} {A : Set α} → (xs : List A) → ((xs ++ []) ≡ xs) → (x : A) → ((x ∷ xs) ++ []) ≡ (x ∷ xs)
[xs++[]≡xs]-ind {α} {A} xs [xs++[]≡xs] x = [x∷xs++[]≡x∷xs]
 where
  [x∷xs++[]]≡x∷[xs++[]] : ((x ∷ xs) ++ []) ≡ x ∷ (xs ++ [])
  [x∷xs++[]]≡x∷[xs++[]] = refl (x ∷ (xs ++ []))

  x∷_ : (l : List A) → Set α
  x∷ l = (x ∷ (xs ++ [])) ≡ (x ∷ l)

  x∷[xs++[]]≡x∷xs : (x ∷ (xs ++ [])) ≡ (x ∷ xs)
  x∷[xs++[]]≡x∷xs = [x≡y]→[Px→Py] x∷_ (xs ++ []) xs [xs++[]≡xs] (refl (x ∷ (xs ++ [])))

  [x∷xs++[]≡x∷xs] : ((x ∷ xs) ++ []) ≡ (x ∷ xs)
  [x∷xs++[]≡x∷xs] = ≡-⇶ [x∷xs++[]]≡x∷[xs++[]] x∷[xs++[]]≡x∷xs



xs++[]≡xs : ∀ {α} {A : Set α} → (xs : List A) → (xs ++ []) ≡ xs
xs++[]≡xs [] = refl []
xs++[]≡xs (x ∷ xs) = [xs++[]≡xs]-ind xs (xs++[]≡xs xs) x


listmap : ∀ {α β} {A : Set α} {B : Set β} (f : A → B) → List A → List B
listmap f [] = []
listmap f (x ∷ xs) = (f x) ∷ (listmap f xs) 

list-inl : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → List (A × C) → List ((A ⊹ B) × C)
list-inl {i} {j} {k} {A} {B} {C} [] = []
list-inl {i} {j} {k} {A} {B} {C} (x ∷ xs) = ((inl (first x)) , (second x)) ∷ (list-inl xs)

list-inr : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → List (B × C) → List ((A ⊹ B) × C)
list-inr {i} {j} {k} {A} {B} {C} [] = []
list-inr {i} {j} {k} {A} {B} {C} (x ∷ xs) = ((inr (first x)) , (second x)) ∷ (list-inr xs)

concat : ∀ {i} {A : Set i} → List (List A) → List A
concat [] = []
concat (x ∷ xs) = x ++ (concat xs)

-- see [1]
listListPairs : ∀ {i j} {A : Set i} {B : Set j} → List A → List B → List (List (A × B))
listListPairs as bs = listmap (λ x → (listmap (λ y → (x , y)) bs)) as

allPairs : ∀ {i j} {A : Set i} {B : Set j} → List A → List B → List (A × B)
allPairs as bs = concat (listmap (λ x → (listmap (λ y → (x , y)) bs)) as)

{-
[1] gallais
    on list-comprehensions in Agda
    http://stackoverflow.com/questions/31394404/agda-forming-all-pairs-x-y-x-in-xs-y-in-ys
    https://gist.github.com/gallais/2e31c020937198a85529

-}




