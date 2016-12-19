module Data.List where

open import Agda.Primitive
open import BaseLogic

infixr 3 _∷_
data List {α} (A : Set α) : Set α where
 [] : List A
 _∷_ : A → List A → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL []    #-}
{-# BUILTIN CONS _∷_  #-}

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

