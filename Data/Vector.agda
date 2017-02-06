module Data.Vector where

open import Data.Nat

infixr 5 _∷_
data Vector {α} (A : Set α) : Nat → Set α where
 []  : Vector A 0
 _∷_ : {n : Nat} → A → Vector A n → Vector A (suc n) 
