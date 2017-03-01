module BaseN where

open import Data.Maybe
open import Data.Nat
open import Data.List
open import Data.List.Operations
open import Data.Fin

BaseN-Nat : Nat → Set
BaseN-Nat n = List (Fin n)

Base2-Nat : Set
Base2-Nat = BaseN-Nat 2

Base3-Nat : Set
Base3-Nat = BaseN-Nat 3

Base4-Nat : Set
Base4-Nat = BaseN-Nat 4

Base8-Nat : Set
Base8-Nat = BaseN-Nat 8

Base10-Nat : Set
Base10-Nat = BaseN-Nat 10



{-
inc : Base2-Nat → Base2-Nat
inc 
-}
