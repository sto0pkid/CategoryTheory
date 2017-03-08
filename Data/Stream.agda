module Data.Stream where

open import Data.Prim.Coinduction

data Stream {i} (A : Set i) : Set i where
 _∷_ : A → ∞ (Stream A) → Stream A
