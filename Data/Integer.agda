module Data.Integer where

open import Data.Nat
open import Data.NonZeroNat

data Integer : Set where
 zero : Integer
 pos : Nat → Integer
 neg : Nat → Integer

data Integer₂ : Set where
 zero : Integer₂
 pos : NonZeroNat → Integer₂
 neg : NonZeroNat → Integer₂

data Integer₃ : Set where
 zero : Integer₃
 pos : NonZeroNat₂ → Integer₃
 neg : NonZeroNat₂ → Integer₃
