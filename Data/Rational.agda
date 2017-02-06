module Data.Rational where

open import Data.Nat
open import Data.Integer
open import Data.NonZeroNat

data Rational : Set where
 numerator : Integer → Rational
 denominator : NonZeroNat → Rational
