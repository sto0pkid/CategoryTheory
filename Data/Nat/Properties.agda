module Data.Nat.Properties where

open import Agda.Primitive
open import BaseLogic
open import Data.Nat
open import Data.Bool

isZero : Nat → Bool
isZero zero = true
isZero (suc x) = false
