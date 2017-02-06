module Data.Nat.Relations where

open import BaseLogic
open import Data.Nat
open import Data.Nat.Operations
open import Data.Product
open import Data.PropositionalEquality

-- need to irrelefy π₂
infixr 3 _≥_
_≥_ : Nat → Nat → Set
x ≥ y = ∃ n ∈ Nat , (plus y n ≡ x)

infixr 3 _≤_ 
_≤_ : Nat → Nat → Set
x ≤ y = y ≥ x

infixr 3 _>_
-- need to irrelefy π₂
_>_ : Nat → Nat → Set
x > y = ∃ n ∈ Nat , (plus y (suc n) ≡ x)

infixr 3 _<_
_<_ : Nat → Nat → Set
x < y = y > x

{-
x+k≡y→y-x≡k : (x y k : Nat) → plus x k ≡ y → minus y x ≡ k
x+k≡y→y-x≡k 
-}

{-
x≥y→x-y≥0 : (x y : Nat) → x ≥ y → Data.Nat.Operations._minus_ x y ≥ 0
-}

{-
x>y→x-y>0 : (x y : Nat) → x > y → Data.Nat.Operations._minus_ x y > 0
-}

𝕤x>0 : (x : Nat) → suc x > 0
𝕤x>0 x = (x , [0+𝕤x≡𝕤x])
 where
  [0+𝕤x≡𝕤x] : plus 0 (suc x) ≡ suc x
  [0+𝕤x≡𝕤x] = refl
