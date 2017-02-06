module Data.Nat.Proofs where

open import Agda.Primitive
open import BaseLogic
open import Data.Bool
open import Data.Bool.Proofs
open import Data.Nat
open import Data.Nat.Operations
open import Data.Nat.Relations
open import Data.Nat.Properties
open import Data.False
open import Data.Product
open import Data.PropositionalEquality


𝕤x+y≡𝕤[x+y] : (x y : Nat) → suc x + y ≡ suc (x + y)
𝕤x+y≡𝕤[x+y] x y = refl

[𝕤x≡𝕤y]→[x≡y] : (x y : Nat) → suc x ≡ suc y → x ≡ y
[𝕤x≡𝕤y]→[x≡y] x y [𝕤x≡𝕤y] = [x≡y]→[fx≡fy] pred (suc x) (suc y) [𝕤x≡𝕤y]

[𝕤x+y≡𝕤z]→[x+y≡z] : (x y z : Nat) → suc x + y ≡ suc z → x + y ≡ z
[𝕤x+y≡𝕤z]→[x+y≡z] x y z [𝕤x+y≡𝕤z] = [x+y≡z]
 where
  [𝕤[x+y]≡𝕤x+y] : suc (x + y) ≡ suc x + y
  [𝕤[x+y]≡𝕤x+y] = ≡-↑↓ (𝕤x+y≡𝕤[x+y] x y)   

  [𝕤[x+y]≡𝕤z] : suc (x + y) ≡ suc z
  [𝕤[x+y]≡𝕤z] = ≡-⇶ [𝕤[x+y]≡𝕤x+y] [𝕤x+y≡𝕤z]
 
  [x+y≡z] : x + y ≡ z
  [x+y≡z] = [𝕤x≡𝕤y]→[x≡y] (x + y) z [𝕤[x+y]≡𝕤z]


[𝕤x<𝕤y]→[x<y] : (x y : Nat) → suc x < suc y → x < y
[𝕤x<𝕤y]→[x<y] x y (z , [𝕤x+𝕤z≡𝕤y]) = (z , [x+𝕤z≡y])
 where
  [x+𝕤z≡y] : x + suc z ≡ y
  [x+𝕤z≡y] = [𝕤x+y≡𝕤z]→[x+y≡z] x (suc z) y [𝕤x+𝕤z≡𝕤y]


𝕤x≠0 : (x : Nat) → (suc x) ≠ zero
𝕤x≠0 x [𝕤x≡𝕫] = ☢
 where
  [𝕥≡isZero-𝕫] : true ≡ isZero zero
  [𝕥≡isZero-𝕫] = refl

  [isZero-𝕤x≡𝕗] : isZero (suc x) ≡ false
  [isZero-𝕤x≡𝕗] = refl

  [isZero-𝕫≡isZero-𝕤x] : isZero zero ≡ isZero (suc x)
  [isZero-𝕫≡isZero-𝕤x] = [x≡y]→[fx≡fy] isZero zero (suc x) (≡-↑↓ [𝕤x≡𝕫])

  [𝕥≡𝕗] : true ≡ false
  [𝕥≡𝕗] = ≡-⇶ (≡-⇶ [𝕥≡isZero-𝕫] [isZero-𝕫≡isZero-𝕤x]) [isZero-𝕤x≡𝕗]

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]


𝕫+𝕤y≡𝕤[𝕫+y] : (y : Nat) → zero + suc y ≡ suc (zero + y)
𝕫+𝕤y≡𝕤[𝕫+y] y = refl

[x+𝕤y≡𝕤[x+y]]→[𝕤x+𝕤y≡𝕤𝕤[x+y]] :
 (x y : Nat) → 
 x + suc y ≡ suc (x + y) → 
 suc x + suc y ≡ suc (suc (x + y))
[x+𝕤y≡𝕤[x+y]]→[𝕤x+𝕤y≡𝕤𝕤[x+y]] x y [x+𝕤y≡𝕤[x+y]] = [𝕤x+𝕤y≡𝕤𝕤[x+y]]
 where
  [𝕤x+𝕤y≡𝕤[x+𝕤y]] : suc x + suc y ≡ suc (x + suc y)
  [𝕤x+𝕤y≡𝕤[x+𝕤y]] = 𝕤x+y≡𝕤[x+y] x (suc y)

  [𝕤[x+𝕤y]≡𝕤𝕤[x+y]] : suc (x + suc y) ≡ suc (suc (x + y))
  [𝕤[x+𝕤y]≡𝕤𝕤[x+y]] = [x≡y]→[fx≡fy] suc (x + suc y) (suc (x + y)) [x+𝕤y≡𝕤[x+y]]

  [𝕤x+𝕤y≡𝕤𝕤[x+y]] : suc x + suc y ≡ suc (suc (x + y))
  [𝕤x+𝕤y≡𝕤𝕤[x+y]] = ≡-⇶ [𝕤x+𝕤y≡𝕤[x+𝕤y]] [𝕤[x+𝕤y]≡𝕤𝕤[x+y]]

x+𝕤y≡𝕤[x+y] : (x y : Nat) → x + suc y ≡ suc (x + y)
x+𝕤y≡𝕤[x+y] zero y = 𝕫+𝕤y≡𝕤[𝕫+y] y
x+𝕤y≡𝕤[x+y] (suc x) y = [x+𝕤y≡𝕤[x+y]]→[𝕤x+𝕤y≡𝕤𝕤[x+y]] x y (x+𝕤y≡𝕤[x+y] x y)

 

x≮0 : (x : Nat) → x < zero → ⊥
x≮0 x (z , [x+𝕤z≡0]) = ☢
 where
  [x+𝕤z≡𝕤[x+z]] : x + suc z ≡ suc (x + z)
  [x+𝕤z≡𝕤[x+z]] = x+𝕤y≡𝕤[x+y] x z

  [𝕤[x+z]≡0] : suc (x + z) ≡ zero
  [𝕤[x+z]≡0] = ≡-⇶ (≡-↑↓ [x+𝕤z≡𝕤[x+z]]) [x+𝕤z≡0]

  ☢ : ⊥
  ☢ = 𝕤x≠0 (x + z) [𝕤[x+z]≡0]


𝕤x≮1 : (x : Nat) → suc x < suc zero → ⊥
𝕤x≮1 x [𝕤x<1] = ☢
 where
  [x<0] : x < 0
  [x<0] = [𝕤x<𝕤y]→[x<y] x 0 [𝕤x<1]

  ☢ : ⊥
  ☢ = x≮0 x [x<0]



{-
NoEmptyNonEmptyVectors : {A : Set} → NEVec A zero → ⊥
-- Agda knows there's a conflict here:
-- NoEmptyNonEmptyVectors {A} (end a) = {!!}
-- Agda knows there's a conflict here:
-- NoEmptyNonEmptyVectors {A} (a ∷ as) = {!!}
{- We've exhausted all possible cases, we know that this set NEVec A zero must be empty
   but Agda doesn't know this: -}
NoEmptyNonEmptyVectors {A} vec = {!!}
-}


1>0 : 1 > 0
1>0 = (0 , refl)

[x>0]→[𝕤x>0] : (x : Nat) → x > 0 → suc x > 0
[x>0]→[𝕤x>0] x (z , [0+𝕤z≡x]) = (suc z , [0+𝕤𝕤z≡𝕤x])
 where
  [𝕤z≡0+𝕤z] : suc z ≡ 0 + suc z
  [𝕤z≡0+𝕤z] = refl

  [𝕤z≡x] : suc z ≡ x
  [𝕤z≡x] = ≡-⇶ [𝕤z≡0+𝕤z] [0+𝕤z≡x]

  [0+𝕤𝕤z≡𝕤𝕤z] : 0 + suc (suc z) ≡ suc (suc z)
  [0+𝕤𝕤z≡𝕤𝕤z] = refl

  [𝕤𝕤z≡𝕤x] : suc (suc z) ≡ suc x
  [𝕤𝕤z≡𝕤x] = [x≡y]→[fx≡fy] suc (suc z) x [𝕤z≡x]

  [0+𝕤𝕤z≡𝕤x] : 0 + suc (suc z) ≡ suc x
  [0+𝕤𝕤z≡𝕤x] = ≡-⇶ [0+𝕤𝕤z≡𝕤𝕤z] [𝕤𝕤z≡𝕤x]



[x+0≡x]→[𝕤x+0≡𝕤x] : (x : Nat) → x + 0 ≡ x → suc x + 0 ≡ suc x
[x+0≡x]→[𝕤x+0≡𝕤x] x [x+0≡x] = [𝕤x+0≡𝕤x]
 where
  [𝕤x+0≡𝕤[x+0]] : (suc x) + 0 ≡ suc (x + 0)
  [𝕤x+0≡𝕤[x+0]] = 𝕤x+y≡𝕤[x+y] x 0

  [𝕤[x+0]≡𝕤x] : suc (x + 0) ≡ suc x
  [𝕤[x+0]≡𝕤x] = [x≡y]→[fx≡fy] suc (x + 0) x [x+0≡x]

  [𝕤x+0≡𝕤x] : (suc x) + 0 ≡ suc x
  [𝕤x+0≡𝕤x] = ≡-⇶ [𝕤x+0≡𝕤[x+0]] [𝕤[x+0]≡𝕤x]


x+0≡x : (x : Nat) → x + 0 ≡ x
x+0≡x 0 = refl
x+0≡x (suc x) = [x+0≡x]→[𝕤x+0≡𝕤x] x (x+0≡x x)


x<𝕤x : (x : Nat) → x < suc x
x<𝕤x x = (zero , [x+1≡𝕤x])
 where
  [x+1≡𝕤[x+0]] : x + 1 ≡ suc (x + 0)
  [x+1≡𝕤[x+0]] = x+𝕤y≡𝕤[x+y] x 0

  [x+0≡x] : x + 0 ≡ x
  [x+0≡x] = x+0≡x x
  
  [𝕤[x+0]≡𝕤x] : suc (x + 0) ≡ suc x
  [𝕤[x+0]≡𝕤x] = [x≡y]→[fx≡fy] suc (x + 0) x [x+0≡x]

  [x+1≡𝕤x] : x + 1 ≡ suc x
  [x+1≡𝕤x] = ≡-⇶ [x+1≡𝕤[x+0]] [𝕤[x+0]≡𝕤x]
