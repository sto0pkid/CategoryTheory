module Data.Nat.Proofs where

open import Agda.Primitive
open import BaseLogic
open import Data.Bool
open import Data.Bool.Proofs
open import Data.Nat
open import Data.Nat.Operations
open import Data.Nat.Relations
open import Data.Nat.Properties
open import Data.Nat.BinPreds
open import Data.False
open import Data.Product
open import Data.PropositionalEquality


𝕤x+y≡𝕤[x+y] : (x y : Nat) → suc x + y ≡ suc (x + y)
𝕤x+y≡𝕤[x+y] x y = refl


-- suc is injective
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

-- suc is injective wrt _<_
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

𝕤x≡[𝕤𝕫+x] : (x : Nat) → suc x ≡ (suc zero) + x
𝕤x≡[𝕤𝕫+x] x = refl

𝕤x≡[1+x] : (x : Nat) → suc x ≡ 1 + x
𝕤x≡[1+x] x = refl

[𝕤𝕫+x]≡𝕤x : (x : Nat) → (suc zero) + x ≡ (suc x)
[𝕤𝕫+x]≡𝕤x x = refl

[1+x]≡𝕤x : (x : Nat) → 1 + x ≡ suc x
[1+x]≡𝕤x x = refl

suc2sum : Nat → Nat
suc2sum zero = zero
suc2sum (suc x) = (suc zero) + (suc2sum x)

suc2sum-x≡x-ind : (x : Nat) → x ≡ suc2sum x → (suc x) ≡ (suc2sum (suc x))
suc2sum-x≡x-ind x [x≡suc2sum-x] = proof
 where
  [𝕤x≡[1+x]] : suc x ≡ (1 + x)
  [𝕤x≡[1+x]] = 𝕤x≡[1+x] x

  [suc2sum-𝕤x≡1+suc2sum-x] : (suc2sum (suc x)) ≡ 1 + (suc2sum x)
  [suc2sum-𝕤x≡1+suc2sum-x] = refl

  1+ : Nat → Nat
  1+ n = 1 + n

  [1+x≡1+suc2sum-x] : (1 + x) ≡ (1 + (suc2sum x))
  [1+x≡1+suc2sum-x] = [x≡y]→[fx≡fy] 1+ x (suc2sum x) [x≡suc2sum-x]

  proof : (suc x) ≡ (suc2sum (suc x))
  proof = ≡-trans [𝕤x≡[1+x]] (≡-trans [1+x≡1+suc2sum-x] (≡-sym [suc2sum-𝕤x≡1+suc2sum-x]))

suc2sum-x≡x : (x : Nat) → x ≡ suc2sum x
suc2sum-x≡x zero = refl
suc2sum-x≡x (suc x) = suc2sum-x≡x-ind x (suc2sum-x≡x x)

𝕤x-eq-𝕤y→x-eq-y : (x y : Nat) → (suc x) eq (suc y) ≡ true → x eq y ≡ true
𝕤x-eq-𝕤y→x-eq-y x y [𝕤x-eq-𝕤y] = proof
 where
  [𝕤x-eq-𝕤y]≡[x-eq-y] : (suc x) eq (suc y) ≡ x eq y
  [𝕤x-eq-𝕤y]≡[x-eq-y] = refl
 
  proof : x eq y ≡ true
  proof = ≡-trans (≡-sym [𝕤x-eq-𝕤y]≡[x-eq-y]) [𝕤x-eq-𝕤y]

x-eq-y→x≡y-ind : (x y : Nat) → (x eq y ≡ true → x ≡ y) → (suc x) eq (suc y) ≡ true → (suc x) ≡ (suc y)
x-eq-y→x≡y-ind x y hyp [𝕤x-eq-𝕤y] = proof
 where
  [x-eq-y] : x eq y ≡ true
  [x-eq-y] = 𝕤x-eq-𝕤y→x-eq-y x y [𝕤x-eq-𝕤y]

  [x≡y] : x ≡ y
  [x≡y] = hyp [x-eq-y]

  proof : (suc x) ≡ (suc y)
  proof = [x≡y]→[fx≡fy] suc x y [x≡y]


x-eq-y→x≡y : (x y : Nat) → x eq y ≡ true → x ≡ y
x-eq-y→x≡y zero zero refl = refl
x-eq-y→x≡y zero (suc y) [false≡true] = ω (true≠false (≡-sym [false≡true]))
x-eq-y→x≡y (suc x) zero [false≡true] = ω (true≠false (≡-sym [false≡true]))
x-eq-y→x≡y (suc x) (suc y) [𝕤x-eq-𝕤y] = x-eq-y→x≡y-ind x y (x-eq-y→x≡y x y) [𝕤x-eq-𝕤y]

x-eq-x-ind : (x : Nat) → x eq x ≡ true → (suc x) eq (suc x) ≡ true
x-eq-x-ind x [x-eq-x] = proof
 where
  [𝕤x-eq-𝕤x≡x-eq-x] : (suc x) eq (suc x) ≡ x eq x
  [𝕤x-eq-𝕤x≡x-eq-x] = refl

  proof : (suc x) eq (suc x) ≡ true
  proof = ≡-trans [𝕤x-eq-𝕤x≡x-eq-x] [x-eq-x]

x-eq-x : (x : Nat) → x eq x ≡ true
x-eq-x zero = refl
x-eq-x (suc x) = x-eq-x-ind  x (x-eq-x x)

x≡y→x-eq-y : (x y : Nat) → x ≡ y → x eq y ≡ true
x≡y→x-eq-y x .x refl = x-eq-x x

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

x>y→𝕤x>𝕤y : (x y : Nat) → x > y → (suc x) > (suc y)
x>y→𝕤x>𝕤y x y (n , [y+𝕤n≡x]) = (n , [𝕤y+𝕤n≡𝕤x])
 where
  [𝕤y+𝕤n≡𝕤[y+𝕤n]] : (suc y) + (suc n) ≡ suc (y + (suc n))
  [𝕤y+𝕤n≡𝕤[y+𝕤n]] = refl

  [𝕤[y+𝕤n]≡𝕤x] : suc (y + (suc n)) ≡ suc x
  [𝕤[y+𝕤n]≡𝕤x] = [x≡y]→[fx≡fy] suc (y + (suc n)) x [y+𝕤n≡x]

  [𝕤y+𝕤n≡𝕤x] : (suc y) + (suc n) ≡ (suc x)
  [𝕤y+𝕤n≡𝕤x] = ≡-trans [𝕤y+𝕤n≡𝕤[y+𝕤n]] [𝕤[y+𝕤n]≡𝕤x]

x-gt-y→x>y-ind : (x y : Nat) → (x gt y ≡ true → x > y) → (suc x) gt (suc y) ≡ true → (suc x) > (suc y)
x-gt-y→x>y-ind x y hyp [𝕤x-gt-𝕤y] = [𝕤x>𝕤y]
 where
  [𝕤x-gt-𝕤y≡x-gt-y] : (suc x) gt (suc y) ≡ x gt y
  [𝕤x-gt-𝕤y≡x-gt-y] = refl

  [x-gt-y] : x gt y ≡ true
  [x-gt-y] = ≡-trans (≡-sym [𝕤x-gt-𝕤y≡x-gt-y]) [𝕤x-gt-𝕤y]

  [x>y] : x > y
  [x>y] = hyp [x-gt-y]

  [𝕤x>𝕤y] : (suc x) > (suc y)
  [𝕤x>𝕤y] = x>y→𝕤x>𝕤y x y [x>y]

x-gt-y→x>y : (x y : Nat) → x gt y ≡ true → x > y
x-gt-y→x>y zero zero [false≡true] = ω (true≠false (≡-sym [false≡true]))
x-gt-y→x>y zero (suc y) [false≡true] = ω (true≠false (≡-sym [false≡true]))
x-gt-y→x>y (suc x) zero [true≡true] = (x , refl)
x-gt-y→x>y (suc x) (suc y) [𝕤x-gt-𝕤y] = x-gt-y→x>y-ind x y (x-gt-y→x>y x y) [𝕤x-gt-𝕤y]

𝕤x>𝕤y→x>y : (x y : Nat) → (suc x) > (suc y) → x > y
𝕤x>𝕤y→x>y x y (n , [𝕤y+𝕤n≡𝕤x]) = (n , [y+𝕤n≡x])
 where
  [𝕤y+𝕤n≡𝕤[y+𝕤n]] : (suc y) + (suc n) ≡ suc (y + (suc n))
  [𝕤y+𝕤n≡𝕤[y+𝕤n]] = refl

  [𝕤[y+𝕤n]≡𝕤x] : suc (y + (suc n)) ≡ suc x
  [𝕤[y+𝕤n]≡𝕤x] = ≡-trans (≡-sym [𝕤y+𝕤n≡𝕤[y+𝕤n]]) [𝕤y+𝕤n≡𝕤x]

  [y+𝕤n≡x] : y + (suc n) ≡ x
  [y+𝕤n≡x] = [𝕤x≡𝕤y]→[x≡y] (y + (suc n)) x [𝕤[y+𝕤n]≡𝕤x]
  

x>y→x-gt-y-ind : (x y : Nat) → (x > y → x gt y ≡ true) → (suc x) > (suc y) → (suc x) gt (suc y) ≡ true
x>y→x-gt-y-ind x y hyp (n , [𝕤y+𝕤n≡𝕤x]) = proof
 where
  [x>y] : x > y
  [x>y] = 𝕤x>𝕤y→x>y x y (n , [𝕤y+𝕤n≡𝕤x])

  [x-gt-y] : x gt y ≡ true
  [x-gt-y] = hyp [x>y]

  [𝕤x-gt-𝕤y≡x-gt-y] : (suc x) gt (suc y) ≡ x gt y
  [𝕤x-gt-𝕤y≡x-gt-y] = refl

  proof : (suc x) gt (suc y) ≡ true
  proof = ≡-trans [𝕤x-gt-𝕤y≡x-gt-y] [x-gt-y]

x>y→x-gt-y : (x y : Nat) → x > y → x gt y ≡ true
x>y→x-gt-y 0 0 (n , [0+𝕤n≡0]) = ω disproof
 where
  [0+𝕤n≡𝕤[0+n]] : 0 + (suc n) ≡ suc (0 + n)
  [0+𝕤n≡𝕤[0+n]] = x+𝕤y≡𝕤[x+y] 0 n

  [𝕤[0+n]≡𝕫] : suc (0 + n) ≡ zero
  [𝕤[0+n]≡𝕫] = ≡-trans (≡-sym [0+𝕤n≡𝕤[0+n]]) [0+𝕤n≡0]

  disproof : ⊥
  disproof = 𝕤x≠0 (0 + n) [𝕤[0+n]≡𝕫]
x>y→x-gt-y 0 (suc y) (n , [𝕤y+𝕤n≡0]) = ω disproof
 where
  [𝕤y+𝕤n≡𝕤[y+𝕤n]] : (suc y) + (suc n) ≡ suc (y + (suc n))
  [𝕤y+𝕤n≡𝕤[y+𝕤n]] = refl

  [𝕤[y+𝕤n]≡0] : suc (y + (suc n)) ≡ 0
  [𝕤[y+𝕤n]≡0] = ≡-trans (≡-sym  [𝕤y+𝕤n≡𝕤[y+𝕤n]]) [𝕤y+𝕤n≡0]

  disproof : ⊥
  disproof = 𝕤x≠0 (y + (suc n)) [𝕤[y+𝕤n]≡0]
x>y→x-gt-y (suc x) 0 (n , [0+𝕤n≡𝕤x]) = refl
x>y→x-gt-y (suc x) (suc y) [𝕤x>𝕤y] = x>y→x-gt-y-ind x y (x>y→x-gt-y x y) [𝕤x>𝕤y]

x-lt-y≡y-gt-x-ind : (x y : Nat) → x lt y ≡ y gt x → (suc x) lt (suc y) ≡ (suc y) gt (suc x)
x-lt-y≡y-gt-x-ind x y hyp = proof
 where
  [𝕤x-lt-𝕤y≡x-lt-y] : (suc x) lt (suc y) ≡ x lt y
  [𝕤x-lt-𝕤y≡x-lt-y] = refl

  [y-gt-x≡𝕤y-gt-𝕤x] : y gt x ≡ (suc y) gt (suc x)
  [y-gt-x≡𝕤y-gt-𝕤x] = refl

  proof : (suc x) lt (suc y) ≡ (suc y) gt (suc x)
  proof = ≡-trans [𝕤x-lt-𝕤y≡x-lt-y] [y-gt-x≡𝕤y-gt-𝕤x]

x-lt-y≡y-gt-x : (x y : Nat) → x lt y ≡ y gt x
x-lt-y≡y-gt-x zero zero = refl
x-lt-y≡y-gt-x zero (suc y) = refl
x-lt-y≡y-gt-x (suc x) zero = refl
x-lt-y≡y-gt-x (suc x) (suc y) = x-lt-y≡y-gt-x-ind x y (x-lt-y≡y-gt-x x y)

{-
x-lt-y→x<y : (x y : Nat) → x lt y ≡ true → x < y
x-lt-y→x<y zero zero [false≡true] = ω (true≠false (≡-sym [false≡true]))
x-lt-y→x<y (suc x) zero [false≡true] = ω (true≠false (≡-sym [false≡true]))
x-lt-y→x<y zero (suc y) [true≡true] = (y , [
-}

x-lt-y→x<y : (x y : Nat) → x lt y ≡ true → x < y
x-lt-y→x<y x y [x-lt-y] = x-gt-y→x>y y x (≡-trans (≡-sym (x-lt-y≡y-gt-x x y)) [x-lt-y])

x<y→x-lt-y : (x y : Nat) → x < y → x lt y ≡ true
x<y→x-lt-y x y [y>x] = ≡-trans (x-lt-y≡y-gt-x x y) (x>y→x-gt-y y x [y>x]) 

x-gte-y→x≥y-ind : (x y : Nat) → (x gte y ≡ true → x ≥ y) → (suc x) gte (suc y) ≡ true → (suc x) ≥ (suc y)
x-gte-y→x≥y-ind x y hyp [𝕤x-gte-𝕤y] = (n , [𝕤y+n≡𝕤x])
 where
  [x-gte-y≡𝕤x-gte-𝕤y] : x gte y ≡ (suc x) gte (suc y)
  [x-gte-y≡𝕤x-gte-𝕤y] = refl

  [x-gte-y] : x gte y ≡ true
  [x-gte-y] = ≡-trans [x-gte-y≡𝕤x-gte-𝕤y] [𝕤x-gte-𝕤y]

  [x≥y] : x ≥ y
  [x≥y] = hyp [x-gte-y]

  n : Nat
  n = π₁ [x≥y]

  [y+n≡x] : y + n ≡ x
  [y+n≡x] = π₂ [x≥y]

  [𝕤y+n≡𝕤[y+n]] : (suc y) + n ≡ suc (y + n)
  [𝕤y+n≡𝕤[y+n]] = refl

  [𝕤[y+n]≡𝕤x] : suc (y + n) ≡ suc x
  [𝕤[y+n]≡𝕤x] = [x≡y]→[fx≡fy] suc (y + n) x  [y+n≡x]

  [𝕤y+n≡𝕤x] : (suc y) + n ≡ suc x
  [𝕤y+n≡𝕤x] = ≡-trans [𝕤y+n≡𝕤[y+n]] [𝕤[y+n]≡𝕤x]


x-gte-y→x≥y : (x y : Nat) → x gte y ≡ true → x ≥ y
x-gte-y→x≥y zero zero refl = (zero , refl)
x-gte-y→x≥y (suc x) zero refl = (suc x , refl)
x-gte-y→x≥y zero (suc y) [false≡true] = ω (true≠false (≡-sym [false≡true]))
x-gte-y→x≥y (suc x) (suc y) [𝕤x-gte-𝕤y] = x-gte-y→x≥y-ind x y (x-gte-y→x≥y x y) [𝕤x-gte-𝕤y]

0≱𝕤x : (x : Nat) → ¬ (0 ≥ (suc x))
0≱𝕤x x (n , [𝕤x+n≡0]) = ω (𝕤x≠0 (x + n) [𝕤x+n≡0])

𝕤x≥𝕤y→x≥y : (x y : Nat) → (suc x) ≥ (suc y) → x ≥ y
𝕤x≥𝕤y→x≥y x y (n , [𝕤y+n≡𝕤x]) = (n , [y+n≡x])
 where
  [y+n≡x] : y + n ≡ x
  [y+n≡x] = [𝕤x≡𝕤y]→[x≡y] (y + n) x [𝕤y+n≡𝕤x]


x≥y→x-gte-y-ind : (x y : Nat) → (x ≥ y → x gte y ≡ true) → (suc x) ≥ (suc y) → (suc x) gte (suc y) ≡ true
x≥y→x-gte-y-ind x y hyp [𝕤x≥𝕤y] = [𝕤x-gte-𝕤y]
 where
  [𝕤x-gte-𝕤y≡x-gte-y] : (suc x) gte (suc y) ≡ x gte y
  [𝕤x-gte-𝕤y≡x-gte-y] = refl

  [x≥y] : x ≥ y
  [x≥y] = 𝕤x≥𝕤y→x≥y x y [𝕤x≥𝕤y]

  [x-gte-y] : x gte y ≡ true
  [x-gte-y] = hyp [x≥y]

  [𝕤x-gte-𝕤y] : (suc x) gte (suc y) ≡ true
  [𝕤x-gte-𝕤y] = ≡-trans [𝕤x-gte-𝕤y≡x-gte-y] [x-gte-y]


x≥y→x-gte-y : (x y : Nat) → x ≥ y → x gte y ≡ true
x≥y→x-gte-y zero zero [zero≥zero] = refl
x≥y→x-gte-y (suc x) zero [𝕤x≥zero] = refl
x≥y→x-gte-y zero (suc y) [zero≥𝕤y] = ω (0≱𝕤x y [zero≥𝕤y])
x≥y→x-gte-y (suc x) (suc y) [𝕤x≥𝕤y] = x≥y→x-gte-y-ind x y (x≥y→x-gte-y x y) [𝕤x≥𝕤y]

x-lte-y≡y-gte-x-ind : (x y : Nat) → x lte y ≡ y gte x → (suc x) lte (suc y) ≡ (suc y) gte (suc x)
x-lte-y≡y-gte-x-ind x y hyp = proof
 where
  [𝕤x-lte-𝕤y≡x-lte-y] : (suc x) lte (suc y) ≡ x lte y
  [𝕤x-lte-𝕤y≡x-lte-y] = refl

  [y-gte-x≡𝕤y-gte-𝕤x] : y gte x ≡ (suc y) gte (suc x)
  [y-gte-x≡𝕤y-gte-𝕤x] = refl

  proof : (suc x) lte (suc y) ≡ (suc y) gte (suc x)
  proof = ≡-trans [𝕤x-lte-𝕤y≡x-lte-y] (≡-trans hyp [y-gte-x≡𝕤y-gte-𝕤x])

x-lte-y≡y-gte-x : (x y : Nat) → x lte y ≡ y gte x
x-lte-y≡y-gte-x zero zero = refl
x-lte-y≡y-gte-x zero (suc y) = refl
x-lte-y≡y-gte-x (suc x) zero = refl
x-lte-y≡y-gte-x (suc x) (suc y) = x-lte-y≡y-gte-x-ind x y (x-lte-y≡y-gte-x x y)

x-lte-y→x≤y : (x y : Nat) → x lte y ≡ true → x ≤ y
x-lte-y→x≤y x y [x-lte-y] = x-gte-y→x≥y y x (≡-trans (≡-sym (x-lte-y≡y-gte-x x y)) [x-lte-y])

x≤y→x-lte-y : (x y : Nat) → x ≤ y → x lte y ≡ true
x≤y→x-lte-y x y [y≥x] = ≡-trans (x-lte-y≡y-gte-x x y) (x≥y→x-gte-y y x [y≥x]) 
