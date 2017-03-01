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

{-
Proofs about successor and addition:
1) zero is not the successor of any number
2) suc is injective
3) pred (suc n) ≡ n
4) n ≡ pred (suc n)
5) suc x ≠ x
6) x ≠ suc x
7) (suc x) + y ≡ suc (x + y)
8) suc (x + y) ≡ (suc x) + y
9) 0 + x ≡ x
10) x ≡ 0 + x
11) x + 0 ≡ x
12) x ≡ x + 0
13) 1 + x ≡ suc x
14) suc x ≡ 1 + x
15) x + 1 ≡ suc x
16) suc x ≡ x + 1
17) x + (suc y) ≡ suc (x + y)
18) suc (x + y) ≡ x + (suc y)
19) (a + x) + y ≡ x + (a + y)
20) x + (a + y) ≡ (a + x) + y
21) x + y ≡ y + x ; addition is commutative
22) (a + b) + c ≡ a + (b + c) ; addition is associative, 1
23) a + (b + c) ≡ (a + b) + c ; addition is associative, 2
24) 0 is the unique right identity for +
25) 0 is the unique left identity for +
26) if x + y ≡ 0 , then x ≡ 0 and y ≡ 0
-}

-- 1) zero is not the successor of any number
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

-- 2) suc is injective
[𝕤x≡𝕤y]→[x≡y] : (x y : Nat) → suc x ≡ suc y → x ≡ y
[𝕤x≡𝕤y]→[x≡y] x y [𝕤x≡𝕤y] = [x≡y]→[fx≡fy] pred (suc x) (suc y) [𝕤x≡𝕤y]

-- 3) pred (suc n) ≡ n
pred-𝕤n≡n : (n : Nat) → pred (suc n) ≡ n
pred-𝕤n≡n n = refl

-- 4) n ≡ pred (suc n)
n≡pred-𝕤n : (n : Nat) → n ≡ pred (suc n)
n≡pred-𝕤n n = refl

-- 5) suc x ≠ x
𝕤x≠x-ind : (x : Nat) → suc x ≠ x → (suc (suc x)) ≠ (suc x)
𝕤x≠x-ind x [𝕤x≠x] [𝕤𝕤x≡𝕤x] = disproof
 where
  [𝕤x≡x] : suc x ≡ x
  [𝕤x≡x] = [x≡y]→[fx≡fy] pred (suc (suc x)) (suc x) [𝕤𝕤x≡𝕤x]

  disproof : ⊥
  disproof = [𝕤x≠x] [𝕤x≡x]

𝕤x≠x : (x : Nat) → suc x ≠ x
𝕤x≠x 0 = 𝕤x≠0 0
𝕤x≠x (suc x) = 𝕤x≠x-ind x (𝕤x≠x x)

-- 6) x ≠ suc x
x≠𝕤x : (x : Nat) → x ≠ suc x
x≠𝕤x x = ≠-sym (𝕤x≠x x)

-- 7) (suc x) + y ≡ suc (x + y)
𝕤x+y≡𝕤[x+y] : (x y : Nat) → suc x + y ≡ suc (x + y)
𝕤x+y≡𝕤[x+y] x y = refl

-- 8) suc (x + y) ≡ (suc x) + y
𝕤[x+y]≡𝕤x+y : (x y : Nat) → suc (x + y) ≡ (suc x) + y
𝕤[x+y]≡𝕤x+y x y = refl

-- 9) 0 + x ≡ x
0+x≡x : (x : Nat) → 0 + x ≡ x
0+x≡x x = refl

-- 10) x ≡ 0 + x
x≡0+x : (x : Nat) → x ≡ 0 + x
x≡0+x x = refl

-- 11) x + 0 ≡ x
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

-- 12) x ≡ x + 0
x≡x+0 : (x : Nat) → x ≡ x + 0
x≡x+0 x = ≡-sym (x+0≡x x)

-- 13) 1 + x ≡ suc x
1+x≡𝕤x : (x : Nat) → 1 + x ≡ suc x
1+x≡𝕤x x = refl

-- 14) suc x ≡ 1 + x
𝕤x≡1+x : (x : Nat) → suc x ≡ 1 + x
𝕤x≡1+x x = refl

-- 15) x + 1 ≡ suc x
x+1≡𝕤x-ind : (x : Nat) → x + 1 ≡ suc x → (suc x) + 1 ≡ suc (suc x)
x+1≡𝕤x-ind x hyp = proof
 where
  𝕤x+1≡𝕤[x+1] : (suc x) + 1 ≡ suc (x + 1)
  𝕤x+1≡𝕤[x+1] = refl

  proof : (suc x) + 1 ≡ suc (suc x)
  proof = [x≡y]→[fx≡fy] suc (x + 1) (suc x) hyp

x+1≡𝕤x : (x : Nat) → x + 1 ≡ suc x
x+1≡𝕤x 0 = refl
x+1≡𝕤x (suc x) = x+1≡𝕤x-ind x (x+1≡𝕤x x)

-- 16) suc x ≡ x + 1
𝕤x≡x+1 : (x : Nat) → suc x ≡ x + 1
𝕤x≡x+1 x = ≡-sym (x+1≡𝕤x x)

-- 17) x + (suc y) ≡ suc (x + y)
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

-- 18) suc (x + y) ≡ x + (suc y)
𝕤[x+y]≡x+𝕤y : (x y : Nat) → suc (x + y) ≡ x + (suc y)
𝕤[x+y]≡x+𝕤y x y = ≡-sym (x+𝕤y≡𝕤[x+y] x y)


-- 19) (a + x) + y ≡ x + (a + y)
[a+x]+y≡x+[a+y]-ind : (x y a : Nat) → (a + x) + y ≡ x + (a + y) → ((suc a) + x) + y ≡ x + ((suc a) + y)
[a+x]+y≡x+[a+y]-ind x y a hyp = proof
 where
  +y : Nat → Nat
  +y n = n + y

  [[𝕤a+x]+y≡[𝕤[a+x]]+y] : ((suc a) + x) + y ≡ (suc (a + x)) + y
  [[𝕤a+x]+y≡[𝕤[a+x]]+y] = [x≡y]→[fx≡fy] +y ((suc a) + x) (suc (a + x)) refl

  [[𝕤[a+x]]+y≡𝕤[[a+x]+y]] : ((suc a) + x) + y ≡ suc ((a + x) + y)
  [[𝕤[a+x]]+y≡𝕤[[a+x]+y]] = refl

  x+ : Nat → Nat
  x+ n = x + n

  [x+[𝕤a+y]≡x+[𝕤[a+y]]] : x + ((suc a) + y) ≡ x + (suc (a + y))
  [x+[𝕤a+y]≡x+[𝕤[a+y]]] = [x≡y]→[fx≡fy] x+ ((suc a) + y) (suc (a + y)) refl

  [x+[𝕤[a+y]]≡𝕤[x+[a+y]]] : x + (suc (a + y)) ≡ suc (x + (a + y))
  [x+[𝕤[a+y]]≡𝕤[x+[a+y]]] = x+𝕤y≡𝕤[x+y] x (a + y)

  [𝕤[[a+x]+y]≡𝕤[x+[a+y]]] : suc ((a + x) + y) ≡ suc (x + (a + y))
  [𝕤[[a+x]+y]≡𝕤[x+[a+y]]] = [x≡y]→[fx≡fy] suc ((a + x) + y) (x + (a + y)) hyp

  proof : ((suc a) + x) + y ≡ x + ((suc a) + y)
  proof = 
    ≡-trans [[𝕤a+x]+y≡[𝕤[a+x]]+y] 
   (≡-trans [[𝕤[a+x]]+y≡𝕤[[a+x]+y]] 
   (≡-trans [𝕤[[a+x]+y]≡𝕤[x+[a+y]]] 
   (≡-trans (≡-sym [x+[𝕤[a+y]]≡𝕤[x+[a+y]]])
     (≡-sym [x+[𝕤a+y]≡x+[𝕤[a+y]]])
   )))

[a+x]+y≡x+[a+y] : (x y a : Nat) → (a + x) + y ≡ x + (a + y)
[a+x]+y≡x+[a+y] x y 0 = refl
[a+x]+y≡x+[a+y] x y (suc a) = [a+x]+y≡x+[a+y]-ind x y a ([a+x]+y≡x+[a+y] x y a)

-- 20) x + (a + y) ≡ (a + x) + y
x+[a+y]≡[a+x]+y : (x y a : Nat) → x + (a + y) ≡ (a + x) + y
x+[a+y]≡[a+x]+y x y a = ≡-sym ([a+x]+y≡x+[a+y] x y a)

-- 21) x + y ≡ y + x ; addition is commutative
x+y≡y+x : (x y : Nat) → x + y ≡ y + x
x+y≡y+x x y = [x+y≡y+x]
 where
  [[x+y]+0≡y+[x+0]] : (x + y) + 0 ≡ y + (x + 0)
  [[x+y]+0≡y+[x+0]] = [a+x]+y≡x+[a+y] y 0 x

  [[x+y]+0≡x+y] : (x + y) + 0 ≡ x + y
  [[x+y]+0≡x+y] = x+0≡x (x + y)

  [x+0≡x] : x + 0 ≡ x
  [x+0≡x] = x+0≡x x

  y+ : Nat → Nat
  y+ n = y + n

  [y+[x+0]≡y+x] : y + (x + 0) ≡ y + x
  [y+[x+0]≡y+x] = [x≡y]→[fx≡fy] y+ (x + 0) x [x+0≡x]

  [x+y≡y+x] : x + y ≡ y + x
  [x+y≡y+x] = ≡-trans (≡-sym [[x+y]+0≡x+y]) (≡-trans [[x+y]+0≡y+[x+0]] [y+[x+0]≡y+x])

+-comm : (x y : Nat) → x + y ≡ y + x
+-comm = x+y≡y+x

-- 22) (a + b) + c ≡ a + (b + c) ; addition is associative
[a+b]+c≡a+[b+c] : (a b c : Nat) → (a + b) + c ≡ a + (b + c)
[a+b]+c≡a+[b+c] a b c = proof
 where
  [a+b≡b+a] : a + b ≡ b + a
  [a+b≡b+a] = +-comm a b

  +c : Nat → Nat
  +c n = n + c

  [[a+b]+c≡[b+a]+c] : (a + b) + c ≡ (b + a) + c
  [[a+b]+c≡[b+a]+c] = [x≡y]→[fx≡fy] +c (a + b) (b + a) (+-comm a b)

  [[b+a]+c≡a+[b+c]] : (b + a) + c ≡ a + (b + c)
  [[b+a]+c≡a+[b+c]] = [a+x]+y≡x+[a+y] a c b

  proof : (a + b) + c ≡ a + (b + c)
  proof = ≡-trans [[a+b]+c≡[b+a]+c] [[b+a]+c≡a+[b+c]]

+-assoc : (a b c : Nat) → (a + b) + c ≡ a + (b + c)
+-assoc = [a+b]+c≡a+[b+c]

-- 23) a + (b + c) ≡ (a + b) + c
a+[b+c]≡[a+b]+c : (a b c : Nat) → a + (b + c) ≡ (a + b) + c
a+[b+c]≡[a+b]+c a b c = ≡-sym ([a+b]+c≡a+[b+c] a b c)

+-assoc₂ : (a b c : Nat) → a + (b + c) ≡ (a + b) + c
+-assoc₂ = a+[b+c]≡[a+b]+c

-- 24) 0 is the unique right identity for Nat
[x+y≡x]→[y≡0]-ind : (x y : Nat) → (x + y ≡ x → y ≡ 0) → (suc x) + y ≡ suc x → y ≡ 0
[x+y≡x]→[y≡0]-ind x y hyp [𝕤x+y≡𝕤x] = [y≡0]
 where
  [𝕤[x+y]≡𝕤x+y] : suc (x + y) ≡ (suc x) + y
  [𝕤[x+y]≡𝕤x+y] = refl

  [𝕤[x+y]≡𝕤x] : suc (x + y) ≡ suc x
  [𝕤[x+y]≡𝕤x] = ≡-trans [𝕤[x+y]≡𝕤x+y] [𝕤x+y≡𝕤x]

  [x+y≡x] : x + y ≡ x
  [x+y≡x] = [𝕤x≡𝕤y]→[x≡y] (x + y) x [𝕤[x+y]≡𝕤x]

  [y≡0] : y ≡ 0
  [y≡0] = hyp [x+y≡x]
  

[x+y≡x]→[y≡0] : (x y : Nat) → x + y ≡ x → y ≡ 0
[x+y≡x]→[y≡0] 0 y [y≡0] = [y≡0]
[x+y≡x]→[y≡0] (suc x) y [𝕤x+y≡𝕤x] = [x+y≡x]→[y≡0]-ind x y ([x+y≡x]→[y≡0] x y) [𝕤x+y≡𝕤x]

-- 25) 0 is the unique left identity for Nat
[y+x≡x]→[y≡0] : (x y : Nat) → y + x ≡ x → y ≡ 0
[y+x≡x]→[y≡0] x y [y+x≡x] = [y≡0]
 where
  [x+y≡y+x] : x + y ≡ y + x
  [x+y≡y+x] = x+y≡y+x x y

  [x+y≡x] : x + y ≡ x
  [x+y≡x] = ≡-trans [x+y≡y+x] [y+x≡x]

  [y≡0] : y ≡ 0
  [y≡0] = [x+y≡x]→[y≡0] x y [x+y≡x]

-- 26) if x + y ≡ 0 , then x ≡ 0 and y ≡ 0
[x+y≡0]→[x≡0∧y≡0] : (x y : Nat) → x + y ≡ 0 → x ≡ 0 ∧ y ≡ 0
[x+y≡0]→[x≡0∧y≡0] 0 0 refl = (refl , refl)
[x+y≡0]→[x≡0∧y≡0] 0 (suc y) [𝕤y≡0] = ω (𝕤x≠0 y [𝕤y≡0])
[x+y≡0]→[x≡0∧y≡0] (suc x) 0 [𝕤x+0≡0] = ω (𝕤x≠0 (x + 0) [𝕤x+0≡0])
[x+y≡0]→[x≡0∧y≡0] (suc x) (suc y) [𝕤x+𝕤y≡0] = ω (𝕤x≠0 (x + (suc y)) [𝕤x+𝕤y≡0])



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




 

x≮0 : (x : Nat) → x < zero → ⊥
x≮0 x (z , [x+𝕤z≡0]) = ☢
 where
  [x+𝕤z≡𝕤[x+z]] : x + suc z ≡ suc (x + z)
  [x+𝕤z≡𝕤[x+z]] = x+𝕤y≡𝕤[x+y] x z

  [𝕤[x+z]≡0] : suc (x + z) ≡ zero
  [𝕤[x+z]≡0] = ≡-⇶ (≡-↑↓ [x+𝕤z≡𝕤[x+z]]) [x+𝕤z≡0]

  ☢ : ⊥
  ☢ = 𝕤x≠0 (x + z) [𝕤[x+z]≡0]

0≯x : (x : Nat) → ¬ (0 > x)
0≯x x = x≮0 x

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

suc2sum : Nat → Nat
suc2sum zero = zero
suc2sum (suc x) = (suc zero) + (suc2sum x)

suc2sum-x≡x-ind : (x : Nat) → x ≡ suc2sum x → (suc x) ≡ (suc2sum (suc x))
suc2sum-x≡x-ind x [x≡suc2sum-x] = proof
 where
  [𝕤x≡[1+x]] : suc x ≡ (1 + x)
  [𝕤x≡[1+x]] = 𝕤x≡1+x x

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

0≮0 : ¬ (0 < 0)
0≮0 = x≮0 0

x≮x-ind : (x : Nat) → ¬ (x < x) → ¬ ((suc x) < (suc x))
x≮x-ind x ¬[x<x] [𝕤x<𝕤x] = ¬[x<x] ([𝕤x<𝕤y]→[x<y] x x [𝕤x<𝕤x])

x≮x : (x : Nat) → ¬ (x < x)
x≮x 0 [0<0] = 0≮0 [0<0]
x≮x (suc x) = x≮x-ind x (x≮x x)

x≯x : (x : Nat) → ¬ (x > x)
x≯x x = x≮x x

x≤x : (x : Nat) → x ≤ x
x≤x x = (0 , (x+0≡x x))

x≥x : (x : Nat) → x ≥ x
x≥x x = x≤x x

x>y→x≥y : (x y : Nat) → x > y → x ≥ y
x>y→x≥y x y (n , [y+𝕤n≡x]) = ((suc n) , [y+𝕤n≡x])

x<y→x≤y : (x y : Nat) → x < y → x ≤ y
x<y→x≤y x y (n , [x+𝕤n≡y]) = ((suc n) , [x+𝕤n≡y])

{-
x>y→x≮y : (x y : Nat) → x > y → ¬ (x < y)
x>y→x≮y x y (n , [y+𝕤n≡x]) (m , [x+𝕤m≡y]) = disproof
 where
  [𝕤[x+m]≡x+𝕤m] : suc (x + m) ≡ x + (suc m)
  [𝕤[x+m]≡x+𝕤m] = ≡-sym (x+𝕤y≡𝕤[x+y] x m)

  [𝕤[x+m]≡y] : suc (x + m) ≡ y
  [𝕤[x+m]≡y] = ≡-trans [𝕤[x+m]≡x+𝕤m] [x+𝕤m≡y]

  [𝕤[y+n]≡y+𝕤n] : suc (y + n) ≡ y + (suc n)
  [𝕤[y+n]≡y+𝕤n] = ≡-sym (x+𝕤y≡𝕤[x+y] y n)

  [𝕤[y+n]≡x] : suc (y + n) ≡ x
  [𝕤[y+n]≡x] = ≡-trans [𝕤[y+n]≡y+𝕤n] [y+𝕤n≡x]

  [𝕤[y+n]≡𝕤[𝕤[x+m]+n]] : suc (y + n) ≡ 

  disproof : ⊥
-}

{-
+-assoc : 
-}

{-
>-trans : (x y z : Nat) → x > y  → y > z → x > z
>-trans x y z (m , [y+𝕤m≡x]) (n , [z+𝕤n≡y]) = ((m + (suc n)) , [z+𝕤[m+𝕤n]≡x])
 where
  [𝕤[m+𝕤n]≡𝕤m+𝕤n] : suc (m + (suc n)) ≡ (suc m) + (suc n)
  [𝕤[m+𝕤n]≡𝕤m+𝕤n] = refl

  z+ : Nat → Nat
  z+ n = z + n

  [z+𝕤[m+𝕤n]≡z+[𝕤m+𝕤n]] : z + suc (m + (suc n)) ≡ z + ((suc m) + (suc n))
  [z+𝕤[m+𝕤n]≡z+[𝕤m+𝕤n]] = [x≡y]→[fx≡fy] z+ (suc (m + (suc n)) ((suc m) + (suc n)) refl

  [z+[𝕤m+𝕤n]≡[z+𝕤m]+𝕤n] : z + ((suc m) + (suc n)) ≡ (z + (suc m)) + (suc n)
  [z+[𝕤m+𝕤n]≡[z+𝕤m]+𝕤n] = 
-}
