module ArithmeticDefinability where

open import Agda.Primitive
open import BaseLogic

{-
The input/output relations of the general recursive functions are definable in Robinson arithmetic:
-}
--http://www.cogsci.rpi.edu/~heuveb/teaching/Logic/CompLogic/Web/Presentations/Arithmetical%20Definability.pdf

{- 
 This gives us the 4 symbols we can use from Robinson arithmetic along with
 appropriate interpretation of their meaning.
-}
data Nat : Set where
 zero : Nat
 suc : Nat → Nat
{-# BUILTIN NATURAL Nat #-}


infixr 4 _+_
_+_ : Nat → Nat → Nat
0 + y = y
(suc x) + y = suc (x + y)

infixr 5 _*_
_*_ : Nat → Nat → Nat
0 * y = 0
(suc x) * y = y + (x * y)


{-
To talk about functions of arbitrary arities, we'll use functions on
finite vectors with a given length:
-}
data Vector {α} (A : Set α) : Nat → Set α where
 [] : Vector A zero
 _∷_ : {n : Nat} → A → Vector A n → Vector A (suc n)

_++_ : ∀ {α} {A : Set α} {n m : Nat} → Vector A n → Vector A m → Vector A (n + m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

{-
Let's make things simpler with non-empty vectors:
-}

data NEVec (A : Set) : Nat → Set where
 end : A → NEVec A (suc zero)
 _∷_ : {n : Nat} → A → NEVec A n → NEVec A (suc n)

infixr 3 _<_
_<_ : Nat → Nat → Set
x < y = ∃ z ∈ Nat , (x + (suc z) ≡ y)

infixr 3 _≤_
_≤_ : Nat → Nat → Set
x ≤ y = ∃ z ∈ Nat , (x + z ≡ y)

infixr 3 _>_
_>_ : Nat → Nat → Set
x > y = ∃ z ∈ Nat , (y + (suc z) ≡ x)

infixr 3 _≥_
_≥_ : Nat → Nat → Set
x ≥ y = ∃ z ∈ Nat , (y + z ≡ x)



pred : Nat → Nat
pred 0 = 0
pred (suc x) = x


𝕤x+y≡𝕤[x+y] : (x y : Nat) → suc x + y ≡ suc (x + y)
𝕤x+y≡𝕤[x+y] x y = refl (suc (x + y))

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


data Bool : Set where
 true : Bool
 false : Bool

BoolToSet : Bool → Set
BoolToSet true = ⊤
BoolToSet false = ⊥

𝕥≠𝕗 : true ≡ false → ⊥
𝕥≠𝕗 [𝕥≡𝕗] = ☢
 where
  [⊤≡⊥] : ⊤ ≡ ⊥
  [⊤≡⊥] = [x≡y]→[fx≡fy] BoolToSet true false [𝕥≡𝕗]

  ☢ : ⊥
  ☢ = ⊤≠⊥ [⊤≡⊥]

isZero : Nat → Bool
isZero zero = true
isZero (suc x) = false

𝕤x≠0 : (x : Nat) → (suc x) ≠ zero
𝕤x≠0 x [𝕤x≡𝕫] = ☢
 where
  [𝕥≡isZero-𝕫] : true ≡ isZero zero
  [𝕥≡isZero-𝕫] = refl true

  [isZero-𝕤x≡𝕗] : isZero (suc x) ≡ false
  [isZero-𝕤x≡𝕗] = refl false

  [isZero-𝕫≡isZero-𝕤x] : isZero zero ≡ isZero (suc x)
  [isZero-𝕫≡isZero-𝕤x] = [x≡y]→[fx≡fy] isZero zero (suc x) (≡-↑↓ [𝕤x≡𝕫])

  [𝕥≡𝕗] : true ≡ false
  [𝕥≡𝕗] = ≡-⇶ (≡-⇶ [𝕥≡isZero-𝕫] [isZero-𝕫≡isZero-𝕤x]) [isZero-𝕤x≡𝕗]

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]

𝕫+𝕤y≡𝕤[𝕫+y] : (y : Nat) → zero + suc y ≡ suc (zero + y)
𝕫+𝕤y≡𝕤[𝕫+y] y = refl (suc y)

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
1>0 = (0 , refl 1)

[x>0]→[𝕤x>0] : (x : Nat) → x > 0 → suc x > 0
[x>0]→[𝕤x>0] x (z , [0+𝕤z≡x]) = (suc z , [0+𝕤𝕤z≡𝕤x])
 where
  [𝕤z≡0+𝕤z] : suc z ≡ 0 + suc z
  [𝕤z≡0+𝕤z] = refl (suc z)

  [𝕤z≡x] : suc z ≡ x
  [𝕤z≡x] = ≡-⇶ [𝕤z≡0+𝕤z] [0+𝕤z≡x]

  [0+𝕤𝕤z≡𝕤𝕤z] : 0 + suc (suc z) ≡ suc (suc z)
  [0+𝕤𝕤z≡𝕤𝕤z] = refl (suc (suc z))

  [𝕤𝕤z≡𝕤x] : suc (suc z) ≡ suc x
  [𝕤𝕤z≡𝕤x] = [x≡y]→[fx≡fy] suc (suc z) x [𝕤z≡x]

  [0+𝕤𝕤z≡𝕤x] : 0 + suc (suc z) ≡ suc x
  [0+𝕤𝕤z≡𝕤x] = ≡-⇶ [0+𝕤𝕤z≡𝕤𝕤z] [𝕤𝕤z≡𝕤x]



get : {A : Set} (n : Nat) → NEVec A (suc n) → (i : Nat) → (i < (suc n)) → A
get {A} zero (end a) zero [𝕫<𝕤𝕫] = a

-- absurd case: (suc x) ≮ 1
get {A} zero (end a) (suc x) [𝕤x<𝕤𝕫] = ω ☢
 where
--proof that this is a throwaway case:
  ☢ : ⊥
  ☢ = 𝕤x≮1 x [𝕤x<𝕤𝕫]

{-
Agda doesn't know there's a conflict between zero and (a ∷ as) here

We can operate on the knowledge that this is actually an impossible case
and just return a throwaway value `a`.

Prove that these are throwaways by proving that the assumptions lead to contradiction
and using the ⊥-elim
-}
-- absurd case: no (a ∷ as) of length 1
get {A} zero (a ∷ as) zero [𝕫<𝕤𝕫] = a
{-
 where
  ☢ : ⊥

-- Not sure how to prove that NEVec Nat (suc zero) cannot have the form (a ∷ as)
-- Maybe if we can prove that as : NEVec Nat zero and NEVec Nat zero → ⊥

-}  

-- absurd case: no (a ∷ as) of length 1, and (suc x) ≮ 1
get {A} zero (a ∷ as) (suc x) [𝕤x<𝕤𝕫] = ω ☢
 where
  ☢ : ⊥
  ☢ = 𝕤x≮1 x [𝕤x<𝕤𝕫]

{-
Agda knows there's a conflict between (suc n) and (end a) here

-- absurd case: no (end a) of length > 1
get {A} (suc n) (end a) zero [𝕫<𝕤𝕤n] = a

-- absurd case: no (end a) of length > 1
get {A} (suc n) (end a) (suc x) [𝕤x<𝕤𝕤n] = a
-}

get {A} (suc n) (a ∷ as) zero [𝕫<𝕤𝕤n] = a
get {A} (suc n) (a ∷ as) (suc x) [𝕤x<𝕤𝕤n] = get {A} n as x [x<𝕤n]
 where
  [x<𝕤n] : x < suc n
  [x<𝕤n] = [𝕤x<𝕤y]→[x<y] x (suc n) [𝕤x<𝕤𝕤n]




data NEVec₂ (A : Set) : (n : Nat) → n > 0 → Set where
 end : A → NEVec₂ A 1 1>0 
 _∷_ : {n : Nat} {[n>0] : n > 0} → A → NEVec₂ A n [n>0] → NEVec₂ A (suc n) ([x>0]→[𝕤x>0] n [n>0])

-- Fin n is a set with n elements.
data Fin : Nat → Set where
 zero : {n : Nat} → Fin (suc n)
 suc : {n : Nat} → (i : Fin n) → Fin (suc n)

--vec[i]=val : vector x at index y has value val
data _[_]=_ {α} {A : Set α} : {n : Nat} → Vector A n → Fin n → A → Set α where
 here : ∀ {n : Nat} {x : A} {xs : Vector A n} → (x ∷ xs) [ zero ]= x
 there : ∀ {n : Nat} {i : Fin n} {x y : A} {xs : Vector A n} (xs[i]=x : xs [ i ]= x) → (y ∷ xs) [ suc i ]= x


data N-ary-relation {α} (A : Set α) : Nat → Set α where
 [in=_,out=_] : {n : Nat} → Vector A n → A → N-ary-relation A (suc n)

-- Note that we could just define Vectors of length n as n-ary relations.

data N-ary-relation₂ {α} (A : Set α) (n : Nat) (P : Vector A n → Set) : Set α where
 [components=_,proof=_] : (vec : Vector A n) → P vec → N-ary-relation₂ A n P

data N-ary-relation₃ {α} (A : Set α) (n : Nat) : Set (lsuc α) where
 rel : (Vector A n → Set α) → N-ary-relation₃ A n

data Relation {α} {β} (A : Set α) (n : Nat) : Set (lsuc β ⊔ α) where
 rel : (Vector A n → Set β) → Relation A n


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
x+0≡x 0 = refl 0
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

fromℕ : (n : Nat) → Fin (suc n)
fromℕ zero = zero
fromℕ (suc n) = suc (fromℕ n)


raise : ∀ {m : Nat} (n : Nat) → Fin m → Fin (n + m)
raise zero i = i
raise (suc n) i = suc (raise n i)


get-rel : {k : Nat} → Relation Nat (suc (suc k)) → Vector Nat (suc (suc k)) → Set
get-rel {k} (rel R) = R

get-inputs : (k : Nat) → Vector Nat (suc (suc k)) → Vector Nat (suc k)
get-inputs zero (x₁ ∷ x₂ ∷ []) = x₁ ∷ []
get-inputs (suc n) (x₁ ∷ x₂ ∷ xs) = x₁ ∷ (get-inputs n (x₂ ∷ xs))

get-output : (k : Nat) → Vector Nat (suc (suc k)) → Nat
get-output zero (x₁ ∷ x₂ ∷ []) = x₂
get-output (suc n) (x₁ ∷ x₂ ∷ xs) = get-output n (x₂ ∷ xs)

Vector-coerce-length : ∀ {α} {A : Set α} {m n : Nat} → Vector A m → m ≡ n → Vector A n
Vector-coerce-length {α} {A} {m} {.m} vec (refl .m) = vec


--Make sure these are pulling from the right indices

AD-pred : Nat → Nat → Set
AD-pred x y = (x ≡ 0 ∧ y ≡ 0) ∨ x ≡ (suc y)

AD-diff : Nat → Nat → Nat → Set
AD-diff x y z = (x ≤ y ∧ z ≡ 0) ∨ x ≡ y + z

{-
Page 7:
The modified quotient function quo(x,y) where
quo(x,y) = 0 for y = 0 and quo(x,y) = largest z such
that y * z < x, is defined by:
-}
AD-quo : Nat → Nat → Nat → Set
AD-quo x y z = (y ≡ 0 ∧ z ≡ 0) ∨ ∃ w ∈ Nat , (w < y ∧ y * z + w ≡ x)


{-
Page 7:
The modified remainder function rem(x,y), where
rem(x,y) = x for y = 0 and rem(x,y) = z such that z < y
and there is some w such that y * w + z = x, is 
defined by the formula:
-}

AD-rem : Nat → Nat → Nat → Set
AD-rem x y z = (y ≡ 0 ∧ z ≡ x) ∨ (z < y ∧ (∃ w ∈ Nat , (y * w + z ≡ x)))

{-
We can also define AD-rem in term of AD-quo:
-}

AD-rem₂ : Nat → Nat → Nat → Set
AD-rem₂ x y z = ∃ w ∈ Nat , (AD-quo x y w ∧ y * w + z ≡ x)



AD-zero₂ : Relation Nat 2
AD-zero₂ = rel (λ vec → ∃ y ∈ Nat , ( (vec [ suc zero ]= y) ∧ (y ≡ 0)))

AD-suc₂ : Relation Nat 2
AD-suc₂ = rel (λ vec → ∃ x ∈ Nat , (∃ y ∈ Nat , ((vec [ zero ]= x) ∧ (vec [ suc zero ]= y) ∧ y ≡ suc x)))

AD-id₂ : (n : Nat) → (i : Fin (suc n)) → Relation Nat (suc (suc n))
AD-id₂ n' i' = rel (λ vec → ∃ x ∈ Nat , (∃ y ∈ Nat , ((vec [ i ]= x) ∧ (vec [ n+1 ]= y) ∧ y ≡ x)))
 where
  i : Fin (suc (suc n'))
  i = raise 1 i'

  n+1 : Fin (suc (suc n'))
  n+1 = fromℕ (suc n')


--Fin (suc (suc n)) has n+2 elements. There will always be at least 2 elements, even when n=0.
--The convention is that the last element will be the output, and the first (n+1) elements will be the inputs.
--The indices start at 0, so the first element is vec[0], and the last element is vec[n+1].
--The input index should only cover the first (n+1) elements, so Fin (suc n).
--Later we can generalize this to include unary relations.



AD-comp : (k m : Nat) → (f : Relation Nat (suc (suc k))) → (gs : Vector (Relation Nat (suc (suc m))) (suc k)) → Relation {lzero} {lsuc lzero} Nat (suc (suc m))
AD-comp k m f gs = rel (λ vec →
  ∃ ys ∈ Vector Nat (suc k) , ( 
   ((i : Fin (suc k)) → 
      ∃ yi ∈ Nat , (
      ∃ gi ∈ Relation Nat (suc (suc m)) , (
         ys [ i ]= yi ∧ 
         gs [ i ]= gi ∧ 
         (get-rel gi) (Vector-coerce-length ((get-inputs m vec) ++ (yi ∷ [])) [𝕤[m+1]≡𝕤𝕤m])
      ))
   ) ∧ (get-rel f) (Vector-coerce-length (ys ++ ((get-output m vec) ∷ [])) [𝕤[k+1]≡𝕤𝕤k])
  )
 )
 where
  [m+1≡𝕤[m+0]] : m + 1 ≡ suc (m + 0)
  [m+1≡𝕤[m+0]] = x+𝕤y≡𝕤[x+y] m 0

  [m+0≡m] : m + 0 ≡ m
  [m+0≡m] = x+0≡x m

  [𝕤[m+0]≡𝕤m] : suc (m + 0) ≡ suc m
  [𝕤[m+0]≡𝕤m] = [x≡y]→[fx≡fy] suc (m + 0) m [m+0≡m]
 
  [m+1≡𝕤m] : m + 1 ≡ suc m
  [m+1≡𝕤m] = ≡-⇶ [m+1≡𝕤[m+0]] [𝕤[m+0]≡𝕤m]

  [𝕤[m+1]≡𝕤𝕤m] : suc (m + 1) ≡ suc (suc m)
  [𝕤[m+1]≡𝕤𝕤m] = [x≡y]→[fx≡fy] suc (m + 1) (suc m) [m+1≡𝕤m]

  [k+1≡𝕤[k+0]] : k + 1 ≡ suc (k + 0)
  [k+1≡𝕤[k+0]] = x+𝕤y≡𝕤[x+y] k 0

  [k+0≡k] : k + 0 ≡ k
  [k+0≡k] = x+0≡x k

  [𝕤[k+0]≡𝕤k] : suc (k + 0) ≡ suc k
  [𝕤[k+0]≡𝕤k] = [x≡y]→[fx≡fy] suc (k + 0) k [k+0≡k]

  [k+1≡𝕤k] : k + 1 ≡ suc k
  [k+1≡𝕤k] = ≡-⇶ [k+1≡𝕤[k+0]] [𝕤[k+0]≡𝕤k]

  [𝕤[k+1]≡𝕤𝕤k] : suc (k + 1) ≡ suc (suc k)
  [𝕤[k+1]≡𝕤𝕤k] = [x≡y]→[fx≡fy] suc (k + 1) (suc k) [k+1≡𝕤k]


{-
AD-prim : ... requires Chinese remainder theorem ...
-}

{-
 Next step would be proving that these actually define the general recursive functions somehow, instead of
 just claiming that they do and assuming it to be correct.
-}
