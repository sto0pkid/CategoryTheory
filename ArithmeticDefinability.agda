module ArithmeticDefinability where

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
data Vector (A : Set) : Nat → Set where
 [] : Vector A zero
 _∷_ : {n : Nat} → A → Vector A n → Vector A (suc n)

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

{-
Now let's define those primitive recursive functions
-}

{-
Page 9:
-}
AD-zero : Nat → Nat → Set
AD-zero x y = y ≡ 0

AD-suc : Nat → Nat → Set
AD-suc x y = y ≡ suc x

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
{-
[A≡B]→[A→B] : ∀ {i} {A B : Set i} → A ≡ B → A → B
[A≡B]→[A→B] {i} {A} {.A} (refl .A) a = a


⊤≠⊥ : ⊤ ≡ ⊥ → ⊥
⊤≠⊥ [⊤≡⊥] = ☢
 where
  [⊤→⊥] : ⊤ → ⊥
  [⊤→⊥] = [A≡B]→[A→B] [⊤≡⊥]
  ☢ : ⊥
  ☢ = [⊤→⊥] ●
-}

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


get : {A : Set} (n : Nat) → NEVec A (suc n) → (i : Nat) → (i < (suc n)) → A
get {A} zero (end a) zero [𝕫<𝕤𝕫] = a

-- absurd case: (suc x) ≮ 1
get {A} zero (end a) (suc x) [𝕤x<𝕤𝕫] = a

{-
Agda doesn't know there's a conflict between zero and (a ∷ as) here

We can operate on the knowledge that this is actually an impossible case
and just return a throwaway value `a`.

Prove that these are throwaways by proving that the assumptions lead to contradiction
and using the ☢-elim
-}
-- absurd case: no (a ∷ as) of length 1
get {A} zero (a ∷ as) zero [𝕫<𝕤𝕫] = a
{-
 where
  ☢ : ⊥
-}  

-- absurd case: no (a ∷ as) of length 1
get {A} zero (a ∷ as) (suc x) [𝕤x<𝕤𝕫] = a

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



AD-id : (n : Nat) → (idx : Nat) → (idx < (suc n)) → NEVec Nat (suc n) → Nat → Set
AD-id n idx [idx<𝕤n] vec y = y ≡ get n vec idx [idx<𝕤n]

--need to formalize n-ary functions / (n+1)-ary relations
--f : NEVec A n → Nat → Set

