module Data.Vector.Operations where

open import BaseLogic
open import Data.Nat
import Data.Nat.Operations
open import Data.Nat.Relations
open import Data.Nat.Proofs
open import Data.Vector
open import Data.Fin
open import Data.False
open import Data.PropositionalEquality

_^_ : ∀ {α} (A : Set α) (n : Nat) → Set α
A ^ n = Vector A n

Vector-first : ∀ {α} {A : Set α} {n : Nat} → Vector A (suc n) → A
Vector-first {α} {A} {n} (a ∷ as) = a

head : ∀ {α} {A : Set α} {n : Nat} → Vector A (suc n) → A
head = Vector-first

Vector-rest : ∀ {α} {A : Set α} {n : Nat} → Vector A (suc n) → Vector A n
Vector-rest {α} {A} {n} (a ∷ as) = as

tail : ∀ {α} {A : Set α} {n : Nat} → Vector A (suc n) → Vector A n
tail = Vector-rest

Vector-coerce-length : ∀ {α} {A : Set α} {m n : Nat} → Vector A m → m ≡ n → Vector A n
Vector-coerce-length {α} {A} {m} {.m} vec refl = vec

Vector-coerce-type : ∀ {α} {A B : Set α} {n : Nat} → Vector A n → A ≡ B → Vector B n
Vector-coerce-type {α} {A} {.A} vec refl = vec


_++_ : ∀ {α} {A : Set α} {n m : Nat} → Vector A n → Vector A m → Vector A (Data.Nat.Operations._+_ n m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

<_> : ∀ {α} {A : Set α} → A → Vector A 1
< x > = (x ∷ [])

_[_] : ∀ {α} {A : Set α} {n : Nat} → Vector A (suc n) → Fin n → A
(a ∷ as) [ zero ] =  a
(a ∷ as) [ suc n ] = as [ n ]

_[_]' : ∀ {α} {A : Set α} {n : Nat} → Vector A n → Fin n → A
(a ∷ as) [ zero ]' = a
(a ∷ as) [ suc n ]' = as [ n ]'

lookup : ∀ {α n} {A : Set α} → Fin n → Vector A n → A
lookup zero (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs

{-
Note that computationally this is not ideal. In C++ for example, arrays
are strings of bitvectors of a particular length <size>. If we want to
access the element at index i, we use the pointer <array-base> + i*<size>.

We will use these more efficient things, but at another level of abstraction.
-}

data NEVec (A : Set) : Nat → Set where
 end : A → NEVec A (suc zero)
 _∷_ : {n : Nat} → A → NEVec A n → NEVec A (suc n)


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

-- x [ i ]:= y ...
-- replace the value at index i in vector x with the value y
_[_]:=_ : ∀ {α} {A : Set α} {n : Nat} → Vector A (suc n) → Fin n → A → Vector A (suc n)
(x ∷ xs) [ zero ]:= y = y ∷ xs
(x ∷ xs) [ suc i ]:= y = x ∷ (xs [ i ]:= y)
