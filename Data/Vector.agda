module Data.Vector where

open import Agda.Primitive
open import BaseLogic
open import Data.Nat
open import Data.Nat.Operations
open import Data.Nat.Relations
open import Data.Nat.Proofs
open import Data.Fin

data Vector {α} (A : Set α) : Nat → Set α where
 []  : Vector A 0
 _∷_ : {n : Nat} → A → Vector A n → Vector A (suc n) 

_^_ : ∀ {α} (A : Set α) (n : Nat) → Set α
A ^ n = Vector A n

Vector-first : ∀ {α} {A : Set α} {n : Nat} → Vector A (suc n) → A
Vector-first {α} {A} {n} (a ∷ as) = a

Vector-rest : ∀ {α} {A : Set α} {n : Nat} → Vector A (suc n) → Vector A n
Vector-rest {α} {A} {n} (a ∷ as) = as

Vector-coerce-length : ∀ {α} {A : Set α} {m n : Nat} → Vector A m → m ≡ n → Vector A n
Vector-coerce-length {α} {A} {m} {.m} vec (refl .m) = vec

Vector-coerce-type : ∀ {α} {A B : Set α} {n : Nat} → Vector A n → A ≡ B → Vector B n
Vector-coerce-type {α} {A} {.A} vec (refl .A) = vec


_++_ : ∀ {α} {A : Set α} {n m : Nat} → Vector A n → Vector A m → Vector A (n + m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)


_[_] : ∀ {α} {A : Set α} {n : Nat} → Vector A (suc n) → Fin n → A
(a ∷ as) [ zero ] =  a
(a ∷ as) [ suc n ] = as [ n ]
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

--vec[i]=val : vector x at index y has value val
data _[_]=_ {α} {A : Set α} : {n : Nat} → Vector A n → Fin n → A → Set α where
 here : ∀ {n : Nat} {x : A} {xs : Vector A n} → (x ∷ xs) [ zero ]= x
 there : ∀ {n : Nat} {i : Fin n} {x y : A} {xs : Vector A n} (xs[i]=x : xs [ i ]= x) → (y ∷ xs) [ suc i ]= x

