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
open import Data.Product
open import Data.Maybe

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

vec-head : ∀ {i} {A : Set i} {n : Nat} → Vector A n → Maybe A
vec-head {i} {A} {zero} [] = Nothing
vec-head {i} {A} {suc n} (a ∷ as) = Just a

vec-tail : ∀ {i} {A : Set i} {n : Nat} → Vector A n → Maybe (Vector A (Data.Nat.Operations.pred n))
vec-tail {i} {A} {zero} [] = Nothing
vec-tail {i} {A} {suc n} (a ∷ as) = Just as

vec-first : ∀ {i} {A : Set i} {n : Nat} → Vector A n → Maybe A
vec-first = vec-head

vec-rest : ∀ {i} {A : Set i} {n : Nat} → Vector A n → Maybe (Vector A (Data.Nat.Operations.pred n))
vec-rest = vec-tail

vec-last : ∀ {i} {A : Set i} {n : Nat} → Vector A n → Maybe A
vec-last {i} {A} {zero} [] = Nothing
vec-last {i} {A} {suc zero} (a ∷ []) = Just a
vec-last {i} {A} {suc (suc n)} (a1 ∷ (a2 ∷ as)) = vec-last (a2 ∷ as)

nevec-head : ∀ {i} {A : Set i} {n : Nat} → Vector A (suc n) → A
nevec-head {i} {A} {zero} (a ∷ []) = a
nevec-head {i} {A} {suc n} (a1 ∷ (a2 ∷ as)) = a1

nevec-tail : ∀ {i} {A : Set i} {n : Nat} → Vector A (suc n) → Vector A n
nevec-tail {i} {A} {zero} (a ∷ []) = []
nevec-tail {i} {A} {suc n} (a1 ∷ (a2 ∷ as)) = (a2 ∷ as)

nevec-first : ∀ {i} {A : Set i} {n : Nat} → Vector A (suc n) → A
nevec-first = nevec-head

nevec-rest : ∀ {i} {A : Set i} {n : Nat} → Vector A (suc n) →  Vector A n
nevec-rest = nevec-tail

nevec-last : ∀ {i} {A : Set i} {n : Nat} → Vector A (suc n) → A
nevec-last {i} {A} {zero} (a ∷ []) = a
nevec-last {i} {A} {suc n} (a1 ∷ (a2 ∷ as)) = nevec-last (a2 ∷ as)


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



map : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → {n : Nat} → Vector A n → Vector B n
map {i} {j} {A} {B} f {zero} [] = []
map {i} {j} {A} {B} f {suc n} (a ∷ as) = (f a) ∷ (map f as)
 
flatten : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B → B) → B → {n : Nat} → Vector A n → B
flatten {i} {j} {A} {B} f b {zero} [] = b
flatten {i} {j} {A} {B} f b {suc n} (a ∷ as) = f a (flatten f b as)

zip : ∀ {i j} {A : Set i} {B : Set j} → {n : Nat} → Vector A n → Vector B n → Vector (A × B) n
zip {i} {j} {A} {B} {zero} [] [] = []
zip {i} {j} {A} {B} {suc n} (a ∷ as) (b ∷ bs) = (a , b) ∷ (zip as bs)

reverse : ∀ {i} {A : Set i} {n : Nat} → Vector A n → Vector A n
reverse {i} {A} {zero} [] = []
reverse {i} {A} {suc n} (a ∷ as) = Vector-coerce-length ((reverse as) ++ (a ∷ [])) (x+1≡suc-x n)

rotate : ∀ {i} {A : Set i} {n : Nat} → Vector A n → Nat → Vector A n
rotate {i} {A} {zero} [] m = []
rotate {i} {A} {suc n} (a ∷ as) zero = (a ∷ as)
rotate {i} {A} {suc n} (a ∷ as) (suc m) = Vector-coerce-length (rotate (as ++ (a ∷ [])) m) (x+1≡suc-x n)

dropl : ∀ {i} {A : Set i} {n : Nat} → Vector A n → (m : Nat) → Vector A (Data.Nat.Operations._minus_ n m)
dropl {i} {A} {zero} [] m = []
dropl {i} {A} {suc n} (a ∷ as) zero = (a ∷ as)
dropl {i} {A} {suc n} (a ∷ as) (suc m) = dropl as m

dropr : ∀ {i} {A : Set i} {n : Nat} → Vector A n → (m : Nat) → Vector A (Data.Nat.Operations._minus_ n m)
dropr {i} {A} {n} v m = reverse (dropl v m)

shiftr : ∀ {i} {A : Set i} {n : Nat} → A → Vector A n → Nat → Vector A n
shiftr {i} {A} {zero} a [] m = []
shiftr {i} {A} {suc n} a (b ∷ bs) zero = (b ∷ bs)
shiftr {i} {A} {suc n} a (b ∷ bs) (suc m) = Vector-coerce-length (a ∷ (shiftr a (dropr (b ∷ bs) 1) m))[suc[suc[n]-1]≡suc[n]]
 where
  [suc[n]-1≡n] : Data.Nat.Operations._minus_ (suc n) 1 ≡ n
  [suc[n]-1≡n] = suc-x-minus-1≡x n

  [suc[suc[n]-1]≡suc[n]] : suc (Data.Nat.Operations._minus_ (suc n) 1) ≡ suc n
  [suc[suc[n]-1]≡suc[n]] = [x≡y]→[fx≡fy] suc (Data.Nat.Operations._minus_ (suc n) 1) n [suc[n]-1≡n]

shiftl : ∀ {i} {A : Set i} {n : Nat} → A → Vector A n → Nat → Vector A n
shiftl {i} {A} {zero} a [] m = []
shiftl {i} {A} {suc n} a (b ∷ bs) zero = (b ∷ bs)
shiftl {i} {A} {suc n} a (b ∷ bs) (suc m) = Vector-coerce-length (shiftl a (bs ++ (a ∷ [])) m) (x+1≡suc-x n)
