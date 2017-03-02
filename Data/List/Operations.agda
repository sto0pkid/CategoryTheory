module Data.List.Operations where

open import BaseLogic
open import Data.Bool
open import Data.Bool.Proofs
open import Data.False
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Operations
open import Data.Nat.BinPreds
open import Data.Nat.Properties
open import Data.Nat.Proofs
open import Data.Product
open import Data.PropositionalEquality

_++_ : ∀ {i} {A : Set i} → List A → List A → List A
[] ++ l₂ = l₂
(a ∷ as) ++ l₂ = a ∷ (as ++ l₂)

length : ∀ {i} {A : Set i} → List A → Nat
length {i} {A} [] = zero
length {i} {A} (a ∷ as) = suc (length as)

suc-inj : (x y : Nat) → (suc x) ≡ (suc y) → x ≡ y
suc-inj x y suc-x≡suc-y = [x≡y]→[fx≡fy] pred (suc x) (suc y) suc-x≡suc-y

|a∷as|≡|b∷bs|→|as|≡|bs| : ∀ {i j} {A : Set i} {B : Set j} → (a : A) → (as : List A) → (b : B) → (bs : List B) → (length (a ∷ as)) ≡ (length (b ∷ bs)) → (length as) ≡ (length bs)
|a∷as|≡|b∷bs|→|as|≡|bs| {i} {j} {A} {B} a as b bs |a∷as|≡|b∷bs| = |as|≡|bs|
 where
  |as|≡|bs| : (length as) ≡ (length bs)
  |as|≡|bs| = suc-inj (length as) (length bs) |a∷as|≡|b∷bs|

reverse : ∀ {i} {A : Set i} → List A → List A
reverse {i} {A} [] = []
reverse {i} {A} (a ∷ as) = (reverse as) ++ (a ∷ [])


_[_] : ∀ {i} {A : Set i} → List A → Nat → Maybe A
[] [ n ] = Nothing
(a ∷ as) [ zero ] = Just a
(a ∷ as) [ suc n ] = as [ n ]




map : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → List A → List B
map {i} {j} {A} {B} f [] = []
map {i} {j} {A} {B} f (a ∷ as) = (f a) ∷ (map f as)

flatten : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B → B) → B → List A → B
flatten {i} {j} {A} {B} f b [] = b
flatten {i} {j} {A} {B} f b (a ∷ as) = f a (flatten f b as)



zip' : ∀ {i j} {A : Set i} {B : Set j} → (l : List A) → (r : List B) → (length l) ≡ (length r) → List (A × B)
zip' {i} {j} {A} {B} [] [] 0≡0 = []
zip' {i} {j} {A} {B} (a ∷ as) [] |a∷as|≡0 = ω disproof
 where
  true≡false : true ≡ false
  true≡false = ≡-sym ([x≡y]→[fx≡fy] isZero (length (a ∷ as)) zero |a∷as|≡0)

  disproof : ⊥
  disproof = true≠false true≡false
zip' {i} {j} {A} {B} [] (b ∷ bs) 0≡|b∷bs| = ω disproof
 where
  disproof : ⊥
  disproof = true≠false ([x≡y]→[fx≡fy] isZero zero (length (b ∷ bs)) 0≡|b∷bs|)
zip' {i} {j} {A} {B} (a ∷ as) (b ∷ bs) |a∷as|≡|b∷bs| = (a , b) ∷ (zip' as bs |as|≡|bs|)
 where
  |as|≡|bs| : (length as) ≡ (length bs)
  |as|≡|bs| = |a∷as|≡|b∷bs|→|as|≡|bs| a as b bs |a∷as|≡|b∷bs|

zip'' : ∀ {i j} {A : Set i} {B : Set j} → (l : List A) → (r : List B) → (length l) ≡ (length r) → List ((Maybe A) × (Maybe B))
zip'' {i} {j} {A} {B} [] [] 0≡0 = []
zip'' {i} {j} {A} {B} (a ∷ as) [] |a∷as|≡0 = ω disproof
 where
  true≡false : true ≡ false
  true≡false = ≡-sym ([x≡y]→[fx≡fy] isZero (length (a ∷ as)) zero |a∷as|≡0)

  disproof : ⊥
  disproof = true≠false true≡false
zip'' {i} {j} {A} {B} [] (b ∷ bs) 0≡|b∷bs| = ω disproof
 where
  disproof : ⊥
  disproof = true≠false ([x≡y]→[fx≡fy] isZero zero (length (b ∷ bs)) 0≡|b∷bs|)
zip'' {i} {j} {A} {B} (a ∷ as) (b ∷ bs) |a∷as|≡|b∷bs| = (Just a , Just b) ∷ (zip'' as bs |as|≡|bs|)
 where
  |as|≡|bs| : (length as) ≡ (length bs)
  |as|≡|bs| = |a∷as|≡|b∷bs|→|as|≡|bs| a as b bs |a∷as|≡|b∷bs|
  

remove-first-N : ∀ {i} {A : Set i} → List A → (n : Nat) → List A
remove-first-N {i} {A} [] n = []
remove-first-N {i} {A} (a ∷ as) zero = (a ∷ as)
remove-first-N {i} {A} (a ∷ as) (suc n) = remove-first-N as n

{-
lemma : ∀ {i j} {A : Set i} {B : Set j} → (l : List A) → (r : List B) → ((first (diff₂ l r)) ≤ (length l)) ⊹ ((first (diff₂ l r)) ≤ (length r))
-}

{-
zip : ∀ {i j} {A : Set i} {B : Set j} → List A → List B → List ((Maybe A) × (Maybe B))
zip {i} {j} {A} {B} 
-}

zip₁' : ∀ {i j} {A : Set i} {B : Set j} → List A → List B → List ((Maybe A) × (Maybe B)) → List ((Maybe A) × (Maybe B))
zip₁' {i} {j} {A} {B} [] [] l = l
zip₁' {i} {j} {A} {B} [] (b ∷ bs) l = zip₁' [] bs ((Nothing , Just b) ∷ l)
zip₁' {i} {j} {A} {B} (a ∷ as) [] l = zip₁' as [] ((Just a , Nothing) ∷ l)
zip₁' {i} {j} {A} {B} (a ∷ as) (b ∷ bs) l = zip₁' as bs ((Just a , Just b) ∷ l)

zip₁ : ∀ {i j} {A : Set i} {B : Set j} → List A → List B → List ((Maybe A) × (Maybe B))
zip₁ {i} {j} {A} {B} l1 l2 = zip₁' (reverse l1) (reverse l2) []


op-rev : ∀ {i} {A : Set i} → A → List A → List A
op-rev a l = l ++ (a ∷ [])

op-len : ∀ {i} {A : Set i} → A → Nat → Nat
op-len {i} {A} a n = suc n

op-app : ∀ {i} {A : Set i} → A → List A → List A
op-app a l = a ∷ l




flat-reverse : ∀ {i} {A : Set i} → List A → List A
flat-reverse {i} {A} l = flatten op-rev [] l

flat-length : ∀ {i} {A : Set i} → List A → Nat
flat-length {i} {A} l = flatten op-len zero l

flat-append : ∀ {i} {A : Set i} → List A → List A → List A
flat-append {i} {A} l1 l2 = flatten op-app l2 l1


list-head : ∀ {i} {A : Set i} → List A → Maybe A
list-head {i} {A} [] = Nothing
list-head {i} {A} (a ∷ as) = Just a

list-tail : ∀ {i} {A : Set i} → List A → Maybe (List A)
list-tail {i} {A} [] = Nothing
list-tail {i} {A} (a ∷ as) = Just as

list-first : ∀ {i} {A : Set i} → List A → Maybe A
list-first = list-head

list-rest : ∀ {i} {A : Set i} → List A → Maybe (List A)
list-rest = list-tail

list-last : ∀ {i} {A : Set i} → List A → Maybe A
list-last {i} {A} [] = Nothing
list-last {i} {A} (a ∷ []) = Just a
list-last {i} {A} (a1 ∷ (a2 ∷ as)) = list-last (a2 ∷ as)

nelist-head : ∀ {i} {A : Set i} → (l : List A) → (length l) ≠ 0 → A
nelist-head {i} {A} [] [0≠0] = ω ([0≠0] refl)
nelist-head {i} {A} (Data.List._∷_ a as) [length[a∷as]≠0] = a

nelist-tail : ∀ {i} {A : Set i} → (l : List A) → (length l) ≠ 0 → List A
nelist-tail {i} {A} [] [0≠0] = ω ([0≠0] refl)
nelist-tail {i} {A} (Data.List._∷_ a as) [length[a∷as]≠0] = as

nelist-first : ∀ {i} {A : Set i} → (l : List A) → (length l) ≠ 0 → A
nelist-first = nelist-head

nelist-rest : ∀ {i} {A : Set i} → (l : List A) → (length l) ≠ 0 → List A
nelist-rest = nelist-tail

nelist-last : ∀ {i} {A : Set i} → (l : List A) → (length l) ≠ 0 → A
nelist-last {i} {A} [] [0≠0] = ω ([0≠0] refl)
nelist-last {i} {A} (a ∷ []) [1≠0] = a
nelist-last {i} {A} (a1 ∷ (a2 ∷ as)) [suc[suc|as|]≠0] = nelist-last (a2 ∷ as) [suc|as|≠0]
 where
  [suc|as|≠0] : suc (length as) ≠ 0
  [suc|as|≠0] = suc-x≠0 (length as)
