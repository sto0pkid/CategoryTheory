module BoolNat where

open import BaseLogic
open import Data.Bool
open import Data.Bool.Operations
open import Data.False
open import Data.Nat
import Data.Nat.Operations
open import Data.List
open import Data.List.Operations
open import Data.Maybe
open import Data.Product
open import Data.PropositionalEquality
open import Data.Vector
open import Data.Vector.Operations
open import Functions
open import ListVector


BinaryNat : Set
BinaryNat = List Bool

BitVector : (n : Nat) → Set
BitVector n = Vector Bool n 

Bool2Nat : Bool → Nat
Bool2Nat false = zero
Bool2Nat true = suc zero

Binary2Unary-helper : BinaryNat → Maybe Nat → Maybe Nat
Binary2Unary-helper [] Nothing = Nothing
Binary2Unary-helper [] (Just acc) = Just acc
Binary2Unary-helper (a ∷ as) Nothing = Binary2Unary-helper as (Just (Bool2Nat a))
Binary2Unary-helper (a ∷ as) (Just acc) = Binary2Unary-helper as (Just (Data.Nat.Operations._+_ (Data.Nat.Operations._*_ (Data.Nat.Operations._^_ 2 (length (a ∷ as))) (Bool2Nat a)) acc))

Binary2Unary : BinaryNat → Maybe Nat
Binary2Unary n = Binary2Unary-helper n Nothing

BitVector2Unary-helper : {n : Nat} → BitVector n → Maybe Nat → Maybe Nat
BitVector2Unary-helper {zero} [] Nothing = Nothing
BitVector2Unary-helper {zero} [] (Just acc) = Just acc
BitVector2Unary-helper {suc n} (a ∷ as) Nothing = BitVector2Unary-helper {n} as (Just (Bool2Nat a))
BitVector2Unary-helper {suc n} (a ∷ as) (Just acc) = BitVector2Unary-helper {n} as (Just (Data.Nat.Operations._+_ (Data.Nat.Operations._*_ (Data.Nat.Operations._^_ 2 (suc n)) (Bool2Nat a)) acc))

BitVector2Unary : {n : Nat} → BitVector n → Maybe Nat
BitVector2Unary v = BitVector2Unary-helper v Nothing

first-nonzero : BinaryNat → Maybe Nat
first-nonzero [] = Nothing
first-nonzero (false ∷ rest) = first-nonzero rest
first-nonzero (true ∷ rest) = Just (length (true ∷ rest))

first-digit : BinaryNat → Maybe Bool
first-digit [] = Nothing
first-digit (a ∷ as) = Just a

last-digit : BinaryNat → Maybe Bool
last-digit [] = Nothing
last-digit (a ∷ []) = Just a
last-digit (a1 ∷ (a2 ∷ as)) = last-digit (a2 ∷ as)

first-nonzero-vec : {n : Nat} → BitVector n → Maybe Nat
first-nonzero-vec {zero} [] = Nothing
first-nonzero-vec {suc n} (false ∷ rest) = first-nonzero-vec {n} rest
first-nonzero-vec {suc n} (true ∷ rest) = Just n

first-digit-vec : {n : Nat} → BitVector n → Maybe Bool
first-digit-vec [] = Nothing
first-digit-vec (a ∷ as) = Just a

first-digit-nevec : {n : Nat} → BitVector (suc n) → Bool
first-digit-nevec {zero} (a ∷ []) = a
first-digit-nevec {suc n} (a1 ∷ (a2 ∷ as)) = a1

last-digit-vec : {n : Nat} → BitVector n → Maybe Bool
last-digit-vec {zero} [] = Nothing
last-digit-vec {suc zero} (a ∷ []) = Just a
last-digit-vec {suc (suc n)} (a1 ∷ (a2 ∷ as)) = last-digit-vec (a2 ∷ as)

last-digit-nevec : {n : Nat} → BitVector (suc n) → Bool
last-digit-nevec {zero} (a ∷ []) = a
last-digit-nevec {suc n} (a1 ∷ (a2 ∷ as)) = last-digit-nevec {n} (a2 ∷ as)

nevec-head : ∀ {i} {A : Set i} {n : Nat} → Vector A (suc n) → A
nevec-head {i} {A} {zero} (a ∷ []) = a
nevec-head {i} {A} {suc n} (a1 ∷ (a2 ∷ as)) = a1

nevec-tail : ∀ {i} {A : Set i} {n : Nat} → Vector A (suc n) → Vector A n
nevec-tail {i} {A} {zero} (a ∷ []) = []
nevec-tail {i} {A} {suc n} (a1 ∷ (a2 ∷ as)) = (a2 ∷ as)

nelist-head : ∀ {i} {A : Set i} → (l : List A) → (length l) ≠ 0 → A
nelist-head {i} {A} [] [0≠0] = ω ([0≠0] refl)
nelist-head {i} {A} (a ∷ as) [length[a∷as]≠0] = a

nelist-tail : ∀ {i} {A : Set i} → (l : List A) → (length l) ≠ 0 → List A
nelist-tail {i} {A} [] [0≠0] = ω ([0≠0] refl)
nelist-tail {i} {A} (a ∷ as) [length[a∷as]≠0] = as


bit-add-direct : Bool → Bool → Bool
bit-add-direct false false = false
bit-add-direct false true = true
bit-add-direct true false = true
bit-add-direct true true = false

bit-add-direct' : Bool → Bool → Bool
bit-add-direct' b1 b2 = b1 xor b2

bit-add-carry : Bool → Bool → Bool
bit-add-carry false false = false
bit-add-carry false true = false
bit-add-carry true false = false
bit-add-carry true true = true

bit-add-carry' : Bool → Bool → Bool
bit-add-carry' b1 b2 = b1 and b2

bit-add-with-carry : Bool → Bool → Bool × Bool
bit-add-with-carry b1 b2 = (bit-add-direct b1 b2 , bit-add-carry b1 b2)

bit-add-half : Bool → Bool → Bool × Bool
bit-add-half b1 b2 = (bit-add-direct b1 b2 , bit-add-carry b1 b2)

bit-add-half' : Bool → Bool → Bool × Bool
bit-add-half' b1 b2 = ((b1 xor b2) , (b1 and b2))

bit-add-full : Bool → Bool → Bool → Bool × Bool
bit-add-full b1 b2 c = (o1 , o2)
 where
  t1 : Bool
  t1 = bit-add-direct b1 b2

  c1 : Bool
  c1 = bit-add-carry b1 b2

  o1 : Bool
  o1 = bit-add-direct t1 c

  c2 : Bool
  c2 = bit-add-carry t1 c

  o2 : Bool
  o2 = bit-add-direct c1 c2

bit-add-full' : Bool → Bool → Bool → Bool × Bool
bit-add-full' b1 b2 c = (o1 , o2)
 where
  t1 = b1 xor b2
  c1 = b1 and b2
  o1 = t1 xor c
  c2 = t1 and c
  o2 = c1 xor c2

{-
bit-adder-adj : BinaryNat → BinaryNat → BinaryNat → BinaryNat → Maybe BinaryNat
bit-adder-adj [] l-acc r r-acc 

bit-adder : BinaryNat → BinaryNat → Maybe BinaryNat
bit-adder [] n = Nothing
bit-adder n [] = Nothing
bit-adder (b ∷ bs) (c ∷ cs) = 
-}

{-
bit-adder-part : BinaryNat → BinaryNat → List (Bool × Bool)
bit-adder-part l1 l2 = 
-}


bitvector-adder-part1 : {n : Nat} → BitVector n → BitVector n → Vector (Bool × Bool) n
bitvector-adder-part1 {n} v1 v2 = Data.Vector.Operations.map (uncurry bit-add-half) (zip v1 v2)

maybe-suc : Nat → Nat
maybe-suc 0 = 0
maybe-suc (suc n) = (suc (suc n))

{-
bitvector-adder-part2 : {n : Nat} → Vector (Bool × Bool) n → BitVector (maybe-suc n)
bitvector-adder-part2 {n} v 
-}

pad-zeroes' : BinaryNat → Nat → BinaryNat
pad-zeroes' [] zero = []
pad-zeroes' [] (suc n) = (false ∷ (pad-zeroes' [] n))
pad-zeroes' (a ∷ as) zero = (a ∷ (pad-zeroes' as zero))
pad-zeroes' (a ∷ as) (suc n) = (a ∷ (pad-zeroes' as n))

pad-zeroes : BinaryNat → Nat → BinaryNat
pad-zeroes b n = pad-zeroes' (reverse b) n

strip-leading-zeroes : BinaryNat → BinaryNat
strip-leading-zeroes [] = []
strip-leading-zeroes (false ∷ rest) = strip-leading-zeroes rest
strip-leading-zeroes (true ∷ rest) = (true ∷ rest)

strip-leading-zeroes-vec : {n : Nat} → (v : BitVector n) → BitVector (length (strip-leading-zeroes (vector2list v)))
strip-leading-zeroes-vec {n} v = list2vector (strip-leading-zeroes (vector2list v))


bitvector-adder' : {n : Nat} → BitVector n → BitVector n → BitVector (maybe-suc n)
bitvector-adder' {zero} [] [] = []
bitvector-adder' {suc zero} (a ∷ []) (b ∷ []) = (second (bit-add-full a b false)) ∷ ((first (bit-add-full a b false)) ∷ [])
bitvector-adder' {suc (suc n)} (a1 ∷ (a2 ∷ as)) (b1 ∷ (b2 ∷ bs)) = 
  (second (bit-add-full a1 b1 (nevec-head (bitvector-adder' {suc n} (a2 ∷ as) (b2 ∷ bs))))) ∷ 
  ((first (bit-add-full a1 b1 (nevec-head (bitvector-adder' {suc n} (a2 ∷ as) (b2 ∷ bs))))) ∷ 
  (nevec-tail (bitvector-adder' {suc n} (a2 ∷ as) (b2 ∷ bs))))

{-
Now need to prove the correctness of this bit-adder.
-}

bitvector-adder : {n : Nat} → (v1 : BitVector n) → (v2 : BitVector n) → BitVector (length (strip-leading-zeroes (vector2list (bitvector-adder' v1 v2))))
bitvector-adder {n} v1 v2 = strip-leading-zeroes-vec (bitvector-adder' v1 v2)


{-
pad-zeroes-length-lemma : (l1 l2 : BinaryNat) → length (pad-zeroes' l1 (length l2)) ≡ length (pad-zeroes' l2 (length l1))
-}
