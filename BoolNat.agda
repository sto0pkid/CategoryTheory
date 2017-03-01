module BoolNat where

open import Data.Bool
open import Data.Bool.Operations
open import Data.Nat
open import Data.Nat.Operations
open import Data.List
open import Data.List.Operations
open import Data.Maybe
open import Data.Product
open import Data.PropositionalEquality


BinaryNat : Set
BinaryNat = List Bool

Bool2Nat : Bool → Nat
Bool2Nat false = zero
Bool2Nat true = suc zero

Binary2Unary-helper : BinaryNat → Maybe Nat → Maybe Nat
Binary2Unary-helper [] Nothing = Nothing
Binary2Unary-helper [] (Just acc) = Just acc
Binary2Unary-helper (a ∷ as) Nothing = Binary2Unary-helper as (Just (Bool2Nat a))
Binary2Unary-helper (a ∷ as) (Just acc) = Binary2Unary-helper as (Just (((2 ^ (length (a ∷ as))) * (Bool2Nat a)) + acc))

Binary2Unary : BinaryNat → Maybe Nat
Binary2Unary n = Binary2Unary-helper n Nothing

first-nonzero : BinaryNat → Maybe Nat
first-nonzero [] = Nothing
first-nonzero (false ∷ rest) = first-nonzero rest
first-nonzero (true ∷ rest) = Just (length (true ∷ rest))

last-digit : BinaryNat → Maybe Bool
last-digit [] = Nothing
last-digit (a ∷ []) = Just a
last-digit (a1 ∷ (a2 ∷ as)) = last-digit (a2 ∷ as)

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

pad-zeroes' : BinaryNat → Nat → BinaryNat
pad-zeroes' [] zero = []
pad-zeroes' [] (suc n) = (false ∷ (pad-zeroes' [] n))
pad-zeroes' (a ∷ as) zero = (a ∷ (pad-zeroes' as zero))
pad-zeroes' (a ∷ as) (suc n) = (a ∷ (pad-zeroes' as n))

pad-zeroes : BinaryNat → Nat → BinaryNat
pad-zeroes b n = pad-zeroes' (reverse b) n



{-
pad-zeroes-length-lemma : (l1 l2 : BinaryNat) → length (pad-zeroes' l1 (length l2)) ≡ length (pad-zeroes' l2 (length l1))
-}
