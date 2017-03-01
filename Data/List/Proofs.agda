module Data.List.Proofs where

open import BaseLogic
open import Data.List
open import Data.List.Operations
open import Data.Nat
open import Data.Nat.Operations
open import Data.PropositionalEquality

[a∷as]≡[a++as] : ∀ {i} {A : Set i} → (first : A) → (rest : List A) → ((first ∷ rest) ≡ (first ∷ []) ++ rest)
[a∷as]≡[a++as] {i} {A} first rest = refl

[a++as]≡[a∷as] : ∀ {i} {A : Set i} → (first : A) → (rest : List A) → ((first ∷ [] ++ rest) ≡ (first ∷ rest))
[a++as]≡[a∷as] {i} {A} first rest = refl

|[]++l|≡|l| : ∀ {i} {A : Set i} → (l : List A) → length ([] ++ l) ≡ length l
|[]++l|≡|l| {i} {A} l = refl

[a∷l1]++l2≡a∷[l1++l2] : ∀ {i} {A : Set i} → (a : A) → (l1 l2 : List A) → (a ∷ l1) ++ l2 ≡ (a ∷ (l1 ++ l2))
[a∷l1]++l2≡a∷[l1++l2] {i} {A} a l1 l2 = refl


|l1++l2|≡|l1|+|l2|-ind : ∀ {i} {A : Set i} → (l1 l2 : List A) → length (l1 ++ l2) ≡ (length l1) + (length l2) → (a : A) → length ((a ∷ l1) ++ l2) ≡ (length (a ∷ l1)) + (length l2)
|l1++l2|≡|l1|+|l2|-ind {i} {A} l1 l2 hyp a = proof
 where
  lem2 : (a ∷ l1) ++ l2 ≡ a ∷ (l1 ++ l2)
  lem2 = refl

  length[[a∷l1]++l2]≡length[a∷[l1++l2]] : length ((a ∷ l1) ++ l2) ≡ length ( a ∷ (l1 ++ l2))
  length[[a∷l1]++l2]≡length[a∷[l1++l2]] = [x≡y]→[fx≡fy] length ((a ∷ l1) ++ l2) (a ∷ (l1 ++ l2)) lem2

  length[a∷[l1++l2]]≡suc[length[l1++l2]] : length ( a ∷ (l1 ++ l2)) ≡ suc (length (l1 ++ l2))
  length[a∷[l1++l2]]≡suc[length[l1++l2]] = refl

  length[[a∷l1]++l2]≡suc[length[l1++l2]] : length ((a ∷ l1) ++ l2) ≡ suc ( length ( l1 ++ l2 ))
  length[[a∷l1]++l2]≡suc[length[l1++l2]] = ≡-trans length[[a∷l1]++l2]≡length[a∷[l1++l2]] length[a∷[l1++l2]]≡suc[length[l1++l2]]



  length[a∷l1]≡suc[length[l1]] : length (a ∷ l1) ≡ suc (length l1)
  length[a∷l1]≡suc[length[l1]] = refl

  suc[length[l1]]+length[l2]≡suc[length[l1]+length[l2]] : suc (length l1) + (length l2) ≡ suc ((length l1) + (length l2))
  suc[length[l1]]+length[l2]≡suc[length[l1]+length[l2]] = refl

  +length[l2] : Nat → Nat
  +length[l2] n = n + (length l2)

  length[a∷l1]+length[l2]≡suc[length[l1]]+length[l2] : (length (a ∷ l1)) + (length l2) ≡ (suc (length l1)) + (length l2)
  length[a∷l1]+length[l2]≡suc[length[l1]]+length[l2] = [x≡y]→[fx≡fy] +length[l2] (length (a ∷ l1)) (suc (length l1)) length[a∷l1]≡suc[length[l1]]

  length[a∷l1]+length[l2]≡suc[length[l1]+length[l2]] : length (a ∷ l1) + (length l2) ≡ suc ((length l1) + (length l2))
  length[a∷l1]+length[l2]≡suc[length[l1]+length[l2]] = ≡-trans length[a∷l1]+length[l2]≡suc[length[l1]]+length[l2] suc[length[l1]]+length[l2]≡suc[length[l1]+length[l2]]

  lem1 : suc ( length (l1 ++ l2)) ≡ suc ((length l1) + (length l2))
  lem1 = [x≡y]→[fx≡fy] suc (length (l1 ++ l2)) ((length l1) + (length l2)) hyp

  proof : length ((a ∷ l1) ++ l2) ≡ (length (a ∷ l1)) + (length l2)
  proof = ≡-trans (≡-trans length[[a∷l1]++l2]≡suc[length[l1++l2]] lem1) (≡-sym length[a∷l1]+length[l2]≡suc[length[l1]+length[l2]])

|l1++l2|≡|l1|+|l2| : ∀ {i} {A : Set i} → (l1 l2 : List A) → length (l1 ++ l2) ≡ (length l1) + (length l2)
|l1++l2|≡|l1|+|l2| {i} {A} [] l2 = refl
|l1++l2|≡|l1|+|l2| {i} {A} (a ∷ l1) l2 = |l1++l2|≡|l1|+|l2|-ind l1 l2 (|l1++l2|≡|l1|+|l2| l1 l2) a

