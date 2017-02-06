module Data.Bool.Relations where

open import Agda.Primitive
open import BaseLogic
open import Data.Bool
open import Data.Nat
open import Data.Vector
open import Relations

-- Equality of bits

BitEq : Bool → Bool → Bool
BitEq true true = true
BitEq true false = false
BitEq false true = false
BitEq false false = true



--BitEq is reflexive; the hard way
BitEq-isRefl : isReflexive BitEq
BitEq-isRefl true = refl true
BitEq-isRefl false = refl true

--BitEq is symmetric; the hard way
BitEq-isSym : isSymmetric BitEq
BitEq-isSym true true [𝕥≡𝕥]≡𝕥 = refl true
BitEq-isSym true false [𝕥≡𝕗]≡𝕥 = ω ☢
 where
  [𝕥≡𝕗]≡𝕗 : BitEq true false ≡ false
  [𝕥≡𝕗]≡𝕗 = refl false

  [𝕥≡𝕗] : true ≡ false
  [𝕥≡𝕗] = ≡-⇶ (≡-↑↓ [𝕥≡𝕗]≡𝕥) [𝕥≡𝕗]≡𝕗
 
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]
BitEq-isSym false true [𝕗≡𝕥]≡𝕥 = ω ☢
 where
  [𝕗≡𝕥]≡𝕗 : BitEq true false ≡ false
  [𝕗≡𝕥]≡𝕗 = refl false

  [𝕥≡𝕗] : true ≡ false
  [𝕥≡𝕗] = ≡-⇶ (≡-↑↓ [𝕗≡𝕥]≡𝕥) [𝕗≡𝕥]≡𝕗
 
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]
BitEq-isSym false false [𝕗≡𝕗]≡𝕥 = refl true


--BitEq is transitive; the hard way
BitEq-isTrans : isTransitive BitEq
BitEq-isTrans true true true prf₁ prf₂ = refl true
BitEq-isTrans true true false [𝕥≡𝕥]≡𝕥 [𝕥≡𝕗]≡𝕥 = ω ☢
 where
  [𝕥≡𝕗]≡𝕗 : BitEq true false ≡ false
  [𝕥≡𝕗]≡𝕗 = refl false

  [𝕥≡𝕗] : true ≡ false
  [𝕥≡𝕗] = ≡-⇶ (≡-↑↓ [𝕥≡𝕗]≡𝕥) [𝕥≡𝕗]≡𝕗

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]
BitEq-isTrans true false b [𝕥≡𝕗]≡𝕥 [𝕗≡b]≡𝕥 = ω ☢
 where
  [𝕥≡𝕗]≡𝕗 : BitEq true false ≡ false
  [𝕥≡𝕗]≡𝕗 = refl false

  [𝕥≡𝕗] : true ≡ false
  [𝕥≡𝕗] = ≡-⇶ (≡-↑↓ [𝕥≡𝕗]≡𝕥) [𝕥≡𝕗]≡𝕗

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]
BitEq-isTrans false true b [𝕗≡𝕥]≡𝕥 [𝕥≡b]≡𝕥 = ω ☢
 where
  [𝕗≡𝕥]≡𝕗 : BitEq false true ≡ false
  [𝕗≡𝕥]≡𝕗 = refl false

  [𝕥≡𝕗] : true ≡ false
  [𝕥≡𝕗] = ≡-⇶ (≡-↑↓ [𝕗≡𝕥]≡𝕥) [𝕗≡𝕥]≡𝕗

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]
BitEq-isTrans false false true [𝕗≡𝕗]≡𝕥 [𝕗≡𝕥]≡𝕥 = ω ☢
 where
  [𝕗≡𝕥]≡𝕗 : BitEq false true ≡ false
  [𝕗≡𝕥]≡𝕗 = refl false

  [𝕥≡𝕗] : true ≡ false
  [𝕥≡𝕗] = ≡-⇶ (≡-↑↓ [𝕗≡𝕥]≡𝕥) [𝕗≡𝕥]≡𝕗
 
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]   
BitEq-isTrans false false false prf₁ prf₂ = refl true


BitEq-isEquiv₁ : isEquivalenceRelation BitEq
BitEq-isEquiv₁ = (BitEq-isRefl , (BitEq-isSym , BitEq-isTrans))

{-
 Here is proof that BitEq is the decider for propositional equality of Bits
-}

-- BitEq x y → x ≡ y
BitEq-a-b→a≡b : (x y : Bit) → BitEq x y ≡ true → x ≡ y
BitEq-a-b→a≡b true true BitEq-𝕗𝕗 = refl true
BitEq-a-b→a≡b true false BitEq-𝕥𝕗 = ω ☢
 where
  ¬BitEq-𝕥𝕗 : BitEq true false ≡ false
  ¬BitEq-𝕥𝕗 = refl false

  𝕥≡𝕗 : true ≡ false 
  𝕥≡𝕗 = ≡-⇶ (≡-↑↓ BitEq-𝕥𝕗) ¬BitEq-𝕥𝕗

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 𝕥≡𝕗
BitEq-a-b→a≡b false true BitEq-𝕗𝕥 = ω ☢
 where
  ¬BitEq-𝕗𝕥 : BitEq false true ≡ false
  ¬BitEq-𝕗𝕥 = refl false

  𝕥≡𝕗 : true ≡ false 
  𝕥≡𝕗 = ≡-⇶ (≡-↑↓ BitEq-𝕗𝕥) ¬BitEq-𝕗𝕥

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 𝕥≡𝕗
BitEq-a-b→a≡b false false BitEq-𝕗𝕗 = refl false


-- x ≡ y → BitEq x y
a≡b→BitEq-a-b : (x y : Bit) → x ≡ y → BitEq x y ≡ true
a≡b→BitEq-a-b true true [𝕥≡𝕥] = refl true
a≡b→BitEq-a-b true false [𝕥≡𝕗] = ω (𝕥≠𝕗 [𝕥≡𝕗])
a≡b→BitEq-a-b false true [𝕗≡𝕥] = ω (𝕥≠𝕗 (≡-↑↓ [𝕗≡𝕥]))
a≡b→BitEq-a-b false false [𝕗≡𝕗] = refl true

{-
Thus, BitEq decides propositional equality for Bits
-}

BitEq-isEqDec : isEqDec BitEq
BitEq-isEqDec x y = (BitEq-a-b→a≡b x y , a≡b→BitEq-a-b x y)

BitEq-isEquiv₂ : isEquivalenceRelation BitEq
BitEq-isEquiv₂ = isEqDec-R→isEquiv-R BitEq BitEq-isEqDec




-- Equality of bit vectors

BitVectorEq : {n : Nat} → Bit ^ n → Bit ^ n → Bool
BitVectorEq {zero} [] [] = true
BitVectorEq {suc n} (a ∷ as) (b ∷ bs) = 
 if (BitEq a b) then 
  BitVectorEq {n} as bs 
 else 
  false



{-
We can generalize these proofs about bit vectors to proofs about a general
vector equality decision function given the equality decision function for its
elements.
-}

--If two bit vectors are equal by BitVectorEq, then their tails are equal by BitVectorEq
[a∷as≡b∷bs]→[as≡bs] : {n : Nat} → {as bs : Vector Bit (suc n)} → BitVectorEq as bs ≡ true → BitVectorEq (Vector-rest as) (Vector-rest bs) ≡ true
[a∷as≡b∷bs]→[as≡bs] {n} {true ∷ as} {true ∷ bs} [𝕥∷as≡𝕥∷bs]≡𝕥 = [as≡bs]≡𝕥
 where
  [𝕥∷as≡𝕥∷bs]≡[as≡bs] : BitVectorEq (true ∷ as) (true ∷ bs) ≡ BitVectorEq as bs
  [𝕥∷as≡𝕥∷bs]≡[as≡bs] = refl (BitVectorEq as bs)

  [as≡bs]≡𝕥 : BitVectorEq as bs ≡ true
  [as≡bs]≡𝕥 = ≡-⇶ (≡-↑↓ [𝕥∷as≡𝕥∷bs]≡[as≡bs]) [𝕥∷as≡𝕥∷bs]≡𝕥
[a∷as≡b∷bs]→[as≡bs] {n} {true ∷ as} {false ∷ bs} [𝕥∷as≡𝕗∷bs]≡𝕥 = ω ☢
 where
  [𝕥∷as≡𝕗∷bs]≡𝕗 : BitVectorEq (true ∷ as) (false ∷ bs) ≡ false
  [𝕥∷as≡𝕗∷bs]≡𝕗 = refl false

  [𝕥≡𝕗] : true ≡ false
  [𝕥≡𝕗] = ≡-⇶ (≡-↑↓ [𝕥∷as≡𝕗∷bs]≡𝕥) [𝕥∷as≡𝕗∷bs]≡𝕗

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]
[a∷as≡b∷bs]→[as≡bs] {n} {false ∷ as} {true ∷ bs} [𝕗∷as≡𝕥∷bs]≡𝕥 = ω ☢
 where
  [𝕗∷as≡𝕥∷bs]≡𝕗 : BitVectorEq (false ∷ as) (true ∷ bs) ≡ false
  [𝕗∷as≡𝕥∷bs]≡𝕗 = refl false

  [𝕥≡𝕗] : true ≡ false
  [𝕥≡𝕗] = ≡-⇶ (≡-↑↓ [𝕗∷as≡𝕥∷bs]≡𝕥) [𝕗∷as≡𝕥∷bs]≡𝕗

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]
[a∷as≡b∷bs]→[as≡bs] {n} {false ∷ as} {false ∷ bs} [𝕗∷as≡𝕗∷bs]≡𝕥 = [as≡bs]≡𝕥
 where
  [𝕗∷as≡𝕗∷bs]≡[as≡bs] : BitVectorEq (false ∷ as) (false ∷ bs) ≡ BitVectorEq as bs 
  [𝕗∷as≡𝕗∷bs]≡[as≡bs] = refl (BitVectorEq as bs)

  [as≡bs]≡𝕥 : BitVectorEq as bs ≡ true
  [as≡bs]≡𝕥 = ≡-⇶ (≡-↑↓ [𝕗∷as≡𝕗∷bs]≡[as≡bs]) [𝕗∷as≡𝕗∷bs]≡𝕥


-- If two bit vectors are equal by BitVectorEq, then their first elements are equal by BitEq
[a∷as≡b∷bs]→[BitEq-a-b] : {n : Nat} → {as bs : Vector Bit (suc n)} → BitVectorEq as bs ≡ true → BitEq (Vector-first as) (Vector-first bs) ≡ true
[a∷as≡b∷bs]→[BitEq-a-b] {n} {true ∷ as} {true ∷ bs} [𝕥∷as≡𝕥∷bs]≡𝕥 = refl true
[a∷as≡b∷bs]→[BitEq-a-b] {n} {true ∷ as} {false ∷ bs} [𝕥∷as≡𝕗∷bs]≡𝕥 = ω ☢
 where
  [𝕥∷as≡𝕗∷bs]≡𝕗 : BitVectorEq (true ∷ as) (false ∷ bs) ≡ false
  [𝕥∷as≡𝕗∷bs]≡𝕗 = refl false

  [𝕥≡𝕗] : true ≡ false
  [𝕥≡𝕗] = ≡-⇶ (≡-↑↓ [𝕥∷as≡𝕗∷bs]≡𝕥) [𝕥∷as≡𝕗∷bs]≡𝕗

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]
[a∷as≡b∷bs]→[BitEq-a-b] {n} {false ∷ as} {true ∷ bs} [𝕗∷as≡𝕥∷bs]≡𝕥 = ω ☢
 where
  [𝕗∷as≡𝕥∷bs]≡𝕗 : BitVectorEq (true ∷ as) (false ∷ bs) ≡ false
  [𝕗∷as≡𝕥∷bs]≡𝕗 = refl false

  [𝕥≡𝕗] : true ≡ false
  [𝕥≡𝕗] = ≡-⇶ (≡-↑↓ [𝕗∷as≡𝕥∷bs]≡𝕥) [𝕗∷as≡𝕥∷bs]≡𝕗

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]
[a∷as≡b∷bs]→[BitEq-a-b] {n} {false ∷ as} {false ∷ bs} [𝕗∷as≡𝕗∷bs]≡𝕥 = refl true



-- If two bitvectors x and y are equal by BitVectorEq, then for any bit b, the vectors
-- (b ∷ x) and (b ∷ y) are also equal by BitVectorEq
BitVectorEq-+1 : {n : Nat} → {as bs : Vector Bit n} → {v : Bool} → BitVectorEq as bs ≡ v → (b : Bit) → BitVectorEq (b ∷ as) (b ∷ bs) ≡ v
BitVectorEq-+1 {n} {as} {bs} [as≡bs]≡v true = [[𝕥∷as]≡[𝕥∷bs]]≡v
 where
  [[𝕥∷as]≡[𝕥∷bs]]≡[as≡bs] : BitVectorEq (true ∷ as) (true ∷ bs) ≡ BitVectorEq as bs
  [[𝕥∷as]≡[𝕥∷bs]]≡[as≡bs] = refl (BitVectorEq as bs)

  [[𝕥∷as]≡[𝕥∷bs]]≡v = ≡-⇶ [[𝕥∷as]≡[𝕥∷bs]]≡[as≡bs] [as≡bs]≡v
{-
-- wtf, why did Agda accept this
BitVectorEq-+1 {n} {as} {bs} [as≡bs]≡v false = [[𝕗∷as]≡[𝕗∷bs]]≡v
 where
  [[𝕗∷as]≡[𝕗∷bs]]≡[as≡bs] : BitVectorEq (true ∷ as) (true ∷ bs) ≡ BitVectorEq as bs
  [[𝕗∷as]≡[𝕗∷bs]]≡[as≡bs] = refl (BitVectorEq as bs)

  [[𝕗∷as]≡[𝕗∷bs]]≡v = ≡-⇶ [[𝕗∷as]≡[𝕗∷bs]]≡[as≡bs] [as≡bs]≡v
-}
BitVectorEq-+1 {n} {as} {bs} [as≡bs]≡v false = [[𝕗∷as]≡[𝕗∷bs]]≡v
 where
  [[𝕗∷as]≡[𝕗∷bs]]≡[as≡bs] : BitVectorEq (false ∷ as) (false ∷ bs) ≡ BitVectorEq as bs
  [[𝕗∷as]≡[𝕗∷bs]]≡[as≡bs] = refl (BitVectorEq as bs)

  [[𝕗∷as]≡[𝕗∷bs]]≡v = ≡-⇶ [[𝕗∷as]≡[𝕗∷bs]]≡[as≡bs] [as≡bs]≡v










-- BitVectorEq is reflexive ; the hard way

BitVectorEq-isRefl-ind : {n : Nat} → isReflexive (BitVectorEq {n}) → isReflexive (BitVectorEq {suc n})
BitVectorEq-isRefl-ind {n} isRefl-n (true ∷ as) = [rxx≡true]
 where
  BitVectorEq-[𝕥∷as][𝕥∷as]≡BitVectorEq-[as][as] : BitVectorEq (true ∷ as) (true ∷ as) ≡ BitVectorEq as as
  BitVectorEq-[𝕥∷as][𝕥∷as]≡BitVectorEq-[as][as] = refl (BitVectorEq as as)

  BitVectorEq-[as][as]≡true : BitVectorEq as as ≡ true
  BitVectorEq-[as][as]≡true = isRefl-n as

  [rxx≡true] : BitVectorEq (true ∷ as) (true ∷ as) ≡ true
  [rxx≡true] = ≡-⇶ BitVectorEq-[𝕥∷as][𝕥∷as]≡BitVectorEq-[as][as] BitVectorEq-[as][as]≡true
BitVectorEq-isRefl-ind {n} isRefl-n (false ∷ as) = [rxx≡true]
 where
  BitVectorEq-[𝕗∷as][𝕗∷as]≡BitVectorEq-[as][as] : BitVectorEq (false ∷ as) (false ∷ as) ≡ BitVectorEq as as
  BitVectorEq-[𝕗∷as][𝕗∷as]≡BitVectorEq-[as][as] = refl (BitVectorEq as as)

  BitVectorEq-[as][as]≡true : BitVectorEq as as ≡ true
  BitVectorEq-[as][as]≡true = isRefl-n as

  [rxx≡true] : BitVectorEq (false ∷ as) (false ∷ as) ≡ true
  [rxx≡true] = ≡-⇶ BitVectorEq-[𝕗∷as][𝕗∷as]≡BitVectorEq-[as][as] BitVectorEq-[as][as]≡true


BitVectorEq-isRefl : (n : Nat) → isReflexive (BitVectorEq {n})
BitVectorEq-isRefl zero [] = refl true
BitVectorEq-isRefl (suc n) = BitVectorEq-isRefl-ind (BitVectorEq-isRefl n)

{-
BitVectorEq-a-b→∀i-BitEq-a[i]-b[i] : {n : Nat} → {a b : Vector Bit n} → BitVectorEq a b → ((i : Fin n) → a [ i ] ≡ b [ i ]
-}

{-


isReflexive : ∀ {i} {A : Set i} (r : A → A → Bool) → Set i
isReflexive {i} {A} r = (x : A) → (r x x ≡ true)

isSymmetric : ∀ {i} {A : Set i} (r : A → A → Bool) → Set i
isSymmetric {i} {A} r = (x y : A) → (r x y ≡ true) → (r y x ≡ true)

isSymmetric' : ∀ {i} {A : Set i} (r : A → A → Bool) → Set i
isSymmetric' {i} {A} r = (x y : A) (z : Bool) → (r x y ≡ z) → (r y x ≡ z)

isTransitive : ∀ {i} {A : Set i} (r : A → A → Bool) → Set i
isTransitive {i} {A} r = (x y z : A) → (r x y ≡ true) → (r y z ≡ true) → (r x z ≡ true)

isEquivalenceRelation : ∀ {i} {A : Set i} (r : A → A → Bool) → Set i
isEquivalenceRelation {i} {A} r = (isReflexive r) ∧ ((isSymmetric r) ∧ (isTransitive r))
-}


--These proofs are very simple, they're just very wordy




BitVectorEq-isSym-ind : {n : Nat} → isSymmetric (BitVectorEq {n}) → isSymmetric (BitVectorEq {suc n})
BitVectorEq-isSym-ind {n} isSym-n (true ∷ as) (true ∷ bs) [𝕥∷αs≡𝕥∷bs]≡𝕥 = [𝕥∷bs≡𝕥∷as]≡𝕥
 where
  [𝕥∷as≡𝕥∷bs]≡[as≡bs] : BitVectorEq (true ∷ as) (true ∷ bs) ≡ BitVectorEq as bs
  [𝕥∷as≡𝕥∷bs]≡[as≡bs] = refl (BitVectorEq as bs)
  
  [𝕥∷bs≡𝕥∷as]≡[bs≡as] : BitVectorEq (true ∷ bs) (true ∷ as) ≡ BitVectorEq bs as
  [𝕥∷bs≡𝕥∷as]≡[bs≡as] = refl (BitVectorEq bs as)

  [as≡bs]≡𝕥 : BitVectorEq as bs ≡ true
  [as≡bs]≡𝕥 = ≡-⇶ (≡-↑↓ [𝕥∷as≡𝕥∷bs]≡[as≡bs]) [𝕥∷αs≡𝕥∷bs]≡𝕥

  [bs≡as]≡𝕥 : BitVectorEq bs as ≡ true
  [bs≡as]≡𝕥 = isSym-n as bs [as≡bs]≡𝕥

  [𝕥∷bs≡𝕥∷as]≡𝕥 : BitVectorEq (true ∷ bs) (true ∷ as) ≡ true
  [𝕥∷bs≡𝕥∷as]≡𝕥 = BitVectorEq-+1 {n} {bs} {as} [bs≡as]≡𝕥 true
BitVectorEq-isSym-ind {n} isSym-n (true ∷ as) (false ∷ bs) [𝕥∷as≡𝕗∷bs]≡𝕥 = ω ☢
 where
  [𝕥∷as≡𝕗∷bs]≡𝕗 : BitVectorEq (true ∷ as) (false ∷ bs) ≡ false
  [𝕥∷as≡𝕗∷bs]≡𝕗 = refl false

  𝕥≡𝕗 : true ≡ false
  𝕥≡𝕗 = ≡-⇶ (≡-↑↓ [𝕥∷as≡𝕗∷bs]≡𝕥) [𝕥∷as≡𝕗∷bs]≡𝕗

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 𝕥≡𝕗
BitVectorEq-isSym-ind {n} isSym-n (false ∷ as) (true ∷ bs) [𝕗∷as≡𝕥∷bs]≡𝕥 = ω ☢
 where
  [𝕗∷as≡𝕥∷bs]≡𝕗 : BitVectorEq (false ∷ as) (true ∷ bs) ≡ false
  [𝕗∷as≡𝕥∷bs]≡𝕗 = refl false

  𝕥≡𝕗 : true ≡ false
  𝕥≡𝕗 = ≡-⇶ (≡-↑↓ [𝕗∷as≡𝕥∷bs]≡𝕥) [𝕗∷as≡𝕥∷bs]≡𝕗

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 𝕥≡𝕗
BitVectorEq-isSym-ind {n} isSym-n (false ∷ as) (false ∷ bs) [𝕗∷as≡𝕗∷bs]≡𝕥 = [𝕗∷bs≡𝕗∷as]≡𝕥
 where
  [𝕗∷as≡𝕗∷bs]≡[as≡bs] : BitVectorEq (false ∷ as) (false ∷ bs) ≡ BitVectorEq as bs
  [𝕗∷as≡𝕗∷bs]≡[as≡bs] = refl (BitVectorEq as bs)
  
  [𝕗∷bs≡𝕗∷as]≡[bs≡as] : BitVectorEq (false ∷ bs) (false ∷ as) ≡ BitVectorEq bs as
  [𝕗∷bs≡𝕗∷as]≡[bs≡as] = refl (BitVectorEq bs as)

  [as≡bs]≡𝕥 : BitVectorEq as bs ≡ true
  [as≡bs]≡𝕥 = ≡-⇶ (≡-↑↓ [𝕗∷as≡𝕗∷bs]≡[as≡bs]) [𝕗∷as≡𝕗∷bs]≡𝕥

  [bs≡as]≡𝕥 : BitVectorEq bs as ≡ true
  [bs≡as]≡𝕥 = isSym-n as bs [as≡bs]≡𝕥

  [𝕗∷bs≡𝕗∷as]≡𝕥 : BitVectorEq (false ∷ bs) (false ∷ as) ≡ true
  [𝕗∷bs≡𝕗∷as]≡𝕥 = BitVectorEq-+1 {n} {bs} {as} [bs≡as]≡𝕥 false


BitVectorEq-isSym : (n : Nat) → isSymmetric (BitVectorEq {n})
BitVectorEq-isSym zero [] [] [r[][]≡true] = refl true
BitVectorEq-isSym (suc n) = BitVectorEq-isSym-ind (BitVectorEq-isSym n)



{-
BitVectorEq-isTrans-ind : {n : Nat} → isTransitive (BitVectorEq {n}) → isTransitive (BitVectorEq {suc n})
BitVectorEq-isTrans-ind {n} isTrans-n (a ∷ as) (b ∷ bs) (c ∷ cs) [a∷as≡b∷bs]≡𝕥 [b∷bs≡c∷cs]≡𝕥 = [a∷as≡c∷cs]≡𝕥
 where
  [as≡bs]≡𝕥 : BitVectorEq as bs ≡ true
  [as≡bs]≡𝕥 = [a∷as≡b∷bs]→[as≡bs] [a∷as≡b∷bs]≡𝕥

  [bs≡cs]≡𝕥 : BitVectorEq bs cs ≡ true
  [bs≡cs]≡𝕥 = [a∷as≡b∷bs]→[as≡bs] [b∷bs≡c∷cs]≡𝕥

  [as≡cs]≡𝕥 : BitVectorEq as cs ≡ true
  [as≡cs]≡𝕥 = isTrans-n as bs cs [as≡bs]≡𝕥 [bs≡cs]≡𝕥

  [a≡b]≡𝕥 : BitEq a b ≡ true
  [a≡b]≡𝕥 

  [a≡c]≡𝕥 : BitVectorEq a c
-}

{-
BitVectorEq-isTrans : (n : Nat) → isTransitive (BitVectorEq {n})
BitVectorEq-isTrans zero [] [] [] [r[][]≡true]₁ [r[][]≡true]₂ = refl true
BitVectorEq-isTrans (suc n) = BitVectorEq-isTrans-ind (BitVectorEq-isTrans n)
-}


{-
BitVectorEq-isEquiv : {n : Nat} → isEquivalenceRelation (BitVectorEq {n})
BitVectorEq-isEquiv {n} = (BitVectorEq-isRefl , ( BitVectorEq-isSym , BitVectorEq-isTrans ))
-}


as≡bs→[c∷as]≡[c∷bs] : {n : Nat} → (x y : Vector Bit n) → (b : Bit) → x ≡ y → (b ∷ x) ≡ (b ∷ y)
as≡bs→[c∷as]≡[c∷bs] {n} x y b [x≡y] = [b∷x≡b∷y]
 where
  b∷ : Vector Bit n → Vector Bit (suc n)
  b∷ v = b ∷ v

  [b∷x≡b∷y] : (b ∷ x) ≡ (b ∷ y)
  [b∷x≡b∷y] = [x≡y]→[fx≡fy] b∷ x y [x≡y]

BitVectorEq-as-bs→BitVectorEq-[c∷as][c∷bs] : {n : Nat} → (x y : Vector Bit n) → (b : Bit) → BitVectorEq x y ≡ true → BitVectorEq (b ∷ x) (b ∷ y) ≡ true 
BitVectorEq-as-bs→BitVectorEq-[c∷as][c∷bs] {n} x y true [x≡y]≡𝕥 = [𝕥∷x≡𝕥∷y]≡𝕥
 where
  [𝕥∷x≡𝕥∷y]≡[x≡y] : BitVectorEq (true ∷ x) (true ∷ y) ≡ BitVectorEq x y
  [𝕥∷x≡𝕥∷y]≡[x≡y] = refl (BitVectorEq x y)

  [𝕥∷x≡𝕥∷y]≡𝕥 : BitVectorEq (true ∷ x) (true ∷ y) ≡ true
  [𝕥∷x≡𝕥∷y]≡𝕥 = ≡-⇶ [𝕥∷x≡𝕥∷y]≡[x≡y] [x≡y]≡𝕥
BitVectorEq-as-bs→BitVectorEq-[c∷as][c∷bs] {n} x y false [x≡y]≡𝕥 = [𝕗∷x≡𝕗∷y]≡𝕥
 where
  [𝕗∷x≡𝕗∷y]≡[x≡y] : BitVectorEq (false ∷ x) (false ∷ y) ≡ BitVectorEq x y
  [𝕗∷x≡𝕗∷y]≡[x≡y] = refl (BitVectorEq x y)

  [𝕗∷x≡𝕗∷y]≡𝕥 : BitVectorEq (false ∷ x) (false ∷ y) ≡ true
  [𝕗∷x≡𝕗∷y]≡𝕥 = ≡-⇶ [𝕗∷x≡𝕗∷y]≡[x≡y] [x≡y]≡𝕥


BitVectorEq-[c∷as][c∷bs]≡BitVectorEq-as-bs : {n : Nat} → (x y : Vector Bit n) → (b : Bit) → BitVectorEq (b ∷ x) (b ∷ y) ≡ BitVectorEq x y
BitVectorEq-[c∷as][c∷bs]≡BitVectorEq-as-bs {n} x y true = refl (BitVectorEq x y)
BitVectorEq-[c∷as][c∷bs]≡BitVectorEq-as-bs {n} x y false = refl (BitVectorEq x y)





-- Proof that BitVectorEq is the decider for propositional equality of Bit vectors:
-- First a ≡ b → BitVectorEq a b ≡ true
a≡b→BitVectorEq-a-b : {n : Nat} → (x y : Vector Bit n) → x ≡ y → BitVectorEq x y ≡ true
a≡b→BitVectorEq-a-b {n} x .x (refl .x) = BitVectorEq-isRefl n x



-- Second, BitVectorEq a b ≡ true → a ≡ b
BitVectorEq-a-b→a≡b-ind : {n : Nat} → (x y : Vector Bit n) → (b : Bit) → (BitVectorEq x y ≡ true → x ≡ y) → BitVectorEq (b ∷ x) (b ∷ y) ≡ true → (b ∷ x) ≡ (b ∷ y)
BitVectorEq-a-b→a≡b-ind {n} x y b hyp [b∷x≡b∷y]≡𝕥 = [b∷x≡b∷y]
 where
  [b∷x≡b∷y]≡[x≡y] : BitVectorEq (b ∷ x) (b ∷ y) ≡ BitVectorEq x y
  [b∷x≡b∷y]≡[x≡y] = BitVectorEq-[c∷as][c∷bs]≡BitVectorEq-as-bs x y b

  [x≡y]≡𝕥 : BitVectorEq x y ≡ true
  [x≡y]≡𝕥 = ≡-⇶ (≡-↑↓ [b∷x≡b∷y]≡[x≡y]) [b∷x≡b∷y]≡𝕥

  [x≡y] : x ≡ y
  [x≡y] = hyp [x≡y]≡𝕥

  b∷ : Vector Bit n → Vector Bit (suc n)
  b∷ v = b ∷ v

  [b∷x≡b∷y] : (b ∷ x) ≡ (b ∷ y)
  [b∷x≡b∷y] = [x≡y]→[fx≡fy] b∷ x y [x≡y]

  
BitVectorEq-a-b→a≡b : {n : Nat} → (x y : Vector Bit n) → BitVectorEq x y ≡ true → x ≡ y
BitVectorEq-a-b→a≡b {zero} [] [] [[]≡[]]≡𝕥 = refl []
BitVectorEq-a-b→a≡b {suc n} (true ∷ as) (true ∷ bs) = BitVectorEq-a-b→a≡b-ind as bs true (BitVectorEq-a-b→a≡b as bs)
BitVectorEq-a-b→a≡b {suc n} (false ∷ as) (false ∷ bs) = BitVectorEq-a-b→a≡b-ind as bs false (BitVectorEq-a-b→a≡b as bs)
BitVectorEq-a-b→a≡b {suc n} (true ∷ as) (false ∷ bs) [𝕥∷as≡𝕗∷bs]≡𝕥 = ω ☢
 where
  [𝕥∷as≡𝕗∷bs]≡𝕗 : BitVectorEq (true ∷ as) (false ∷ bs) ≡ false
  [𝕥∷as≡𝕗∷bs]≡𝕗 = refl false

  [𝕥≡𝕗] : true ≡ false
  [𝕥≡𝕗] = ≡-⇶ (≡-↑↓ [𝕥∷as≡𝕗∷bs]≡𝕥) [𝕥∷as≡𝕗∷bs]≡𝕗

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]
BitVectorEq-a-b→a≡b {suc n} (false ∷ as) (true ∷ bs) [𝕗∷as≡𝕥∷bs]≡𝕥 = ω ☢
 where
  [𝕗∷as≡𝕥∷bs]≡𝕗 : BitVectorEq (false ∷ as) (true ∷ bs) ≡ false
  [𝕗∷as≡𝕥∷bs]≡𝕗 = refl false

  [𝕥≡𝕗] : true ≡ false
  [𝕥≡𝕗] = ≡-⇶ (≡-↑↓ [𝕗∷as≡𝕥∷bs]≡𝕥) [𝕗∷as≡𝕥∷bs]≡𝕗

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]



{-
Can we give generalized proofs about what happens for decider functions in the "false"
cases?
-}
