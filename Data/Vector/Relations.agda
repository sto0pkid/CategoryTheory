module Data.Vector.Relations where

open import Agda.Primitive
open import BaseLogic
open import Data.Bool
open import Data.Bool.Relations
open import Data.Nat
open import Data.Vector
open import Relations

VectorEq : ∀ {α} {A : Set α} → (R : A → A → Bool) → isEqDec R → (n : Nat) → Vector A n → Vector A n → Bool
VectorEq {α} {A} R isEqDec-R zero [] [] = true
VectorEq {α} {A} R isEqDec-R (suc n) (a ∷ as) (b ∷ bs) = 
 if (R a b) then
  VectorEq R isEqDec-R n as bs
 else
  false 


{-
-- Not true! Consider the case when a₁≡a₂. 
-- if false then a₁ else a₂ ≡ a₂ ≡ a₁, but b ≡ false. 
if[b]then[a₁]else[a₂]≡a₁→b≡true
-}



{-
-- So then can we prove it by induction?
-- We can prove it by contradiction but that's not really sufficient (it's non-constructive).
-- If VectorEq-[a∷as][b∷bs]≡𝕥, then at every step, R a b ≡ true, because if there is any
-- x, y in the Vector such that R x y ≡ false, then VectorEq-[a∷as][b∷bs]≡𝕗

VectorEq-[a∷as][b∷bs]→Rab : ∀ {α} {A : Set α} (R : A → A → Bool) → isEqDec R → (n : Nat) → (a b : Vector A (suc n)) → VectorEq R isEqDec (suc n) a b ≡ true → R (vector-first a) (vector-first b) ≡ true
VectorEq-[a∷as][b∷bs]→Rab {α} {A} R isEqDec-R zero (a ∷ []) (b ∷ []) VectorEq-[a∷[]][b∷[]]≡𝕥 = Rab
 where

  Rab
VectorEq-[a∷as][b∷bs]→Rab {α} {A} R isEqDec-R n (a ∷ as) (b ∷ bs) VectorEq-[a∷as][b∷bs]≡𝕥 = Rab
 where
  
  Rab
-}

{-
VectorEq-[a∷as][b∷bs]→VectorEq-as-bs : ∀ {α} {A : Set α} (R : A → A → Bool) → (isEqDec-R : isEqDec R) → (n : Nat) → (a b : Vector A (suc n)) → VectorEq R isEqDec-R (suc n) a b ≡ true → VectorEq R isEqDec-R (suc n) (vector-rest a) (vector-rest b) ≡ true
VectorEq-[a∷as][b∷bs]→VectorEq-as-bs {α} {A} R isEqDec-R zero (a ∷ []) (b ∷ []) VectorEq-[a∷[]][b∷[]] = refl true
VectorEq-[a∷as][b∷bs]→VectorEq-as-bs {α} {A} R isEqDec-R (suc n) (a ∷ as) (b ∷ bs) VectorEq-[a∷as][b∷bs] = 
-}

{-
VectorEq-[a∷as][b∷bs]→a≡b : ∀ {α} {A : Set α} (R : A → A → Bool) → isEqDec R → (n : Nat) → (a b : Vector A (suc n)) → VectorEq a b → (vector-first a) ≡ (vector-first b)
VectorEq-[a∷as][b∷bs]→a≡b {α} {A} R isEqDec-R n a b VectorEq-a-b = [ 
-}
{-
Now we want to prove that `Vector α A R isEqDec-R n` will decide propositional equality for Vector A n


-}


Rxy→VectorEq-[x∷as][y∷bs]≡VectorEq-as-bs : ∀ {α} {A : Set α} (R : A → A → Bool) → (isEqDec-R : isEqDec R) → (x y : A) → R x y ≡ true → (n : Nat) → (as bs : Vector A n) → VectorEq R isEqDec-R (suc n) (x ∷ as) (y ∷ bs) ≡ VectorEq R isEqDec-R n as bs
Rxy→VectorEq-[x∷as][y∷bs]≡VectorEq-as-bs {α} {A} R isEqDec-R x y Rxy n as bs = b≡true→if[b]then[a₁]else[a₂]≡a₁ (VectorEq R isEqDec-R n as bs) false (R x y) Rxy

-- Need to use the proof isEqDec-R to extract a proof that R is an equivalence relation so that
-- we can get the proof that it's reflexive.


VectorEq-isRefl-ind : ∀ {α} {A : Set α} (R : A → A → Bool) → (isEqDec-R : isEqDec R) → (n : Nat) → isReflexive (VectorEq R isEqDec-R n) → isReflexive (VectorEq R isEqDec-R (suc n))
VectorEq-isRefl-ind {α} {A} R isEqDec-R n isRefl-n (a ∷ as) = VectorEq-[a∷as][a∷as]
 where
  R-isEquiv : isEquivalenceRelation R
  R-isEquiv = isEqDec-R→isEquiv-R R isEqDec-R

  R-isRefl : isReflexive R
  R-isRefl = first R-isEquiv
  
  Raa : R a a ≡ true
  Raa = R-isRefl a

  VectorEq-[a∷as][a∷as]≡VectorEq-as-as : VectorEq R isEqDec-R (suc n) (a ∷ as) (a ∷ as) ≡ VectorEq R isEqDec-R n as as
  VectorEq-[a∷as][a∷as]≡VectorEq-as-as = Rxy→VectorEq-[x∷as][y∷bs]≡VectorEq-as-bs R isEqDec-R a a Raa n as as

  VectorEq-as-as : VectorEq R isEqDec-R n as as ≡ true
  VectorEq-as-as = isRefl-n as

  VectorEq-[a∷as][a∷as] : VectorEq R isEqDec-R (suc n) (a ∷ as) (a ∷ as) ≡ true
  VectorEq-[a∷as][a∷as] = ≡-⇶ VectorEq-[a∷as][a∷as]≡VectorEq-as-as VectorEq-as-as



VectorEq-isRefl : ∀ {α} {A : Set α} (R : A → A → Bool) → (isEqDec-R : isEqDec R) → (n : Nat) → (a : Vector A n) → VectorEq R isEqDec-R n a a ≡ true
VectorEq-isRefl {α} {A} R isEqDec-R zero [] = refl true
VectorEq-isRefl {α} {A} R isEqDec-R (suc n) = VectorEq-isRefl-ind R isEqDec-R n (VectorEq-isRefl R isEqDec-R n)

a≡b→VectorEq-a-b : ∀ {α} {A : Set α} (R : A → A → Bool) → (isEqDec-R : isEqDec R) → (n : Nat) → (a b : Vector A n) → a ≡ b → VectorEq R isEqDec-R n a b ≡ true
a≡b→VectorEq-a-b {α} {A} R isEqDec-R n a .a (refl .a) = VectorEq-isRefl R isEqDec-R n a


{-
VectorEq-a-b→a≡b-ind : ∀ {α} {A : Set α} (R : A → A → Bool) → (isEqDec-R : isEqDec R) → (n : Nat) → (a b : Vector A n) → (VectorEq R isEqDec-R n a b ≡ true → a ≡ b) → (x y : A) → VectorEq R isEqDec-R (suc n) (x ∷ a) (y ∷ b) ≡ true → (x ∷ a) ≡ (y ∷ b)
VectorEq-a-b→a≡b-ind {α} {A} R isEqDec-R n a b hyp x y VectorEq-[x∷a][y∷b] = [x∷a≡y∷b]
 where
-}

{-
VectorEq-a-b→a≡b : ∀ {α} {A : Set α} (R : A → A → Bool) → (isEqDec-R : isEqDec R) → (n : Nat) → (a b : Vector A n) → VectorEq R isEqDec-R n a b ≡ true → a ≡ b
VectorEq-a-b→a≡b {α} {A} R isEqDec-R zero [] [] VectorEq-[][] = refl []
VectorEq-a-b→a≡b {α} {A} R isEqDec-R (suc n) (a ∷ as) (b ∷ bs) VectorEq-[a∷as][b∷bs] = [a∷as≡b∷bs]
-}
