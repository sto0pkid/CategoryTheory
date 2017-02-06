module Data.Vector.Relations where

open import Agda.Primitive
open import BaseLogic
open import Data.Bool
open import Data.Bool.Relations
open import Data.Nat
open import Data.Vector
open import Data.Fin
open import Relations

VectorEq : ∀ {α} {A : Set α} → (R : A → A → Bool) → isEqDec R → (n : Nat) → Vector A n → Vector A n → Bool
VectorEq {α} {A} R isEqDec-R zero [] [] = true
VectorEq {α} {A} R isEqDec-R (suc n) (a ∷ as) (b ∷ bs) = 
 if (R a b) then
  VectorEq R isEqDec-R n as bs
 else
  false 

{-
VectorEq-Pointwise : ∀ {α} {A : Set α} → (R : A → A → Bool) → isEqDec R → (n : Nat) → (x y : Vector A n) → Set α
VectorEq-Pointwise {α} {A} R isEqDec-R (suc n) x y = (i : Fin n) → (x [ i ]) ≡ (y [ i ])
-}

Vector-Pointwise-Rel : ∀ {α β} {A : Set α} {n : Nat} → (R : A → A → Set β) → (xs ys : Vector A n) → Set β
Vector-Pointwise-Rel {α} {β} {A} {n} R xs ys = (i : Fin n) → R (lookup i xs) (lookup i ys)

data Vector-Pointwise-Rel' {α} {β} {A : Set α} (R : A → A → Set β) : {n : Nat} (xs ys : Vector A n) → Set β where
 [] : Vector-Pointwise-Rel' R [] []
 _∷_ : {n : Nat} → {x y : A} → {xs ys : Vector A n} → (Rxy : R x y) → Vector-Pointwise-Rel' R xs ys → Vector-Pointwise-Rel' R (x ∷ xs) (y ∷ ys)

{-
Vector-Pointwise-Rel-Equiv : ∀ {α β} {A : Set α} {n : Nat} → {R : A → A → Set β} → {xs ys : Vector A n} → Vector-Pointwise-Rel R xs ys <=> Vector-Pointwise-Rel' R xs ys
Vector-Pointwise-Rel-Equiv {α} {β} {A} {n} {R} {xs} {ys} = (Rel→Rel' , Rel'→Rel)
 where
  Rel→Rel' : Vector-Pointwise-Rel R xs ys → Vector-Pointwise-Rel' R xs ys
  

  Rel'→Rel : Vector-Pointwise-Rel' R xs ys → Vector-Pointwise-Rel R xs ys
-}

Vector-Pointwise-≡ : ∀ {α} {A : Set α} {n : Nat} → (xs ys : Vector A n) → Set α
Vector-Pointwise-≡ {α} {A} {n} xs ys = (i : Fin n) → (lookup i xs) ≡ (lookup i ys)

Vector-Pointwise-≡' : ∀ {α} {A : Set α} {n : Nat} → (xs ys : Vector A n) → Set α
Vector-Pointwise-≡' {α} {A} {n} xs ys = (i : Fin n) → xs [ i ]' ≡ ys [ i ]'

Vector-Pointwise-≡-isRefl : ∀ {α} {A : Set α} {n : Nat} → (xs : Vector A n) → Vector-Pointwise-≡ xs xs
Vector-Pointwise-≡-isRefl {α} {A} {n} xs i = refl (lookup i xs)

Vector-Pointwise-≡'-isRefl : ∀ {α} {A : Set α} {n : Nat} → (xs : Vector A n) → Vector-Pointwise-≡' xs xs
Vector-Pointwise-≡'-isRefl {α} {A} {n} xs i = refl (xs [ i ]')

xs≡ys→Vector-Pointwise-≡ : ∀ {α} {A : Set α} {n : Nat} → (xs ys : Vector A n) → xs ≡ ys → Vector-Pointwise-≡ xs ys
xs≡ys→Vector-Pointwise-≡ {α} {A} {n} xs .xs (refl .xs) = Vector-Pointwise-≡-isRefl xs

Vector-Pointwise-≡-[x∷xs][y∷ys]→x≡y : ∀ {α} {A : Set α} {n : Nat} → (xs ys : Vector A n) → (x y : A) → Vector-Pointwise-≡ (x ∷ xs) (y ∷ ys) → x ≡ y
Vector-Pointwise-≡-[x∷xs][y∷ys]→x≡y {α} {A} {n} xs ys x y x∷xs[pw-≡]y∷ys = [x≡y]
 where
  x∷xs[0]≡x : lookup zero (x ∷ xs) ≡ x
  x∷xs[0]≡x = refl x

  y∷ys[0]≡y : lookup zero (y ∷ ys) ≡ y
  y∷ys[0]≡y = refl y

  x∷xs[0]≡y∷ys[0] : lookup zero (x ∷ xs) ≡ lookup zero (y ∷ ys)
  x∷xs[0]≡y∷ys[0] = x∷xs[pw-≡]y∷ys zero

  [x≡y] : x ≡ y
  [x≡y] = ≡-⇶ (≡-↑↓ x∷xs[0]≡x) (≡-⇶ x∷xs[0]≡y∷ys[0] y∷ys[0]≡y)

Vector-Pointwise-≡-[x∷xs][y∷ys]→Vector-Pointwise-≡-xs-ys : ∀ {α} {A : Set α} {n : Nat} → (xs ys : Vector A n) → (x y : A) → Vector-Pointwise-≡ (x ∷ xs) (y ∷ ys) → Vector-Pointwise-≡ xs ys
Vector-Pointwise-≡-[x∷xs][y∷ys]→Vector-Pointwise-≡-xs-ys {α} {A} {n} xs ys x y x∷xs[pw-≡]y∷ys = xs[pw-≡]ys
 where
  xs[pw-≡]ys : (i : Fin n) → (lookup i xs) ≡ (lookup i ys)
  xs[pw-≡]ys i = x∷xs[pw-≡]y∷ys (raise 1 i)

[f≡g]→[fx≡gx] : ∀ {α β} {A : Set α} {B : Set β} (f g : A → B) → f ≡ g → (x : A) → f x ≡ g x
[f≡g]→[fx≡gx] {α} {β} {A} {B} f .f (refl .f) x = refl (f x)


x≡y→x∷xs≡y∷xs : ∀ {α} {A : Set α} {n : Nat} → (xs : Vector A n) → (x y : A) → x ≡ y → (x ∷ xs) ≡ (y ∷ xs)
x≡y→x∷xs≡y∷xs {α} {A} {n} xs x y [x≡y] = x∷xs≡y∷xs
 where
  ∙∷ : A → Vector A n → Vector A (suc n)
  ∙∷ z zs = z ∷ zs

  x∷ : Vector A n → Vector A (suc n)
  x∷ = ∙∷ x

  y∷ : Vector A n → Vector A (suc n)
  y∷ = ∙∷ y

  x∷≡y∷ : x∷ ≡ y∷
  x∷≡y∷ = [x≡y]→[fx≡fy] ∙∷ x y [x≡y]

  x∷xs≡y∷xs : (x ∷ xs) ≡ (y ∷ xs)
  x∷xs≡y∷xs = [f≡g]→[fx≡gx] x∷ y∷ x∷≡y∷ xs

xs≡ys→x∷xs≡x∷ys : ∀ {α} {A : Set α} {n : Nat} (xs ys : Vector A n) → xs ≡ ys → (x : A) → (x ∷ xs) ≡ (x ∷ ys)
xs≡ys→x∷xs≡x∷ys {α} {A} {n} xs ys [xs≡ys] x = [x∷xs≡x∷ys]
 where
  x∷ : Vector A n → Vector A (suc n)
  x∷ v = x ∷ v

  [x∷xs≡x∷ys] : (x ∷ xs) ≡ (x ∷ ys)
  [x∷xs≡x∷ys] = [x≡y]→[fx≡fy] x∷ xs ys [xs≡ys]

[x≡y]→[f≡g]→[fx≡gy] : ∀ {α β} {A : Set α} {B : Set β} → (x y : A) → x ≡ y → (f g : A → B) → f ≡ g → f x ≡ g y
[x≡y]→[f≡g]→[fx≡gy] {α} {β} {A} {B} x .x (refl .x) f .f (refl .f) = refl (f x)
  

xs≡ys→x≡y→x∷xs≡y∷ys : ∀ {α} {A : Set α} {n : Nat} → (xs ys : Vector A n) → (x y : A) → xs ≡ ys → x ≡ y → (x ∷ xs) ≡ (y ∷ ys)
xs≡ys→x≡y→x∷xs≡y∷ys {α} {A} {n} xs ys x y [xs≡ys] [x≡y] = [x∷xs≡y∷ys]
 where
  ∙∷ : A → Vector A n → Vector A (suc n)
  ∙∷ z zs = z ∷ zs

  x∷ : Vector A n → Vector A (suc n)
  x∷ = ∙∷ x

  y∷ : Vector A n → Vector A (suc n)
  y∷ = ∙∷ y

  x∷≡y∷ : x∷ ≡ y∷
  x∷≡y∷ = [x≡y]→[fx≡fy] ∙∷ x y [x≡y]

  [x∷xs≡y∷ys] : (x ∷ xs) ≡ (y ∷ ys)
  [x∷xs≡y∷ys] = [x≡y]→[f≡g]→[fx≡gy] xs ys [xs≡ys] x∷ y∷ x∷≡y∷
  


Vector-Pointwise-≡→xs≡ys-ind : ∀ {α} {A : Set α} {n : Nat} → (xs ys : Vector A n) → (x y : A) → (Vector-Pointwise-≡ xs ys → xs ≡ ys) → Vector-Pointwise-≡ (x ∷ xs) (y ∷ ys) → (x ∷ xs) ≡ (y ∷ ys)
Vector-Pointwise-≡→xs≡ys-ind {α} {A} {n} xs ys x y hyp x∷xs[pw-≡]y∷ys = [x∷xs≡y∷ys]
 where
  x≡y : x ≡ y
  x≡y = Vector-Pointwise-≡-[x∷xs][y∷ys]→x≡y xs ys x y x∷xs[pw-≡]y∷ys

  xs[pw-≡]ys : Vector-Pointwise-≡ xs ys
  xs[pw-≡]ys = Vector-Pointwise-≡-[x∷xs][y∷ys]→Vector-Pointwise-≡-xs-ys xs ys x y x∷xs[pw-≡]y∷ys

  xs≡ys : xs ≡ ys
  xs≡ys = hyp xs[pw-≡]ys
  
  [x∷xs≡y∷ys] : (x ∷ xs) ≡ (y ∷ ys)
  [x∷xs≡y∷ys] = xs≡ys→x≡y→x∷xs≡y∷ys xs ys x y xs≡ys x≡y


Vector-Pointwise-≡→xs≡ys : ∀ {α} {A : Set α} {n : Nat} → (xs ys : Vector A n) → Vector-Pointwise-≡ xs ys → xs ≡ ys
Vector-Pointwise-≡→xs≡ys {α} {A} {zero} [] [] [][pw-≡][] = refl []
Vector-Pointwise-≡→xs≡ys {α} {A} {suc n} (x ∷ xs) (y ∷ ys) = Vector-Pointwise-≡→xs≡ys-ind xs ys x y  (Vector-Pointwise-≡→xs≡ys {α} {A} {n} xs ys)

Vector-Pointwise-≡⇔≡ : ∀ {α} {A : Set α} {n : Nat} → (xs ys : Vector A n) → (Vector-Pointwise-≡ xs ys) <=> (xs ≡ ys)
Vector-Pointwise-≡⇔≡ {α} {A} {n} xs ys = ([pw-≡]→[≡] , [≡]→[pw-≡])
 where
  [pw-≡]→[≡] : Vector-Pointwise-≡ xs ys → xs ≡ ys
  [pw-≡]→[≡] = Vector-Pointwise-≡→xs≡ys xs ys

  [≡]→[pw-≡] : xs ≡ ys → Vector-Pointwise-≡ xs ys
  [≡]→[pw-≡] = xs≡ys→Vector-Pointwise-≡ xs ys

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
