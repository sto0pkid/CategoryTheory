module Data.Sets.Relations where

open import Agda.Primitive
open import BaseLogic
open import Data.Bool
open import Data.Bool.Proofs
open import Data.False
open import Data.Fin
open import Data.Nat
open import Data.Nat.Operations renaming (_^_ to exp)
open import Data.Nat.Proofs
open import Data.Nat.Relations
open import Data.Product
open import Data.PropositionalEquality
open import Data.True
open import Data.Vector
open import Data.Vector.Operations renaming (_^_ to _^^^_)
open import Functions renaming (_^_ to _^^_)
open import Level
open import SetTheory

same-cardinality : ∀ {i j} (A : Set i) → (B : Set j) → Set (i ⊔ j)
same-cardinality {i} {j} A B = ∃bijection A B

same-cardinality-refl : ∀ {i} (A : Set i) → same-cardinality A A
same-cardinality-refl {i} A = (id , id-bijective)

same-cardinality-sym : ∀ {i j} (A : Set i) (B : Set j) → same-cardinality A B → same-cardinality B A
same-cardinality-sym {i} {j} A B bij-AB = ∃bijection-sym bij-AB

same-cardinality-trans : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → same-cardinality A B → same-cardinality B C → same-cardinality A C
same-cardinality-trans {i} {j} {k} bij-AB bij-AC = ∃bijection-trans bij-AB bij-AC

is-empty : ∀ {i} (A : Set i) → Set (i ⊔ lzero)
is-empty {i} A = same-cardinality A ⊥

is-singleton : ∀ {i} (A : Set i) → Set (i ⊔ lzero)
is-singleton {i} A = same-cardinality A ⊤

Vector-A-0~⊤ : ∀ {i} {A : Set i} → same-cardinality (Vector A 0) ⊤
Vector-A-0~⊤ {i} {A} = (f , (f-inj , f-surj))
 where
  f : Vector A 0 → ⊤
  f [] = ●

  f-inj : injective f
  f-inj [] [] refl = refl
  
  f-surj : surjective f
  f-surj ● = ([] , refl)

Vector-A-0~Lift-⊤ : ∀ {i} {A : Set i} → same-cardinality (Vector A 0) (Lift {lzero} {i} ⊤)
Vector-A-0~Lift-⊤ {i} {A} = (f , (f-inj , f-surj))
 where
  f : Vector A 0 → Lift {lzero} {i} ⊤
  f [] = lift ●

  f-inj : injective f
  f-inj [] [] refl = refl

  f-surj : surjective f
  f-surj (lift ●) = ([] , refl)


Vector-A-1~A : ∀ {i} {A : Set i} → same-cardinality (Vector A 1) A
Vector-A-1~A {i} {A} = (f , (f-inj , f-surj))
 where
  f : Vector A 1 → A
  f (a ∷ []) = a

  f-inj : injective f
  f-inj (a₁ ∷ []) (a₂ ∷ []) [a₁≡a₂] = proof
   where
    a₁∷ : Vector A 0 → Vector A 1
    a₁∷ = _∷_ a₁
 
    a₂∷ : Vector A 0 → Vector A 1
    a₂∷ = _∷_ a₂

    a₁∷≡a₂∷ : a₁∷ ≡ a₂∷
    a₁∷≡a₂∷ = continuity _∷_ a₁ a₂ [a₁≡a₂]

    proof : (a₁ ∷ []) ≡ (a₂ ∷ [])
    proof = [f≡g]→[fx≡gx] a₁∷ a₂∷ a₁∷≡a₂∷ []

  f-surj : surjective f
  f-surj a = ((a ∷ []) , refl)

_^_ : ∀ {i} (A : Set i) → Nat → Set i
A ^ zero = (Lift ⊤)
A ^ (suc n) = A × (A ^ n)

Vector-A-n~A^n-ind : ∀ {i} {A : Set i} {n : Nat} → same-cardinality (Vector A n) (A ^ n) → same-cardinality (Vector A (suc n)) (A ^ (suc n))
Vector-A-n~A^n-ind {i} {A} {n} (f , (f-inj , f-surj)) = (g , (g-inj , g-surj))
 where
  g : Vector A (suc n) → A ^ (suc n)
  g (a ∷ as) = (a , (f as))

  g-inj : injective g
  g-inj (a ∷ as) (b ∷ bs) [g[a∷as]≡g[b∷bs]] = proof
   where
    a≡b : a ≡ b
    a≡b = continuity first (g (a ∷ as)) (g (b ∷ bs)) [g[a∷as]≡g[b∷bs]]

    f[as]≡f[bs] : f as ≡ f bs
    f[as]≡f[bs] = continuity second (g (a ∷ as)) (g (b ∷ bs)) [g[a∷as]≡g[b∷bs]]

    as≡bs : as ≡ bs
    as≡bs = f-inj as bs f[as]≡f[bs]

    a∷ : Vector A n → Vector A (suc n)
    a∷ = _∷_ a

    b∷ : Vector A n → Vector A (suc n)
    b∷ = _∷_ b

    a∷≡b∷ : a∷ ≡ b∷
    a∷≡b∷ = continuity _∷_ a b a≡b

    proof : (a ∷ as) ≡ (b ∷ bs)
    proof = [x≡y]→[f≡g]→[fx≡gy] as bs as≡bs a∷ b∷ a∷≡b∷

  g-surj : surjective g
  g-surj (a , rest) = (V , gV≡[a,rest])
   where
    V-rest : Vector A n
    V-rest = π₁ (f-surj rest)

    f-V-rest≡rest : (f V-rest) ≡ rest
    f-V-rest≡rest = π₂ (f-surj rest)

    V : Vector A (suc n)
    V = a ∷ V-rest

    gV≡[a,f-V-rest] : (g V) ≡ (a , (f V-rest))
    gV≡[a,f-V-rest] = refl

    [a,_] : A ^ n → A ^ (suc n)
    [a, r ] = (a , r)

    [a,f-V-rest]≡[a,rest] : (a , (f V-rest)) ≡ (a , rest)
    [a,f-V-rest]≡[a,rest] = continuity [a,_] (f V-rest) rest f-V-rest≡rest

    gV≡[a,rest] : (g V) ≡ (a , rest)
    gV≡[a,rest] = ≡-trans gV≡[a,f-V-rest] [a,f-V-rest]≡[a,rest]


Vector-A-n~A^n : ∀ {i} {A : Set i} → (n : Nat) → same-cardinality (Vector A n) (A ^ n)
Vector-A-n~A^n {i} {A} zero = Vector-A-0~Lift-⊤
Vector-A-n~A^n {i} {A} (suc n) = Vector-A-n~A^n-ind (Vector-A-n~A^n n)

singleton~⊤ : ∀ {i} {A : Set i} → ∃ a ∈ A , ((a' : A) → a ≡ a') → same-cardinality A ⊤
singleton~⊤ {i} {A} (a , a-uniq) = (f , (f-inj , f-surj))
 where
  f : A → ⊤
  f x = ●

  f-inj : injective f
  f-inj a₁ a₂ [fa₁≡fa₂] = a₁≡a₂
   where
    a≡a₁ : a ≡ a₁
    a≡a₁ = a-uniq a₁

    a≡a₂ : a ≡ a₂
    a≡a₂ = a-uniq a₂

    a₁≡a₂ : a₁ ≡ a₂
    a₁≡a₂ = ≡-trans (≡-sym a≡a₁) a≡a₂

  f-surj : surjective f
  f-surj ● = (a , refl)

singleton~Lift-⊤ : ∀ {i} {A : Set i} → ∃ a ∈ A , ((a' : A) → a ≡ a') → same-cardinality A (Lift {lzero} {i} ⊤)
singleton~Lift-⊤ {i} {A} (a , a-uniq) = (f , (f-inj , f-surj))
 where
  f : A → Lift {lzero} {i} ⊤
  f x = lift ●

  f-inj : injective f
  f-inj a₁ a₂ [fa₁≡a₂] = a₁≡a₂
   where
    a≡a₁ : a ≡ a₁
    a≡a₁ = a-uniq a₁

    a≡a₂ : a ≡ a₂
    a≡a₂ = a-uniq a₂

    a₁≡a₂ : a₁ ≡ a₂
    a₁≡a₂ = ≡-trans (≡-sym a≡a₁) a≡a₂

  f-surj : surjective f
  f-surj (lift ●) = (a , refl)

is-singleton' : ∀ {i} (A : Set i) → Set i
is-singleton' {i} A = ∃ a ∈ A , ((a' : A) → a ≡ a')

is-singleton'-A→A~⊤ : ∀ {i} {A : Set i} → is-singleton' A → same-cardinality A ⊤
is-singleton'-A→A~⊤ = singleton~⊤

is-singleton'-A→A~Lift-⊤ : ∀ {i} {A : Set i} → is-singleton' A → same-cardinality A (Lift {lzero} {i} ⊤)
is-singleton'-A→A~Lift-⊤ = singleton~Lift-⊤

is-singleton'-A→is-singleton-A : ∀ {i} {A : Set i} → is-singleton' A → is-singleton A
is-singleton'-A→is-singleton-A = singleton~⊤

is-singleton'-⊤ : is-singleton' ⊤
is-singleton'-⊤ = (● , ●-uniq)
 where
  ●-uniq : (x : ⊤) → ● ≡ x
  ●-uniq ● = refl


is-singleton-A→is-singleton'-A : ∀ {i} {A : Set i} → is-singleton A → is-singleton' A
is-singleton-A→is-singleton'-A {i} {A} (f , (f-inj , f-surj)) = (a , a-uniq)
 where
  a : A
  a = π₁ (f-surj ●)

  ●≡fx : (x : A) → ● ≡ (f x)
  ●≡fx x = (π₂ is-singleton'-⊤) (f x)

  a-uniq : (x : A) → a ≡ x
  a-uniq x = [a≡x]
   where
    [●≡fa] : ● ≡ (f a)
    [●≡fa] = ●≡fx a
    [●≡fx] : ● ≡ (f x)
    [●≡fx] = ●≡fx x

    [fa≡fx] : (f a) ≡ (f x)
    [fa≡fx] = ≡-trans (≡-sym [●≡fa]) [●≡fx]

    [a≡x] : a ≡ x
    [a≡x] = f-inj a x [fa≡fx]

singleton→A-inj : ∀ {i j} {B : Set i} {A : Set j} → is-singleton B → (f : B → A) → injective f
singleton→A-inj {i} {j} {B} {A} B-single f b₁ b₂ [fb₁≡fb₂] = b₁≡b₂
 where
  B-single' : is-singleton' B
  B-single' = is-singleton-A→is-singleton'-A B-single

  b : B
  b = π₁ B-single'

  b≡b' : (b' : B) → b ≡ b'
  b≡b' = π₂ B-single'

  b≡b₁ : b ≡ b₁
  b≡b₁ = b≡b' b₁

  b≡b₂ : b ≡ b₂
  b≡b₂ = b≡b' b₂

  b₁≡b₂ : b₁ ≡ b₂
  b₁≡b₂ = ≡-trans (≡-sym b≡b₁) b≡b₂

≡-class : ∀ {i} (A : Set i) → Set (lsuc i)
≡-class {i} A = ∃ S ∈ (Subset {i} {i} A) , (∃ a ∈ A , ((S a) × ((a' : A) → S a' → a ≡ a')))


Bool-true-class : ≡-class Bool
Bool-true-class = ((λ b → b ≡ true) , (true , (refl , f)))
 where
  f : (b' : Bool) → b' ≡ true → true ≡ b'
  f true refl = refl
  f false [false≡true] = ω (true≠false (≡-sym [false≡true]))

Bool-false-class : ≡-class Bool
Bool-false-class = ((λ b → b ≡ false) , (false , (refl , f)))
 where
  f : (b' : Bool) → b' ≡ false → false ≡ b'
  f false refl = refl
  f true [true≡false] = ω (true≠false [true≡false])

_is-smallest-Nat-such-that_ : ∀ {i} → Nat → (F : Nat → Set i) → Set i
n is-smallest-Nat-such-that F = (F n) × ((m : Nat) → m < n → ¬ (F m))

_is-smallest-Nat-such-that'_ : ∀ {i} → Nat → (F : Nat → Set i) → Set i
n is-smallest-Nat-such-that' F = (F n) × ((m : Nat) → F m → m ≥ n)


smallest-Nat-such-that : ∀ {i} → (F : Nat → Set i) → Set i
smallest-Nat-such-that F = ∃ n ∈ Nat , (n is-smallest-Nat-such-that F)

smallest-Nat-such-that' : ∀ {i} → (F : Nat → Set i) → Set i
smallest-Nat-such-that' F = ∃ n ∈ Nat , (n is-smallest-Nat-such-that' F)


non-repeating-vector : ∀ {i} (A : Set i) (n : Nat) → Set i
non-repeating-vector {i} A n = ∃ V ∈ (Vector A n) , ((i j : Fin n) → i ≠ j → (V [ i ]') ≠ (V [ j ]'))

NRV' : ∀ {i} (A : Set i) (n : Nat) → Set i
NRV' {i} A n = ∃ V ∈ (Vector A n) , ((i j : (∃ m ∈ Nat , (m < n))) → (π₁ i) ≠ (π₁ j) → (lookup' V (π₁ i) (π₂ i)) ≠ (lookup' V (π₁ j) (π₂ j)))
 
hasFiniteCardinality : ∀ {i} (A : Set i) → Set i
hasFiniteCardinality {i} A = ∃ n ∈ Nat , (∃ V ∈ (non-repeating-vector A n) , ((a : A) → ∃ i ∈ (Fin n) , (a ≡ (π₁ V) [ i ]')))

hasFiniteCardinality≤N : ∀ {i} (A : Set i) (n : Nat) → Set i
hasFiniteCardinality≤N {i} A n = ∃ V ∈ (non-repeating-vector A n) , ((a : A) → ∃ i ∈ (Fin n) , (a ≡ (π₁ V) [ i ]' ))

hasFiniteCardinality' : ∀ {i} (A : Set i) → Set i
hasFiniteCardinality' {i} A = ∃ n ∈ Nat , (∃ V ∈ (NRV' A n) , ((a : A) → ∃ i ∈ (∃ m ∈ Nat , (m < n)) , (a ≡ lookup' (π₁ V) (π₁ i) (π₂ i))))

hasFiniteCardinality≤N' : ∀ {i} (A : Set i) (n : Nat) → Set i
hasFiniteCardinality≤N' {i} A n = ∃ V ∈ (NRV' A n) , ((a : A) → ∃ i ∈ (∃ m ∈ Nat , (m < n)) , (a ≡ lookup' (π₁ V) (π₁ i) (π₂ i)))

FiniteCardinality : ∀ {i} (A : Set i) → Set i
FiniteCardinality {i} A = smallest-Nat-such-that (hasFiniteCardinality≤N A)

FiniteCardinality' : ∀ {i} (A : Set i) → Set i
FiniteCardinality' {i} A = smallest-Nat-such-that' (hasFiniteCardinality≤N A)

_is-cardinality-of_ : ∀ {i} → Nat → (A : Set i) → Set i
n is-cardinality-of A = n is-smallest-Nat-such-that (hasFiniteCardinality≤N A)

_is-cardinality-of'_ : ∀ {i} → Nat → (A : Set i) → Set i
n is-cardinality-of' A = n is-smallest-Nat-such-that' (hasFiniteCardinality≤N A)

{-
NRV-Bool : non-repeating-vector Bool 2
NRV-Bool = (V , V-non-repeating)
 where
  V : Vector Bool 2
  V = (true ∷ false ∷ [])

  V-non-repeating : (i j : Fin 2) → i ≠ j → V [ i ]' ≠ V [ j ]'
  V-non-repeating zero zero [zero≠zero] = ω ([zero≠zero] refl)
  V-non-repeating zero (suc zero) [zero≠suc-zero] [true≡false] = true≠false [true≡false]
  V-non-repeating (suc zero) zero [suc-zero≠zero] [false≡true] = true≠false (≡-sym [false≡true])
  V-non-repeating (suc zero) (suc zero) [suc-zero≠suc-zero] = ω ([suc-zero≠suc-zero] refl)
  V-non-repeating (suc (suc zero)) x [sucsuczero≠x] = ω main
-}

is-non-repeating : ∀ {i} {A : Set i} {n : Nat} → Vector A n → Set i
is-non-repeating {i} {A} {n} V = (i j : (∃ m ∈ Nat , (m < n))) → (π₁ i) ≠ (π₁ j) → (lookup' V (π₁ i) (π₂ i)) ≠ (lookup' V (π₁ j) (π₂ j))

NRV'-⊥ : NRV' ⊥ 0
NRV'-⊥ = (V , V-non-repeating)
 where
  V : Vector ⊥ 0
  V = []
 
  V-non-repeating : is-non-repeating V
  V-non-repeating (x , [x<0]) = ω (x≮0 x [x<0])

∥⊥∥≤0 : hasFiniteCardinality≤N' ⊥ 0
∥⊥∥≤0 = (NRV'-⊥ , f)
 where
  f : (q : ⊥) → ∃ i ∈ (∃ m ∈ Nat , m < 0) , (q ≡ lookup' (π₁ NRV'-⊥) (π₁ i) (π₂ i))
  f q = ω q

NRV'-⊤ : NRV' ⊤ 1
NRV'-⊤ = (V , V-non-repeating)
 where
  V : Vector ⊤ 1
  V = (● ∷ [])

  V-non-repeating : (i j : (∃ m ∈ Nat , (m < 1))) → (π₁ i) ≠ (π₁ j) → (lookup' V (π₁ i) (π₂ i)) ≠ (lookup' V (π₁ j) (π₂ j))
  V-non-repeating (0 , [0<1]₁) (0 , [0<1]₂) [0≠0] = ω ([0≠0] refl)
  V-non-repeating (0 , [0<1]₁) (1 , [1<1]₂) = ω ((x≮x 1) [1<1]₂)
  V-non-repeating (0 , [0<1]₁) (suc (suc y) , [2+y<1]) = ω (x>y→x≮y (2 + y) 1 (x>y→x+k>y 2 1 (0 , refl) y) [2+y<1])
  V-non-repeating (1 , [1<1]₁) = ω ((x≮x 1) [1<1]₁)
  V-non-repeating (suc (suc x) , [2+x<1]) = ω (x>y→x≮y (2 + x) 1 (x>y→x+k>y 2 1 (0 , refl) x) [2+x<1])


∥⊤∥≤1 : hasFiniteCardinality≤N' ⊤ 1
∥⊤∥≤1 = (NRV'-⊤ , f)
 where
  f : (t : ⊤) → ∃ i ∈ (∃ m ∈ Nat , m < 1) , (t ≡ lookup' (π₁ NRV'-⊤) (π₁ i) (π₂ i))
  f ● = ((0 , (0 , refl)) , refl)


NRV'-Bool : NRV' Bool 2
NRV'-Bool = (V , V-non-repeating)
 where
  V : Vector Bool 2
  V = (true ∷ false ∷ [])

  V-non-repeating : (i j : (∃ m ∈ Nat , (m < 2))) → (π₁ i) ≠ (π₁ j) → (lookup' V (π₁ i) (π₂ i)) ≠ (lookup' V (π₁ j) (π₂ j))
  V-non-repeating (0 , [0<2]₁) (0 , [0<2]₂) [0≠0] = ω ([0≠0] refl)
  V-non-repeating (0 , [0<2]₁) (1 , [1<2]₂) [0≠1] [true≡false] = true≠false [true≡false]
  V-non-repeating (0 , [0<2]₁) (2 , [2<2]₂) = ω ((x≮x 2) [2<2]₂)
  V-non-repeating (0 , [0<2]₁) (suc (suc (suc y)) , [3+y<2]) = ω (x>y→x≮y (3 + y) 2 (x>y→x+k>y 3 2 (0 , refl) y) [3+y<2])
  V-non-repeating (1 , [1<2]₁) (0 , [0<2]₂) [1≠0] [false≡true] = true≠false (≡-sym [false≡true])
  V-non-repeating (1 , [1<2]₁) (1 , [1<2]₂) [1≠1] = ω ([1≠1] refl)
  V-non-repeating (1 , [1<2]₁) (2 , [2<2]₂) = ω ((x≮x 2) [2<2]₂)
  V-non-repeating (1 , [1<2]₁) (suc (suc (suc y)) , [3+y<2]) = ω (x>y→x≮y (3 + y) 2 (x>y→x+k>y 3 2 (0 , refl) y) [3+y<2])
  V-non-repeating (2 , [2<2]₁) = ω ((x≮x 2) [2<2]₁)
  V-non-repeating (suc (suc (suc x)) , [3+x<2]) = ω (x>y→x≮y (3 + x) 2 (x>y→x+k>y 3 2 (0 , refl) x) [3+x<2])


∥Bool∥≤2 : hasFiniteCardinality≤N' Bool 2
∥Bool∥≤2 = (NRV'-Bool , f)
 where
  f : (b : Bool) → ∃ i ∈ (∃ m ∈ Nat , m < 2) , (b ≡ lookup' (π₁ NRV'-Bool) (π₁ i) (π₂ i))
  f true = ((0 , (1 , refl)) , refl)
  f false = ((1 , (0 , refl)) , refl)

NRV'-Bool₂ : NRV' Bool 0
NRV'-Bool₂ = (V , V-non-repeating)
 where
  V : Vector Bool 0
  V = []

  V-non-repeating : (i j : (∃ m ∈ Nat , (m < 0))) → (π₁ i) ≠ (π₁ j) → (lookup' V (π₁ i) (π₂ i)) ≠ (lookup' V (π₁ j) (π₂ j))
  V-non-repeating (x , [x<0]) = ω (x≮0 x [x<0])

{-
NRV'-singleton : ∀ {i} (A : Set i) → is-singleton' A → NRV' A 1
NRV'-singleton {i} A (a , [a≡a']) = (V , V-non-repeating)
 where
  V : Vector A 1
  V = (a ∷ [])

  V-non-repeating : is-non-repeating V
  V-non-repeating (0 , [0<1]₁) (0 , [0<1]₁) [0≠0] = ω ([0≠0] refl)
  V-non-repeating (0

∥singleton∥≤1 : 
-}
Vector-A-0-is-non-repeating : ∀ {i} {A : Set i} → (V : Vector A 0) → is-non-repeating V
Vector-A-0-is-non-repeating {i} {A} [] = proof
 where
  proof : is-non-repeating []
  proof (x , [x<0]) = ω (x≮0 x [x<0])


Vector-A-1-is-non-repeating : ∀ {i} {A : Set i} → (V : Vector A 1) → is-non-repeating V
Vector-A-1-is-non-repeating {i} {A} (a ∷ []) = proof
 where
  proof : is-non-repeating (a ∷ [])
  proof (0 , [0<1]₁) (0 , [0<1]₂) [0≠0] = ω ([0≠0] refl)
  proof (0 , [0<1]₁) (1 , [1<1]₂) = ω (x≮x 1 [1<1]₂)
  proof (0 , [0<1]₁) (suc (suc y) , [2+y<1]) = ω (x>y→x≮y (2 + y) 1 (x>y→x+k>y 2 1 (0 , refl) y) [2+y<1])
  proof (1 , [1<1]₁) = ω (x≮x 1 [1<1]₁)
  proof (suc (suc x) , [2+x<1]) = ω (x>y→x≮y (2 + x) 1 (x>y→x+k>y 2 1 (0 , refl) x) [2+x<1])

NRV'-singleton : ∀ {i} (A : Set i) → is-singleton' A → NRV' A 1
NRV'-singleton {i} A (a , [a≡a']) = ((a ∷ []) , Vector-A-1-is-non-repeating (a ∷ []))

∥singleton∥≤1 : ∀ {i} {A : Set i} → is-singleton' A → hasFiniteCardinality≤N' A 1
∥singleton∥≤1 {i} {A} (a , [a≡a']) = ((NRV'-singleton A (a , [a≡a'])) , f)
 where
  V : NRV' A 1
  V = NRV'-singleton A (a , [a≡a'])

  f : (a' : A) → ∃ i ∈ (∃ m ∈ Nat , m < 1) , (a' ≡ lookup' (π₁ V) (π₁ i) (π₂ i))
  f a' = ((0 , (0 , refl)) , proof)
   where
    a≡V[i] : a ≡ (lookup' (π₁ V) 0 (0 , refl))
    a≡V[i] = [a≡a'] (lookup' (π₁ V) 0 (0 , refl))

    a≡a' : a ≡ a'
    a≡a' = [a≡a'] a'

    proof : a' ≡ lookup' (π₁ V) 0 (0 , refl)
    proof = ≡-trans (≡-sym a≡a') a≡V[i]

