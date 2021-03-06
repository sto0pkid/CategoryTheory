module BooleanAlgebra where

open import Agda.Primitive

data _×_ {i} {j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
 _,_ : A → B → A × B

first : ∀ {i j} {A : Set i} {B : Set j} → A × B → A
first (a , b) = a

second : ∀ {i j} {A : Set i} {B : Set j} → A × B → B
second (a , b) = b

isReflexive : ∀ {i j} {A : Set i} (R : A → A → Set j) → Set (i ⊔ j)
isReflexive {i} {j} {A} R = (x : A) → R x x

isSymmetric : ∀ {i j} {A : Set i} (R : A → A → Set j) → Set (i ⊔ j)
isSymmetric {i} {j} {A} R = (x y : A) → R x y → R y x

isTransitive : ∀ {i j} {A : Set i} (R : A → A → Set j) → Set (i ⊔ j)
isTransitive {i} {j} {A} R = (x y z : A) → R x y → R y z → R x z

record Equivalence : Set₁ where
 field
  carrier : Set
  _≡_ : carrier → carrier → Set
  ≡-refl : (x : carrier) → x ≡ x
  ≡-sym : (x y : carrier) → x ≡ y → y ≡ x
  ≡-trans : (x y z : carrier) → x ≡ y → y ≡ z → x ≡ z

record Equivalence' {i} {j} (A : Set i) : Set ((lsuc i) ⊔ (lsuc j)) where
 field
  _≡_ : A → A → Set j
  ≡-refl : (x : A) → x ≡ x
  ≡-sym : (x y : A) → x ≡ y → y ≡ x
  ≡-trans : (x y z : A) → x ≡ y → y ≡ z → x ≡ z

record isEquivalence {i} {j} {A : Set i} (_≡_ : A → A → Set j) : Set ((lsuc i) ⊔ (lsuc j)) where
 field
  ≡-refl : (x : A) → x ≡ x
  ≡-sym : {x y : A} → x ≡ y → y ≡ x
  ≡-trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z


isAntisymmetric : ∀ {i j k} {A : Set i} (R : A → A → Set j) (_≡_ : A → A → Set k) → {p : isEquivalence _≡_} → Set ((i ⊔ j) ⊔ k)
isAntisymmetric {i} {j} {k} {A} R _≡_ = (x y : A) → R x y → R y x → x ≡ y



record PartialOrder : Set₁ where
 field
  carrier : Set
  _≤_ : carrier → carrier → Set
  _≡_ : carrier → carrier → Set
  ≡-refl : (x : carrier) → x ≡ x
  ≡-sym : (x y : carrier) → x ≡ y → y ≡ x
  ≡-trans : (x y z : carrier) → x ≡ y → y ≡ z → x ≡ z
  ≤-refl : (x : carrier) → x ≤ x
  ≤-trans : (x y z : carrier) → x ≤ y → y ≤ z → x ≤ z
  ≤-antisym : (x y : carrier) → x ≤ y → y ≤ x → x ≡ y

record PartialOrder' {i} {j} {k} (A : Set i) : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  _≤_ : A → A → Set j
  _≡_ : A → A → Set k
  ≡-refl : (x : A) → x ≡ x
  ≡-sym : (x y : A) → x ≡ y → y ≡ x
  ≡-trans : (x y z : A) → x ≡ y → y ≡ z → x ≡ z
  ≤-refl : (x : A) → x ≤ x
  ≤-trans : (x y z : A) → x ≤ y → y ≤ z → x ≤ z
  ≤-antisym : (x y : A) → x ≤ y → y ≤ x → x ≡ y  

record PartialOrder'' {i} {j} {k} : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  carrier : Set i
  _≤_ : carrier → carrier → Set j
  _≡_ : carrier → carrier → Set k
  ≡-refl : (x : carrier) → x ≡ x
  ≡-sym : (x y : carrier) → x ≡ y → y ≡ x
  ≡-trans : (x y z : carrier) → x ≡ y → y ≡ z → x ≡ z
  ≤-refl : (x : carrier) → x ≤ x 
  ≤-trans : (x y z : carrier) → x ≤ y → y ≤ z → x ≤ z
  ≤-antisym : (x y : carrier) → x ≤ y → y ≤ x → x ≡ y

record isPartialOrder {i} {j} {k} {A : Set i} (_≤_ : A → A → Set j) : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  _≡_ : A → A → Set k
  ≡-equiv : isEquivalence _≡_
  ≤-refl : isReflexive _≤_
  ≤-sym : isAntisymmetric _≤_ _≡_ {≡-equiv}
  ≤-trans : isTransitive _≤_

record isPartialOrder' {i} {j} {k} {A : Set i} (_≡_ : A → A → Set k) (≡-equiv : isEquivalence _≡_) (_≤_ : A → A → Set j) : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  ≤-refl : (x y : A) → x ≡ y → (x ≤ y) × (y ≤ x)
  ≤-sym : isAntisymmetric _≤_ _≡_ {≡-equiv}
  ≤-trans : isTransitive _≤_

{-
≤-cont : ∀ {i j k} {A : Set i} {_≡_ : A → A → Set k} {≡-equiv : isEquivalence _≡_} (_≤_ : A → A → Set j) → isPartialOrder' {i} {j} {k} {A} {_≡_} {≡-equiv} _≤_ → (a b c d : A) → (a ≡ b) → (c ≡ d) → a ≤ c → b ≤ d
≤-cont {i} {j} {k} {A} {_≡_} {≡-equiv} _≤_ ≤-po a b c d [a≡b] [c≡d] [a≤c] = proof
 where
  ≤-refl : (x y : A) → x ≡ y → (x ≤ y) × (y ≤ x)
  ≤-refl = isPartialOrder'.≤-refl ≤-po

  ≤-trans : isTransitive _≤_
  ≤-trans = isPartialOrder'.≤-trans ≤-po
 
  [b≤a] : b ≤ a
  [b≤a] = second (≤-refl a b [a≡b])

  [c≤d] : c ≤ d
  [c≤d] = first (≤-refl c d [c≡d])

  proof : b ≤ d
  proof = ≤-trans b a d [b≤a] (≤-trans a c d [a≤c] [c≤d])
-}

isCommutative : ∀ {i j k} {A : Set i} {B : Set j} (_≡_ : B → B → Set k) (p : isEquivalence _≡_) → (f : A → A → B) → Set (i ⊔ k)
isCommutative {i} {j} {k} {A} {B} _≡_ ≡-equiv f = (x y : A) → (f x y) ≡ (f y x)

isAssociative : ∀ {i j} {A : Set i} (_≡_ : A → A → Set j) (p : isEquivalence _≡_) → (f : A → A → A) → Set (i ⊔ j)
isAssociative {i} {j} {A} _≡_ ≡-equiv f = (x y z : A) → (f x (f y z)) ≡ (f (f x y) z)

absorbs : ∀ {i j} {A : Set i} (_≡_ : A → A → Set j) (p : isEquivalence _≡_) → (f : A → A → A) → (g : A → A → A) → Set (i ⊔ j)
absorbs {i} {j} {A} _≡_ ≡-equiv f g = (x y : A) → (f x (g x y)) ≡ x

distributesOver : ∀ {i j} {A : Set i} (_≡_ : A → A → Set j) (p : isEquivalence _≡_) → (f : A → A → A) → (g : A → A → A) → Set (i ⊔ j)
distributesOver {i} {j} {A} _≡_ ≡-equiv f g = (x y z : A) → (f x (g y z)) ≡ (g (f x y) (f x z)) 

  
{-
http://documents.kenyon.edu/math/SamTay.pdf
Definition 1.1.2
-}
data PVar : Set where
 p : PVar
 + : PVar → PVar

{-
http://documents.kenyon.edu/math/SamTay.pdf
Definition 1.1.3
-}
data L : Set where
 var : PVar → L
 ¬ : L → L
 _=>_ : L → L → L

_∨-L_ : L → L → L
x ∨-L y = (¬ x) => y

_∧-L_ : L → L → L
x ∧-L y = (¬ (x => (¬ y)))

_<=>-L_ : L → L → L
x <=>-L y = ((x => y) ∧-L (y => x))

{-
http://documents.kenyon.edu/math/SamTay.pdf
Beginning of 1.2 "Deductions"
-}

data L-axiom : L → Set where
 A1 : (x : L) → L-axiom ((x ∨-L x) => x)
 A2 : (x y : L) → L-axiom (x => (x ∨-L y))
 A3 : (x y : L) → L-axiom ((x ∨-L y) => (y ∨-L x))
 A4 : (x y z : L) → L-axiom ((x => y) => ((z ∨-L x) => (z ∨-L y)))

data L-axiom' : L → Set where
 A1 : (x : L) → L-axiom' (((¬ x) => x) => x)
 A2 : (x y : L) → L-axiom' (x => ((¬ x) => y))
 A3 : (x y : L) → L-axiom' (((¬ x) => y) => ((¬ y) => x))
 A4 : (x y z : L) → L-axiom' ((x => y) => (((¬ z) => x) => ((¬ z) => y)))

data List {i} (A : Set i) : Set i where
 [] : List A
 _∷_ : A → List A → List A

{-
http://documents.kenyon.edu/math/SamTay.pdf
Definition 1.2.1
-}
data L-theorem : L → Set where
 ax : {x : L} → L-axiom x → L-theorem x
 mp : {x y : L} → L-theorem x → L-theorem (x => y) → L-theorem y

data L-theorem' : L → Set where
 ax : {x : L} → L-axiom' x → L-theorem' x
 mp : {x y : L} → L-theorem x → L-theorem' (x => y) → L-theorem' y
 
L⊢ : L → Set
L⊢ x = L-theorem x

data Bool : Set where
 true : Bool
 false : Bool

data _==_ {i} {A : Set i} (x : A) : A → Set i where
 refl : x == x

data _=='_ {i} {A : Set i} : A → A → Set i where
 refl : (x : A) → x ==' x

{-
http://documents.kenyon.edu/math/SamTay.pdf
Example 1.2.2
-}
{-
L⊢x=>x : (x : L) → L⊢ (x => x)
L⊢x=>x x = proof
 where
  P1 : L⊢ (x => (x ∨-L x))
  P1 = ax (A2 x x)

  P2 : L⊢ ((x ∨-L x) => x)
  P2 = ax (A1 x)

  -- confirmed error: we can't get this from A4.
  P3 : L⊢ (((x ∨-L x) => x) => ((x => (x ∨-L x)) => (x => x)))
  P3 = ax (A4 (x ∨-L x) x x)
  
  proof
-}

{-
http://documents.kenyon.edu/math/SamTay.pdf
Definition 1.2.3
-}

data L-deduction (A : L → Set) : L → Set where
 ax : {x : L} → L-axiom x → L-deduction A x
 hyp : {x : L} → A x → L-deduction A x
 mp : {x y : L} → L-deduction A x → L-deduction A (x => y) → L-deduction A y

_L⊢_ : (A : L → Set) → L → Set
A L⊢ y = L-deduction A y

data ∃ {i} {j} (A : Set i) (P : A → Set j) : Set (i ⊔ j) where
 _,_ : (a : A) → (b : P a) → ∃ A P

syntax ∃ A (λ x → e) = ∃ x ∈ A , e

π₁ : ∀ {i} {j} {A : Set i} {P : A → Set j} → ∃ A P → A
π₁ (a , b) = a

π₂ : ∀ {i} {j} {A : Set i} {P : A → Set j} → (p : ∃ A P) → P (π₁ p)
π₂ (a , b) = b

data ⊥ : Set where
ω : ∀ {α} {A : Set α} → ⊥ → A
ω ()


{-
http://documents.kenyon.edu/math/SamTay.pdf
Definition 1.2.4
-}
inconsistent-L : (A : L → Set) → Set
inconsistent-L A = ∃ L (λ x → (_L⊢_ A (x ∧-L (¬ x))))

consistent-L : (A : L → Set) → Set
consistent-L A = (inconsistent-L A) → ⊥ 


not : Bool → Bool
not true = false
not false = true

_or_ : Bool → Bool → Bool
true or true = true
true or false = true
false or true = true
false or false = false

_and_ : Bool → Bool → Bool
true and true = true
true and false = false
false and true = false
false and false = false

{-
http://documents.kenyon.edu/math/SamTay.pdf
Definition 1.3.1
-}

PValuation : Set
PValuation = PVar → Bool

TValuation : PValuation → L → Bool
TValuation v (var x) = v x
TValuation v (¬ x) = not (TValuation v x)
TValuation v (x => y) = (not (TValuation v x)) or (TValuation v y)

{-
Prove: TValuation v (¬ x)= 1 iff TValuation v(x) = 0
       TValuation v (x => y) = 1 iff TValuation v x = 0 or TValuation v y = 1
-}

{-
http://documents.kenyon.edu/math/SamTay.pdf
Definition 1.3.2
-}
L-Tautology : (x : L) → Set 
L-Tautology x = (v : PValuation) → TValuation v x == true

L⊨ : (x : L) → Set
L⊨ x = L-Tautology x

{-
http://documents.kenyon.edu/math/SamTay.pdf
Definition 1.3.3
-}
L-Contradiction : (x : L) → Set
L-Contradiction x = (v : PValuation) → TValuation v x == false

[x==y]→[fx==fy] : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) (x y : A) (p : x == y) → (f x) == (f y)
[x==y]→[fx==fy] {i} {j} {A} {B} f x .x refl = refl

L-Contradiction-x→L-Tautology-¬x : (x : L) → L-Contradiction x → L-Tautology (¬ x)
L-Contradiction-x→L-Tautology-¬x x L-Contradiction-x v = proof
 where
  v[x]==false : (TValuation v x) == false
  v[x]==false = L-Contradiction-x v

  proof : not (TValuation v x) == true
  proof = [x==y]→[fx==fy] not (TValuation v x) false v[x]==false

{-
http://documents.kenyon.edu/math/SamTay.pdf
Definition 1.3.4
-}
L-satisfiable : (S : L → Set) → Set
L-satisfiable S = ∃ v ∈ PValuation , ((x : L) → S x → TValuation v x == true)

_L-satisfies_ : (v : PValuation) → (S : L → Set) → Set
v L-satisfies S = (x : L) → S x → TValuation v x == true

{-
http://documents.kenyon.edu/math/SamTay.pdf
Definition 1.3.5
-}
_L-semantic-consequence-of_ : (y : L) → (S : L → Set) → Set
y L-semantic-consequence-of S = (v : PValuation) → v L-satisfies S → TValuation v y == true


[A==B]→[A→B] : ∀ {i} {A B : Set i} → A == B → A → B
[A==B]→[A→B] {i} {A} {.A} refl a = a
  
{-
http://documents.kenyon.edu/math/SamTay.pdf
Definition 2.1.1
-}
record OrderLattice {i} {j} {k} : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  carrier : Set i
  _≤_ : carrier → carrier → Set j
  _≡_ : carrier → carrier → Set k
  ≡-refl : (x : carrier) → x ≡ x
  ≡-sym : (x y : carrier) → x ≡ y → y ≡ x
  ≡-trans : ( x y z : carrier) → x ≡ y → y ≡ z → x ≡ z
  ≤-refl : (x : carrier) → x ≤ x
  ≤-trans : (x y z : carrier) → x ≤ y → y ≤ z → x ≤ z
  ≤-antisym : (x y : carrier) → x ≤ y → y ≤ x → x ≡ y
  _∧_ : carrier → carrier → carrier
  ∧-glb : (x y : carrier) → ((x ∧ y) ≤ x) × (((x ∧ y) ≤ y) × ((z : carrier) → (z ≤ x) × (z ≤ y) → (z ≤ (x ∧ y))))  
  _∨_ : carrier → carrier → carrier  
  ∨-lub : (x y : carrier) → (x ≤ (x ∨ y)) × ((y ≤ (x ∨ y)) × ((z : carrier) → (x ≤ z) × (y ≤ z) → ((x ∨ y) ≤ z)))

record OrderLattice' {i} {j} {k} : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  carrier : Set i
  _≡_ : carrier → carrier → Set k
  ≡-refl : (x : carrier) → x ≡ x
  ≡-sym : {x y : carrier} → x ≡ y → y ≡ x
  ≡-trans : {x y z : carrier} → x ≡ y → y ≡ z → x ≡ z
  _≤_ : carrier → carrier → Set j
  ≤-refl : {x y : carrier} → x ≡ y → (x ≤ y) × (y ≤ x)
  ≤-trans : {x y z : carrier} → x ≤ y → y ≤ z → x ≤ z
  ≤-antisym : {x y : carrier} → x ≤ y → y ≤ x → x ≡ y
  _∧_ : carrier → carrier → carrier
  ∧-glb : (x y : carrier) → ((x ∧ y) ≤ x) × (((x ∧ y) ≤ y) × ((z : carrier) → (z ≤ x) × (z ≤ y) → (z ≤ (x ∧ y))))
  _∨_ : carrier → carrier → carrier
  ∨-lub : (x y : carrier) → (x ≤ (x ∨ y)) × ((y ≤ (x ∨ y)) × ((z : carrier) → (x ≤ z) × (y ≤ z) → (x ∨ y) ≤ z))

record OrderLattice'' {i} {j} {k} : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  carrier : Set i
  _≡_ : carrier → carrier → Set k
  ≡-equiv : isEquivalence {i} {k} {carrier} _≡_
  _≤_ : carrier → carrier → Set j
  ≤-po : isPartialOrder' _≡_ ≡-equiv _≤_
  _∧_ : carrier → carrier → carrier
  ∧-cont : (a b c d : carrier) → (a ≡ b) → (c ≡ d) → (a ∧ b) ≡ (c ∧ d)
  ∧-glb : (x y : carrier) → ((x ∧ y) ≤ x) × (((x ∧ y) ≤ y) × ((z : carrier) → (z ≤ x) × (z ≤ y) → (z ≤ (x ∧ y))))
  _∨_ : carrier → carrier → carrier
  ∨-cont : (a b c d : carrier) → (a ≡ b) → (c ≡ d) → (a ∨ b) ≡ (c ∨ d)
  ∨-lub : (x y : carrier) → (x ≤ (x ∨ y)) × ((y ≤ (x ∨ y)) × ((z : carrier) → (x ≤ z) × (y ≤ z) → ((x ∨ y) ≤ z)))

record OrderLattice''' {i} {j} {k} : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  carrier : Set i
  _≡_ : carrier → carrier → Set k
  ≡-refl : (x : carrier) → x ≡ x
  ≡-sym : {x y : carrier} → x ≡ y → y ≡ x
  ≡-trans : {x y z : carrier} → x ≡ y → y ≡ z → x ≡ z
  _≤_ : carrier → carrier → Set j
  ≤-refl : {x y : carrier} → x ≡ y → x ≤ y
  ≤-trans : {x y z : carrier} → x ≤ y → y ≤ z → x ≤ z
  ≤-antisym : {x y : carrier} → x ≤ y → y ≤ x → x ≡ y
  _∧_ : carrier → carrier → carrier
  ∧-glb : (x y : carrier) → ((x ∧ y) ≤ x) × (((x ∧ y) ≤ y) × ((z : carrier) → (z ≤ x) × (z ≤ y) → (z ≤ (x ∧ y))))
  _∨_ : carrier → carrier → carrier
  ∨-lub : (x y : carrier) → (x ≤ (x ∨ y)) × ((y ≤ (x ∨ y)) × ((z : carrier) → (x ≤ z) × (y ≤ z) → (x ∨ y) ≤ z))


record isOrderLattice {i} {j} {k} (A : Set i) (_≡_ : A → A → Set k) (_≤_ : A → A → Set j) (_∧_ : A → A → A) (_∨_ : A → A → A) : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  ≡-refl : (x : A) → x ≡ x
  ≡-sym : {x y : A} → x ≡ y → y ≡ x
  ≡-trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  ≤-refl : {x y : A} → x ≡ y → (x ≤ y) × (y ≤ x)
  ≤-antisym : {x y : A} → x ≤ y → y ≤ x → x ≡ y
  ≤-trans : {x y z : A} → x ≤ y → y ≤ z → x ≤ z
  ∨-lub : (x y : A) → (x ≤ (x ∨ y)) × ((y ≤ (x ∨ y)) × ((z : A) → (x ≤ z) × (y ≤ z) → (x ∨ y) ≤ z))
  ∧-glb : (x y : A) → ((x ∧ y) ≤ x) × (((x ∧ y) ≤ y) × ((z : A) → (z ≤ x) × (z ≤ y) → z ≤ (x ∧ y)))

record isOrderLattice'' {i} {j} {k} (A : Set i) (_≡_ : A → A → Set k) (_≤_ : A → A → Set j) (_∧_ : A → A → A) (_∨_ : A → A → A) : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  ≡-refl : (x : A) → x ≡ x
  ≡-sym : {x y : A} → x ≡ y → y ≡ x
  ≡-trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  ≤-refl : (x : A) → x ≤ x
  ≤-antisym : {x y : A} → x ≤ y → y ≤ x → x ≡ y
  ≤-trans : {x y z : A} → x ≤ y → y ≤ z → x ≤ z
  ∨-lub : (x y : A) → (x ≤ (x ∨ y)) × ((y ≤ (x ∨ y)) × ((z : A) → (x ≤ z) × (y ≤ z) → (x ∨ y) ≤ z))
  ∧-glb : (x y : A) → ((x ∧ y) ≤ x) × (((x ∧ y) ≤ y) × ((z : A) → (z ≤ x) × (z ≤ y) → z ≤ (x ∧ y)))


record isOrderLattice''' {i} {j} {k} (A : Set i) (_≡_ : A → A → Set k) (_≤_ : A → A → Set j) (_∧_ : A → A → A) (_∨_ : A → A → A) : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  ≡-refl : (x : A) → x ≡ x
  ≡-sym : {x y : A} → x ≡ y → y ≡ x
  ≡-trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  ≤-refl : {x y : A} → x ≡ y → x ≤ y
  ≤-antisym : {x y : A} → x ≤ y → y ≤ x → x ≡ y
  ≤-trans : {x y z : A} → x ≤ y → y ≤ z → x ≤ z
  ∨-lub : (x y : A) → (x ≤ (x ∨ y)) × ((y ≤ (x ∨ y)) × ((z : A) → (x ≤ z) × (y ≤ z) → (x ∨ y) ≤ z))
  ∧-glb : (x y : A) → ((x ∧ y) ≤ x) × (((x ∧ y) ≤ y) × ((z : A) → (z ≤ x) × (z ≤ y) → z ≤ (x ∧ y)))


x≤y-iff-[x∨y≡y-and-x∧y≡x] : 
 ∀ {i j k} (O : OrderLattice' {i} {j} {k}) →
 let 
  open OrderLattice' O
 in
  (x y : carrier) → ((x ≤ y) → ((x ∨ y) ≡ y) × ((x ∧ y) ≡ x)) × (((x ∨ y) ≡ y) × ((x ∧ y) ≡ x) → (x ≤ y)) 
x≤y-iff-[x∨y≡y-and-x∧y≡x] {i} {j} {k} O x y = (LTR , RTL)
 where
  open OrderLattice' O

  LTR : (x ≤ y) → (((x ∨ y) ≡ y) × ((x ∧ y) ≡ x))
  LTR [x≤y] = (left , right)
   where
    [y≤x∨y] : y ≤ (x ∨ y)
    [y≤x∨y] = first (second (∨-lub x y))
    
    [y≡y] : y ≡ y
    [y≡y] = ≡-refl y

    [y≤y] : y ≤ y
    [y≤y] = first (≤-refl [y≡y])
 
    [x∨y≤y] : (x ∨ y) ≤ y
    [x∨y≤y] = (second (second (∨-lub x y))) y ([x≤y] , [y≤y])
       
    left : (x ∨ y) ≡ y
    left = ≤-antisym [x∨y≤y] [y≤x∨y]

    [x∧y≤x] : (x ∧ y) ≤ x
    [x∧y≤x] = first (∧-glb x y)

    [x≡x] : x ≡ x
    [x≡x] = ≡-refl x

    [x≤x] : x ≤ x
    [x≤x] = first (≤-refl [x≡x])

    [x≤x∧y] : x ≤ (x ∧ y)
    [x≤x∧y] = (second (second (∧-glb x y))) x ([x≤x] , [x≤y])

    right : (x ∧ y) ≡ x
    right = ≤-antisym [x∧y≤x] [x≤x∧y]

  RTL : (((x ∨ y) ≡ y) × ((x ∧ y) ≡ x)) → (x ≤ y)
  RTL ([x∨y≡y] , [x∧y≡x]) = proof
   where
    [x≤x∧y] : x ≤ (x ∧ y)
    [x≤x∧y] = second (≤-refl [x∧y≡x])

    [x∧y≤y] : (x ∧ y) ≤ y
    [x∧y≤y] = first (second (∧-glb x y))    

    proof : x ≤ y
    proof = ≤-trans [x≤x∧y] [x∧y≤y]


    
{-
http://documents.kenyon.edu/math/SamTay.pdf
Example 2.1.2
-}

[_||_∪_] : ∀ {i} (A : Set i) (S₁ S₂ : A → Bool) → A → Bool
[ A || S₁ ∪ S₂ ] = λ a → (S₁ a) or (S₂ a)

[_||_∩_] : ∀ {i} (A : Set i) (S₁ S₂ : A → Bool) → A → Bool
[ A || S₁ ∩ S₂ ] = λ a → (S₁ a) and (S₂ a)

[_||_⊆_] : ∀ {i} (A : Set i) (S₁ S₂ : A → Bool) → Set i
[ A || S₁ ⊆ S₂ ] = (a : A) → (S₁ a) == true → (S₂ a) == true

⊆-refl : ∀ {i} (A : Set i) (S : A → Bool) → [ A || S ⊆ S ]
⊆-refl {i} A S a [Sa] = [Sa]

⊆-trans : ∀ {i} {A : Set i} {S₁ S₂ S₃ : A → Bool} → [ A || S₁ ⊆ S₂ ] → [ A || S₂ ⊆ S₃ ] → [ A || S₁ ⊆ S₃ ]
⊆-trans {i} {A} {S₁} {S₂} {S₃} p₁₂ p₂₃ a [S₁a] = p₂₃ a (p₁₂ a [S₁a])

⊆-refl' : ∀ {i} {A : Set i} {S₁ S₂ : A → Bool} → ([ A || S₁ ⊆ S₂ ]) × ([ A || S₂ ⊆ S₁ ]) → ([ A || S₁ ⊆ S₂ ]) × ([ A || S₂ ⊆ S₁ ])
⊆-refl' {A} {S₁} {S₂} [S₁≡S₂] = [S₁≡S₂]

⊆-antisym : ∀ {i} {A : Set i} {S₁ S₂ : A → Bool} → [ A || S₁ ⊆ S₂ ] → [ A || S₂ ⊆ S₁ ] → [ A || S₁ ⊆ S₂ ] × [ A || S₂ ⊆ S₁ ]
⊆-antisym {i} {A} {S₁} {S₂} [S₁⊆S₂] [S₂⊆S₁] = ([S₁⊆S₂] , [S₂⊆S₁])

==-refl : ∀ {i} {A : Set i} (a : A) → a == a
==-refl {i} {A} a = refl

==-sym : ∀ {i} {A : Set i} {a b : A} → a == b → b == a
==-sym {i} {A} {a} {.a} refl = refl

==-trans : ∀ {i} {A : Set i} {a b c : A} → a == b → b == c → a == c
==-trans {i} {A} {a} {.a} {.a} refl refl = refl

x⊆x∪y : ∀ {i} {A : Set i} (S₁ S₂ : A → Bool) → [ A || S₁ ⊆ ([ A || S₁ ∪ S₂ ]) ]
x⊆x∪y {i} {A} S₁ S₂ a [S₁a] = proof
 where
  true-or-x==true : (x : Bool) → (true or x) == true
  true-or-x==true true = refl
  true-or-x==true false = refl

  true-or-[S₂a]==true : (true or (S₂ a)) == true
  true-or-[S₂a]==true = true-or-x==true (S₂ a)

  [S₁a]-or-[S₂a]==true-or-[S₂a] : ((S₁ a) or (S₂ a)) == (true or (S₂ a))
  [S₁a]-or-[S₂a]==true-or-[S₂a] = subproof
   where
    _or'_ : Bool → Bool → Bool
    x or' y = y or x
 
    subproof : ((S₁ a) or (S₂ a)) == (true or (S₂ a))
    subproof = [x==y]→[fx==fy] (_or'_ (S₂ a)) (S₁ a) true [S₁a]

  proof : ((S₁ a) or (S₂ a)) == true
  proof = ==-trans  [S₁a]-or-[S₂a]==true-or-[S₂a] true-or-[S₂a]==true

y⊆x∪y : ∀ {i} {A : Set i} (S₁ S₂ : A → Bool) → [ A || S₂ ⊆ ([ A || S₁ ∪ S₂ ]) ]
y⊆x∪y {i} {A} S₁ S₂ a [S₂a] = proof
 where
  x-or-true==true : (x : Bool) → (x or true) == true
  x-or-true==true true = refl
  x-or-true==true false = refl

  [S₁a]-or-true==true : ((S₁ a) or true) == true
  [S₁a]-or-true==true = x-or-true==true (S₁ a)

  [S₁a]-or-[S₂a]==[S₁a]-or-true : ((S₁ a) or (S₂ a)) == ((S₁ a) or true)
  [S₁a]-or-[S₂a]==[S₁a]-or-true = [x==y]→[fx==fy] (_or_ (S₁ a)) (S₂ a) true [S₂a]

  proof : ((S₁ a) or (S₂ a)) == true
  proof = ==-trans [S₁a]-or-[S₂a]==[S₁a]-or-true [S₁a]-or-true==true

data _⊹_ {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
 inl : A → A ⊹ B
 inr : B → A ⊹ B

data ⊤ : Set where
 ● : ⊤

⊤→⊤ : ⊤ → ⊤
⊤→⊤ x = x

⊥→⊥ : ⊥ → ⊥
⊥→⊥ x = x

⊥→⊤ : ⊥ → ⊤
⊥→⊤ x = ω x

[⊤→⊥]→⊥ : (⊤ → ⊥) → ⊥
[⊤→⊥]→⊥ [⊤→⊥] = [⊤→⊥] ●

Bool→Set : Bool → Set
Bool→Set true = ⊤
Bool→Set false = ⊥

_≠_ : ∀ {i} {A : Set i} (x y : A) → Set i
x ≠ y = (x == y) → ⊥

⊤≠⊥ : ⊤ ≠ ⊥
⊤≠⊥ [⊤==⊥] = [⊤→⊥]→⊥ ([A==B]→[A→B] [⊤==⊥])

true≠false : true ≠ false
true≠false [true==false] = ⊤≠⊥ ([x==y]→[fx==fy] Bool→Set true false [true==false])

≠-sym : ∀ {i} {A : Set i} {x y : A} → x ≠ y → y ≠ x
≠-sym {i} {A} {x} {.x} [x≠x] refl = [x≠x] refl


x-or-y==true→x==true-or-y==true : (x y : Bool) → (x or y) == true → (x == true) ⊹ (y == true)
x-or-y==true→x==true-or-y==true true true [true-or-true==true] = (inl refl)
x-or-y==true→x==true-or-y==true true false [true-or-false==true] = (inl refl)
x-or-y==true→x==true-or-y==true false true [false-or-true==true] = (inr refl)
x-or-y==true→x==true-or-y==true false false [false-or-false==true] = ω (true≠false (==-sym [false-or-false==true]))

x⊆z→y⊆z→x∪y⊆z : ∀ {i} {A : Set i} (S₁ S₂ S₃ : A → Bool) → ([ A || S₁ ⊆ S₃ ]) × ([ A || S₂ ⊆ S₃ ]) → [ A || [ A || S₁ ∪ S₂ ] ⊆ S₃ ]
x⊆z→y⊆z→x∪y⊆z {i} {A} S₁ S₂ S₃ ([S₁⊆S₃] , [S₂⊆S₃]) a [[S₁∪S₂]a] = [S₃a]
 where
  [S₁a⊹S₂a] : ((S₁ a) == true) ⊹ ((S₂ a) == true)
  [S₁a⊹S₂a] = x-or-y==true→x==true-or-y==true (S₁ a) (S₂ a) [[S₁∪S₂]a]  

  [S₁a⊹S₂a]→[S₃a] : (((S₁ a) == true) ⊹ ((S₂ a) == true)) → (S₃ a) == true
  [S₁a⊹S₂a]→[S₃a] (inl [S₁a]) = [S₁⊆S₃] a [S₁a]
  [S₁a⊹S₂a]→[S₃a] (inr [S₂a]) = [S₂⊆S₃] a [S₂a]

  [S₃a] : (S₃ a) == true
  [S₃a] = [S₁a⊹S₂a]→[S₃a] [S₁a⊹S₂a]

x-and-y==true→x==true-and-y==true : (x y : Bool) → (x and y) == true → (x == true) × (y == true)
x-and-y==true→x==true-and-y==true true true [true-and-true==true] = (refl , refl)
x-and-y==true→x==true-and-y==true true false [true-and-false==true] = ω (true≠false (==-sym [true-and-false==true]))
x-and-y==true→x==true-and-y==true false true [false-and-true==true] = ω (true≠false (==-sym [false-and-true==true]))
x-and-y==true→x==true-and-y==true false false [false-and-false==true] = ω (true≠false (==-sym [false-and-false==true]))

x∩y⊆x : ∀ {i} {A : Set i} (S₁ S₂ : A → Bool) → [ A || [ A || S₁ ∩ S₂ ] ⊆ S₁ ]
x∩y⊆x {i} {A} S₁ S₂ a [[S₁∩S₂]a] = first (x-and-y==true→x==true-and-y==true (S₁ a) (S₂ a) [[S₁∩S₂]a])

x∩y⊆y : ∀ {i} {A : Set i} (S₁ S₂ : A → Bool) → [ A || [ A || S₁ ∩ S₂ ] ⊆ S₂ ]
x∩y⊆y {i} {A} S₁ S₂ a [[S₁∩S₂]a] = second (x-and-y==true→x==true-and-y==true (S₁ a) (S₂ a) [[S₁∩S₂]a])

z⊆x→z⊆y→z⊆x∩y : ∀ {i} {A : Set i} (S₁ S₂ S₃ : A → Bool) → ([ A || S₃ ⊆ S₁ ]) × ([ A || S₃ ⊆ S₂ ]) → [ A || S₃ ⊆ [ A || S₁ ∩ S₂ ] ]
z⊆x→z⊆y→z⊆x∩y {i} {A} S₁ S₂ S₃ ([S₃⊆S₁] , [S₃⊆S₂]) a [S₃a] = proof
 where
  [S₁a] : (S₁ a) == true
  [S₁a] = [S₃⊆S₁] a [S₃a]

  [S₂a] : (S₂ a) == true
  [S₂a] = [S₃⊆S₂] a [S₃a]

  _and'_ : Bool → Bool → Bool
  x and' y = y and x

  x-and-[S₂a] : Bool → Bool
  x-and-[S₂a] = _and'_ (S₂ a)

  true-and-x : Bool → Bool
  true-and-x = _and_ true

  [S₁a]-and-[S₂a]==true-and-[S₂a] : ((S₁ a) and (S₂ a)) == (true and (S₂ a))
  [S₁a]-and-[S₂a]==true-and-[S₂a] = [x==y]→[fx==fy] x-and-[S₂a] (S₁ a) true [S₁a]
  
  true-and-[S₂a]==true-and-true : (true and (S₂ a)) == (true and true)
  true-and-[S₂a]==true-and-true = [x==y]→[fx==fy] true-and-x (S₂ a) true [S₂a]

  proof : ((S₁ a) and (S₂ a)) == true
  proof = ==-trans [S₁a]-and-[S₂a]==true-and-[S₂a] true-and-[S₂a]==true-and-true

PowerSetLattice : ∀ {i} (A : Set i) → OrderLattice' {i} {i} {i}
PowerSetLattice {i} A = 
 record {
  carrier = A → Bool ;
  _≡_ = λ x y → [ A || x ⊆ y ] × [ A || y ⊆ x ] ;
  ≡-refl = λ x → (⊆-refl A x , ⊆-refl A x) ;
  ≡-sym = λ p → (second p , first p) ;
  ≡-trans = λ p₁ p₂ → ((⊆-trans (first p₁) (first p₂)) , (⊆-trans (second p₂) (second p₁))) ;
  _≤_ = [_||_⊆_] A ;
  ≤-refl = ⊆-refl' ;
  ≤-trans = ⊆-trans ;
  ≤-antisym = ⊆-antisym ;
  _∧_ = [_||_∩_] A ;
  ∧-glb = λ x y → ((x∩y⊆x x y) , ((x∩y⊆y x y) , λ z → (z⊆x→z⊆y→z⊆x∩y x y z))) ;
  _∨_ = [_||_∪_] A ;
  ∨-lub = λ x y → ((x⊆x∪y x y) , ((y⊆x∪y x y) , λ z → (x⊆z→y⊆z→x∪y⊆z x y z)))
 
 }


{-
http://documents.kenyon.edu/math/SamTay.pdf
Proposition 2.1.3
-}


record AlgebraicLattice {i} {j} : Set ((lsuc i) ⊔ (lsuc j)) where
 field
  carrier : Set i
  _≡_ : carrier → carrier → Set j
  ≡-refl : (x : carrier) → x ≡ x
  ≡-sym : {x y : carrier} → x ≡ y → y ≡ x
  ≡-trans : {x y z : carrier} → x ≡ y → y ≡ z → x ≡ z
  _∧_ : carrier → carrier → carrier
  _∨_ : carrier → carrier → carrier
  ∧-comm : (x y : carrier) → (x ∧ y) ≡ (y ∧ x)
  ∧-assoc : (x y z : carrier) → (x ∧ (y ∧ z)) ≡ ((x ∧ y) ∧ z)
  ∧∨-absorp : (x y : carrier) → (x ∧ (x ∨ y)) ≡ x
  ∨-comm : (x y : carrier) → (x ∨ y) ≡ (y ∨ x)
  ∨-assoc : (x y z : carrier) → (x ∨ (y ∨ z)) ≡ ((x ∨ y) ∨ z)
  ∨∧-absorp : (x y : carrier) → (x ∨ (x ∧ y)) ≡ x


record AlgebraicLattice' {i} {j} : Set ((lsuc i) ⊔ (lsuc j)) where
 field
  carrier : Set i
  _≡_ : carrier → carrier → Set j
  ≡-equiv : isEquivalence _≡_
  _∧_ : carrier → carrier → carrier
  _∨_ : carrier → carrier → carrier
  ∧-comm : isCommutative _≡_ ≡-equiv _∧_
  ∧-assoc : isAssociative _≡_ ≡-equiv _∧_
  ∧∨-absorp : absorbs _≡_ ≡-equiv _∧_ _∨_
  ∨-comm : isCommutative _≡_ ≡-equiv _∨_
  ∨-assoc : isAssociative _≡_ ≡-equiv _∨_
  ∨∧-absorp : absorbs _≡_ ≡-equiv _∨_ _∧_

record isAlgebraicLattice {i} {j} (A : Set i) : Set ((lsuc i) ⊔ (lsuc j)) where
 field
  _≡_ : A → A → Set j
  ≡-equiv : isEquivalence _≡_
  _∧_ : A → A → A
  _∨_ : A → A → A
  ∧-comm : isCommutative _≡_ ≡-equiv _∧_
  ∧-assoc : isAssociative _≡_ ≡-equiv _∧_
  ∧∨-absorp : absorbs _≡_ ≡-equiv _∧_ _∨_
  ∨-comm : isCommutative _≡_ ≡-equiv _∨_
  ∨-assoc : isAssociative _≡_ ≡-equiv _∨_
  ∨∧-absorp : absorbs _≡_ ≡-equiv _∨_ _∧_

record isAlgebraicLattice' {i} {j} (A : Set i) (_≡_ : A → A → Set j) (≡-equiv : isEquivalence _≡_) : Set ((lsuc i) ⊔ (lsuc j)) where
 field
  _∧_ : A → A → A
  _∨_ : A → A → A
  ∧-comm : isCommutative _≡_ ≡-equiv _∧_
  ∧-assoc : isAssociative _≡_ ≡-equiv _∧_
  ∧∨-absorp : absorbs _≡_ ≡-equiv _∧_ _∨_
  ∨-comm : isCommutative _≡_ ≡-equiv _∨_
  ∨-assoc : isAssociative _≡_ ≡-equiv _∨_
  ∨∧-absorp : absorbs _≡_ ≡-equiv _∨_ _∧_

record isAlgebraicLattice'' {i} {j} (A : Set i) (_≡_ : A → A → Set j) (≡-equiv : isEquivalence _≡_) (_∧_ : A → A → A) (_∨_ : A → A → A) : Set ((lsuc i) ⊔ (lsuc j)) where
 field 
  ∧-comm : isCommutative _≡_ ≡-equiv _∧_
  ∧-assoc : isAssociative _≡_ ≡-equiv _∧_
  ∧∨-absorp : absorbs _≡_ ≡-equiv _∧_ _∨_
  ∨-comm : isCommutative _≡_ ≡-equiv _∨_
  ∨-assoc : isAssociative _≡_ ≡-equiv _∨_
  ∨∧-absorp : absorbs _≡_ ≡-equiv _∨_ _∧_

record isAlgebraicLattice''' {i} {j} (A : Set i) (_≡_ : A → A → Set j) (≡-equiv : isEquivalence _≡_) (_∧_ : A → A → A) (_∨_ : A → A → A) : Set ((lsuc i) ⊔ (lsuc j)) where
 field
  ∧-cont : (x x' y y' : A) → x ≡ x' → y ≡ y' → (x ∧ y) ≡ (x' ∧ y')
  ∧-comm : isCommutative _≡_ ≡-equiv _∧_
  ∧-assoc : isAssociative _≡_ ≡-equiv _∧_
  ∧∨-absorp : absorbs _≡_ ≡-equiv _∧_ _∨_
  ∨-cont : (x x' y y' : A) → x ≡ x' → y ≡ y' → (x ∨ y) ≡ (x' ∨ y')
  ∨-comm : isCommutative _≡_ ≡-equiv _∨_
  ∨-assoc : isAssociative _≡_ ≡-equiv _∨_
  ∨∧-absorp : absorbs _≡_ ≡-equiv _∨_ _∧_
  


OrderLattice→isAlgebraicLattice :
 ∀ {i j k} (O : OrderLattice' {i} {j} {k}) → 
 let 
  open OrderLattice' O
 
  ≡-equiv : isEquivalence _≡_
  ≡-equiv = 
      record {
       ≡-refl = ≡-refl ;
       ≡-sym = ≡-sym ;
       ≡-trans = ≡-trans 
      }
 
 in 
  isAlgebraicLattice'' carrier _≡_ ≡-equiv _∧_ _∨_
OrderLattice→isAlgebraicLattice {i} {j} {k} O = 
 record {
  ∧-comm = ∧-comm ;
  ∧-assoc = ∧-assoc ;
  ∧∨-absorp = ∧∨-absorp ;
  ∨-comm = ∨-comm ;
  ∨-assoc = ∨-assoc ;
  ∨∧-absorp = ∨∧-absorp
 }
 where
  open OrderLattice' O
  
  ∧-comm : (x y : carrier) → (x ∧ y) ≡ (y ∧ x)
  ∧-comm x y = ≤-antisym [x∧y≤y∧x] [y∧x≤x∧y]
   where
    [x∧y≤y∧x] : (x ∧ y) ≤ (y ∧ x)
    [x∧y≤y∧x] = (second (second (∧-glb y x))) (x ∧ y) ([x∧y≤y] , [x∧y≤x])
     where 
      [x∧y≤x] : (x ∧ y) ≤ x
      [x∧y≤x] = first (∧-glb x y)

      [x∧y≤y] : (x ∧ y) ≤ y
      [x∧y≤y] = first (second (∧-glb x y))

    [y∧x≤x∧y] : (y ∧ x) ≤ (x ∧ y)
    [y∧x≤x∧y] = (second (second (∧-glb x y))) (y ∧ x) ([y∧x≤x] , [y∧x≤y])
     where
      [y∧x≤y] : (y ∧ x) ≤ y
      [y∧x≤y] = first (∧-glb y x)

      [y∧x≤x] : (y ∧ x) ≤ x
      [y∧x≤x] = first (second (∧-glb y x))



  ∧-assoc : (x y z : carrier) → (x ∧ (y ∧ z)) ≡ ((x ∧ y) ∧ z)
  ∧-assoc x y z = ≤-antisym [x∧[y∧z]≤[x∧y]∧z] [[x∧y]∧z≤x∧[y∧z]]
   where
    [x∧[y∧z]≤[x∧y]∧z] : (x ∧ (y ∧ z)) ≤ ((x ∧ y) ∧ z)
    [x∧[y∧z]≤[x∧y]∧z] = (second (second (∧-glb (x ∧ y) z))) (x ∧ (y ∧ z)) ([x∧[y∧z]≤x∧y] , [x∧[y∧z]≤z] )
     where
      [x∧[y∧z]≤x] : (x ∧ (y ∧ z)) ≤ x
      [x∧[y∧z]≤x] = first (∧-glb x (y ∧ z))

      [x∧[y∧z]≤y∧z] : (x ∧ (y ∧ z)) ≤ (y ∧ z)
      [x∧[y∧z]≤y∧z] = first (second (∧-glb x (y ∧ z)))
 
      [y∧z≤y] : (y ∧ z) ≤ y
      [y∧z≤y] = first (∧-glb y z)

      [y∧z≤z] : (y ∧ z) ≤ z
      [y∧z≤z] = first (second (∧-glb y z))

      [x∧[y∧z]≤y] : (x ∧ (y ∧ z)) ≤ y
      [x∧[y∧z]≤y] = ≤-trans [x∧[y∧z]≤y∧z] [y∧z≤y]

      [x∧[y∧z]≤z] : (x ∧ (y ∧ z)) ≤ z
      [x∧[y∧z]≤z] = ≤-trans [x∧[y∧z]≤y∧z] [y∧z≤z]

      [x∧[y∧z]≤x∧y] : (x ∧ (y ∧ z)) ≤ (x ∧ y)
      [x∧[y∧z]≤x∧y] = (second (second (∧-glb x y))) (x ∧ (y ∧ z)) ([x∧[y∧z]≤x] , [x∧[y∧z]≤y] )

    [[x∧y]∧z≤x∧[y∧z]] : ((x ∧ y) ∧ z) ≤ (x ∧ (y ∧ z))
    [[x∧y]∧z≤x∧[y∧z]] = (second (second (∧-glb x (y ∧ z)))) ((x ∧ y) ∧ z) ([[x∧y]∧z≤x] , [[x∧y]∧z≤y∧z])
     where
      [[x∧y]∧z≤x∧y] : ((x ∧ y) ∧ z) ≤ (x ∧ y)
      [[x∧y]∧z≤x∧y] = first (∧-glb (x ∧ y) z)

      [[x∧y]∧z≤z] : ((x ∧ y) ∧ z) ≤ z
      [[x∧y]∧z≤z] = first (second (∧-glb (x ∧ y) z))

      [x∧y≤x] : (x ∧ y) ≤ x
      [x∧y≤x] = first (∧-glb x y)

      [x∧y≤y] : (x ∧ y) ≤ y
      [x∧y≤y] = first (second (∧-glb x y))

      [[x∧y]∧z≤x] : ((x ∧ y) ∧ z) ≤ x
      [[x∧y]∧z≤x] = ≤-trans [[x∧y]∧z≤x∧y] [x∧y≤x]

      [[x∧y]∧z≤y] : ((x ∧ y) ∧ z) ≤ y
      [[x∧y]∧z≤y] = ≤-trans [[x∧y]∧z≤x∧y] [x∧y≤y] 

      [[x∧y]∧z≤y∧z] : ((x ∧ y) ∧ z) ≤ (y ∧ z)
      [[x∧y]∧z≤y∧z] = (second (second (∧-glb y z))) ((x ∧ y) ∧ z) ([[x∧y]∧z≤y] , [[x∧y]∧z≤z])



  ∨-comm : (x y : carrier) → (x ∨ y) ≡ (y ∨ x)
  ∨-comm x y = ≤-antisym [x∨y≤y∨x] [y∨x≤x∨y]
   where
    [y∨x≤x∨y] : (y ∨ x) ≤ (x ∨ y)
    [y∨x≤x∨y] = (second (second (∨-lub y x))) (x ∨ y) ([y≤x∨y] , [x≤x∨y])
     where
      [x≤x∨y] : x ≤ (x ∨ y)
      [x≤x∨y] = first (∨-lub x y)
 
      [y≤x∨y] : y ≤ (x ∨ y)
      [y≤x∨y] = first (second (∨-lub x y))

    [x∨y≤y∨x] : (x ∨ y) ≤ (y ∨ x)
    [x∨y≤y∨x] = (second (second (∨-lub x y))) (y ∨ x) ([x≤y∨x] , [y≤y∨x])
     where 
      [y≤y∨x] : y ≤ (y ∨ x)
      [y≤y∨x] = first (∨-lub y x)

      [x≤y∨x] : x ≤ (y ∨ x)
      [x≤y∨x] = first (second (∨-lub y x))


  ∨-assoc : (x y z : carrier) → (x ∨ (y ∨ z)) ≡ ((x ∨ y) ∨ z)
  ∨-assoc x y z = ≤-antisym [x∨[y∨z]≤[x∨y]∨z] [[x∨y]∨z≤x∨[y∨z]]
   where
    [[x∨y]∨z≤x∨[y∨z]] : ((x ∨ y) ∨ z) ≤ (x ∨ (y ∨ z))
    [[x∨y]∨z≤x∨[y∨z]] = (second (second (∨-lub (x ∨ y) z))) (x ∨ (y ∨ z)) ([x∨y≤x∨[y∨z]] , [z≤x∨[y∨z]])
     where
      [x≤x∨[y∨z]] : x ≤ (x ∨ (y ∨ z))
      [x≤x∨[y∨z]] = first (∨-lub x (y ∨ z))

      [y∨z≤x∨[y∨z]] : (y ∨ z) ≤ (x ∨ (y ∨ z))
      [y∨z≤x∨[y∨z]] = first (second (∨-lub x (y ∨ z)))

      [y≤y∨z] : y ≤ (y ∨ z)
      [y≤y∨z] = first (∨-lub y z)

      [z≤y∨z] : z ≤ (y ∨ z)
      [z≤y∨z] = first (second (∨-lub y z))

      [y≤x∨[y∨z]] : y ≤ (x ∨ (y ∨ z))
      [y≤x∨[y∨z]] = ≤-trans [y≤y∨z] [y∨z≤x∨[y∨z]]

      [z≤x∨[y∨z]] : z ≤ (x ∨ (y ∨ z))
      [z≤x∨[y∨z]] = ≤-trans [z≤y∨z] [y∨z≤x∨[y∨z]]

      [x∨y≤x∨[y∨z]] : (x ∨ y) ≤ (x ∨ (y ∨ z))
      [x∨y≤x∨[y∨z]] = (second (second (∨-lub x y))) (x ∨ (y ∨ z)) ([x≤x∨[y∨z]] , [y≤x∨[y∨z]])
   
    [x∨[y∨z]≤[x∨y]∨z] : (x ∨ (y ∨ z)) ≤ ((x ∨ y) ∨ z)
    [x∨[y∨z]≤[x∨y]∨z] = (second (second (∨-lub x (y ∨ z)))) ((x ∨ y) ∨ z) ([x≤[x∨y]∨z] , [y∨z≤[x∨y]∨z])
     where
      [x∨y≤[x∨y]∨z] : (x ∨ y) ≤ ((x ∨ y) ∨ z)
      [x∨y≤[x∨y]∨z] = first (∨-lub (x ∨ y) z)
 
      [z≤[x∨y]∨z] : z ≤ ((x ∨ y) ∨ z)
      [z≤[x∨y]∨z] = first (second (∨-lub (x ∨ y) z))

      [x≤x∨y] : x ≤ (x ∨ y)
      [x≤x∨y] = first (∨-lub x y)
   
      [y≤x∨y] : y ≤ (x ∨ y)
      [y≤x∨y] = first (second (∨-lub x y))

      [x≤[x∨y]∨z] : x ≤ ((x ∨ y) ∨ z)
      [x≤[x∨y]∨z] = ≤-trans [x≤x∨y] [x∨y≤[x∨y]∨z]

      [y≤[x∨y]∨z] : y ≤ ((x ∨ y) ∨ z)
      [y≤[x∨y]∨z] = ≤-trans [y≤x∨y] [x∨y≤[x∨y]∨z]
    
      [y∨z≤[x∨y]∨z] : (y ∨ z) ≤ ((x ∨ y) ∨ z)
      [y∨z≤[x∨y]∨z] = (second (second (∨-lub y z))) ((x ∨ y) ∨ z) ([y≤[x∨y]∨z] , [z≤[x∨y]∨z])

  ∧∨-absorp : (x y : carrier) → (x ∧ (x ∨ y)) ≡ x
  ∧∨-absorp x y = ≤-antisym [x∧[x∨y]≤x] [x≤x∧[x∨y]]
   where
    [x∧[x∨y]≤x] : (x ∧ (x ∨ y)) ≤ x
    [x∧[x∨y]≤x] = first (∧-glb x (x ∨ y))

    [x≤x∧[x∨y]] : x ≤ (x ∧ (x ∨ y))
    [x≤x∧[x∨y]] = (second (second (∧-glb x (x ∨ y)))) x ([x≤x] , [x≤x∨y])
     where
      [x≤x] : x ≤ x
      [x≤x] = first (≤-refl (≡-refl x))

      [x≤x∨y] : x ≤ (x ∨ y)
      [x≤x∨y] = first (∨-lub x y)
       

  ∨∧-absorp : (x y : carrier) → (x ∨ (x ∧ y)) ≡ x
  ∨∧-absorp x y = ≤-antisym [x∨[x∧y]≤x] [x≤x∨[x∧y]]
   where
    [x≤x∨[x∧y]] : x ≤ (x ∨ (x ∧ y))
    [x≤x∨[x∧y]] = first (∨-lub x (x ∧ y))

    [x∨[x∧y]≤x] : (x ∨ (x ∧ y)) ≤ x
    [x∨[x∧y]≤x] = (second (second (∨-lub x (x ∧ y)))) x ([x≤x] , [x∧y≤x])
     where
      [x≤x] : x ≤ x
      [x≤x] = first (≤-refl (≡-refl x))

      [x∧y≤x] : (x ∧ y) ≤ x
      [x∧y≤x] = first (∧-glb x y)


{-
Detour for analysis of properties of associative and commutative operations.
-}

{-
http://documents.kenyon.edu/math/SamTay.pdf
Definition 2.1.4
-}
record OrderDistributiveLattice {i} {j} {k} : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  carrier : Set i
  _≡_ : carrier → carrier → Set j
  ≡-refl : (x : carrier) → x ≡ x
  ≡-sym : (x y : carrier) → x ≡ y → y ≡ x
  ≡-trans : (x y z : carrier) → x ≡ y → y ≡ z → x ≡ z
  _≤_ : carrier → carrier → Set k
  ≤-refl : (x y : carrier) → x ≡ y → (x ≤ y) × (y ≤ x)
  ≤-antisym : (x y : carrier) → (x ≤ y) → (y ≤ x) → x ≡ y
  ≤-trans : (x y z : carrier) → x ≤ y → y ≤ z → x ≤ z
  _∧_ : carrier → carrier → carrier
  ∧-glb : (x y : carrier) → ((x ∧ y) ≤ x) × (((x ∧ y) ≤ y) × ((z : carrier) → (z ≤ x) × (z ≤ y) → (z ≤ (x ∧ y))))
  _∨_ : carrier → carrier → carrier
  ∨-lub : (x y : carrier) → (x ≤ (x ∨ y)) × ((y ≤ (x ∨ y)) × ((z : carrier) → (x ≤ z) × (y ≤ z) → ((x ∨ y) ≤ z)))
  ∧∨-distr : (x y z : carrier) → (x ∧ (y ∨ z)) ≡ ((x ∧ y) ∨ (x ∧ z))
  ∨∧-distr : (x y z : carrier) → (x ∨ (y ∧ z)) ≡ ((x ∨ y) ∧ (x ∨ z))

record OrderDistributiveLattice' {i} {j} {k} : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  lattice : OrderLattice' {i} {j} {k}
  ∧∨-distr : 
   let 
    open OrderLattice' lattice
   in
    (x y z : carrier) → (x ∧ (y ∨ z)) ≡ ((x ∧ y) ∨ (x ∧ z))
  ∨∧-distr : 
   let
    open OrderLattice' lattice
   in
    (x y z : carrier) → (x ∨ (y ∧ z)) ≡ ((x ∨ y) ∧ (x ∨ z))

record isDistributiveLattice {i} {j} {k} (O : OrderLattice' {i} {j} {k}) : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  ∧∨-distr : 
   let open OrderLattice' O
   in  (x y z : carrier) → (x ∧ (y ∨ z)) ≡ ((x ∧ y) ∨ (x ∧ z))
  ∨∧-distr :
   let open OrderLattice' O
   in  (x y z : carrier) → (x ∨ (y ∧ z)) ≡ ((x ∨ y) ∧ (x ∨ z))

left-distributes-over : ∀ {i} {j} {A : Set i} {_≡_ : A → A → Set j} {≡-equiv : isEquivalence _≡_} (f : A → A → A) (g : A → A → A) → Set (i ⊔ j)
left-distributes-over {i} {j} {A} {_≡_} {≡-equiv} f g = (x y z : A) → (f x (g y z)) ≡ (g (f x y) (f x z))

right-distributes-over : ∀ {i j} {A : Set i} {_≡_ : A → A → Set j} {≡-equiv : isEquivalence _≡_} (f : A → A → A) (g : A → A → A) → Set (i ⊔ j)
right-distributes-over {i} {j} {A} {_≡_} {≡-equiv} f g = (x y z : A) → (f (g x y) z) ≡ (g (f x z) (f y z))

record OrderDistributiveLattice'' {i} {j} {k} : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  lattice : OrderLattice' {i} {j} {k}
  ∧∨-distr : 
    let 
     open OrderLattice' lattice
     ≡-equiv : isEquivalence _≡_
     ≡-equiv = 
         record {
           ≡-refl = ≡-refl ;
           ≡-sym = ≡-sym  ;
           ≡-trans = ≡-trans
         }
    in 
     left-distributes-over {i} {k} {carrier} {_≡_} {≡-equiv} _∧_ _∨_
  ∨∧-distr :  
    let 
      open OrderLattice' lattice
      
      ≡-equiv : isEquivalence _≡_
      ≡-equiv = 
         record {
           ≡-refl = ≡-refl ;
           ≡-sym = ≡-sym ;
           ≡-trans = ≡-trans
         }
    in 
     left-distributes-over {i} {k} {carrier} {_≡_} {≡-equiv} _∨_ _∧_


record LatticeContinuity {i} {j} {k} (O : OrderLattice' {i} {j} {k}) : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  ≤-cont : 
    let
     open OrderLattice' O
    in 
     (a b c d : carrier) → (a ≡ b) → (c ≡ d) → (a ≤ c) → (b ≤ d)
  ∧-cont :
    let
     open OrderLattice' O
    in
     (a b c d : carrier) → (a ≡ b) → (c ≡ d) → (a ∧ c) ≡ (b ∧ d)
  ∨-cont :
    let
     open OrderLattice' O
    in
     (a b c d : carrier) → (a ≡ b) → (c ≡ d) → (a ∨ c) ≡ (b ∨ d)

OrderLatticesContinuous : ∀ {i} {j} {k} (O : OrderLattice' {i} {j} {k}) → LatticeContinuity {i} {j} {k} O
OrderLatticesContinuous {i} {j} {k} O =
 record {
  ≤-cont = ≤-cont ;
  ∧-cont = ∧-cont ;
  ∨-cont = ∨-cont
 }
 where
  open OrderLattice' O

  ≤-cont : (a b c d : carrier) → (a ≡ b) → (c ≡ d) → (a ≤ c) → (b ≤ d)
  ≤-cont a b c d [a≡b] [c≡d] [a≤c] = [b≤d]
   where
    [b≤a] : b ≤ a
    [b≤a] = second (≤-refl [a≡b])

    [c≤d] : c ≤ d
    [c≤d] = first (≤-refl [c≡d])

    [b≤d] : b ≤ d
    [b≤d] = ≤-trans [b≤a] (≤-trans [a≤c] [c≤d])

  ∧-cont : (a b c d : carrier) → (a ≡ b) → (c ≡ d) → (a ∧ c) ≡ (b ∧ d)
  ∧-cont a b c d [a≡b] [c≡d] = [a∧c]≡[b∧d]
   where
    [b∧d≤a∧c] : (b ∧ d) ≤ (a ∧ c)
    [b∧d≤a∧c] = (second (second (∧-glb a c))) (b ∧ d) ([b∧d≤a] , [b∧d≤c])
     where
      [b∧d≤a] : (b ∧ d) ≤ a
      [b∧d≤a] = ≤-trans [b∧d≤b] [b≤a]
       where
        [b≤a] : b ≤ a
        [b≤a] = second (≤-refl [a≡b])

        [b∧d≤b] : (b ∧ d) ≤ b
        [b∧d≤b] = first (∧-glb b d)

      [b∧d≤c] : (b ∧ d) ≤ c
      [b∧d≤c] = ≤-trans [b∧d≤d] [d≤c]
       where
        [d≤c] : d ≤ c
        [d≤c] = second (≤-refl [c≡d])

        [b∧d≤d] : (b ∧ d) ≤ d
        [b∧d≤d] = first (second (∧-glb b d))

    [a∧c≤b∧d] : (a ∧ c) ≤ (b ∧ d)
    [a∧c≤b∧d] = (second (second (∧-glb b d))) (a ∧ c ) ([a∧c≤b] , [a∧c≤d])
     where
      [a∧c≤b] : (a ∧ c) ≤ b
      [a∧c≤b] = ≤-trans [a∧c≤a] [a≤b]
       where
        [a≤b] : a ≤ b
        [a≤b] = first (≤-refl [a≡b])
 
        [a∧c≤a] : (a ∧ c) ≤ a
        [a∧c≤a] = first (∧-glb a c)

      [a∧c≤d] : (a ∧ c) ≤ d
      [a∧c≤d] = ≤-trans [a∧c≤c] [c≤d]
       where
        [c≤d] : c ≤ d
        [c≤d] = first (≤-refl [c≡d])

        [a∧c≤c] : (a ∧ c) ≤ c
        [a∧c≤c] = first (second (∧-glb a c))
      

    [a∧c]≡[b∧d] : (a ∧ c) ≡ (b ∧ d)
    [a∧c]≡[b∧d] = ≤-antisym [a∧c≤b∧d] [b∧d≤a∧c]

  ∨-cont : (a b c d : carrier) → (a ≡ b) → (c ≡ d) → (a ∨ c) ≡ (b ∨ d)
  ∨-cont a b c d [a≡b] [c≡d] = [a∨c]≡[b∨d]
   where
    [a∨c]≡[b∨d] : (a ∨ c) ≡ (b ∨ d)
    [a∨c]≡[b∨d] = ≤-antisym [a∨c≤b∨d] [b∨d≤a∨c]
     where
      [a∨c≤b∨d] : (a ∨ c) ≤ (b ∨ d)
      [a∨c≤b∨d] = (second (second (∨-lub a c))) (b ∨ d) ([a≤b∨d] , [c≤b∨d])
       where
        [a≤b] : a ≤ b
        [a≤b] = first (≤-refl [a≡b])

        [b≤b∨d] : b ≤ (b ∨ d)
        [b≤b∨d] = first (∨-lub b d)

        [a≤b∨d] : a ≤ (b ∨ d)
        [a≤b∨d] = ≤-trans [a≤b] [b≤b∨d]

        [c≤d] : c ≤ d
        [c≤d] = first (≤-refl [c≡d])
 
        [d≤b∨d] : d ≤ (b ∨ d)
        [d≤b∨d] = first (second (∨-lub b d))

        [c≤b∨d] : c ≤ (b ∨ d)
        [c≤b∨d] = ≤-trans [c≤d] [d≤b∨d]

      [b∨d≤a∨c] : (b ∨ d) ≤ (a ∨ c)
      [b∨d≤a∨c] = (second (second (∨-lub b d))) (a ∨ c) ([b≤a∨c] , [d≤a∨c])
       where
        [b≤a] : b ≤ a
        [b≤a] = second (≤-refl [a≡b])

        [a≤a∨c] : a ≤ (a ∨ c)
        [a≤a∨c] = first (∨-lub a c)

        [b≤a∨c] : b ≤ (a ∨ c)
        [b≤a∨c] = ≤-trans [b≤a] [a≤a∨c]

        [d≤c] : d ≤ c
        [d≤c] = second (≤-refl [c≡d])
 
        [c≤a∨c] : c ≤ (a ∨ c)
        [c≤a∨c] = first (second (∨-lub a c))

        [d≤a∨c] : d ≤ (a ∨ c)
        [d≤a∨c] = ≤-trans [d≤c] [c≤a∨c]
  

∨∧-distr→∧∨-distr : 
 ∀ {i} {j} {k} → (O : OrderLattice' {i} {j} {k}) → 
 let
  open OrderLattice' O

  ≡-equiv : isEquivalence _≡_
  ≡-equiv = 
       record {
         ≡-refl = OrderLattice'.≡-refl O ;
         ≡-sym = OrderLattice'.≡-sym O ;
         ≡-trans = OrderLattice'.≡-trans O
       }
 in
  left-distributes-over {i} {k} {carrier} {_≡_} {≡-equiv} _∨_ _∧_ →
  left-distributes-over {i} {k} {carrier} {_≡_} {≡-equiv} _∧_ _∨_
∨∧-distr→∧∨-distr {i} {j} {k} O [∨∧-distr] a b c = proof
 where
  open OrderLattice' O

  O-isAlgebraicLattice : isAlgebraicLattice'' carrier _≡_ (record {≡-refl = ≡-refl ; ≡-sym = ≡-sym ; ≡-trans = ≡-trans }) _∧_ _∨_
  O-isAlgebraicLattice = OrderLattice→isAlgebraicLattice O

  open isAlgebraicLattice'' O-isAlgebraicLattice

  O-isContinuous : LatticeContinuity O
  O-isContinuous = OrderLatticesContinuous O

  open LatticeContinuity O-isContinuous




  [a∧b]∨[a∧c]≡[[a∧b]∨a]∧[[a∧b]∨c] : ((a ∧ b) ∨ (a ∧ c)) ≡ (((a ∧ b) ∨ a) ∧ ((a ∧ b) ∨ c))
  [a∧b]∨[a∧c]≡[[a∧b]∨a]∧[[a∧b]∨c] = [∨∧-distr] (a ∧ b) a c


  [[a∧b]∨a]∧[[a∧b]∨c]≡[[a∧b]∨a]∧[[c∨a]∧[c∨b]] : (((a ∧ b) ∨ a) ∧ ((a ∧ b) ∨ c)) ≡ (((a ∧ b) ∨ a) ∧ ((c ∨ a) ∧ (c ∨ b)))
  [[a∧b]∨a]∧[[a∧b]∨c]≡[[a∧b]∨a]∧[[c∨a]∧[c∨b]] = ∧-cont ((a ∧ b) ∨ a) ((a ∧ b) ∨ a) ((a ∧ b) ∨ c) ((c ∨ a) ∧ (c ∨ b)) (≡-refl ((a ∧ b) ∨ a)) [[a∧b]∨c]≡[[c∨a]∧[c∨b]]
   where
    [[a∧b]∨c]≡[c∨[a∧b]] : ((a ∧ b) ∨ c) ≡ (c ∨ (a ∧ b))
    [[a∧b]∨c]≡[c∨[a∧b]] = ∨-comm (a ∧ b) c

    [c∨[a∧b]]≡[[c∨a]∧[c∨b]] : (c ∨ (a ∧ b)) ≡ ((c ∨ a) ∧ (c ∨ b))
    [c∨[a∧b]]≡[[c∨a]∧[c∨b]] = [∨∧-distr] c a b

    [[a∧b]∨c]≡[[c∨a]∧[c∨b]] : ((a ∧ b) ∨ c) ≡ ((c ∨ a) ∧ (c ∨ b))
    [[a∧b]∨c]≡[[c∨a]∧[c∨b]] = ≡-trans [[a∧b]∨c]≡[c∨[a∧b]] [c∨[a∧b]]≡[[c∨a]∧[c∨b]]



  [[a∧b]∨a]∧[[c∨a]∧[c∨b]]≡a∧[[c∨a]∧[c∨b]] : (((a ∧ b) ∨ a) ∧ ((c ∨ a) ∧ (c ∨ b))) ≡ (a ∧ ((c ∨ a) ∧ (c ∨ b)))
  [[a∧b]∨a]∧[[c∨a]∧[c∨b]]≡a∧[[c∨a]∧[c∨b]] = ∧-cont ((a ∧ b) ∨ a) a ((c ∨ a) ∧ (c ∨ b)) ((c ∨ a) ∧ (c ∨ b)) [[a∧b]∨a]≡a (≡-refl ((c ∨ a) ∧ (c ∨ b)))
   where
    [[a∧b]∨a]≡[a∨[a∧b]] : ((a ∧ b) ∨ a) ≡ (a ∨ (a ∧ b))
    [[a∧b]∨a]≡[a∨[a∧b]] = ∨-comm (a ∧ b) a

    [a∨[a∧b]]≡a : (a ∨ (a ∧ b)) ≡ a
    [a∨[a∧b]]≡a = ∨∧-absorp a b

    [[a∧b]∨a]≡a : ((a ∧ b) ∨ a) ≡ a
    [[a∧b]∨a]≡a = ≡-trans [[a∧b]∨a]≡[a∨[a∧b]] [a∨[a∧b]]≡a


  a∧[[c∨a]∧[c∨b]]≡[a∧[c∨a]]∧[c∨b] : (a ∧ ((c ∨ a) ∧ (c ∨ b))) ≡ ((a ∧ (c ∨ a)) ∧ (c ∨ b))
  a∧[[c∨a]∧[c∨b]]≡[a∧[c∨a]]∧[c∨b] = ∧-assoc a (c ∨ a) (c ∨ b)

  [a∧[c∨a]]∧[c∨b]≡a∧[c∨b] : ((a ∧ (c ∨ a)) ∧ (c ∨ b)) ≡ (a ∧ (c ∨ b))
  [a∧[c∨a]]∧[c∨b]≡a∧[c∨b] = ∧-cont (a ∧ (c ∨ a)) a (c ∨ b) (c ∨ b) [a∧[c∨a]]≡a (≡-refl (c ∨ b))
   where
    [a∧[c∨a]]≡[a∧[a∨c]] : (a ∧ (c ∨ a)) ≡ (a ∧ (a ∨ c))
    [a∧[c∨a]]≡[a∧[a∨c]] = ∧-cont a a (c ∨ a) (a ∨ c) (≡-refl a) (∨-comm c a)

    [a∧[a∨c]]≡a : (a ∧ (a ∨ c)) ≡ a
    [a∧[a∨c]]≡a = ∧∨-absorp a c

    [a∧[c∨a]]≡a : (a ∧ (c ∨ a)) ≡ a
    [a∧[c∨a]]≡a = ≡-trans [a∧[c∨a]]≡[a∧[a∨c]] [a∧[a∨c]]≡a


  a∧[c∨b]≡a∧[b∨c] : (a ∧ (c ∨ b)) ≡ (a ∧ (b ∨ c))
  a∧[c∨b]≡a∧[b∨c] = ∧-cont a a (c ∨ b) (b ∨ c) (≡-refl a) (∨-comm c b)

  proof : (a ∧ (b ∨ c)) ≡ ((a ∧ b) ∨ (a ∧ c))
  proof = ≡-sym (≡-trans [a∧b]∨[a∧c]≡[[a∧b]∨a]∧[[a∧b]∨c] 
                (≡-trans [[a∧b]∨a]∧[[a∧b]∨c]≡[[a∧b]∨a]∧[[c∨a]∧[c∨b]]
                (≡-trans [[a∧b]∨a]∧[[c∨a]∧[c∨b]]≡a∧[[c∨a]∧[c∨b]]
                (≡-trans a∧[[c∨a]∧[c∨b]]≡[a∧[c∨a]]∧[c∨b]
                (≡-trans [a∧[c∨a]]∧[c∨b]≡a∧[c∨b] a∧[c∨b]≡a∧[b∨c]
                )))))


                     

∧∨-distr→∨∧-distr :
 ∀ {i} {j} {k} → (O : OrderLattice' {i} {j} {k}) → 
 let
  open OrderLattice' O

  ≡-equiv : isEquivalence _≡_
  ≡-equiv = 
       record {
         ≡-refl = OrderLattice'.≡-refl O ;
         ≡-sym = OrderLattice'.≡-sym O ;
         ≡-trans = OrderLattice'.≡-trans O
       }
 in
  left-distributes-over {i} {k} {carrier} {_≡_} {≡-equiv} _∧_ _∨_ →
  left-distributes-over {i} {k} {carrier} {_≡_} {≡-equiv} _∨_ _∧_
∧∨-distr→∨∧-distr {i} {j} {k} O [∧∨-distr] a b c = proof
 where
  open OrderLattice' O

  O-isAlgebraicLattice : isAlgebraicLattice'' carrier _≡_ (record {≡-refl = ≡-refl ; ≡-sym = ≡-sym ; ≡-trans = ≡-trans }) _∧_ _∨_
  O-isAlgebraicLattice = OrderLattice→isAlgebraicLattice O

  open isAlgebraicLattice'' O-isAlgebraicLattice

  O-isContinuous : LatticeContinuity O
  O-isContinuous = OrderLatticesContinuous O

  open LatticeContinuity O-isContinuous




  [a∨b]∧[a∨c]≡[[a∨b]∧a]∨[[a∨b]∧c] : ((a ∨ b) ∧ (a ∨ c)) ≡ (((a ∨ b) ∧ a) ∨ ((a ∨ b) ∧ c))
  [a∨b]∧[a∨c]≡[[a∨b]∧a]∨[[a∨b]∧c] = [∧∨-distr] (a ∨ b) a c


  [[a∨b]∧a]∨[[a∨b]∧c]≡[[a∨b]∧a]∨[[c∧a]∨[c∧b]] : (((a ∨ b) ∧ a) ∨ ((a ∨ b) ∧ c)) ≡ (((a ∨ b) ∧ a) ∨ ((c ∧ a) ∨ (c ∧ b)))
  [[a∨b]∧a]∨[[a∨b]∧c]≡[[a∨b]∧a]∨[[c∧a]∨[c∧b]] = ∨-cont ((a ∨ b) ∧ a) ((a ∨ b) ∧ a) ((a ∨ b) ∧ c) ((c ∧ a) ∨ (c ∧ b)) (≡-refl ((a ∨ b) ∧ a)) [[a∨b]∧c]≡[[c∧a]∨[c∧b]]
   where
    [[a∨b]∧c]≡[c∧[a∨b]] : ((a ∨ b) ∧ c) ≡ (c ∧ (a ∨ b))
    [[a∨b]∧c]≡[c∧[a∨b]] = ∧-comm (a ∨ b) c

    [c∧[a∨b]]≡[[c∧a]∨[c∧b]] : (c ∧ (a ∨ b)) ≡ ((c ∧ a) ∨ (c ∧ b))
    [c∧[a∨b]]≡[[c∧a]∨[c∧b]] = [∧∨-distr] c a b

    [[a∨b]∧c]≡[[c∧a]∨[c∧b]] : ((a ∨ b) ∧ c) ≡ ((c ∧ a) ∨ (c ∧ b))
    [[a∨b]∧c]≡[[c∧a]∨[c∧b]] = ≡-trans [[a∨b]∧c]≡[c∧[a∨b]] [c∧[a∨b]]≡[[c∧a]∨[c∧b]]



  [[a∨b]∧a]∨[[c∧a]∨[c∧b]]≡a∨[[c∧a]∨[c∧b]] : (((a ∨ b) ∧ a) ∨ ((c ∧ a) ∨ (c ∧ b))) ≡ (a ∨ ((c ∧ a) ∨ (c ∧ b)))
  [[a∨b]∧a]∨[[c∧a]∨[c∧b]]≡a∨[[c∧a]∨[c∧b]] = ∨-cont ((a ∨ b) ∧ a) a ((c ∧ a) ∨ (c ∧ b)) ((c ∧ a) ∨ (c ∧ b)) [[a∨b]∧a]≡a (≡-refl ((c ∧ a) ∨ (c ∧ b)))
   where
    [[a∨b]∧a]≡[a∧[a∨b]] : ((a ∨ b) ∧ a) ≡ (a ∧ (a ∨ b))
    [[a∨b]∧a]≡[a∧[a∨b]] = ∧-comm (a ∨ b) a

    [a∧[a∨b]]≡a : (a ∧ (a ∨ b)) ≡ a
    [a∧[a∨b]]≡a = ∧∨-absorp a b

    [[a∨b]∧a]≡a : ((a ∨ b) ∧ a) ≡ a
    [[a∨b]∧a]≡a = ≡-trans [[a∨b]∧a]≡[a∧[a∨b]] [a∧[a∨b]]≡a


  a∨[[c∧a]∨[c∧b]]≡[a∨[c∧a]]∨[c∧b] : (a ∨ ((c ∧ a) ∨ (c ∧ b))) ≡ ((a ∨ (c ∧ a)) ∨ (c ∧ b))
  a∨[[c∧a]∨[c∧b]]≡[a∨[c∧a]]∨[c∧b] = ∨-assoc a (c ∧ a) (c ∧ b)

  [a∨[c∧a]]∨[c∧b]≡a∨[c∧b] : ((a ∨ (c ∧ a)) ∨ (c ∧ b)) ≡ (a ∨ (c ∧ b))
  [a∨[c∧a]]∨[c∧b]≡a∨[c∧b] = ∨-cont (a ∨ (c ∧ a)) a (c ∧ b) (c ∧ b) [a∨[c∧a]]≡a (≡-refl (c ∧ b))
   where
    [a∨[c∧a]]≡[a∨[a∧c]] : (a ∨ (c ∧ a)) ≡ (a ∨ (a ∧ c))
    [a∨[c∧a]]≡[a∨[a∧c]] = ∨-cont a a (c ∧ a) (a ∧ c) (≡-refl a) (∧-comm c a)

    [a∨[a∧c]]≡a : (a ∨ (a ∧ c)) ≡ a
    [a∨[a∧c]]≡a = ∨∧-absorp a c

    [a∨[c∧a]]≡a : (a ∨ (c ∧ a)) ≡ a
    [a∨[c∧a]]≡a = ≡-trans [a∨[c∧a]]≡[a∨[a∧c]] [a∨[a∧c]]≡a


  a∨[c∧b]≡a∨[b∧c] : (a ∨ (c ∧ b)) ≡ (a ∨ (b ∧ c))
  a∨[c∧b]≡a∨[b∧c] = ∨-cont a a (c ∧ b) (b ∧ c) (≡-refl a) (∧-comm c b)

  proof : (a ∨ (b ∧ c)) ≡ ((a ∨ b) ∧ (a ∨ c))
  proof = ≡-sym (≡-trans [a∨b]∧[a∨c]≡[[a∨b]∧a]∨[[a∨b]∧c] 
                (≡-trans [[a∨b]∧a]∨[[a∨b]∧c]≡[[a∨b]∧a]∨[[c∧a]∨[c∧b]]
                (≡-trans [[a∨b]∧a]∨[[c∧a]∨[c∧b]]≡a∨[[c∧a]∨[c∧b]]
                (≡-trans a∨[[c∧a]∨[c∧b]]≡[a∨[c∧a]]∨[c∧b]
                (≡-trans [a∨[c∧a]]∨[c∧b]≡a∨[c∧b] a∨[c∧b]≡a∨[b∧c]
                )))))
  
{-
http://documents.kenyon.edu/math/SamTay.pdf
Definition 2.1.5
-}
record isBounded {i} {j} {k} (O : OrderLattice' {i} {j} {k}) : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  max : OrderLattice'.carrier O
  max-is-max :
   let
    open OrderLattice' O
   in
    (x : carrier) → (x ≤ max)
  min : OrderLattice'.carrier O
  min-is-min :
   let
    open OrderLattice' O
   in
    (x : carrier) → (min ≤ x)

isComplemented : ∀ {i j k} (O : OrderLattice' {i} {j} {k}) → Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k))
isComplemented {i} {j} {k} O = 
 ∃ b ∈ isBounded O , (
  let 
   open isBounded b
  in
   (x : carrier) → ∃ y ∈ carrier , (((x ∨ y) ≡ max) × ((x ∧ y) ≡ min))
 )
 where
  open OrderLattice' O
  
{-
http://documents.kenyon.edu/math/SamTay.pdf
Proposition 2.1.6
-}
isTrivialLattice : ∀ {i j k} → (O : OrderLattice' {i} {j} {k}) → (c : isComplemented O) → Set (i ⊔  k)
isTrivialLattice {i} {j} {k} O c = (x : carrier) → (x ≡ max) ⊹ (x ≡ min)
 where
  open OrderLattice' O
  open isBounded (π₁ c)

record isTrivialLattice' {i} {j} {k} (O : OrderLattice' {i} {j} {k}) : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  bounded : isBounded O
  trivial : 
   let open OrderLattice' O
       open isBounded bounded
   in  (x : carrier) → (x ≡ max) ⊹ (x ≡ min)  

[A→C]→[B→C]→[A⊹B→C] : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (A → C) → (B → C) → (A ⊹ B) → C
[A→C]→[B→C]→[A⊹B→C] f g (inl a) = f a
[A→C]→[B→C]→[A⊹B→C] f g (inr b) = g b

every-totally-ordered-complemented-lattice-is-trivial : 
 ∀ {i j k} → (O : OrderLattice' {i} {j} {k}) → (c : isComplemented O) → 
 let 
  open OrderLattice' O
  open isBounded (π₁ c)
 in
  ((x y : carrier) → ((x ≤ y) ⊹ (y ≤ x))) → isTrivialLattice' O
every-totally-ordered-complemented-lattice-is-trivial {i} {j} {k} O c t = 
 record {
  bounded = π₁ c ;
  trivial = trivial 
 }
 where
  open OrderLattice' O
  open isBounded (π₁ c)
  ~ : carrier → carrier
  ~ z = π₁ ((π₂ c) z)

  O-isAlgebraicLattice : isAlgebraicLattice'' carrier _≡_ (record {≡-refl = ≡-refl ; ≡-sym = ≡-sym ; ≡-trans = ≡-trans }) _∧_ _∨_
  O-isAlgebraicLattice = OrderLattice→isAlgebraicLattice O

  open isAlgebraicLattice'' O-isAlgebraicLattice


  x∨y≡y : (x y : carrier) → (x ≤ y) → (x ∨ y) ≡ y
  x∨y≡y x y [x≤y] = first ((first (x≤y-iff-[x∨y≡y-and-x∧y≡x] O x y)) [x≤y])

  x∧y≡x : (x y : carrier) → (x ≤ y) → (x ∧ y) ≡ x
  x∧y≡x x y [x≤y] = second ((first (x≤y-iff-[x∨y≡y-and-x∧y≡x] O x y)) [x≤y])
 
 
  trivial : (x : carrier) → (x ≡ max) ⊹ (x ≡ min)
  trivial x = proof
   where
    x-comp : ∃ ~x ∈ carrier , (((x ∨ ~x) ≡ max) × ((x ∧ ~x) ≡ min))
    x-comp = (π₂ c) x

    ~x : carrier
    ~x = π₁ x-comp

    x∨~x≡max : (x ∨ ~x) ≡ max
    x∨~x≡max = first (π₂ x-comp)

    x∧~x≡min : (x ∧ ~x) ≡ min
    x∧~x≡min = second (π₂ x-comp)
    
    x≤~x-or-~x≤x : (x ≤ ~x) ⊹ (~x ≤ x)
    x≤~x-or-~x≤x = t x ~x

    x≤~x→x≡min : (x ≤ ~x) → (x ≡ max) ⊹ (x ≡ min)
    x≤~x→x≡min [x≤~x] = inr x≡min
     where
      x∧~x≡x : (x ∧ ~x) ≡ x
      x∧~x≡x = x∧y≡x x ~x [x≤~x]

      x≡min : (x ≡ min)
      x≡min = ≡-trans (≡-sym x∧~x≡x) x∧~x≡min

    ~x≤x→x≡max : (~x ≤ x) → (x ≡ max) ⊹ (x ≡ min)
    ~x≤x→x≡max [~x≤x] = inl x≡max
     where
      ~x∨x≡x : (~x ∨ x) ≡ x
      ~x∨x≡x = x∨y≡y ~x x [~x≤x]

      x≡max : (x ≡ max)
      x≡max = ≡-trans (≡-sym ~x∨x≡x) (≡-trans (∨-comm ~x x) x∨~x≡max)
 

    proof : (x ≡ max) ⊹ (x ≡ min)
    proof = [A→C]→[B→C]→[A⊹B→C] ~x≤x→x≡max x≤~x→x≡min (t ~x x)

{-
http://documents.kenyon.edu/math/SamTay.pdf
Proposition 2.1.7
-}
distributive-lattices-have-unique-complements : 
 ∀ {i j k} (O : OrderLattice' {i} {j} {k}) → (dist : isDistributiveLattice O) → (bnd : isBounded O) → 
 let open OrderLattice' O
     open isDistributiveLattice dist
     open isBounded bnd
 in  (x : carrier) → (y y' : carrier) → (((x ∨ y) ≡ max) × ((x ∧ y) ≡ min)) → (((x ∨ y') ≡ max) × ((x ∧ y') ≡ min)) → y ≡ y'
distributive-lattices-have-unique-complements 
 {i} {j} {k} O dist bnd x y y' y-compl y'-compl
 = y≡y'
 where
  open OrderLattice' O
 
  O-isAlgebraicLattice : isAlgebraicLattice'' carrier _≡_ (record {≡-refl = ≡-refl ; ≡-sym = ≡-sym ; ≡-trans = ≡-trans }) _∧_ _∨_
  O-isAlgebraicLattice = OrderLattice→isAlgebraicLattice O

  open isAlgebraicLattice'' O-isAlgebraicLattice


  O-isContinuous : LatticeContinuity O
  O-isContinuous = OrderLatticesContinuous O

  open LatticeContinuity O-isContinuous

  open isDistributiveLattice dist
  open isBounded bnd

  lemma : (~x₁ ~x₂ : carrier) → (((x ∨ ~x₁) ≡ max) × ((x ∧ ~x₁) ≡ min)) → (((x ∨ ~x₂) ≡ max) × ((x ∧ ~x₂) ≡ min)) → ~x₂ ≤ ~x₁
  lemma ~x₁ ~x₂ p₁ p₂ = ~x₂≤~x₁
   where

    [~x₁≡~x₁∨min] : ~x₁ ≡ (~x₁ ∨ min)
    [~x₁≡~x₁∨min] = ≡-trans (≡-sym ((first ((first (x≤y-iff-[x∨y≡y-and-x∧y≡x] O min ~x₁)) (min-is-min ~x₁))))) (∨-comm min ~x₁)

    [~x₁∨min≡~x₁∨[x∧~x₂]] : (~x₁ ∨ min) ≡ (~x₁ ∨ (x ∧ ~x₂))
    [~x₁∨min≡~x₁∨[x∧~x₂]] = ∨-cont ~x₁ ~x₁ min (x ∧ ~x₂) (≡-refl ~x₁) (≡-sym (second p₂))

    [~x₁∨[x∧~x₂]≡[~x₁∨x]∧[~x₁∨~x₂]] : (~x₁ ∨ (x ∧ ~x₂)) ≡ ((~x₁ ∨ x) ∧ (~x₁ ∨ ~x₂))
    [~x₁∨[x∧~x₂]≡[~x₁∨x]∧[~x₁∨~x₂]] = ∨∧-distr ~x₁ x ~x₂

    [[~x₁∨x]∧[~x₁∨~x₂]≡max∧[~x₁∨~x₂]] : ((~x₁ ∨ x) ∧ (~x₁ ∨ ~x₂)) ≡ (max ∧ (~x₁ ∨ ~x₂))
    [[~x₁∨x]∧[~x₁∨~x₂]≡max∧[~x₁∨~x₂]] = ∧-cont (~x₁ ∨ x) max (~x₁ ∨ ~x₂) (~x₁ ∨ ~x₂) (≡-trans (∨-comm ~x₁ x) (first p₁)) (≡-refl (~x₁ ∨ ~x₂))

    [max∧[~x₁∨~x₂]≡~x₁∨~x₂] : (max ∧ (~x₁ ∨ ~x₂)) ≡ (~x₁ ∨ ~x₂)
    [max∧[~x₁∨~x₂]≡~x₁∨~x₂] = ≡-trans (∧-comm max (~x₁ ∨ ~x₂)) (second ((first (x≤y-iff-[x∨y≡y-and-x∧y≡x] O (~x₁ ∨ ~x₂) max)) (max-is-max (~x₁ ∨ ~x₂))))

    ~x₁≡~x₁∨~x₂ : ~x₁ ≡ (~x₁ ∨ ~x₂)
    ~x₁≡~x₁∨~x₂ =  ≡-trans [~x₁≡~x₁∨min]
                (≡-trans [~x₁∨min≡~x₁∨[x∧~x₂]]
                (≡-trans [~x₁∨[x∧~x₂]≡[~x₁∨x]∧[~x₁∨~x₂]]
                (≡-trans [[~x₁∨x]∧[~x₁∨~x₂]≡max∧[~x₁∨~x₂]] [max∧[~x₁∨~x₂]≡~x₁∨~x₂])))

    x₁∨~x₂≤~x₁ : (~x₁ ∨ ~x₂) ≤ ~x₁
    x₁∨~x₂≤~x₁ = second (≤-refl ~x₁≡~x₁∨~x₂)

    ~x₂≤~x₁∨~x₂ : ~x₂ ≤ (~x₁ ∨ ~x₂)
    ~x₂≤~x₁∨~x₂ = first (second (∨-lub ~x₁ ~x₂))

    ~x₂≤~x₁ : ~x₂ ≤ ~x₁
    ~x₂≤~x₁ = ≤-trans ~x₂≤~x₁∨~x₂ x₁∨~x₂≤~x₁

  y≡y' : y ≡ y'
  y≡y' = ≤-antisym (lemma y' y y'-compl y-compl) (lemma y y' y-compl y'-compl)

{-
http://documents.kenyon.edu/math/SamTay.pdf
Definition 2.1.8
-}

record BooleanAlgebra {i} {j} {k} : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  lattice : OrderLattice' {i} {j} {k}
  complemented : isComplemented lattice
  distributive : isDistributiveLattice lattice

{-
Start of section 2.2
-}

record start-of-2,2 {i} {j} {k} (B : BooleanAlgebra {i} {j} {k}) : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  B1 :
   let open BooleanAlgebra B 
       open OrderLattice' lattice 
   in ((x y : carrier) → (x ∨ y) ≡ (y ∨ x)) × 
      ((x y : carrier) → ((x ∧ y) ≡ (y ∧ x)))
  B2 : 
   let open BooleanAlgebra B
       open OrderLattice' lattice
   in ((x y z : carrier) → ((x ∨ (y ∨ z)) ≡ ((x ∨ y) ∨ z))) × 
      ((x y z : carrier) → (x ∧ (y ∧ z)) ≡ ((x ∧ y) ∧ z))
  B3 : 
   let open BooleanAlgebra B
       open OrderLattice' lattice
   in ((x y : carrier) → ((x ∨ (x ∧ y)) ≡ x)) × 
      ((x y : carrier) → (x ∧ (x ∨ y)) ≡ x)
  B4 : 
   let open BooleanAlgebra B
       open OrderLattice' lattice
   in ((x y z : carrier) → ((x ∧ (y ∨ z)) ≡ ((x ∧ y) ∨ (x ∧ z)))) × 
      ((x y z : carrier) → (x ∨ (y ∧ z)) ≡ ((x ∨ y) ∧ (x ∨ z)))
  B5 : 
   let open BooleanAlgebra B
       open OrderLattice' lattice
       open isBounded (π₁ complemented)
   in (x : carrier) → ∃ y ∈ carrier , (((x ∨ y) ≡ max) × ((x ∧ y) ≡ min))



proof-of-start-of-2,2 : ∀ {i j k} (B : BooleanAlgebra {i} {j} {k}) → start-of-2,2 B
proof-of-start-of-2,2 {i} {j} {k} B = 
 record {
  B1 = B1 ;
  B2 = B2 ;
  B3 = B3 ;
  B4 = B4 ;
  B5 = B5
 }
 where
  open BooleanAlgebra B
 
  O : OrderLattice' {i} {j} {k}
  O = lattice

  open OrderLattice' O

  O-isAlgebraicLattice : isAlgebraicLattice'' carrier _≡_ (record {≡-refl = ≡-refl ; ≡-sym = ≡-sym ; ≡-trans = ≡-trans }) _∧_ _∨_
  O-isAlgebraicLattice = OrderLattice→isAlgebraicLattice O

  open isAlgebraicLattice'' O-isAlgebraicLattice


  open isDistributiveLattice distributive
  open isBounded (π₁ complemented)    


  B1 : ((x y : carrier) → (x ∨ y) ≡ (y ∨ x)) × 
      ((x y : carrier) → ((x ∧ y) ≡ (y ∧ x)))
  B1 = (∨-comm , ∧-comm)
  B2 : ((x y z : carrier) → ((x ∨ (y ∨ z)) ≡ ((x ∨ y) ∨ z))) × 
      ((x y z : carrier) → (x ∧ (y ∧ z)) ≡ ((x ∧ y) ∧ z))
  B2 = (∨-assoc , ∧-assoc)
  B3 : ((x y : carrier) → ((x ∨ (x ∧ y)) ≡ x)) × 
      ((x y : carrier) → (x ∧ (x ∨ y)) ≡ x)
  B3 = (∨∧-absorp , ∧∨-absorp) 
  B4 : ((x y z : carrier) → ((x ∧ (y ∨ z)) ≡ ((x ∧ y) ∨ (x ∧ z)))) × 
      ((x y z : carrier) → (x ∨ (y ∧ z)) ≡ ((x ∨ y) ∧ (x ∨ z)))
  B4 = (∧∨-distr , ∨∧-distr)
  B5 : (x : carrier) → ∃ y ∈ carrier , (((x ∨ y) ≡ max) × ((x ∧ y) ≡ min))
  B5 = π₂ complemented


{-
http://documents.kenyon.edu/math/SamTay.pdf
Theorem 2.2.1
-}

record BooleanStructure {i} {j} {k} : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  carrier : Set i
  _∨_ : carrier → carrier → carrier
  _∧_ : carrier → carrier → carrier
  * : carrier → carrier
  min : carrier
  max : carrier
  _≡_ : carrier → carrier → Set k
  ≡-refl : (x : carrier) → x ≡ x
  ≡-sym : {x y : carrier} → x ≡ y → y ≡ x
  ≡-trans : {x y z : carrier} → x ≡ y → y ≡ z → x ≡ z 
  ∨-comm : (x y : carrier) → (x ∨ y) ≡ (y ∨ x)
  ∧-comm : (x y : carrier) → (x ∧ y) ≡ (y ∧ x)
  ∨-assoc : (x y z : carrier) → (x ∨ (y ∨ z)) ≡ ((x ∨ y) ∨ z)
  ∧-assoc : (x y z : carrier) → (x ∧ (y ∧ z)) ≡ ((x ∧ y) ∧ z)
  ∨∧-absorp : (x y : carrier) → (x ∨ (x ∧ y)) ≡ x
  ∧∨-absorp : (x y : carrier) → (x ∧ (x ∨ y)) ≡ x
  ∨∧-distr : (x y z : carrier) → (x ∨ (y ∧ z)) ≡ ((x ∨ y) ∧ (x ∨ z))
  ∧∨-distr : (x y z : carrier) → (x ∧ (y ∨ z)) ≡ ((x ∧ y) ∨ (x ∧ z)) 
  *-∨-compl : (x : carrier) → (x ∨ (* x)) ≡ max
  *-∧-compl : (x : carrier) → (x ∧ (* x)) ≡ min


≤' : 
 ∀ {i} {k} (L : AlgebraicLattice {i} {k}) →
 let open AlgebraicLattice L
 in carrier → carrier → Set k
≤' {i} {k} L x y = criteria
 where
  open AlgebraicLattice L
  
  criteria : Set k
  criteria = (x ∧ y) ≡ x


record AlgebraicLatticeContinuity {i} {k} (L : AlgebraicLattice {i} {k}) : Set (i ⊔ k)
 where
  field
   ∧-cont : 
    let open AlgebraicLattice L
    in (a b c d : carrier) → a ≡ b → c ≡ d → (a ∧ c) ≡ (b ∧ d)
   ∨-cont :
    let open AlgebraicLattice L
    in (a b c d : carrier) → a ≡ b → c ≡ d → (a ∨ c) ≡ (b ∨ c)

≡-continuity : ∀ {i j k l} → Set ((((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) ⊔ (lsuc l))
≡-continuity {i} {j} {k} {l} = (A : Set i) (B : Set j) → (_≡A_ : A → A → Set k) → (≡A-equiv : isEquivalence _≡A_) → (_≡B_ : B → B → Set l) → (≡B-equiv : isEquivalence _≡B_) → (f : A → B) → (a a' : A) → a ≡A a' → (f a) ≡B (f a')

data ⊤i (i : Level) : Set i where
 ●i : ⊤i i

record ⊥i (i : Level) : Set i where
 field
  dummy : ⊤i i
  cons : ⊥

data Boolᵢ (i : Level) : Set i where
 trueᵢ : Boolᵢ i
 falseᵢ : Boolᵢ i

¬[≡-continuous] : (i j k l : Level) → ≡-continuity {i} {j} {k} {l} → ⊥
¬[≡-continuous] i j k l continuity = proof 
 where
  _≡₁_ : Boolᵢ i → Boolᵢ i → Set k
  x ≡₁ y = ⊤i k
  ≡₁-equiv : isEquivalence {i} {k} {Boolᵢ i} _≡₁_
  ≡₁-equiv = 
   record {
    ≡-refl = ≡₁-refl ;
    ≡-sym = λ {x} {y} p₁ → ≡₁-sym {x} {y} p₁ ;
    ≡-trans = λ {x} {y} {z} p₁ p₂ → ≡₁-trans {x} {y} {z} p₁ p₂
   }
   where
    [x≡y==⊤] : (x y : Boolᵢ i) → (x ≡₁ y) == ⊤i k
    [x≡y==⊤] x y = refl

    ≡₁-refl : (x : Boolᵢ i) → x ≡₁ x
    ≡₁-refl x = [A==B]→[A→B] (==-sym ([x≡y==⊤] x x)) ●i

    ≡₁-sym : {x y : Boolᵢ i} → (p₁ : x ≡₁ y) → y ≡₁ x
    ≡₁-sym {x} {y} p₁ = [A==B]→[A→B] (==-sym ([x≡y==⊤] y x)) ●i

    ≡₁-trans : {x y z : Boolᵢ i} → x ≡₁ y → y ≡₁ z → x ≡₁ z
    ≡₁-trans {x} {y} {z} p₁ p₂ = [A==B]→[A→B] (==-sym ([x≡y==⊤] x z)) ●i

  _≡₂_ : Boolᵢ j → Boolᵢ j → Set l
  trueᵢ ≡₂ trueᵢ = ⊤i l
  trueᵢ ≡₂ falseᵢ = ⊥i l
  falseᵢ ≡₂ trueᵢ = ⊥i l
  falseᵢ ≡₂ falseᵢ = ⊤i l


  ≡₂-equiv : isEquivalence _≡₂_
  ≡₂-equiv =
   record {
    ≡-refl = ≡₂-refl ;
    ≡-sym = λ {x} {y} p₁ → ≡₂-sym {x} {y} p₁ ;
    ≡-trans = λ {x} {y} {z} p₁ p₂ → ≡₂-trans {x} {y} {z} p₁ p₂
   }
   where
    ≡₂-refl : (x : Boolᵢ j) → x ≡₂ x
    ≡₂-refl trueᵢ = ●i
    ≡₂-refl falseᵢ = ●i

    ≡₂-sym : {x y : Boolᵢ j} → x ≡₂ y → y ≡₂ x
    ≡₂-sym {trueᵢ}  {trueᵢ}  p₁ = ●i
    ≡₂-sym {trueᵢ}  {falseᵢ} p₁ = ω (⊥i.cons p₁)
    ≡₂-sym {falseᵢ} {trueᵢ}  p₁ = ω (⊥i.cons p₁)
    ≡₂-sym {falseᵢ} {falseᵢ} p₁ = ●i

    ≡₂-trans : {x y z : Boolᵢ j} → x ≡₂ y → y ≡₂ z → x ≡₂ z
    ≡₂-trans {trueᵢ}  {trueᵢ}  {trueᵢ}  p₁            p₂            = ●i
    ≡₂-trans {trueᵢ}  {falseᵢ} {trueᵢ}  p₁            p₂            = ●i 
    ≡₂-trans {trueᵢ}  {trueᵢ}  {falseᵢ} p₁            [true≡₂false] = ω (⊥i.cons [true≡₂false])
    ≡₂-trans {trueᵢ}  {falseᵢ} {falseᵢ} [true≡₂false] p₂            = ω (⊥i.cons [true≡₂false])
    ≡₂-trans {falseᵢ} {trueᵢ}  {falseᵢ} p₁            p₂            = ●i
    ≡₂-trans {falseᵢ} {falseᵢ} {falseᵢ} p₁            p₂            = ●i 
    ≡₂-trans {falseᵢ} {trueᵢ}  {trueᵢ}  [false≡₂true] p₂            = ω (⊥i.cons [false≡₂true])
    ≡₂-trans {falseᵢ} {falseᵢ} {trueᵢ}  p₁            [false≡₂true] = ω (⊥i.cons [false≡₂true])

  id : Boolᵢ i → Boolᵢ j
  id trueᵢ = trueᵢ
  id falseᵢ = falseᵢ 

  true≡₁false : trueᵢ ≡₁ falseᵢ
  true≡₁false = ●i

  true≢₂false : (trueᵢ ≡₂ falseᵢ) → ⊥
  true≢₂false [true≡₂false] = ⊥i.cons [true≡₂false]


  true≡₂false : trueᵢ ≡₂ falseᵢ
  true≡₂false = continuity (Boolᵢ i) (Boolᵢ j) _≡₁_ ≡₁-equiv _≡₂_ ≡₂-equiv id trueᵢ falseᵢ true≡₁false

  proof : ⊥
  proof = true≢₂false true≡₂false

data Nat : Set where
 zero : Nat
 suc : Nat → Nat

x==0⊹x==suc-k : (x : Nat) → (x == zero) ⊹ (∃ k ∈ Nat , (x == (suc k)))
x==0⊹x==suc-k zero = inl refl
x==0⊹x==suc-k (suc x) = inr (x , refl)


plus : Nat → Nat → Nat
plus zero y    = y
plus (suc x) y = suc (plus x y)

mult : Nat → Nat → Nat
mult zero y    = zero
mult (suc x) y = plus y (mult x y)

_divides_ : Nat → Nat → Set
x divides y = ∃ k ∈ Nat , ((mult k x) == y) 

x+0==x-ind : (x : Nat) → plus x zero == x → plus (suc x) zero == (suc x)
x+0==x-ind x [x+0==x] = [suc-x+0==suc-x]
 where
  [1+x]+0==1+[x+0] : plus (suc x) zero == suc (plus x zero)
  [1+x]+0==1+[x+0] = refl

  1+[x+0]==1+x : suc (plus x zero) == suc x
  1+[x+0]==1+x = [x==y]→[fx==fy] suc (plus x zero) x [x+0==x]

  [suc-x+0==suc-x] : plus (suc x) zero == suc x
  [suc-x+0==suc-x] = ==-trans [1+x]+0==1+[x+0] 1+[x+0]==1+x




x+0==x : (x : Nat) → plus x zero == x
x+0==x zero = refl
x+0==x (suc x) = x+0==x-ind x (x+0==x x)

1*x==x : (x : Nat) → mult (suc zero) x == x
1*x==x x = proof
 where
  1*x==x+0*x : mult (suc zero) x == plus x (mult zero x)
  1*x==x+0*x = refl
  
  0*x==0 : mult zero x == zero
  0*x==0 = refl
 
  x+0*x==x+0 : plus x (mult zero x) == plus x zero
  x+0*x==x+0 = [x==y]→[fx==fy] (plus x) (mult zero x) zero 0*x==0

  [x+0==x] : plus x zero == x
  [x+0==x] = x+0==x x
  
  proof : mult (suc zero) x == x
  proof = ==-trans 1*x==x+0*x (==-trans x+0*x==x+0 [x+0==x])

x*0==0-ind : (x : Nat) → mult x zero == zero → mult (suc x) zero == zero
x*0==0-ind x x*0==0 = proof
 where
  l1 : mult (suc x) zero == plus zero (mult x zero)
  l1 = refl

  l2 : plus zero (mult x zero) == mult x zero
  l2 = refl

  proof : mult (suc x) zero == zero
  proof = ==-trans l1 (==-trans l2 x*0==0)

x*0==0 : (x : Nat) → mult x zero == zero
x*0==0 zero = refl
x*0==0 (suc x) = x*0==0-ind x (x*0==0 x)


¬[suc-x==0] : (x : Nat) → suc x == zero → ⊥
¬[suc-x==0] x [suc-x==zero] = proof
 where
  f : Nat → Bool
  f zero = false
  f (suc x) = true

  [true==false] : true == false
  [true==false] = [x==y]→[fx==fy] f (suc x) zero [suc-x==zero]

  proof : ⊥
  proof = true≠false [true==false]

¬[0-divides-suc-x] : (x : Nat) → zero divides (suc x) → ⊥
¬[0-divides-suc-x] x (k , k*0==suc-x) = proof
 where
  l1 : mult k zero == zero
  l1 = x*0==0 k

  l2 : suc x == zero
  l2 = ==-trans (==-sym k*0==suc-x) l1 

  proof : ⊥
  proof = ¬[suc-x==0] x l2


x+suc-y==suc[x+y]-ind : (x y : Nat) → plus x (suc y) == suc (plus x y) → plus (suc x) (suc y) == suc (plus (suc x) y)
x+suc-y==suc[x+y]-ind x y [x+suc-y==suc[x+y]] = proof
 where
  [suc-x+suc-y==suc[x+suc-y]] : plus (suc x) (suc y) == suc (plus x (suc y))
  [suc-x+suc-y==suc[x+suc-y]] = refl

  [suc[x+suc-y]==suc[suc[x+y]]] : suc (plus x (suc y)) == suc (suc (plus x y))
  [suc[x+suc-y]==suc[suc[x+y]]] = [x==y]→[fx==fy] suc (plus x (suc y)) (suc (plus x y)) [x+suc-y==suc[x+y]]

  [suc[suc[x+y]]==suc[suc-x+y]] : suc (suc (plus x y)) == suc (plus (suc x) y)
  [suc[suc[x+y]]==suc[suc-x+y]] = refl

  proof : plus (suc x) (suc y) == suc (plus (suc x) y)
  proof = ==-trans [suc-x+suc-y==suc[x+suc-y]] (==-trans [suc[x+suc-y]==suc[suc[x+y]]] [suc[suc[x+y]]==suc[suc-x+y]])


x+suc-y==suc[x+y] : (x y : Nat) → plus x (suc y) == suc (plus x y)
x+suc-y==suc[x+y] zero y = proof
 where
  [0+suc-y==suc-y] : plus zero (suc y) == suc y
  [0+suc-y==suc-y] = refl

  [y==0+y] : y == plus zero y
  [y==0+y] = refl

  [suc-y==suc[0+y]] : suc y == suc (plus zero y)
  [suc-y==suc[0+y]] = [x==y]→[fx==fy] suc y (plus zero y) [y==0+y]

  proof : plus zero (suc y) == suc (plus zero y)
  proof = ==-trans [0+suc-y==suc-y] [suc-y==suc[0+y]]
x+suc-y==suc[x+y] (suc x) y = x+suc-y==suc[x+y]-ind x y (x+suc-y==suc[x+y] x y)


x+y==y+x-ind : (x y : Nat) → plus x y == plus y x → plus (suc x) (suc y) == plus (suc y) (suc x)
x+y==y+x-ind x y [x+y==y+x] = proof
 where
  [suc-x+suc-y==suc[x+suc-y]] : plus (suc x) (suc y) == suc (plus x (suc y))
  [suc-x+suc-y==suc[x+suc-y]] = refl

  [x+suc-y==suc[x+y]] : plus x (suc y) == suc (plus x y)
  [x+suc-y==suc[x+y]] = x+suc-y==suc[x+y] x y

  [suc[x+suc-y]==suc[suc[x+y]]] : suc (plus x (suc y)) == suc (suc (plus x y))
  [suc[x+suc-y]==suc[suc[x+y]]] = [x==y]→[fx==fy] suc (plus x (suc y)) (suc (plus x y)) [x+suc-y==suc[x+y]]

  [suc-y+suc-x==suc[y+suc-x]] : plus (suc y) (suc x) == suc (plus y (suc x))
  [suc-y+suc-x==suc[y+suc-x]] = refl

  [y+suc-x==suc[y+x]] : plus y (suc x) == suc (plus y x)
  [y+suc-x==suc[y+x]] = x+suc-y==suc[x+y] y x

  [suc[y+suc-x]==suc[suc[y+x]]] : suc (plus y (suc x)) == suc (suc (plus y x))
  [suc[y+suc-x]==suc[suc[y+x]]] = [x==y]→[fx==fy] suc (plus y (suc x)) (suc (plus y x)) [y+suc-x==suc[y+x]]

  [suc[suc[x+y]]==suc[suc[y+x]]] : suc (suc (plus x y)) == suc (suc (plus y x))
  [suc[suc[x+y]]==suc[suc[y+x]]] = [x==y]→[fx==fy] (λ x → suc (suc x)) (plus x y) (plus y x) [x+y==y+x]

  proof : plus (suc x) (suc y) == plus (suc y) (suc x)
  proof =  ==-trans [suc-x+suc-y==suc[x+suc-y]] 
          (==-trans [suc[x+suc-y]==suc[suc[x+y]]] 
          (==-trans [suc[suc[x+y]]==suc[suc[y+x]]]
          (==-trans (==-sym [suc[y+suc-x]==suc[suc[y+x]]]) (==-sym [suc-y+suc-x==suc[y+suc-x]]))))

x+y==y+x : (x y : Nat) → plus x y == plus y x
x+y==y+x zero zero = refl
x+y==y+x zero (suc x) = proof
 where
  [suc-x+0==suc-x] : plus (suc x) zero == (suc x)
  [suc-x+0==suc-x] = x+0==x (suc x)

  [0+suc-x==suc-x] : plus zero (suc x) == (suc x)
  [0+suc-x==suc-x] = refl

  proof : plus zero (suc x) == plus (suc x) zero
  proof = ==-trans [0+suc-x==suc-x] (==-sym [suc-x+0==suc-x])
x+y==y+x (suc x) zero = proof
 where
  [suc-x+0==suc-x] : plus (suc x) zero == (suc x)
  [suc-x+0==suc-x] = x+0==x (suc x)

  [0+suc-x==suc-x] : plus zero (suc x) == suc x
  [0+suc-x==suc-x] = refl

  proof : plus (suc x) zero == plus zero (suc x)
  proof = ==-trans [suc-x+0==suc-x] (==-sym [0+suc-x==suc-x])

x+y==y+x (suc x) (suc y) = x+y==y+x-ind x y (x+y==y+x x y)

x*y==0→x==0⊹y==0 : (x y : Nat) → mult x y == zero → (x == zero) ⊹ (y == zero)
x*y==0→x==0⊹y==0 zero x refl = inl refl
x*y==0→x==0⊹y==0 (suc x) zero [suc-x*0==0] = inr refl
x*y==0→x==0⊹y==0 (suc x) (suc y) [suc-x*suc-y==0] = ω (¬[suc-x==0] (plus y (mult x (suc y))) [suc-x*suc-y==0])

proof-by-elimination : ∀ {i j} {A : Set i} {B : Set j} → A ⊹ B → (A → ⊥) → B
proof-by-elimination {i} {j} {A} {B} (inl a) ¬A = ω (¬A a)
proof-by-elimination {i} {j} {A} {B} (inr b) ¬A = b



x+[y+z]==[x+y]+z-ind : (x y z : Nat) → plus x (plus y z) == plus (plus x y) z → plus (suc x) (plus (suc y) (suc z)) == plus (plus (suc x) (suc y)) (suc z)
x+[y+z]==[x+y]+z-ind x y z [x+[y+z]==[x+y]+z] = proof
 where
  l1 : plus (suc x) (plus (suc y) (suc z)) == suc (plus x (suc (plus y (suc z))))
  l1 = refl
  
  l2 : suc (plus x (suc (plus y (suc z)))) == suc (suc (plus x (plus y (suc z))))
  l2 = [x==y]→[fx==fy] suc (plus x (suc (plus y (suc z)))) (suc (plus x (plus y (suc z)))) (x+suc-y==suc[x+y] x (plus y (suc z)))

  l3 : suc (suc (plus x (plus y (suc z)))) == suc (suc (suc (plus x (plus y z))))
  l3 = [x==y]→[fx==fy] (λ q → suc (suc q)) (plus x (plus y (suc z))) (suc (plus x (plus y z))) (==-trans ([x==y]→[fx==fy] (plus x) (plus y (suc z)) (suc (plus y z)) (x+suc-y==suc[x+y] y z)) (x+suc-y==suc[x+y] x (plus y z)))

  l4 : plus (plus (suc x) (suc y)) (suc z) == suc (suc (suc (plus (plus x y) z)))
  l4 = l4-proof
   where
    l4-1 : suc (plus (plus x (suc y)) (suc z)) == suc (suc (plus (plus x (suc y)) z))
    l4-1 = [x==y]→[fx==fy] suc (plus (plus x (suc y)) (suc z)) (suc (plus (plus x (suc y)) z)) (x+suc-y==suc[x+y] (plus x (suc y)) z)
    

    l4-2 : suc (suc (plus (plus x (suc y)) z)) == suc (suc (suc (plus (plus x y) z)))
    l4-2 = [x==y]→[fx==fy] (λ q → suc (suc (plus q z))) (plus x (suc y)) (suc (plus x y)) (x+suc-y==suc[x+y] x y) 

    l4-proof = ==-trans l4-1 l4-2

  l5 : suc (suc (suc (plus x (plus y z)))) == suc (suc (suc (plus (plus x y) z)))
  l5 = [x==y]→[fx==fy] (λ q → suc (suc (suc q))) (plus x (plus y z)) (plus (plus x y) z) [x+[y+z]==[x+y]+z]

  proof = ==-trans l1 (==-trans l2 (==-trans l3 (==-trans l5 (==-sym l4))))

x+[y+z]==[x+y]+z : (x y z : Nat) → plus x (plus y z) == plus (plus x y) z
x+[y+z]==[x+y]+z zero x y = refl
x+[y+z]==[x+y]+z (suc x) zero z = ==-trans refl (==-sym ([x==y]→[fx==fy] (λ q → plus q z) (plus (suc x) zero) (suc x) (x+0==x (suc x))))
x+[y+z]==[x+y]+z (suc x) (suc y) zero = ==-trans ([x==y]→[fx==fy] (plus (suc x)) (plus (suc y) zero) (suc y) (x+0==x (suc y))) (==-sym (x+0==x (plus (suc x) (suc y))))
x+[y+z]==[x+y]+z (suc x) (suc y) (suc z) = x+[y+z]==[x+y]+z-ind x y z (x+[y+z]==[x+y]+z x y z)

x*1==x-ind : (x : Nat) → mult x (suc zero) == x → mult (suc x) (suc zero) == suc x
x*1==x-ind x [x*1==x] = proof
 where
  l1 : mult (suc x) (suc zero) == suc (mult x (suc zero))
  l1 = refl

  l2 : suc (mult x (suc zero)) == suc x
  l2 = [x==y]→[fx==fy] suc (mult x (suc zero)) x [x*1==x]

  proof : mult (suc x) (suc zero) == suc x
  proof = ==-trans l1 l2 


x*1==x : (x : Nat) → mult x (suc zero) == x
x*1==x zero = refl
x*1==x (suc x) = x*1==x-ind x (x*1==x x)




-- 5) Multiplication left-distributes over addition :
1-5-base<a,0> : (b c : Nat) → mult zero (plus b c) == plus (mult zero b) (mult zero c)
1-5-base<a,0> b c = refl 


1-5-ind<a,𝕤> : (a b c : Nat) → mult a (plus b c) == plus (mult a b) (mult a c) → mult (suc a) (plus b c) == plus (mult (suc a) b) (mult (suc a) c)
1-5-ind<a,𝕤> a b c [a*[b+c]≡a*b+a*c] = proof
 where
  {- (suc a) * (b + c) == (b + c) + (a * (b + c)) == (b + c) + (a*b + a*c) -}
  l1 : mult (suc a) (plus b c) == plus (plus b c) (plus (mult a b) (mult a c))
  l1 = [x==y]→[fx==fy] (plus (plus b c)) (mult a (plus b c)) (plus (mult a b) (mult a c)) [a*[b+c]≡a*b+a*c] 

  {- (suc a)*b + (suc a)*c == b + (a*b + (c + a*c)) -}
  l2 : plus (mult (suc a) b) (mult (suc a) c) == plus b (plus (mult a b) (plus c (mult a c)))
  l2 = ==-sym (x+[y+z]==[x+y]+z b (mult a b) (plus c (mult a c)))

  {- a*b + (c + a*c) == c + (a*b + a*c) -}
  l3 : plus (mult a b) (plus c (mult a c)) == plus c (plus (mult a b) (mult a c))
  l3 = ==-trans (x+y==y+x (mult a b) (plus c (mult a c))) (==-trans (==-sym (x+[y+z]==[x+y]+z c (mult a c) (mult a b))) ([x==y]→[fx==fy] (plus c) (plus (mult a c) (mult a b)) (plus (mult a b) (mult a c)) (x+y==y+x (mult a c) (mult a b))))

  
  l4 : plus b (plus (mult a b) (plus c (mult a c))) == plus (plus b c) (plus (mult a b) (mult a c))
  l4 = ==-trans ([x==y]→[fx==fy] (plus b) (plus (mult a b) (plus c (mult a c))) (plus c (plus (mult a b) (mult a c))) l3) (x+[y+z]==[x+y]+z b c (plus (mult a b) (mult a c)))

  proof : mult (suc a) (plus b c) == plus (mult (suc a) b) (mult (suc a) c)
  proof = ==-trans l1 (==-sym (==-trans l2 l4)) 


-- final step
a*[b+c]≡a*b+a*c : (a b c : Nat) → mult a (plus b c) == plus (mult a b) (mult a c)
a*[b+c]≡a*b+a*c zero b c = 1-5-base<a,0> b c
a*[b+c]≡a*b+a*c (suc a) b c = 1-5-ind<a,𝕤> a b c (a*[b+c]≡a*b+a*c a b c)


-- 6) Multiplication right-distributes over addition
-- a=0 base case
[0+𝕤b]*c≡0*c+𝕤b*c : (b c : Nat) → (mult (plus zero (suc b)) c) == plus (mult zero c) (mult (suc b) c)
[0+𝕤b]*c≡0*c+𝕤b*c b c = refl


-- b=0 base case
[𝕤a+0]*c≡𝕤a*c+0*c : (a c : Nat) → (mult (plus (suc a) zero) c) == (plus (mult (suc a) c) (mult zero c)) 
[𝕤a+0]*c≡𝕤a*c+0*c a c = proof
 where
  l1 : (plus (mult (suc a) c) zero) == (mult (suc a) c)
  l1 = x+0==x (mult (suc a) c)

  
  l2 : (mult (plus (suc a) zero) c) == (mult (suc a) c) 
  l2 = [x==y]→[fx==fy] (λ q → mult q c) (plus (suc a) zero) (suc a) (x+0==x (suc a))

  proof = ==-trans l2 (==-sym l1)


-- ab-inductive
[[a+b]*c≡a*c+b*c]→[[𝕤a+𝕤b]*c≡𝕤a*c+𝕤b*c] : 
 (a b c : Nat) → mult (plus a b) c == plus (mult a c) (mult b c) → mult (plus (suc a) (suc b)) c == plus (mult (suc a) c) (mult (suc b) c)
[[a+b]*c≡a*c+b*c]→[[𝕤a+𝕤b]*c≡𝕤a*c+𝕤b*c] a b c [[a+b]*c≡a*c+b*c] = proof
 where
  l1 : plus (mult (suc a) c) (mult (suc b) c) == plus (plus c c) (plus (mult a c) (mult b c))
  l1 = ==-trans (x+[y+z]==[x+y]+z (plus c (mult a c)) c (mult b c)) (==-trans ([x==y]→[fx==fy] (λ q → plus q (mult b c)) (plus (plus c (mult a c)) c) (plus (plus c c) (mult a c)) (==-trans (==-sym (x+[y+z]==[x+y]+z c (mult a c) c)) (==-trans ([x==y]→[fx==fy] (plus c) (plus (mult a c) c) (plus c (mult a c)) (x+y==y+x (mult a c) c)) (x+[y+z]==[x+y]+z c c (mult a c))))) (==-sym (x+[y+z]==[x+y]+z (plus c c) (mult a c) (mult b c))))

  l2 : mult (plus (suc a) (suc b)) c == mult (suc (suc (plus a b))) c 
  l2 = [x==y]→[fx==fy] (λ q → (mult q c)) (plus (suc a) (suc b)) (suc (suc (plus a b))) ([x==y]→[fx==fy] suc (plus a (suc b)) (suc (plus a b)) (x+suc-y==suc[x+y] a b))

  l3 : mult (plus (suc a) (suc b)) c == plus (plus c c) (plus (mult a c) (mult b c))
  l3 = ==-trans l2 (==-trans (x+[y+z]==[x+y]+z c c (mult (plus a b) c)) ([x==y]→[fx==fy] (plus (plus c c)) (mult (plus a b) c) (plus (mult a c) (mult b c)) [[a+b]*c≡a*c+b*c]))

  
  proof = ==-trans l3 (==-sym l1)


-- final step
[a+b]*c≡a*c+b*c : (a b c : Nat) → mult (plus a b) c == plus (mult a c) (mult b c)
[a+b]*c≡a*c+b*c zero zero c = refl
[a+b]*c≡a*c+b*c (suc a) zero c = [𝕤a+0]*c≡𝕤a*c+0*c a c
[a+b]*c≡a*c+b*c zero (suc b) c = refl
[a+b]*c≡a*c+b*c (suc a) (suc b) c = [[a+b]*c≡a*c+b*c]→[[𝕤a+𝕤b]*c≡𝕤a*c+𝕤b*c] a b c ([a+b]*c≡a*c+b*c a b c)


-- 7) Lemma: (a * x ) * y ≡ x * (a * y)
-- base case
[0*x]*y≡x*[0*y] : (x y : Nat) → mult (mult zero x) y == mult x (mult zero y)
[0*x]*y≡x*[0*y] x y = [[0*x]*y≡x*[0*y]]
 where
-- Defs :

  [0*x≡0] : mult zero x == zero
  [0*x≡0] = refl

  [0*y≡0] : mult zero y == zero
  [0*y≡0] = refl
 
  [[0*x]*y≡0] : mult (mult zero x) y == zero
  [[0*x]*y≡0] = [x==y]→[fx==fy] (λ q → mult q y) (mult zero x) zero refl

  [x*0≡x*[0*y]] : mult x zero == mult x (mult zero y)
  [x*0≡x*[0*y]] = [x==y]→[fx==fy] (mult x) zero (mult zero y) refl
  
  [0≡x*[0*y]] : zero == mult x (mult zero y)
  [0≡x*[0*y]] = ==-trans (==-sym (x*0==0 x)) [x*0≡x*[0*y]]

  [[0*x]*y≡x*[0*y]] : mult (mult zero x) y == mult x (mult zero y)
  [[0*x]*y≡x*[0*y]] = ==-trans [[0*x]*y≡0] [0≡x*[0*y]]
  

-- inductive step
[[a*x]*y≡x*[a*y]]-ind<𝕤,a> :
 (x y a : Nat) → mult (mult a x) y == mult x (mult a y) → mult (mult (suc a) x) y == mult x (mult (suc a) y)
[[a*x]*y≡x*[a*y]]-ind<𝕤,a> x y a [[a*x]*y≡x*[a*y]] = proof
 where
  l1 : mult x (mult (suc a) y) == mult x (plus y (mult a y))
  l1 = [x==y]→[fx==fy] (mult x) (mult (suc a) y) (plus y (mult a y)) refl

  l2 : mult x (plus y (mult a y)) == plus (mult x y) (mult x (mult a y))
  l2 = a*[b+c]≡a*b+a*c x y (mult a y)

  l3 : mult (mult (suc a) x) y == plus (mult x y) (mult (mult a x) y)
  l3 = [a+b]*c≡a*c+b*c x (mult a x) y
  
  l4 : plus (mult x y) (mult x (mult a y)) == plus (mult x y) (mult (mult a x) y) 
  l4 = [x==y]→[fx==fy] (plus (mult x y)) (mult x (mult a y)) (mult (mult a x) y) (==-sym [[a*x]*y≡x*[a*y]])

  proof = ==-trans l3 (==-sym (==-trans l1 (==-trans l2 l4)))

-- final step
[a*x]*y≡x*[a*y] : (x y a : Nat) → mult (mult a x) y == mult x (mult a y)
[a*x]*y≡x*[a*y] x y zero = [0*x]*y≡x*[0*y] x y
[a*x]*y≡x*[a*y] x y (suc a) = [[a*x]*y≡x*[a*y]]-ind<𝕤,a> x y a ([a*x]*y≡x*[a*y] x y a)





-- 8) Multiplication is commutative
x*y≡y*x : (x y : Nat) → mult x y == mult y x
x*y≡y*x x y = [x*y≡y*x]
 where
  
  [[x*y]*1≡y*[x*1]] : mult (mult x y) (suc zero) == mult y (mult x (suc zero))
  [[x*y]*1≡y*[x*1]] = [a*x]*y≡x*[a*y] y (suc zero) x

  
  [[x*y]*1≡x*y] : mult (mult x y) (suc zero) == mult x y
  [[x*y]*1≡x*y] = x*1==x (mult x y)

  
  [x*1≡x] : mult x (suc zero) == x
  [x*1≡x] = x*1==x x

  
  [y*[x*1]≡y*x] : mult y (mult x (suc zero)) == mult y x
  [y*[x*1]≡y*x] = [x==y]→[fx==fy] (mult y) (mult x (suc zero)) x [x*1≡x]

  [x*y≡y*x] : mult x y == mult y x
  [x*y≡y*x] = ==-trans (==-sym [[x*y]*1≡x*y]) (==-trans [[x*y]*1≡y*[x*1]] [y*[x*1]≡y*x])
  

-- 9) (a * b) * c ≡ a * (b * c)  ; Multiplication is associative
[a*b]*c≡a*[b*c] : (a b c : Nat) → mult (mult a b) c == mult a (mult b c)
[a*b]*c≡a*[b*c] a b c = [[a*b]*c≡a*[b*c]]
 where
  [a*b≡b*a] : mult a b == mult b a
  [a*b≡b*a] = x*y≡y*x a b

  [[a*b]*c≡[b*a]*c] : mult (mult a b) c == mult (mult b a) c
  [[a*b]*c≡[b*a]*c] = [x==y]→[fx==fy] (λ q → mult q c) (mult a b) (mult b a) (x*y≡y*x a b)

  [[b*a]*c≡a*[b*c]] : mult (mult b a) c == mult a (mult b c)
  [[b*a]*c≡a*[b*c]] = [a*x]*y≡x*[a*y] a c b

  [[a*b]*c≡a*[b*c]] : mult (mult a b) c == mult a (mult b c)
  [[a*b]*c≡a*[b*c]] = ==-trans [[a*b]*c≡[b*a]*c] [[b*a]*c≡a*[b*c]]



⊹-comm : ∀ {i j} {A : Set i} {B : Set j} → A ⊹ B → B ⊹ A
⊹-comm (inl a) = inr a
⊹-comm (inr b) = inl b


x*suc-y==0→x==0 : (x y : Nat) → mult x (suc y) == zero → x == zero
x*suc-y==0→x==0 x y [x*suc-y==zero] = proof-by-elimination (⊹-comm (x*y==0→x==0⊹y==0 x (suc y) [x*suc-y==zero])) (¬[suc-x==0] y)


pred : Nat → Nat
pred zero = zero
pred (suc x) = x

suc-injective : (x x' : Nat) → suc x == suc x' → x == x'
suc-injective x y [suc-x==suc-y] = [x==y]→[fx==fy] pred (suc x) (suc y) [suc-x==suc-y]


x+y==y→x==0-ind : (x y : Nat) → (plus x y == y → x == zero) → (plus x (suc y) == (suc y) → x == zero)
x+y==y→x==0-ind x y assump [x+suc-y==suc-y] = proof
 where
  l1 : plus x (suc y) == suc (plus x y)
  l1 = x+suc-y==suc[x+y] x y

  l2 : plus x y == y
  l2 = suc-injective (plus x y) y (==-trans (==-sym l1) [x+suc-y==suc-y])

  proof = assump l2

x+y==y→x==0-ind₂ : (x y : Nat) → plus x (suc y) == (suc y) → plus x y == y
x+y==y→x==0-ind₂ x y [x+suc-y==suc-y] = proof
 where
  l1 : plus x (suc y) == suc (plus x y)
  l1 = x+suc-y==suc[x+y] x y

  l2 : suc (plus x y) == suc y
  l2 = ==-trans (==-sym l1) [x+suc-y==suc-y]

  proof : plus x y == y
  proof = suc-injective (plus x y) y l2

suc-x≠x-ind : (x : Nat) → suc x ≠ x → (suc (suc x)) ≠ (suc x)
suc-x≠x-ind x [suc-x≠x] [suc-suc-x==suc-x] = disproof
 where
  disproof : ⊥
  disproof = [suc-x≠x] ([x==y]→[fx==fy] pred (suc (suc x)) (suc x) [suc-suc-x==suc-x])

suc-x≠x : (x : Nat) → suc x ≠ x
suc-x≠x zero = ¬[suc-x==0] zero
suc-x≠x (suc x) = suc-x≠x-ind x (suc-x≠x x)

[suc-x+y≠y]-ind : (x y : Nat) → plus (suc x) y ≠ y → plus (suc (suc x)) y ≠ y
[suc-x+y≠y]-ind x y [suc-x+y≠y] [suc-suc-x+y==y] = x≮x y ((suc x) , [suc-suc-x+y==y]) 
 where
  l1 : plus (suc (suc x)) y == suc (plus (suc x) y)
  l1 = refl

  l2 : suc (plus (suc x) y) == y
  l2 = ==-trans (==-sym l1) [suc-suc-x+y==y]

  l3 : suc (plus (suc x) y) == suc (plus (suc x) (plus (suc (suc x)) y))
  l3 = [x==y]→[fx==fy] (λ q → (suc (plus (suc x) q))) y (plus (suc (suc x)) y) (==-sym [suc-suc-x+y==y])

  [suc-x<suc-y]→[x<y] : (x y : Nat) → (∃ k ∈ Nat , (plus (suc k) (suc x) == suc y)) → (∃ k ∈ Nat , (plus (suc k) x == y))
  [suc-x<suc-y]→[x<y] x y (k , [suc-k+suc-x==suc-y]) = (k , l6)
   where
    l4 : plus (suc k) (suc x) == suc (plus (suc k) x)
    l4 = x+suc-y==suc[x+y] (suc k) x

    l5 : suc (plus (suc k) x) == suc y
    l5 = ==-trans (==-sym l4) [suc-k+suc-x==suc-y]

    l6 : plus (suc k) x == y
    l6 = suc-injective (plus (suc k) x) y l5


  0≮0 : (∃ x ∈ Nat , (plus (suc x) zero == zero)) → ⊥
  0≮0 (x , [suc-x+0==0]) = ¬[suc-x==0] x (==-trans (==-sym (x+0==x (suc x))) [suc-x+0==0])

  x≮x-ind : (x : Nat) → ((∃ k ∈ Nat , (plus (suc k) x == x)) → ⊥) → (∃ k ∈ Nat , (plus (suc k) (suc x) == (suc x))) → ⊥
  x≮x-ind x ¬[x<x] [suc-x<suc-x] = ¬[x<x] ([suc-x<suc-y]→[x<y] x x [suc-x<suc-x])

  
  x≮x : (x : Nat) → (∃ k ∈ Nat , (plus (suc k) x == x)) → ⊥
  x≮x zero [0<0] = 0≮0 [0<0]
  x≮x (suc x) = x≮x-ind x (x≮x x)


[suc-x+y≠y] : (x y : Nat) → plus (suc x) y ≠ y
[suc-x+y≠y] zero y [suc-zero+y==y] = suc-x≠x y [suc-zero+y==y]
[suc-x+y≠y] (suc x) y = [suc-x+y≠y]-ind x y ([suc-x+y≠y] x y)

x+y==y→x==0-ind₃ : (x y : Nat) → plus (suc x) y == y → plus x y == y
x+y==y→x==0-ind₃ x y [suc-x+y==y] = ω ([suc-x+y≠y] x y [suc-x+y==y])

x+y==y→x==0 : (x y : Nat) → plus x y == y → x == zero
x+y==y→x==0 zero y refl = refl
x+y==y→x==0 (suc x) y [suc-x+y==y] = ω ([suc-x+y≠y] x y [suc-x+y==y])

x+y==x→y==0 : (x y : Nat) → plus x y == x → y == zero
x+y==x→y==0 x y [x+y==x] = proof
 where
  l1 : plus x y == plus y x
  l1 = x+y==y+x x y

  l2 : plus y x == x
  l2 = ==-trans (==-sym l1) [x+y==x]
  
  proof = x+y==y→x==0 y x l2

x*y==y→x==1⊹y==0 : (x y : Nat) → mult x y == y → (x == (suc zero)) ⊹ (y == zero)
x*y==y→x==1⊹y==0 x zero p₁ = inr refl
x*y==y→x==1⊹y==0 zero (suc y) p₁ = ω (¬[suc-x==0] y (==-sym p₁))
x*y==y→x==1⊹y==0 (suc x) (suc y) p₁ = proof
 where
  l1 : mult (suc x) (suc y) == plus (suc y) (mult x (suc y))
  l1 = refl

  l2 : plus (suc y) (mult x (suc y)) == suc (plus y (mult x (suc y)))
  l2 = refl

  l3 : mult x (suc y) == zero
  l3 = x+y==x→y==0 (suc y) (mult x (suc y)) p₁

  l4 : x == zero
  l4 = proof-by-elimination (⊹-comm (x*y==0→x==0⊹y==0 x (suc y) l3)) (¬[suc-x==0] y)

  l5 : suc x == suc zero
  l5 = [x==y]→[fx==fy] suc x zero l4

  proof  = inl l5


¬A→¬B→¬[A⊹B] : ∀ {i j} {A : Set i} {B : Set j} → (A → ⊥) → (B → ⊥) → (A ⊹ B) → ⊥
¬A→¬B→¬[A⊹B] {i} {j} {A} {B} ¬A ¬B (inl a) = ¬A a
¬A→¬B→¬[A⊹B] {i} {j} {A} {B} ¬A ¬B (inr b) = ¬B b


x*y==1→[x==1]×[y==1] : (x y : Nat) → mult x y == suc zero → (x == suc zero) × (y == suc zero)
x*y==1→[x==1]×[y==1] x zero [x*0==1] = ω (¬[suc-x==0] zero (==-sym (==-trans (==-sym (x*0==0 x)) [x*0==1])))
x*y==1→[x==1]×[y==1] zero y [0*y==1] = ω (¬[suc-x==0] zero (==-sym [0*y==1]))
x*y==1→[x==1]×[y==1] (suc zero) (suc zero) [1*1==1] = (refl , refl)
x*y==1→[x==1]×[y==1] (suc (suc x)) (suc zero) [suc-suc-x*1==1] = proof
 where
  l1 : mult (suc (suc x)) (suc zero) == suc (suc x)
  l1 = x*1==x (suc (suc x))

  l2 : suc (suc x) == (suc zero)
  l2 = ==-trans (==-sym l1) [suc-suc-x*1==1]

  l3 : suc x == zero
  l3 = suc-injective (suc x) zero l2

  proof = ω (¬[suc-x==0] x l3)
x*y==1→[x==1]×[y==1] (suc zero) (suc (suc y)) [1*suc-suc-y==1] = proof
 where
  l1 : mult (suc zero) (suc (suc y)) == suc (suc y)
  l1 = x+0==x (suc (suc y))

  l2 : suc (suc y) == suc zero
  l2 = ==-trans (==-sym l1) [1*suc-suc-y==1]

  l3 : suc y == zero
  l3 = suc-injective (suc y) zero l2

  proof = ω (¬[suc-x==0] y l3)
x*y==1→[x==1]×[y==1] (suc (suc x)) (suc (suc y)) [suc-suc-x*suc-suc-y==1] = proof
 where
  l1 : mult (suc (suc x)) (suc (suc y)) == suc (suc (plus y (mult (suc x) (suc (suc y)))))
  l1 = refl

  l2 : suc (suc (plus y (mult (suc x) (suc (suc y))))) == suc zero
  l2 = ==-trans (==-sym l1) [suc-suc-x*suc-suc-y==1]

  l3 : suc (plus y (mult (suc x) (suc (suc y)))) == zero
  l3 = suc-injective (suc (plus y (mult (suc x) (suc (suc y))))) zero l2

  proof = ω (¬[suc-x==0] (plus y (mult (suc x) (suc (suc y)))) l3)


divides-refl : (x : Nat) → x divides x
divides-refl x = (suc zero , 1*x==x x)


divides-antisym : (x y : Nat) → x divides y → y divides x → x == y
divides-antisym zero zero 0|0 0|0' = refl
divides-antisym zero (suc y) 0|suc-y suc-y|0 = ω (¬[0-divides-suc-x] y 0|suc-y)
divides-antisym (suc x) zero suc-x|0 0|suc-x = ω (¬[0-divides-suc-x] x 0|suc-x)
divides-antisym (suc x) (suc y) (k₁ , k₁*[suc-x]==[suc-y]) (k₂ , k₂*[suc-y]==[suc-x]) = proof
 where
  
  [suc-y==[k₁*k₂]*suc-y] : suc y == mult (mult k₁ k₂) (suc y)
  [suc-y==[k₁*k₂]*suc-y] = ==-trans (==-sym k₁*[suc-x]==[suc-y]) (==-trans ([x==y]→[fx==fy] (mult k₁) (suc x) (mult k₂ (suc y)) (==-sym k₂*[suc-y]==[suc-x])) (==-sym ([a*b]*c≡a*[b*c] k₁ k₂ (suc y))))

  [k₁*k₂]==1⊹suc-y==0 : (mult k₁ k₂ == suc zero) ⊹ (suc y == zero)
  [k₁*k₂]==1⊹suc-y==0 = x*y==y→x==1⊹y==0 (mult k₁ k₂) (suc y) (==-sym [suc-y==[k₁*k₂]*suc-y])

  k₁*k₂==1 : mult k₁ k₂ == suc zero
  k₁*k₂==1 = proof-by-elimination (⊹-comm [k₁*k₂]==1⊹suc-y==0) (¬[suc-x==0] y)

  [k₁==1]×[k₂==1] : (k₁ == suc zero) × (k₂ == suc zero)
  [k₁==1]×[k₂==1] = x*y==1→[x==1]×[y==1] k₁ k₂ k₁*k₂==1
 
  k₁*[suc-x]==suc-x : mult k₁ (suc x) == suc x
  k₁*[suc-x]==suc-x = ==-trans ([x==y]→[fx==fy] (λ q → mult q (suc x)) k₁ (suc zero) (first [k₁==1]×[k₂==1])) (x+0==x (suc x))

  proof = ==-trans (==-sym k₁*[suc-x]==suc-x) k₁*[suc-x]==[suc-y]





-- needs associativity of multiplication
divides-trans : (x y z : Nat) → x divides y → y divides z → x divides z
divides-trans x y z (k₁ , k₁*x==y) (k₂ , k₂*y==z) = ((mult k₂ k₁) , [[k₂*k₁]*x==z])
 where
  [k₂*[k₁*x]==z] : (mult k₂ (mult k₁ x)) == z
  [k₂*[k₁*x]==z] = ==-trans (==-sym ([x==y]→[fx==fy] (mult k₂) y (mult k₁ x) (==-sym k₁*x==y))) k₂*y==z

  [[k₂*k₁]*x==z] : (mult (mult k₂ k₁) x) == z
  [[k₂*k₁]*x==z] = ==-trans ([a*b]*c≡a*[b*c] k₂ k₁ x) [k₂*[k₁*x]==z]


data four : Set where
 0' : four
 1' : four
 2' : four
 3' : four

four-∧ : four → four → four
four-∧ 0' 0' = 0'
four-∧ 0' 1' = 0'
four-∧ 0' 2' = 0'
four-∧ 0' 3' = 0'
four-∧ 1' 0' = 0'
four-∧ 1' 1' = 1'
four-∧ 1' 2' = 0'
four-∧ 1' 3' = 1'
four-∧ 2' 0' = 0'
four-∧ 2' 1' = 0'
four-∧ 2' 2' = 2'
four-∧ 2' 3' = 2'
four-∧ 3' 0' = 0'
four-∧ 3' 1' = 1'
four-∧ 3' 2' = 2'
four-∧ 3' 3' = 3'


four-∨ : four → four → four
four-∨ 0' 0' = 0'
four-∨ 0' 1' = 1'
four-∨ 0' 2' = 2'
four-∨ 0' 3' = 3'
four-∨ 1' 0' = 1'
four-∨ 1' 1' = 1'
four-∨ 1' 2' = 3'
four-∨ 1' 3' = 3'
four-∨ 2' 0' = 2'
four-∨ 2' 1' = 3'
four-∨ 2' 2' = 2'
four-∨ 2' 3' = 3'
four-∨ 3' 0' = 3'
four-∨ 3' 1' = 3'
four-∨ 3' 2' = 3'
four-∨ 3' 3' = 3'

four-∧-comm : (x y : four) → four-∧ x y == four-∧ y x
four-∧-comm 0' 0' = refl
four-∧-comm 0' 1' = refl
four-∧-comm 0' 2' = refl
four-∧-comm 0' 3' = refl
four-∧-comm 1' 0' = refl
four-∧-comm 1' 1' = refl
four-∧-comm 1' 2' = refl
four-∧-comm 1' 3' = refl
four-∧-comm 2' 0' = refl
four-∧-comm 2' 1' = refl
four-∧-comm 2' 2' = refl
four-∧-comm 2' 3' = refl
four-∧-comm 3' 0' = refl
four-∧-comm 3' 1' = refl
four-∧-comm 3' 2' = refl
four-∧-comm 3' 3' = refl

four-∧-assoc : (x y z : four) → four-∧ x (four-∧ y z) == four-∧ (four-∧ x y) z
four-∧-assoc 0' 0' 0' = refl
four-∧-assoc 0' 0' 1' = refl
four-∧-assoc 0' 0' 2' = refl
four-∧-assoc 0' 0' 3' = refl
four-∧-assoc 0' 1' 0' = refl
four-∧-assoc 0' 1' 1' = refl
four-∧-assoc 0' 1' 2' = refl
four-∧-assoc 0' 1' 3' = refl
four-∧-assoc 0' 2' 0' = refl
four-∧-assoc 0' 2' 1' = refl
four-∧-assoc 0' 2' 2' = refl
four-∧-assoc 0' 2' 3' = refl
four-∧-assoc 0' 3' 0' = refl
four-∧-assoc 0' 3' 1' = refl
four-∧-assoc 0' 3' 2' = refl
four-∧-assoc 0' 3' 3' = refl
four-∧-assoc 1' 0' 0' = refl
four-∧-assoc 1' 0' 1' = refl
four-∧-assoc 1' 0' 2' = refl
four-∧-assoc 1' 0' 3' = refl
four-∧-assoc 1' 1' 0' = refl
four-∧-assoc 1' 1' 1' = refl
four-∧-assoc 1' 1' 2' = refl
four-∧-assoc 1' 1' 3' = refl
four-∧-assoc 1' 2' 0' = refl
four-∧-assoc 1' 2' 1' = refl
four-∧-assoc 1' 2' 2' = refl
four-∧-assoc 1' 2' 3' = refl
four-∧-assoc 1' 3' 0' = refl
four-∧-assoc 1' 3' 1' = refl
four-∧-assoc 1' 3' 2' = refl
four-∧-assoc 1' 3' 3' = refl
four-∧-assoc 2' 0' 0' = refl
four-∧-assoc 2' 0' 1' = refl
four-∧-assoc 2' 0' 2' = refl
four-∧-assoc 2' 0' 3' = refl
four-∧-assoc 2' 1' 0' = refl
four-∧-assoc 2' 1' 1' = refl
four-∧-assoc 2' 1' 2' = refl
four-∧-assoc 2' 1' 3' = refl
four-∧-assoc 2' 2' 0' = refl
four-∧-assoc 2' 2' 1' = refl
four-∧-assoc 2' 2' 2' = refl
four-∧-assoc 2' 2' 3' = refl
four-∧-assoc 2' 3' 0' = refl
four-∧-assoc 2' 3' 1' = refl
four-∧-assoc 2' 3' 2' = refl
four-∧-assoc 2' 3' 3' = refl
four-∧-assoc 3' 0' 0' = refl
four-∧-assoc 3' 0' 1' = refl
four-∧-assoc 3' 0' 2' = refl
four-∧-assoc 3' 0' 3' = refl
four-∧-assoc 3' 1' 0' = refl
four-∧-assoc 3' 1' 1' = refl
four-∧-assoc 3' 1' 2' = refl
four-∧-assoc 3' 1' 3' = refl
four-∧-assoc 3' 2' 0' = refl
four-∧-assoc 3' 2' 1' = refl
four-∧-assoc 3' 2' 2' = refl
four-∧-assoc 3' 2' 3' = refl
four-∧-assoc 3' 3' 0' = refl
four-∧-assoc 3' 3' 1' = refl
four-∧-assoc 3' 3' 2' = refl
four-∧-assoc 3' 3' 3' = refl

four-∧∨-absorp : (x y : four) → four-∧ x (four-∨ x y) == x
four-∧∨-absorp 0' 0' = refl
four-∧∨-absorp 0' 1' = refl
four-∧∨-absorp 0' 2' = refl
four-∧∨-absorp 0' 3' = refl
four-∧∨-absorp 1' 0' = refl
four-∧∨-absorp 1' 1' = refl
four-∧∨-absorp 1' 2' = refl
four-∧∨-absorp 1' 3' = refl
four-∧∨-absorp 2' 0' = refl
four-∧∨-absorp 2' 1' = refl
four-∧∨-absorp 2' 2' = refl
four-∧∨-absorp 2' 3' = refl
four-∧∨-absorp 3' 0' = refl
four-∧∨-absorp 3' 1' = refl
four-∧∨-absorp 3' 2' = refl
four-∧∨-absorp 3' 3' = refl

four-∨-comm : (x y : four) → four-∨ x y == four-∨ y x
four-∨-comm 0' 0' = refl
four-∨-comm 0' 1' = refl
four-∨-comm 0' 2' = refl
four-∨-comm 0' 3' = refl
four-∨-comm 1' 0' = refl
four-∨-comm 1' 1' = refl
four-∨-comm 1' 2' = refl
four-∨-comm 1' 3' = refl
four-∨-comm 2' 0' = refl
four-∨-comm 2' 1' = refl
four-∨-comm 2' 2' = refl
four-∨-comm 2' 3' = refl
four-∨-comm 3' 0' = refl
four-∨-comm 3' 1' = refl
four-∨-comm 3' 2' = refl
four-∨-comm 3' 3' = refl

four-∨-assoc : (x y z : four) → four-∨ x (four-∨ y z) == four-∨ (four-∨ x y) z
four-∨-assoc 0' 0' 0' = refl
four-∨-assoc 0' 0' 1' = refl
four-∨-assoc 0' 0' 2' = refl
four-∨-assoc 0' 0' 3' = refl
four-∨-assoc 0' 1' 0' = refl
four-∨-assoc 0' 1' 1' = refl
four-∨-assoc 0' 1' 2' = refl
four-∨-assoc 0' 1' 3' = refl
four-∨-assoc 0' 2' 0' = refl
four-∨-assoc 0' 2' 1' = refl
four-∨-assoc 0' 2' 2' = refl
four-∨-assoc 0' 2' 3' = refl
four-∨-assoc 0' 3' 0' = refl
four-∨-assoc 0' 3' 1' = refl
four-∨-assoc 0' 3' 2' = refl
four-∨-assoc 0' 3' 3' = refl
four-∨-assoc 1' 0' 0' = refl
four-∨-assoc 1' 0' 1' = refl
four-∨-assoc 1' 0' 2' = refl
four-∨-assoc 1' 0' 3' = refl
four-∨-assoc 1' 1' 0' = refl
four-∨-assoc 1' 1' 1' = refl
four-∨-assoc 1' 1' 2' = refl
four-∨-assoc 1' 1' 3' = refl
four-∨-assoc 1' 2' 0' = refl
four-∨-assoc 1' 2' 1' = refl
four-∨-assoc 1' 2' 2' = refl
four-∨-assoc 1' 2' 3' = refl
four-∨-assoc 1' 3' 0' = refl
four-∨-assoc 1' 3' 1' = refl
four-∨-assoc 1' 3' 2' = refl
four-∨-assoc 1' 3' 3' = refl
four-∨-assoc 2' 0' 0' = refl
four-∨-assoc 2' 0' 1' = refl
four-∨-assoc 2' 0' 2' = refl
four-∨-assoc 2' 0' 3' = refl
four-∨-assoc 2' 1' 0' = refl
four-∨-assoc 2' 1' 1' = refl
four-∨-assoc 2' 1' 2' = refl
four-∨-assoc 2' 1' 3' = refl
four-∨-assoc 2' 2' 0' = refl
four-∨-assoc 2' 2' 1' = refl
four-∨-assoc 2' 2' 2' = refl
four-∨-assoc 2' 2' 3' = refl
four-∨-assoc 2' 3' 0' = refl
four-∨-assoc 2' 3' 1' = refl
four-∨-assoc 2' 3' 2' = refl
four-∨-assoc 2' 3' 3' = refl
four-∨-assoc 3' 0' 0' = refl
four-∨-assoc 3' 0' 1' = refl
four-∨-assoc 3' 0' 2' = refl
four-∨-assoc 3' 0' 3' = refl
four-∨-assoc 3' 1' 0' = refl
four-∨-assoc 3' 1' 1' = refl
four-∨-assoc 3' 1' 2' = refl
four-∨-assoc 3' 1' 3' = refl
four-∨-assoc 3' 2' 0' = refl
four-∨-assoc 3' 2' 1' = refl
four-∨-assoc 3' 2' 2' = refl
four-∨-assoc 3' 2' 3' = refl
four-∨-assoc 3' 3' 0' = refl
four-∨-assoc 3' 3' 1' = refl
four-∨-assoc 3' 3' 2' = refl
four-∨-assoc 3' 3' 3' = refl


four-∨∧-absorp : (x y : four) → four-∨ x (four-∧ x y) == x
four-∨∧-absorp 0' 0' = refl
four-∨∧-absorp 0' 1' = refl
four-∨∧-absorp 0' 2' = refl
four-∨∧-absorp 0' 3' = refl
four-∨∧-absorp 1' 0' = refl 
four-∨∧-absorp 1' 1' = refl
four-∨∧-absorp 1' 2' = refl
four-∨∧-absorp 1' 3' = refl
four-∨∧-absorp 2' 0' = refl
four-∨∧-absorp 2' 1' = refl
four-∨∧-absorp 2' 2' = refl
four-∨∧-absorp 2' 3' = refl
four-∨∧-absorp 3' 0' = refl
four-∨∧-absorp 3' 1' = refl
four-∨∧-absorp 3' 2' = refl
four-∨∧-absorp 3' 3' = refl


four-≡ : four → four → Set
four-≡ 0' 0' = ⊤
four-≡ 0' 1' = ⊥
four-≡ 0' 2' = ⊥
four-≡ 0' 3' = ⊥
four-≡ 1' 0' = ⊥
four-≡ 1' 1' = ⊤
four-≡ 1' 2' = ⊤
four-≡ 1' 3' = ⊥
four-≡ 2' 0' = ⊥
four-≡ 2' 1' = ⊤
four-≡ 2' 2' = ⊤
four-≡ 2' 3' = ⊥
four-≡ 3' 0' = ⊥
four-≡ 3' 1' = ⊥
four-≡ 3' 2' = ⊥
four-≡ 3' 3' = ⊤

four-≡-refl : (x : four) → four-≡ x x
four-≡-refl 0' = ●
four-≡-refl 1' = ●
four-≡-refl 2' = ●
four-≡-refl 3' = ●

four-≡-sym : (x y : four) → four-≡ x y → four-≡ y x
four-≡-sym 0' 0' q = ●
four-≡-sym 0' 1' q = ω q
four-≡-sym 0' 2' q = ω q
four-≡-sym 0' 3' q = ω q
four-≡-sym 1' 0' q = ω q
four-≡-sym 1' 1' q = ●
four-≡-sym 1' 2' q = ●
four-≡-sym 1' 3' q = ω q
four-≡-sym 2' 0' q = ω q
four-≡-sym 2' 1' q = ●
four-≡-sym 2' 2' q = ●
four-≡-sym 2' 3' q = ω q
four-≡-sym 3' 0' q = ω q
four-≡-sym 3' 1' q = ω q
four-≡-sym 3' 2' q = ω q
four-≡-sym 3' 3' q = ●

four-≡-trans : (x y z : four) → four-≡ x y → four-≡ y z → four-≡ x z
four-≡-trans 0' y 0' q r = ●
four-≡-trans 0' 0' 1' q r = ω r
four-≡-trans 0' 1' 1' q r = ω q
four-≡-trans 0' 2' 1' q r = ω q
four-≡-trans 0' 3' 1' q r = ω q
four-≡-trans 0' 0' 2' q r = ω r
four-≡-trans 0' 1' 2' q r = ω q
four-≡-trans 0' 2' 2' q r = ω q
four-≡-trans 0' 3' 2' q r = ω q
four-≡-trans 0' 0' 3' q r = ω r
four-≡-trans 0' 1' 3' q r = ω q
four-≡-trans 0' 2' 3' q r = ω q
four-≡-trans 0' 3' 3' q r = ω q
four-≡-trans 1' 0' 0' q r = ω q
four-≡-trans 1' 1' 0' q r = ω r
four-≡-trans 1' 2' 0' q r = ω r
four-≡-trans 1' 3' 0' q r = ω q
four-≡-trans 1' y 1' q r = ●
four-≡-trans 1' y 2' q r = ●
four-≡-trans 1' 0' 3' q r = ω q
four-≡-trans 1' 1' 3' q r = ω r
four-≡-trans 1' 2' 3' q r = ω r
four-≡-trans 1' 3' 3' q r = ω q
four-≡-trans 2' 0' 0' q r = ω q
four-≡-trans 2' 1' 0' q r = ω r
four-≡-trans 2' 2' 0' q r = ω r
four-≡-trans 2' 3' 0' q r = ω q
four-≡-trans 2' y 1' q r = ●
four-≡-trans 2' y 2' q r = ●
four-≡-trans 2' 0' 3' q r = ω q
four-≡-trans 2' 1' 3' q r = ω r
four-≡-trans 2' 2' 3' q r = ω r
four-≡-trans 2' 3' 3' q r = ω q
four-≡-trans 3' 0' 0' q r = ω q
four-≡-trans 3' 1' 0' q r = ω q
four-≡-trans 3' 2' 0' q r = ω q
four-≡-trans 3' 3' 0' q r = ω r
four-≡-trans 3' 0' 1' q r = ω q
four-≡-trans 3' 1' 1' q r = ω q
four-≡-trans 3' 2' 1' q r = ω q
four-≡-trans 3' 3' 1' q r = ω r
four-≡-trans 3' 0' 2' q r = ω q
four-≡-trans 3' 1' 2' q r = ω q
four-≡-trans 3' 2' 2' q r = ω q
four-≡-trans 3' 3' 2' q r = ω r
four-≡-trans 3' y 3' q r = ●

four-≡-equiv : isEquivalence four-≡
four-≡-equiv = 
 record {
  ≡-refl = four-≡-refl ;
  ≡-sym = (λ {x} {y} → four-≡-sym x y) ;
  ≡-trans = (λ {x} {y} {z} → four-≡-trans x y z)
 }

¬[four-∧-cont] : ((x x' y y' : four) → (four-≡ x x') → (four-≡ y y') → (four-≡ (four-∧ x y) (four-∧ x' y'))) → ⊥
¬[four-∧-cont] assump = proof
 where
  [1≡1] : four-≡ 1' 1'
  [1≡1] = ●

  [1≡2] : four-≡ 1' 2'
  [1≡2] = ●

  [1∧1≡1] : four-≡ (four-∧ 1' 1') 1'
  [1∧1≡1] = ●

  [1∧2≡0] : four-≡ (four-∧ 1' 2') 0'
  [1∧2≡0] = ●

  ¬[1≡0] : (four-≡ 1' 0') → ⊥
  ¬[1≡0] [1'≡0'] = [1'≡0']

  [1≡0] : four-≡ 1' 0'
  [1≡0] = assump 1' 1' 1' 2' [1≡1] [1≡2]

  proof = ¬[1≡0] [1≡0]

record Formulation1 {i} {j} {k} (A : Set i) (_≡_ : A → A → Set k) (_≤_ : A → A → Set j) (_∧_ : A → A → A) (_∨_ : A → A → A) : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  ≡-refl : (x : A) → x ≡ x
  ≡-sym : {x y : A} → x ≡ y → y ≡ x
  ≡-trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  ≤-refl : {x y : A} → x ≡ y → (x ≤ y) × (y ≤ x)
  ≤-antisym : {x y : A} → x ≤ y → y ≤ x → x ≡ y
  ≤-trans : {x y z : A} → x ≤ y → y ≤ z → x ≤ z
  ∨-lub : (x y : A) → (x ≤ (x ∨ y)) × ((y ≤ (x ∨ y)) × ((z : A) → (x ≤ z) × (y ≤ z) → (x ∨ y) ≤ z))
  ∧-glb : (x y : A) → ((x ∧ y) ≤ x) × (((x ∧ y) ≤ y) × ((z : A) → (z ≤ x) × (z ≤ y) → z ≤ (x ∧ y)))

record Formulation2 {i} {j} {k} (A : Set i) (_≡_ : A → A → Set k) (_≤_ : A → A → Set j) (_∧_ : A → A → A) (_∨_ : A → A → A) : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  ≡-refl : (x : A) → x ≡ x
  ≡-sym : {x y : A} → x ≡ y → y ≡ x
  ≡-trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  ≤-refl : (x : A) → x ≤ x
  ≤-antisym : {x y : A} → x ≤ y → y ≤ x → x ≡ y
  ≤-trans : {x y z : A} → x ≤ y → y ≤ z → x ≤ z
  ∨-lub : (x y : A) → (x ≤ (x ∨ y)) × ((y ≤ (x ∨ y)) × ((z : A) → (x ≤ z) × (y ≤ z) → (x ∨ y) ≤ z))
  ∧-glb : (x y : A) → ((x ∧ y) ≤ x) × (((x ∧ y) ≤ y) × ((z : A) → (z ≤ x) × (z ≤ y) → z ≤ (x ∧ y)))

record Formulation3 {i} {j} {k} (A : Set i) (_≡_ : A → A → Set k) (_≤_ : A → A → Set j) (_∧_ : A → A → A) (_∨_ : A → A → A) : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  ≡-refl : (x : A) → x ≡ x
  ≡-sym : {x y : A} → x ≡ y → y ≡ x
  ≡-trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  ≤-refl : {x y : A} → x ≡ y → x ≤ y
  ≤-antisym : {x y : A} → x ≤ y → y ≤ x → x ≡ y
  ≤-trans : {x y z : A} → x ≤ y → y ≤ z → x ≤ z
  ∨-lub : (x y : A) → (x ≤ (x ∨ y)) × ((y ≤ (x ∨ y)) × ((z : A) → (x ≤ z) × (y ≤ z) → (x ∨ y) ≤ z))
  ∧-glb : (x y : A) → ((x ∧ y) ≤ x) × (((x ∧ y) ≤ y) × ((z : A) → (z ≤ x) × (z ≤ y) → z ≤ (x ∧ y)))

record Formulation4 {i} {j} {k} (A : Set i) (_≡_ : A → A → Set k) (_≤_ : A → A → Set j) (_∧_ : A → A → A) (_∨_ : A → A → A) : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
 field
  ≡-refl : (x : A) → x ≡ x
  ≡-sym : {x y : A} → x ≡ y → y ≡ x
  ≡-trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  ≤-cont : {x x' y y' : A} → x ≡ x' → y ≡ y' → x ≤ y → x' ≤ y'
  ≤-refl : (x : A) → x ≤ x
  ≤-antisym : {x y : A} → x ≤ y → y ≤ x → x ≡ y
  ≤-trans : {x y z : A} → x ≤ y → y ≤ z → x ≤ z
  ∨-lub : (x y : A) → (x ≤ (x ∨ y)) × ((y ≤ (x ∨ y)) × ((z : A) → (x ≤ z) × (y ≤ z) → (x ∨ y) ≤ z))
  ∧-glb : (x y : A) → ((x ∧ y) ≤ x) × (((x ∧ y) ≤ y) × ((z : A) → (z ≤ x) × (z ≤ y) → z ≤ (x ∧ y)))

record Formulation5 {i} {j} (A : Set i) (_≡_ : A → A → Set j) (_∧_ : A → A → A) (_∨_ : A → A → A) : Set ((lsuc i) ⊔ (lsuc j)) where
 field 
  ≡-refl : (x : A) → x ≡ x
  ≡-sym : {x y : A} → x ≡ y → y ≡ x
  ≡-trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  ∧-comm : (x y : A) → (x ∧ y) ≡ (y ∧ x)
  ∧-assoc : (x y z : A) → (x ∧ (y ∧ z)) ≡ ((x ∧ y) ∧ z)
  ∧∨-absorp : (x y : A) → (x ∧ (x ∨ y)) ≡ x
  ∨-comm : (x y : A) → (x ∨ y) ≡ (y ∨ x)
  ∨-assoc : (x y z : A) → (x ∨ (y ∨ z)) ≡ ((x ∨ y) ∨ z)
  ∨∧-absorp : (x y : A) → (x ∨ (x ∧ y)) ≡ x

record Formulation6 {i} {j} (A : Set i) (_≡_ : A → A → Set j) (_∧_ : A → A → A) (_∨_ : A → A → A) : Set ((lsuc i) ⊔ (lsuc j)) where
 field
  ≡-refl : (x : A) → x ≡ x
  ≡-sym : {x y : A} → x ≡ y → y ≡ x
  ≡-trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  ∧-cont : (x x' y y' : A) → x ≡ x' → y ≡ y' → (x ∧ y) ≡ (x' ∧ y')
  ∧-comm : (x y : A) → (x ∧ y) ≡ (y ∧ x)
  ∧-assoc : (x y z : A) → (x ∧ (y ∧ z)) ≡ ((x ∧ y) ∧ z)
  ∧∨-absorp : (x y : A) → (x ∧ (x ∨ y)) ≡ x  
  ∨-cont : (x x' y y' : A) → x ≡ x' → y ≡ y' → (x ∨ y) ≡ (x' ∨ y')
  ∨-comm : (x y : A) → (x ∨ y) ≡ (y ∨ x)
  ∨-assoc : (x y z : A) → (x ∨ (y ∨ z)) ≡ ((x ∨ y) ∨ z)
  ∨∧-absorp : (x y : A) → (x ∨ (x ∧ y)) ≡ x


Formulation1→Formulation2 : ∀ {i j k} (A : Set i) (≡ : A → A → Set k) (≤ : A → A → Set j) (∧ : A → A → A) (∨ : A → A → A) → Formulation1 A ≡ ≤ ∧ ∨ → Formulation2 A ≡ ≤ ∧ ∨
Formulation1→Formulation2 {i} {j} {k} A _≡_ _≤_ _∧_ _∨_ Formulation1-A = Formulation2-A
 where
  open Formulation1 Formulation1-A
  Formulation2-A = 
   record {
    ≡-refl = ≡-refl ;
    ≡-sym = ≡-sym ;
    ≡-trans = ≡-trans ;
    ≤-refl = ≤-refl' ;
    ≤-antisym = ≤-antisym ;
    ≤-trans = ≤-trans ;
    ∨-lub = ∨-lub ;
    ∧-glb = ∧-glb 
   } 
   where
    ≤-refl' : (x : A) → x ≤ x
    ≤-refl' x = first (≤-refl (≡-refl x))

Formulation1→Formulation3 : ∀ {i j k} (A : Set i) (≡ : A → A → Set k) (≤ : A → A → Set j) (∧ : A → A → A) (∨ : A → A → A) → Formulation1 A ≡ ≤ ∧ ∨ → Formulation3 A ≡ ≤ ∧ ∨
Formulation1→Formulation3 {i} {j} {k} A _≡_ _≤_ _∧_ _∨_ Formulation1-A = Formulation3-A
 where
  open Formulation1 Formulation1-A
  Formulation3-A = 
   record {
    ≡-refl = ≡-refl ;
    ≡-sym = ≡-sym ;
    ≡-trans = ≡-trans ;
    ≤-refl = ≤-refl' ;
    ≤-antisym = ≤-antisym ;
    ≤-trans = ≤-trans ;
    ∨-lub = ∨-lub ;
    ∧-glb = ∧-glb
   }
   where
    ≤-refl' : {x y : A} → x ≡ y → x ≤ y
    ≤-refl' p₁ = first (≤-refl p₁)

Formulation1→Formulation4 : ∀ {i j k} (A : Set i) (≡ : A → A → Set k) (≤ : A → A → Set j) (∧ : A → A → A) (∨ : A → A → A) → Formulation1 A ≡ ≤ ∧ ∨ → Formulation4 A ≡ ≤ ∧ ∨
Formulation1→Formulation4 {i} {j} {k} A _≡_ _≤_ _∧_ _∨_ Formulation1-A = Formulation4-A
 where
  open Formulation1 Formulation1-A
  Formulation4-A = 
   record {
    ≡-refl = ≡-refl ;
    ≡-sym = ≡-sym ;
    ≡-trans = ≡-trans ;
    ≤-cont = ≤-cont ;
    ≤-refl = ≤-refl' ;
    ≤-antisym = ≤-antisym ;
    ≤-trans = ≤-trans ;
    ∨-lub = ∨-lub ;
    ∧-glb = ∧-glb 
   }
   where
    ≤-refl' : (x : A) → x ≤ x
    ≤-refl' x = first (≤-refl (≡-refl x))

    ≤-cont : {x x' y y' : A} → x ≡ x' → y ≡ y' → x ≤ y → x' ≤ y'
    ≤-cont {x} {x'} {y} {y'} p₁ p₂ [x≤y] = [x'≤y']
     where
      [x'≤x] : x' ≤ x
      [x'≤x] = first (≤-refl (≡-sym p₁))

      [y≤y'] : y ≤ y'
      [y≤y'] = first (≤-refl p₂)

      [x'≤y'] : x' ≤ y'
      [x'≤y'] = ≤-trans [x'≤x] (≤-trans [x≤y] [y≤y'])


Formulation1→Formulation5 : ∀ {i j k} (A : Set i) (≡ : A → A → Set k) (≤ : A → A → Set j) (∧ : A → A → A) (∨ : A → A → A) → Formulation1 A ≡ ≤ ∧ ∨ → Formulation5 A ≡ ∧ ∨
Formulation1→Formulation5 {i} {j} {k} A _≡_ _≤_ _∧_ _∨_ Formulation1-A = Formulation5-A
 where
  open Formulation1 Formulation1-A
  Formulation5-A = 
   record {
    ≡-refl = ≡-refl ;
    ≡-sym = ≡-sym ;
    ≡-trans = ≡-trans ;
    ∧-comm = ∧-comm ;
    ∧-assoc = ∧-assoc ;
    ∧∨-absorp = ∧∨-absorp ;
    ∨-comm = ∨-comm ;
    ∨-assoc = ∨-assoc ;
    ∨∧-absorp = ∨∧-absorp
   }
   where
    ∧-comm : (x y : A) → (x ∧ y) ≡ (y ∧ x)
    ∧-comm x y = ≤-antisym [x∧y≤y∧x] [y∧x≤x∧y]
     where
      [x∧y≤y∧x] : (x ∧ y) ≤ (y ∧ x)
      [x∧y≤y∧x] = (second (second (∧-glb y x))) (x ∧ y) ([x∧y≤y] , [x∧y≤x])
       where 
        [x∧y≤x] : (x ∧ y) ≤ x
        [x∧y≤x] = first (∧-glb x y)

        [x∧y≤y] : (x ∧ y) ≤ y
        [x∧y≤y] = first (second (∧-glb x y))

      [y∧x≤x∧y] : (y ∧ x) ≤ (x ∧ y)
      [y∧x≤x∧y] = (second (second (∧-glb x y))) (y ∧ x) ([y∧x≤x] , [y∧x≤y])
       where
        [y∧x≤y] : (y ∧ x) ≤ y
        [y∧x≤y] = first (∧-glb y x)

        [y∧x≤x] : (y ∧ x) ≤ x
        [y∧x≤x] = first (second (∧-glb y x))



    ∧-assoc : (x y z : A) → (x ∧ (y ∧ z)) ≡ ((x ∧ y) ∧ z)
    ∧-assoc x y z = ≤-antisym [x∧[y∧z]≤[x∧y]∧z] [[x∧y]∧z≤x∧[y∧z]]
     where
      [x∧[y∧z]≤[x∧y]∧z] : (x ∧ (y ∧ z)) ≤ ((x ∧ y) ∧ z)
      [x∧[y∧z]≤[x∧y]∧z] = (second (second (∧-glb (x ∧ y) z))) (x ∧ (y ∧ z)) ([x∧[y∧z]≤x∧y] , [x∧[y∧z]≤z] )
       where
        [x∧[y∧z]≤x] : (x ∧ (y ∧ z)) ≤ x
        [x∧[y∧z]≤x] = first (∧-glb x (y ∧ z))

        [x∧[y∧z]≤y∧z] : (x ∧ (y ∧ z)) ≤ (y ∧ z)
        [x∧[y∧z]≤y∧z] = first (second (∧-glb x (y ∧ z)))
 
        [y∧z≤y] : (y ∧ z) ≤ y
        [y∧z≤y] = first (∧-glb y z)

        [y∧z≤z] : (y ∧ z) ≤ z
        [y∧z≤z] = first (second (∧-glb y z))

        [x∧[y∧z]≤y] : (x ∧ (y ∧ z)) ≤ y
        [x∧[y∧z]≤y] = ≤-trans [x∧[y∧z]≤y∧z] [y∧z≤y]

        [x∧[y∧z]≤z] : (x ∧ (y ∧ z)) ≤ z
        [x∧[y∧z]≤z] = ≤-trans [x∧[y∧z]≤y∧z] [y∧z≤z]

        [x∧[y∧z]≤x∧y] : (x ∧ (y ∧ z)) ≤ (x ∧ y)
        [x∧[y∧z]≤x∧y] = (second (second (∧-glb x y))) (x ∧ (y ∧ z)) ([x∧[y∧z]≤x] , [x∧[y∧z]≤y] )

      [[x∧y]∧z≤x∧[y∧z]] : ((x ∧ y) ∧ z) ≤ (x ∧ (y ∧ z))
      [[x∧y]∧z≤x∧[y∧z]] = (second (second (∧-glb x (y ∧ z)))) ((x ∧ y) ∧ z) ([[x∧y]∧z≤x] , [[x∧y]∧z≤y∧z])
       where
        [[x∧y]∧z≤x∧y] : ((x ∧ y) ∧ z) ≤ (x ∧ y)
        [[x∧y]∧z≤x∧y] = first (∧-glb (x ∧ y) z)

        [[x∧y]∧z≤z] : ((x ∧ y) ∧ z) ≤ z
        [[x∧y]∧z≤z] = first (second (∧-glb (x ∧ y) z))

        [x∧y≤x] : (x ∧ y) ≤ x
        [x∧y≤x] = first (∧-glb x y)

        [x∧y≤y] : (x ∧ y) ≤ y
        [x∧y≤y] = first (second (∧-glb x y))

        [[x∧y]∧z≤x] : ((x ∧ y) ∧ z) ≤ x
        [[x∧y]∧z≤x] = ≤-trans [[x∧y]∧z≤x∧y] [x∧y≤x]

        [[x∧y]∧z≤y] : ((x ∧ y) ∧ z) ≤ y
        [[x∧y]∧z≤y] = ≤-trans [[x∧y]∧z≤x∧y] [x∧y≤y] 

        [[x∧y]∧z≤y∧z] : ((x ∧ y) ∧ z) ≤ (y ∧ z)
        [[x∧y]∧z≤y∧z] = (second (second (∧-glb y z))) ((x ∧ y) ∧ z) ([[x∧y]∧z≤y] , [[x∧y]∧z≤z])



    ∨-comm : (x y : A) → (x ∨ y) ≡ (y ∨ x)
    ∨-comm x y = ≤-antisym [x∨y≤y∨x] [y∨x≤x∨y]
     where
      [y∨x≤x∨y] : (y ∨ x) ≤ (x ∨ y)
      [y∨x≤x∨y] = (second (second (∨-lub y x))) (x ∨ y) ([y≤x∨y] , [x≤x∨y])
       where
        [x≤x∨y] : x ≤ (x ∨ y)
        [x≤x∨y] = first (∨-lub x y)
 
        [y≤x∨y] : y ≤ (x ∨ y)
        [y≤x∨y] = first (second (∨-lub x y))

      [x∨y≤y∨x] : (x ∨ y) ≤ (y ∨ x)
      [x∨y≤y∨x] = (second (second (∨-lub x y))) (y ∨ x) ([x≤y∨x] , [y≤y∨x])
       where 
        [y≤y∨x] : y ≤ (y ∨ x)
        [y≤y∨x] = first (∨-lub y x)

        [x≤y∨x] : x ≤ (y ∨ x)
        [x≤y∨x] = first (second (∨-lub y x))


    ∨-assoc : (x y z : A) → (x ∨ (y ∨ z)) ≡ ((x ∨ y) ∨ z)
    ∨-assoc x y z = ≤-antisym [x∨[y∨z]≤[x∨y]∨z] [[x∨y]∨z≤x∨[y∨z]]
     where
      [[x∨y]∨z≤x∨[y∨z]] : ((x ∨ y) ∨ z) ≤ (x ∨ (y ∨ z))
      [[x∨y]∨z≤x∨[y∨z]] = (second (second (∨-lub (x ∨ y) z))) (x ∨ (y ∨ z)) ([x∨y≤x∨[y∨z]] , [z≤x∨[y∨z]])
       where
        [x≤x∨[y∨z]] : x ≤ (x ∨ (y ∨ z))
        [x≤x∨[y∨z]] = first (∨-lub x (y ∨ z))

        [y∨z≤x∨[y∨z]] : (y ∨ z) ≤ (x ∨ (y ∨ z))
        [y∨z≤x∨[y∨z]] = first (second (∨-lub x (y ∨ z)))

        [y≤y∨z] : y ≤ (y ∨ z)
        [y≤y∨z] = first (∨-lub y z)

        [z≤y∨z] : z ≤ (y ∨ z)
        [z≤y∨z] = first (second (∨-lub y z))

        [y≤x∨[y∨z]] : y ≤ (x ∨ (y ∨ z))
        [y≤x∨[y∨z]] = ≤-trans [y≤y∨z] [y∨z≤x∨[y∨z]]

        [z≤x∨[y∨z]] : z ≤ (x ∨ (y ∨ z))
        [z≤x∨[y∨z]] = ≤-trans [z≤y∨z] [y∨z≤x∨[y∨z]]

        [x∨y≤x∨[y∨z]] : (x ∨ y) ≤ (x ∨ (y ∨ z))
        [x∨y≤x∨[y∨z]] = (second (second (∨-lub x y))) (x ∨ (y ∨ z)) ([x≤x∨[y∨z]] , [y≤x∨[y∨z]])
   
      [x∨[y∨z]≤[x∨y]∨z] : (x ∨ (y ∨ z)) ≤ ((x ∨ y) ∨ z)
      [x∨[y∨z]≤[x∨y]∨z] = (second (second (∨-lub x (y ∨ z)))) ((x ∨ y) ∨ z) ([x≤[x∨y]∨z] , [y∨z≤[x∨y]∨z])
       where
        [x∨y≤[x∨y]∨z] : (x ∨ y) ≤ ((x ∨ y) ∨ z)
        [x∨y≤[x∨y]∨z] = first (∨-lub (x ∨ y) z)
 
        [z≤[x∨y]∨z] : z ≤ ((x ∨ y) ∨ z)
        [z≤[x∨y]∨z] = first (second (∨-lub (x ∨ y) z))

        [x≤x∨y] : x ≤ (x ∨ y)
        [x≤x∨y] = first (∨-lub x y)
    
        [y≤x∨y] : y ≤ (x ∨ y)
        [y≤x∨y] = first (second (∨-lub x y))

        [x≤[x∨y]∨z] : x ≤ ((x ∨ y) ∨ z)
        [x≤[x∨y]∨z] = ≤-trans [x≤x∨y] [x∨y≤[x∨y]∨z]

        [y≤[x∨y]∨z] : y ≤ ((x ∨ y) ∨ z)
        [y≤[x∨y]∨z] = ≤-trans [y≤x∨y] [x∨y≤[x∨y]∨z]
    
        [y∨z≤[x∨y]∨z] : (y ∨ z) ≤ ((x ∨ y) ∨ z)
        [y∨z≤[x∨y]∨z] = (second (second (∨-lub y z))) ((x ∨ y) ∨ z) ([y≤[x∨y]∨z] , [z≤[x∨y]∨z])

    ∧∨-absorp : (x y : A) → (x ∧ (x ∨ y)) ≡ x
    ∧∨-absorp x y = ≤-antisym [x∧[x∨y]≤x] [x≤x∧[x∨y]]
     where
      [x∧[x∨y]≤x] : (x ∧ (x ∨ y)) ≤ x
      [x∧[x∨y]≤x] = first (∧-glb x (x ∨ y))

      [x≤x∧[x∨y]] : x ≤ (x ∧ (x ∨ y))
      [x≤x∧[x∨y]] = (second (second (∧-glb x (x ∨ y)))) x ([x≤x] , [x≤x∨y])
       where
        [x≤x] : x ≤ x
        [x≤x] = first (≤-refl (≡-refl x))

        [x≤x∨y] : x ≤ (x ∨ y)
        [x≤x∨y] = first (∨-lub x y)
       

    ∨∧-absorp : (x y : A) → (x ∨ (x ∧ y)) ≡ x
    ∨∧-absorp x y = ≤-antisym [x∨[x∧y]≤x] [x≤x∨[x∧y]]
     where
      [x≤x∨[x∧y]] : x ≤ (x ∨ (x ∧ y))
      [x≤x∨[x∧y]] = first (∨-lub x (x ∧ y))

      [x∨[x∧y]≤x] : (x ∨ (x ∧ y)) ≤ x
      [x∨[x∧y]≤x] = (second (second (∨-lub x (x ∧ y)))) x ([x≤x] , [x∧y≤x])
       where
        [x≤x] : x ≤ x
        [x≤x] = first (≤-refl (≡-refl x))

        [x∧y≤x] : (x ∧ y) ≤ x
        [x∧y≤x] = first (∧-glb x y)


Formulation1→Formulation6 : ∀ {i j k} (A : Set i) (≡ : A → A → Set k) (≤ : A → A → Set j) (∧ : A → A → A) (∨ : A → A → A) → Formulation1 A ≡ ≤ ∧ ∨ → Formulation6 A ≡ ∧ ∨
Formulation1→Formulation6 {i} {j} {k} A _≡_ _≤_ _∧_ _∨_ Formulation1-A = Formulation6-A
 where
  open Formulation1 Formulation1-A hiding (≡-refl ; ≡-sym ; ≡-trans)

  Formulation5-A : Formulation5 A _≡_ _∧_ _∨_
  Formulation5-A = Formulation1→Formulation5 A _≡_ _≤_ _∧_ _∨_ Formulation1-A

  open Formulation5 Formulation5-A  

  Formulation6-A = 
   record {
    ≡-refl = ≡-refl ;
    ≡-sym = ≡-sym ;
    ≡-trans = ≡-trans ;
    ∧-cont = ∧-cont ;
    ∧-comm = ∧-comm ;
    ∧-assoc = ∧-assoc ;
    ∧∨-absorp = ∧∨-absorp ;
    ∨-cont = ∨-cont ;
    ∨-comm = ∨-comm ;
    ∨-assoc = ∨-assoc ;
    ∨∧-absorp = ∨∧-absorp
   }
   where
    ∧-cont : (x x' y y' : A) → (x ≡ x') → (y ≡ y') → (x ∧ y) ≡ (x' ∧ y')
    ∧-cont a b c d [a≡b] [c≡d] = [a∧c]≡[b∧d]
     where
      [b∧d≤a∧c] : (b ∧ d) ≤ (a ∧ c)
      [b∧d≤a∧c] = (second (second (∧-glb a c))) (b ∧ d) ([b∧d≤a] , [b∧d≤c])
       where
        [b∧d≤a] : (b ∧ d) ≤ a
        [b∧d≤a] = ≤-trans [b∧d≤b] [b≤a]
         where
          [b≤a] : b ≤ a
          [b≤a] = second (≤-refl [a≡b])

          [b∧d≤b] : (b ∧ d) ≤ b
          [b∧d≤b] = first (∧-glb b d)

        [b∧d≤c] : (b ∧ d) ≤ c
        [b∧d≤c] = ≤-trans [b∧d≤d] [d≤c]
         where
          [d≤c] : d ≤ c
          [d≤c] = second (≤-refl [c≡d])

          [b∧d≤d] : (b ∧ d) ≤ d
          [b∧d≤d] = first (second (∧-glb b d))

      [a∧c≤b∧d] : (a ∧ c) ≤ (b ∧ d)
      [a∧c≤b∧d] = (second (second (∧-glb b d))) (a ∧ c ) ([a∧c≤b] , [a∧c≤d])
       where
        [a∧c≤b] : (a ∧ c) ≤ b
        [a∧c≤b] = ≤-trans [a∧c≤a] [a≤b]
         where
          [a≤b] : a ≤ b
          [a≤b] = first (≤-refl [a≡b])
 
          [a∧c≤a] : (a ∧ c) ≤ a
          [a∧c≤a] = first (∧-glb a c)

        [a∧c≤d] : (a ∧ c) ≤ d
        [a∧c≤d] = ≤-trans [a∧c≤c] [c≤d]
         where
          [c≤d] : c ≤ d
          [c≤d] = first (≤-refl [c≡d])

          [a∧c≤c] : (a ∧ c) ≤ c
          [a∧c≤c] = first (second (∧-glb a c))
      

      [a∧c]≡[b∧d] : (a ∧ c) ≡ (b ∧ d)
      [a∧c]≡[b∧d] = ≤-antisym [a∧c≤b∧d] [b∧d≤a∧c]

    ∨-cont : (a b c d : A) → (a ≡ b) → (c ≡ d) → (a ∨ c) ≡ (b ∨ d)
    ∨-cont a b c d [a≡b] [c≡d] = [a∨c]≡[b∨d]
     where
      [a∨c]≡[b∨d] : (a ∨ c) ≡ (b ∨ d)
      [a∨c]≡[b∨d] = ≤-antisym [a∨c≤b∨d] [b∨d≤a∨c]
       where
        [a∨c≤b∨d] : (a ∨ c) ≤ (b ∨ d)
        [a∨c≤b∨d] = (second (second (∨-lub a c))) (b ∨ d) ([a≤b∨d] , [c≤b∨d])
         where
          [a≤b] : a ≤ b
          [a≤b] = first (≤-refl [a≡b])

          [b≤b∨d] : b ≤ (b ∨ d)
          [b≤b∨d] = first (∨-lub b d)

          [a≤b∨d] : a ≤ (b ∨ d)
          [a≤b∨d] = ≤-trans [a≤b] [b≤b∨d]

          [c≤d] : c ≤ d
          [c≤d] = first (≤-refl [c≡d])
 
          [d≤b∨d] : d ≤ (b ∨ d)
          [d≤b∨d] = first (second (∨-lub b d))

          [c≤b∨d] : c ≤ (b ∨ d)
          [c≤b∨d] = ≤-trans [c≤d] [d≤b∨d]

        [b∨d≤a∨c] : (b ∨ d) ≤ (a ∨ c)
        [b∨d≤a∨c] = (second (second (∨-lub b d))) (a ∨ c) ([b≤a∨c] , [d≤a∨c])
         where
          [b≤a] : b ≤ a
          [b≤a] = second (≤-refl [a≡b])

          [a≤a∨c] : a ≤ (a ∨ c)
          [a≤a∨c] = first (∨-lub a c)

          [b≤a∨c] : b ≤ (a ∨ c)
          [b≤a∨c] = ≤-trans [b≤a] [a≤a∨c]

          [d≤c] : d ≤ c
          [d≤c] = second (≤-refl [c≡d])
 
          [c≤a∨c] : c ≤ (a ∨ c)
          [c≤a∨c] = first (second (∨-lub a c))

          [d≤a∨c] : d ≤ (a ∨ c)
          [d≤a∨c] = ≤-trans [d≤c] [c≤a∨c]
     
{-
¬[Formulation2→Formulation1]
¬[Formulation2→Formulation3]
¬[Formulation2→Formulation4]
-}
Formulation2→Formulation5 : ∀ {i j k} (A : Set i) (≡ : A → A → Set k) (≤ : A → A → Set j) (∧ : A → A → A) (∨ : A → A → A) → Formulation2 A ≡ ≤ ∧ ∨ → Formulation5 A ≡ ∧ ∨
Formulation2→Formulation5 {i} {j} {k} A _≡_ _≤_ _∧_ _∨_ Formulation2-A = Formulation5-A
 where
  open Formulation2 Formulation2-A
  Formulation5-A = 
   record {
    ≡-refl = ≡-refl ;
    ≡-sym = ≡-sym ;
    ≡-trans = ≡-trans ;
    ∧-comm = ∧-comm ;
    ∧-assoc = ∧-assoc ;
    ∧∨-absorp = ∧∨-absorp ;
    ∨-comm = ∨-comm ;
    ∨-assoc = ∨-assoc ;
    ∨∧-absorp = ∨∧-absorp
   }
   where
    ∧-comm : (x y : A) → (x ∧ y) ≡ (y ∧ x)
    ∧-comm x y = ≤-antisym [x∧y≤y∧x] [y∧x≤x∧y]
     where
      [x∧y≤y∧x] : (x ∧ y) ≤ (y ∧ x)
      [x∧y≤y∧x] = (second (second (∧-glb y x))) (x ∧ y) ([x∧y≤y] , [x∧y≤x])
       where 
        [x∧y≤x] : (x ∧ y) ≤ x
        [x∧y≤x] = first (∧-glb x y)

        [x∧y≤y] : (x ∧ y) ≤ y
        [x∧y≤y] = first (second (∧-glb x y))

      [y∧x≤x∧y] : (y ∧ x) ≤ (x ∧ y)
      [y∧x≤x∧y] = (second (second (∧-glb x y))) (y ∧ x) ([y∧x≤x] , [y∧x≤y])
       where
        [y∧x≤y] : (y ∧ x) ≤ y
        [y∧x≤y] = first (∧-glb y x)

        [y∧x≤x] : (y ∧ x) ≤ x
        [y∧x≤x] = first (second (∧-glb y x))



    ∧-assoc : (x y z : A) → (x ∧ (y ∧ z)) ≡ ((x ∧ y) ∧ z)
    ∧-assoc x y z = ≤-antisym [x∧[y∧z]≤[x∧y]∧z] [[x∧y]∧z≤x∧[y∧z]]
     where
      [x∧[y∧z]≤[x∧y]∧z] : (x ∧ (y ∧ z)) ≤ ((x ∧ y) ∧ z)
      [x∧[y∧z]≤[x∧y]∧z] = (second (second (∧-glb (x ∧ y) z))) (x ∧ (y ∧ z)) ([x∧[y∧z]≤x∧y] , [x∧[y∧z]≤z] )
       where
        [x∧[y∧z]≤x] : (x ∧ (y ∧ z)) ≤ x
        [x∧[y∧z]≤x] = first (∧-glb x (y ∧ z))

        [x∧[y∧z]≤y∧z] : (x ∧ (y ∧ z)) ≤ (y ∧ z)
        [x∧[y∧z]≤y∧z] = first (second (∧-glb x (y ∧ z)))
 
        [y∧z≤y] : (y ∧ z) ≤ y
        [y∧z≤y] = first (∧-glb y z)

        [y∧z≤z] : (y ∧ z) ≤ z
        [y∧z≤z] = first (second (∧-glb y z))

        [x∧[y∧z]≤y] : (x ∧ (y ∧ z)) ≤ y
        [x∧[y∧z]≤y] = ≤-trans [x∧[y∧z]≤y∧z] [y∧z≤y]

        [x∧[y∧z]≤z] : (x ∧ (y ∧ z)) ≤ z
        [x∧[y∧z]≤z] = ≤-trans [x∧[y∧z]≤y∧z] [y∧z≤z]

        [x∧[y∧z]≤x∧y] : (x ∧ (y ∧ z)) ≤ (x ∧ y)
        [x∧[y∧z]≤x∧y] = (second (second (∧-glb x y))) (x ∧ (y ∧ z)) ([x∧[y∧z]≤x] , [x∧[y∧z]≤y] )

      [[x∧y]∧z≤x∧[y∧z]] : ((x ∧ y) ∧ z) ≤ (x ∧ (y ∧ z))
      [[x∧y]∧z≤x∧[y∧z]] = (second (second (∧-glb x (y ∧ z)))) ((x ∧ y) ∧ z) ([[x∧y]∧z≤x] , [[x∧y]∧z≤y∧z])
       where
        [[x∧y]∧z≤x∧y] : ((x ∧ y) ∧ z) ≤ (x ∧ y)
        [[x∧y]∧z≤x∧y] = first (∧-glb (x ∧ y) z)

        [[x∧y]∧z≤z] : ((x ∧ y) ∧ z) ≤ z
        [[x∧y]∧z≤z] = first (second (∧-glb (x ∧ y) z))

        [x∧y≤x] : (x ∧ y) ≤ x
        [x∧y≤x] = first (∧-glb x y)

        [x∧y≤y] : (x ∧ y) ≤ y
        [x∧y≤y] = first (second (∧-glb x y))

        [[x∧y]∧z≤x] : ((x ∧ y) ∧ z) ≤ x
        [[x∧y]∧z≤x] = ≤-trans [[x∧y]∧z≤x∧y] [x∧y≤x]

        [[x∧y]∧z≤y] : ((x ∧ y) ∧ z) ≤ y
        [[x∧y]∧z≤y] = ≤-trans [[x∧y]∧z≤x∧y] [x∧y≤y] 

        [[x∧y]∧z≤y∧z] : ((x ∧ y) ∧ z) ≤ (y ∧ z)
        [[x∧y]∧z≤y∧z] = (second (second (∧-glb y z))) ((x ∧ y) ∧ z) ([[x∧y]∧z≤y] , [[x∧y]∧z≤z])



    ∨-comm : (x y : A) → (x ∨ y) ≡ (y ∨ x)
    ∨-comm x y = ≤-antisym [x∨y≤y∨x] [y∨x≤x∨y]
     where
      [y∨x≤x∨y] : (y ∨ x) ≤ (x ∨ y)
      [y∨x≤x∨y] = (second (second (∨-lub y x))) (x ∨ y) ([y≤x∨y] , [x≤x∨y])
       where
        [x≤x∨y] : x ≤ (x ∨ y)
        [x≤x∨y] = first (∨-lub x y)
 
        [y≤x∨y] : y ≤ (x ∨ y)
        [y≤x∨y] = first (second (∨-lub x y))

      [x∨y≤y∨x] : (x ∨ y) ≤ (y ∨ x)
      [x∨y≤y∨x] = (second (second (∨-lub x y))) (y ∨ x) ([x≤y∨x] , [y≤y∨x])
       where 
        [y≤y∨x] : y ≤ (y ∨ x)
        [y≤y∨x] = first (∨-lub y x)

        [x≤y∨x] : x ≤ (y ∨ x)
        [x≤y∨x] = first (second (∨-lub y x))


    ∨-assoc : (x y z : A) → (x ∨ (y ∨ z)) ≡ ((x ∨ y) ∨ z)
    ∨-assoc x y z = ≤-antisym [x∨[y∨z]≤[x∨y]∨z] [[x∨y]∨z≤x∨[y∨z]]
     where
      [[x∨y]∨z≤x∨[y∨z]] : ((x ∨ y) ∨ z) ≤ (x ∨ (y ∨ z))
      [[x∨y]∨z≤x∨[y∨z]] = (second (second (∨-lub (x ∨ y) z))) (x ∨ (y ∨ z)) ([x∨y≤x∨[y∨z]] , [z≤x∨[y∨z]])
       where
        [x≤x∨[y∨z]] : x ≤ (x ∨ (y ∨ z))
        [x≤x∨[y∨z]] = first (∨-lub x (y ∨ z))

        [y∨z≤x∨[y∨z]] : (y ∨ z) ≤ (x ∨ (y ∨ z))
        [y∨z≤x∨[y∨z]] = first (second (∨-lub x (y ∨ z)))

        [y≤y∨z] : y ≤ (y ∨ z)
        [y≤y∨z] = first (∨-lub y z)

        [z≤y∨z] : z ≤ (y ∨ z)
        [z≤y∨z] = first (second (∨-lub y z))

        [y≤x∨[y∨z]] : y ≤ (x ∨ (y ∨ z))
        [y≤x∨[y∨z]] = ≤-trans [y≤y∨z] [y∨z≤x∨[y∨z]]

        [z≤x∨[y∨z]] : z ≤ (x ∨ (y ∨ z))
        [z≤x∨[y∨z]] = ≤-trans [z≤y∨z] [y∨z≤x∨[y∨z]]

        [x∨y≤x∨[y∨z]] : (x ∨ y) ≤ (x ∨ (y ∨ z))
        [x∨y≤x∨[y∨z]] = (second (second (∨-lub x y))) (x ∨ (y ∨ z)) ([x≤x∨[y∨z]] , [y≤x∨[y∨z]])
   
      [x∨[y∨z]≤[x∨y]∨z] : (x ∨ (y ∨ z)) ≤ ((x ∨ y) ∨ z)
      [x∨[y∨z]≤[x∨y]∨z] = (second (second (∨-lub x (y ∨ z)))) ((x ∨ y) ∨ z) ([x≤[x∨y]∨z] , [y∨z≤[x∨y]∨z])
       where
        [x∨y≤[x∨y]∨z] : (x ∨ y) ≤ ((x ∨ y) ∨ z)
        [x∨y≤[x∨y]∨z] = first (∨-lub (x ∨ y) z)
 
        [z≤[x∨y]∨z] : z ≤ ((x ∨ y) ∨ z)
        [z≤[x∨y]∨z] = first (second (∨-lub (x ∨ y) z))

        [x≤x∨y] : x ≤ (x ∨ y)
        [x≤x∨y] = first (∨-lub x y)
    
        [y≤x∨y] : y ≤ (x ∨ y)
        [y≤x∨y] = first (second (∨-lub x y))

        [x≤[x∨y]∨z] : x ≤ ((x ∨ y) ∨ z)
        [x≤[x∨y]∨z] = ≤-trans [x≤x∨y] [x∨y≤[x∨y]∨z]

        [y≤[x∨y]∨z] : y ≤ ((x ∨ y) ∨ z)
        [y≤[x∨y]∨z] = ≤-trans [y≤x∨y] [x∨y≤[x∨y]∨z]
    
        [y∨z≤[x∨y]∨z] : (y ∨ z) ≤ ((x ∨ y) ∨ z)
        [y∨z≤[x∨y]∨z] = (second (second (∨-lub y z))) ((x ∨ y) ∨ z) ([y≤[x∨y]∨z] , [z≤[x∨y]∨z])

    ∧∨-absorp : (x y : A) → (x ∧ (x ∨ y)) ≡ x
    ∧∨-absorp x y = ≤-antisym [x∧[x∨y]≤x] [x≤x∧[x∨y]]
     where
      [x∧[x∨y]≤x] : (x ∧ (x ∨ y)) ≤ x
      [x∧[x∨y]≤x] = first (∧-glb x (x ∨ y))

      [x≤x∧[x∨y]] : x ≤ (x ∧ (x ∨ y))
      [x≤x∧[x∨y]] = (second (second (∧-glb x (x ∨ y)))) x ([x≤x] , [x≤x∨y])
       where
        [x≤x] : x ≤ x
        [x≤x] = ≤-refl x

        [x≤x∨y] : x ≤ (x ∨ y)
        [x≤x∨y] = first (∨-lub x y)
       

    ∨∧-absorp : (x y : A) → (x ∨ (x ∧ y)) ≡ x
    ∨∧-absorp x y = ≤-antisym [x∨[x∧y]≤x] [x≤x∨[x∧y]]
     where
      [x≤x∨[x∧y]] : x ≤ (x ∨ (x ∧ y))
      [x≤x∨[x∧y]] = first (∨-lub x (x ∧ y))

      [x∨[x∧y]≤x] : (x ∨ (x ∧ y)) ≤ x
      [x∨[x∧y]≤x] = (second (second (∨-lub x (x ∧ y)))) x ([x≤x] , [x∧y≤x])
       where
        [x≤x] : x ≤ x
        [x≤x] = ≤-refl x

        [x∧y≤x] : (x ∧ y) ≤ x
        [x∧y≤x] = first (∧-glb x y)



Formulation3→Formulation1 : ∀ {i j k} (A : Set i) (≡ : A → A → Set k) (≤ : A → A → Set j) (∧ : A → A → A) (∨ : A → A → A) → Formulation3 A ≡ ≤ ∧ ∨ → Formulation1 A ≡ ≤ ∧ ∨
Formulation3→Formulation1 {i} {j} {k} A _≡_ _≤_ _∧_ _∨_ Formulation3-A = Formulation1-A
 where
  open Formulation3 Formulation3-A
  Formulation1-A =
   record {
    ≡-refl = ≡-refl ;
    ≡-sym = ≡-sym ;
    ≡-trans = ≡-trans ;
    ≤-refl = ≤-refl' ;
    ≤-antisym = ≤-antisym ;
    ≤-trans = ≤-trans ;
    ∨-lub = ∨-lub ;
    ∧-glb = ∧-glb
   }
   where
    ≤-refl' : {x y : A} → x ≡ y → (x ≤ y) × (y ≤ x)
    ≤-refl' p₁ = (≤-refl p₁ , ≤-refl (≡-sym p₁)) 

{-
Formulation3→Formulation2
Formulation3→Formulation3
Formulation3→Formulation4
Formulation3→Formulation5
-}


Formulation4→Formulation1 : ∀ {i j k} (A : Set i) (≡ : A → A → Set k) (≤ : A → A → Set j) (∧ : A → A → A) (∨ : A → A → A) → Formulation4 A ≡ ≤ ∧ ∨ → Formulation1 A ≡ ≤ ∧ ∨
Formulation4→Formulation1 {i} {j} {k} A _≡_ _≤_ _∧_ _∨_ Formulation4-A = Formulation1-A
 where
  open Formulation4 Formulation4-A
  Formulation1-A =
   record {
    ≡-refl = ≡-refl ;
    ≡-sym = ≡-sym ;
    ≡-trans = ≡-trans ;
    ≤-refl = ≤-refl' ;
    ≤-antisym = ≤-antisym ;
    ≤-trans = ≤-trans ;
    ∨-lub = ∨-lub ;
    ∧-glb = ∧-glb
   }
   where
    ≤-refl' : {x y : A} → x ≡ y → (x ≤ y) × (y ≤ x)
    ≤-refl' {x} {y} p₁ = (≤-cont {x} {x} {x} {y} (≡-refl x) p₁ (≤-refl x) , ≤-cont {y} {y} {y} {x} (≡-refl y) (≡-sym p₁) (≤-refl y))

{-
Formulation4→Formulation2
Formulation4→Formulation3
Formulation4→Formulation5
Formulation4→Formulation6
-}

{-
¬[Formulation5→Formulation2]
-}

Formulation5-==→Formulation5-≡ : ∀ {i k} (A : Set i) (_∧_ : A → A → A) (_∨_ : A → A → A) → Formulation5 A _==_ _∧_ _∨_ → (_≡_ : A → A → Set k) → isEquivalence _≡_ → Formulation5 A _≡_ _∧_ _∨_
Formulation5-==→Formulation5-≡ {i} {k} A _∧_ _∨_ Formulation5-A _≡_ ≡-equiv =
 record {
  ≡-refl = ≡-refl ;
  ≡-sym = ≡-sym ;
  ≡-trans = ≡-trans ;
  ∧-comm = ∧-comm' ;
  ∧-assoc = ∧-assoc' ;
  ∧∨-absorp = ∧∨-absorp' ;
  ∨-comm = ∨-comm' ;
  ∨-assoc = ∨-assoc' ;
  ∨∧-absorp = ∨∧-absorp'  
 }
 where
  open isEquivalence ≡-equiv
  open Formulation5 Formulation5-A hiding (≡-refl ; ≡-sym ; ≡-trans)
  ∧-comm' : (x y : A) → (x ∧ y) ≡ (y ∧ x)
  ∧-comm' x y = proof
   where
    [x∧y==y∧x] : (x ∧ y) == (y ∧ x)
    [x∧y==y∧x] = ∧-comm x y

    [x∧y≡x∧y] : (x ∧ y) ≡ (x ∧ y)
    [x∧y≡x∧y] = ≡-refl (x ∧ y)

    [x∧y≡x∧y]==[x∧y≡y∧x] : ((x ∧ y) ≡ (x ∧ y)) == ((x ∧ y) ≡ (y ∧ x))
    [x∧y≡x∧y]==[x∧y≡y∧x] = [x==y]→[fx==fy] (λ q → (x ∧ y) ≡ q) (x ∧ y) (y ∧ x) [x∧y==y∧x]

    proof = [A==B]→[A→B] [x∧y≡x∧y]==[x∧y≡y∧x] [x∧y≡x∧y]

  ∧-assoc' : (x y z : A) → (x ∧ (y ∧ z)) ≡ ((x ∧ y) ∧ z)
  ∧-assoc' x y z = [A==B]→[A→B] ([x==y]→[fx==fy] (λ q → (x ∧ (y ∧ z)) ≡ q) (x ∧ (y ∧ z)) ((x ∧ y) ∧ z) (∧-assoc x y z)) (≡-refl (x ∧ (y ∧ z)))

  ∧∨-absorp' : (x y : A) → (x ∧ (x ∨ y)) ≡ x
  ∧∨-absorp' x y = [A==B]→[A→B] ([x==y]→[fx==fy] (λ q → (x ∧ (x ∨ y)) ≡ q) (x ∧ (x ∨ y)) x (∧∨-absorp x y)) (≡-refl (x ∧ (x ∨ y)))

  ∨-comm' : (x y : A) → (x ∨ y) ≡ (y ∨ x)
  ∨-comm' x y = [A==B]→[A→B] ([x==y]→[fx==fy] (λ q → (x ∨ y) ≡ q) (x ∨ y) (y ∨ x) (∨-comm x y)) (≡-refl (x ∨ y))

  ∨-assoc' : (x y z : A) → (x ∨ (y ∨ z)) ≡ ((x ∨ y) ∨ z)
  ∨-assoc' x y z = [A==B]→[A→B] ([x==y]→[fx==fy] (λ q → (x ∨ (y ∨ z)) ≡ q) (x ∨ (y ∨ z)) ((x ∨ y) ∨ z) (∨-assoc x y z)) (≡-refl (x ∨ (y ∨ z)))

  ∨∧-absorp' : (x y : A) → (x ∨ (x ∧ y)) ≡ x
  ∨∧-absorp' x y = [A==B]→[A→B] ([x==y]→[fx==fy] (λ q → (x ∨ (x ∧ y)) ≡ q) (x ∨ (x ∧ y)) x (∨∧-absorp x y)) (≡-refl (x ∨ (x ∧ y)))

¬[Formulation5→Formulation6] : (∀ {i k} (A : Set i) (_≡_ : A → A → Set k) (_∧_ : A → A → A) (_∨_ : A → A → A) → Formulation5 A _≡_ _∧_ _∨_ → Formulation6 A _≡_  _∧_ _∨_) → ⊥
¬[Formulation5→Formulation6] assump = proof
 where
  Formulation5-four : Formulation5 four _==_ four-∧ four-∨
  Formulation5-four = 
   record {
    ≡-refl = ==-refl ;
    ≡-sym = ==-sym ;
    ≡-trans = ==-trans ;
    ∧-comm = four-∧-comm ;
    ∧-assoc = four-∧-assoc ;
    ∧∨-absorp = four-∧∨-absorp ;
    ∨-comm = four-∨-comm ;
    ∨-assoc = four-∨-assoc ;
    ∨∧-absorp = four-∨∧-absorp
   }

  Formulation5-four-≡ : Formulation5 four four-≡ four-∧ four-∨
  Formulation5-four-≡ = Formulation5-==→Formulation5-≡ four four-∧ four-∨ Formulation5-four four-≡ four-≡-equiv

  ¬[Formulation6-four-≡] : (Formulation6 four four-≡ four-∧ four-∨) → ⊥
  ¬[Formulation6-four-≡] Formulation6-four = subproof
   where
    open Formulation6 Formulation6-four
    subproof = ¬[four-∧-cont] ∧-cont

  Formulation6-four-≡ : Formulation6 four four-≡ four-∧ four-∨
  Formulation6-four-≡ = assump four four-≡ four-∧ four-∨ Formulation5-four-≡

  proof = ¬[Formulation6-four-≡] Formulation6-four-≡

{-
¬[Formulation5→Formulation1]
¬[Formulation5→Formulation3]
¬[Formulation5→Formulation4]
-}

Formulation6→Formulation1 : ∀ {i k} (A : Set i) (_≡_ : A → A → Set k) (_∧_ : A → A → A) (_∨_ : A → A → A) → Formulation6 A _≡_ _∧_ _∨_ → Formulation1 A _≡_ (λ x y → ((x ∧ y) ≡ x)) _∧_ _∨_
Formulation6→Formulation1 {i} {k} A _≡_ _∧_ _∨_ Formulation6-A = Formulation1-A
 where
  open Formulation6 Formulation6-A

  _≤_ : A → A → Set k
  x ≤ y = (x ∧ y) ≡ x

  ≤-refl : {x y : A} → (x ≡ y) → (x ≤ y) × (y ≤ x)
  ≤-refl {x} {y} [x≡y] = proof
   where
    [x∧y≡x] : (x ∧ y) ≡ x
    [x∧y≡x] = subproof
     where
      [x∧y≡x∧x] : (x ∧ y) ≡ (x ∧ x)
      [x∧y≡x∧x] = ∧-cont x x y x (≡-refl x) (≡-sym [x≡y])

      [x∧x≡x∧[x∨[x∧x]]] : (x ∧ x) ≡ (x ∧ (x ∨ (x ∧ x)))
      [x∧x≡x∧[x∨[x∧x]]] = ∧-cont x x x (x ∨ (x ∧ x)) (≡-refl x) (≡-sym (∨∧-absorp x x))

      [x∧[x∨[x∧x]]≡x] : (x ∧ (x ∨ (x ∧ x))) ≡ x
      [x∧[x∨[x∧x]]≡x] = ∧∨-absorp x (x ∧ x)

      subproof : (x ∧ y) ≡ x
      subproof = ≡-trans [x∧y≡x∧x] (≡-trans [x∧x≡x∧[x∨[x∧x]]] [x∧[x∨[x∧x]]≡x])
    [y∧x≡y] : (y ∧ x) ≡ y
    [y∧x≡y] = subproof
     where
      [y∧x≡y∧y] : (y ∧ x) ≡ (y ∧ y)
      [y∧x≡y∧y] = ∧-cont y y x y (≡-refl y) [x≡y]

      [y∧y≡y∧[y∨[y∧y]]] : (y ∧ y) ≡ (y ∧ (y ∨ (y ∧ y)))
      [y∧y≡y∧[y∨[y∧y]]] = ∧-cont y y y (y ∨ (y ∧ y)) (≡-refl y) (≡-sym (∨∧-absorp y y))

      [y∧[y∨[y∧y]]≡y] : (y ∧ (y ∨ (y ∧ y))) ≡ y
      [y∧[y∨[y∧y]]≡y] = ∧∨-absorp y (y ∧ y)
 
      subproof : (y ∧ x) ≡ y
      subproof = ≡-trans [y∧x≡y∧y] (≡-trans [y∧y≡y∧[y∨[y∧y]]] [y∧[y∨[y∧y]]≡y])
    proof : ((x ∧ y) ≡ x) × ((y ∧ x) ≡ y)
    proof = ([x∧y≡x] , [y∧x≡y])

  ≤-antisym : {x y : A} → x ≤ y → y ≤ x → x ≡ y
  ≤-antisym {x} {y} [x≤y] [y≤x] = ≡-trans (≡-sym [x≤y]) (≡-trans (∧-comm x y) [y≤x])

  ≤-trans : {x y z : A} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans {x} {y} {z} [x≤y] [y≤z] = [x≤z]
   where
    [x∧z≡[x∧y]∧z] : (x ∧ z) ≡ ((x ∧ y) ∧ z)
    [x∧z≡[x∧y]∧z] = ∧-cont x (x ∧ y) z z (≡-sym [x≤y]) (≡-refl z)

    [[x∧y]∧z≡x∧[y∧z]] : ((x ∧ y) ∧ z) ≡ (x ∧ (y ∧ z))
    [[x∧y]∧z≡x∧[y∧z]] = ≡-sym (∧-assoc x y z)

    [x∧[y∧z]≡x∧y] : (x ∧ (y ∧ z)) ≡ (x ∧ y)
    [x∧[y∧z]≡x∧y] = ∧-cont x x (y ∧ z) y (≡-refl x) [y≤z]

    [x≤z] : (x ∧ z) ≡ x
    [x≤z] = ≡-trans [x∧z≡[x∧y]∧z] (≡-trans [[x∧y]∧z≡x∧[y∧z]] (≡-trans [x∧[y∧z]≡x∧y] [x≤y]))

  ∧-glb : (x y : A) → ((x ∧ y) ≤ x) × (((x ∧ y) ≤ y) × ((z : A) → (z ≤ x) × (z ≤ y) → z ≤ (x ∧ y)))
  ∧-glb x y = ([x∧y≤x] , ([x∧y≤y] , [x∧y]-greatest))
   where
    [x∧y≤x] : ((x ∧ y) ∧ x) ≡ (x ∧ y)
    [x∧y≤x] = ≡-trans (∧-comm (x ∧ y) x) (≡-trans (∧-assoc x x y) (∧-cont (x ∧ x) x y y (first (≤-refl (≡-refl x))) (≡-refl y)))

    [x∧y≤y] : ((x ∧ y) ∧ y) ≡ (x ∧ y)
    [x∧y≤y] = ≡-trans (∧-comm (x ∧ y) y) (≡-trans (∧-cont y y (x ∧ y) (y ∧ x) (≡-refl y) (∧-comm x y)) (≡-trans (∧-assoc y y x) (≡-trans (∧-cont (y ∧ y) y x x (first (≤-refl (≡-refl y))) (≡-refl x)) (∧-comm y x))))

    [x∧y]-greatest : (z : A) → (z ≤ x) × (z ≤ y) → z ≤ (x ∧ y)
    [x∧y]-greatest z ([z∧x≡z] , [z∧y≡z]) = ≡-trans (∧-assoc z x y) (≡-trans (∧-cont (z ∧ x) z y y [z∧x≡z] (≡-refl y)) [z∧y≡z])

  ∨-lub : (x y : A) → (x ≤ (x ∨ y)) × ((y ≤ (x ∨ y)) × ((z : A) → (x ≤ z) × (y ≤ z) → ((x ∨ y) ≤ z)))
  ∨-lub x y = ([x≤x∨y] , ([y≤x∨y] , [x∨y]-least))
   where
    [x≤x∨y] : (x ∧ (x ∨ y)) ≡ x
    [x≤x∨y] = ∧∨-absorp x y

    [y≤x∨y] : (y ∧ (x ∨ y)) ≡ y
    [y≤x∨y] = ≡-trans (∧-cont y y (x ∨ y) (y ∨ x) (≡-refl y) (∨-comm x y)) (∧∨-absorp y x)

    [x∨y]-least : (z : A) → (x ≤ z) × (y ≤ z) → (x ∨ y) ≤ z
    [x∨y]-least z ([x∧z≡x] , [y∧z≡y]) = [[x∨y]∧z≡x∨y]
     where
      {- How convenient: https://math.stackexchange.com/questions/1898510/from-algebraic-lattice-to-a-poset-lattice -}
      [x∨z≡z] : (x ∨ z) ≡ z
      [x∨z≡z] = ≡-trans (∨-cont x (z ∧ x) z z (≡-trans (≡-sym [x∧z≡x]) (∧-comm x z)) (≡-refl z)) (≡-trans (∨-comm (z ∧ x) z) (∨∧-absorp z x))

      [y∨z≡z] : (y ∨ z) ≡ z
      [y∨z≡z] = ≡-trans (∨-cont y (z ∧ y) z z (≡-trans (≡-sym [y∧z≡y]) (∧-comm y z)) (≡-refl z)) (≡-trans (∨-comm (z ∧ y) z) (∨∧-absorp z y))

      [[x∨y]∧z≡x∨y] = ≡-trans (∧-cont (x ∨ y) (x ∨ y) z (x ∨ z) (≡-refl (x ∨ y)) (≡-sym [x∨z≡z])) (≡-trans (∧-cont (x ∨ y) (x ∨ y) (x ∨ z) (x ∨ (y ∨ z)) (≡-refl (x ∨ y)) (∨-cont x x z (y ∨ z) (≡-refl x) (≡-sym [y∨z≡z]))) (≡-trans (∧-cont (x ∨ y) (x ∨ y) (x ∨ (y ∨ z)) ((x ∨ y) ∨ z) (≡-refl (x ∨ y)) (∨-assoc x y z)) (∧∨-absorp (x ∨ y) z)))
    
  Formulation1-A = 
   record {
    ≡-refl = ≡-refl ;
    ≡-sym = ≡-sym ;
    ≡-trans = ≡-trans ;
    ≤-refl = ≤-refl ;
    ≤-antisym = ≤-antisym ;
    ≤-trans = ≤-trans ;
    ∧-glb = ∧-glb ;
    ∨-lub = ∨-lub
   }
{-
Formulation6→Formulation2
Formulation6→Formulation3
Formulation6→Formulation4
Formulation6→Formulation5
-}

Formulation2-==→Formulation2-≡ : ∀ {i j k} (A : Set i) (_≤_ : A → A → Set j) (_∧_ : A → A → A) (_∨_ : A → A → A) → Formulation2 A _==_ _≤_ _∧_ _∨_ → (_≡_ : A → A → Set k) → isEquivalence _≡_ → Formulation2 A _≡_ _≤_ _∧_ _∨_
Formulation2-==→Formulation2-≡ {i} {j} {k} A _≤_ _∧_ _∨_ Formulation2-A-== _≡_ ≡-equiv = Formulation2-A-≡
 where
  open isEquivalence ≡-equiv
  open Formulation2 Formulation2-A-== hiding (≡-refl ; ≡-sym ; ≡-trans)
  Formulation2-A-≡ =
   record {
    ≡-refl = ≡-refl ;
    ≡-sym = ≡-sym ;
    ≡-trans = ≡-trans ;
    ≤-refl = ≤-refl ;
    ≤-antisym = ≤-antisym' ;
    ≤-trans = ≤-trans ;
    ∧-glb = ∧-glb ;
    ∨-lub = ∨-lub 
   }
   where
    ≤-antisym' : {x y : A} → x ≤ y → y ≤ x → x ≡ y
    ≤-antisym' {x} {y} [x≤y] [y≤x] = [A==B]→[A→B] ([x==y]→[fx==fy] (λ q → (x ≡ q)) x y (≤-antisym [x≤y] [y≤x])) (≡-refl x)

¬[Formulation2→Formulation6] : (∀ {i j k} (A : Set i) (_≡_ : A → A → Set k) (_≤_ : A → A → Set j) (_∧_ : A → A → A) (_∨_ : A → A → A) → Formulation2 A _≡_ _≤_ _∧_ _∨_ → Formulation6 A _≡_ _∧_ _∨_) → ⊥
¬[Formulation2→Formulation6] assump = proof
 where
  Formulation6-four : Formulation6 four _==_ four-∧ four-∨
  Formulation6-four =
   record {
    ≡-refl = ==-refl ;
    ≡-sym = ==-sym ;
    ≡-trans = ==-trans ;
    ∧-cont = ∧-cont ;
    ∧-comm = four-∧-comm ;
    ∧-assoc = four-∧-assoc ;
    ∧∨-absorp = four-∧∨-absorp ;
    ∨-cont = ∨-cont ;
    ∨-comm = four-∨-comm ;
    ∨-assoc = four-∨-assoc ;
    ∨∧-absorp = four-∨∧-absorp
   }
   where
    ∧-cont : (x x' y y' : four) → x == x' → y == y' → four-∧ x y == four-∧ x' y'
    ∧-cont x .x y .y refl refl = refl

    ∨-cont : (x x' y y' : four) → x == x' → y == y' → four-∨ x y == four-∨ x' y'
    ∨-cont x .x y .y refl refl = refl

  Formulation2-four : Formulation2 four _==_ (λ x y → four-∧ x y == x) four-∧ four-∨
  Formulation2-four = Formulation1→Formulation2 four _==_ (λ x y → four-∧ x y == x) four-∧ four-∨ (Formulation6→Formulation1 four _==_ four-∧ four-∨ Formulation6-four)

  Formulation2-four-≡ : Formulation2 four four-≡ (λ x y → four-∧ x y == x) four-∧ four-∨
  Formulation2-four-≡ = Formulation2-==→Formulation2-≡ four (λ x y → four-∧ x y == x) four-∧ four-∨ Formulation2-four four-≡ four-≡-equiv

  ¬[Formulation6-four-≡] : (Formulation6 four four-≡ four-∧ four-∨) → ⊥
  ¬[Formulation6-four-≡] Formulation6-four-≡ = subproof
   where
    open Formulation6 Formulation6-four-≡
    subproof = ¬[four-∧-cont] ∧-cont

  Formulation6-four-≡ : Formulation6 four four-≡ four-∧ four-∨
  Formulation6-four-≡ = assump four four-≡ (λ x y → four-∧ x y == x) four-∧ four-∨ Formulation2-four-≡

  proof = ¬[Formulation6-four-≡] Formulation6-four-≡
