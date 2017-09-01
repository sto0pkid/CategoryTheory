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
  ≡-sym : (x y : A) → x ≡ y → y ≡ x
  ≡-trans : (x y z : A) → x ≡ y → y ≡ z → x ≡ z


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

record isPartialOrder' {i} {j} {k} {A : Set i} {_≡_ : A → A → Set k} {≡-equiv : isEquivalence _≡_} (_≤_ : A → A → Set j) : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
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

isCommutative : ∀ {i j k} {A : Set i} {B : Set j} {_≡_ : B → B → Set k} {p : isEquivalence _≡_} → (f : A → A → B) → Set (i ⊔ k)
isCommutative {i} {j} {k} {A} {B} {_≡_} {≡-equiv} f = (x y : A) → (f x y) ≡ (f y x)

isAssociative : ∀ {i j} {A : Set i} {_≡_ : A → A → Set j} {p : isEquivalence _≡_} → (f : A → A → A) → Set (i ⊔ j)
isAssociative {i} {j} {A} {_≡_} {≡-equiv} f = (x y z : A) → (f x (f y z)) ≡ (f (f x y) z)

absorbs : ∀ {i j} {A : Set i} {_≡_ : A → A → Set j} {p : isEquivalence _≡_} → (f : A → A → A) → (g : A → A → A) → Set (i ⊔ j)
absorbs {i} {j} {A} {_≡_}{≡-equiv} f g = (x y : A) → (f x (g x y)) ≡ x

distributesOver : ∀ {i j} {A : Set i} {_≡_ : A → A → Set j} {p : isEquivalence _≡_} → (f : A → A → A) → (g : A → A → A) → Set (i ⊔ j)
distributesOver {i} {j} {A} {_≡_} {≡-equiv} f g = (x y z : A) → (f x (g y z)) ≡ (g (f x y) (f x z)) 

  
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
  ≡-sym : (x y : carrier) → x ≡ y → y ≡ x
  ≡-trans : (x y z : carrier) → x ≡ y → y ≡ z → x ≡ z
  _≤_ : carrier → carrier → Set j
  ≤-refl : (x y : carrier) → x ≡ y → (x ≤ y) × (y ≤ x)
  ≤-trans : (x y z : carrier) → x ≤ y → y ≤ z → x ≤ z
  ≤-antisym : (x y : carrier) → x ≤ y → y ≤ x → x ≡ y
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
  ≤-po : isPartialOrder' {i} {j} {k} {carrier} {_≡_} {≡-equiv} _≤_
  _∧_ : carrier → carrier → carrier
  ∧-cont : (a b c d : carrier) → (a ≡ b) → (c ≡ d) → (a ∧ b) ≡ (c ∧ d)
  ∧-glb : (x y : carrier) → ((x ∧ y) ≤ x) × (((x ∧ y) ≤ y) × ((z : carrier) → (z ≤ x) × (z ≤ y) → (z ≤ (x ∧ y))))
  _∨_ : carrier → carrier → carrier
  ∨-cont : (a b c d : carrier) → (a ≡ b) → (c ≡ d) → (a ∨ b) ≡ (c ∨ d)
  ∨-lub : (x y : carrier) → (x ≤ (x ∨ y)) × ((y ≤ (x ∨ y)) × ((z : carrier) → (x ≤ z) × (y ≤ z) → ((x ∨ y) ≤ z)))


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
    [y≤y] = first (≤-refl y y [y≡y])
 
    [x∨y≤y] : (x ∨ y) ≤ y
    [x∨y≤y] = (second (second (∨-lub x y))) y ([x≤y] , [y≤y])
       
    left : (x ∨ y) ≡ y
    left = ≤-antisym (x ∨ y) y [x∨y≤y] [y≤x∨y]

    [x∧y≤x] : (x ∧ y) ≤ x
    [x∧y≤x] = first (∧-glb x y)

    [x≡x] : x ≡ x
    [x≡x] = ≡-refl x

    [x≤x] : x ≤ x
    [x≤x] = first (≤-refl x x [x≡x])

    [x≤x∧y] : x ≤ (x ∧ y)
    [x≤x∧y] = (second (second (∧-glb x y))) x ([x≤x] , [x≤y])

    right : (x ∧ y) ≡ x
    right = ≤-antisym (x ∧ y) x [x∧y≤x] [x≤x∧y]

  RTL : (((x ∨ y) ≡ y) × ((x ∧ y) ≡ x)) → (x ≤ y)
  RTL ([x∨y≡y] , [x∧y≡x]) = proof
   where
    [x≤x∧y] : x ≤ (x ∧ y)
    [x≤x∧y] = second (≤-refl (x ∧ y) x [x∧y≡x])

    [x∧y≤y] : (x ∧ y) ≤ y
    [x∧y≤y] = first (second (∧-glb x y))    

    proof : x ≤ y
    proof = ≤-trans x (x ∧ y) y [x≤x∧y] [x∧y≤y]


    
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

⊆-trans : ∀ {i} (A : Set i) (S₁ S₂ S₃ : A → Bool) → [ A || S₁ ⊆ S₂ ] → [ A || S₂ ⊆ S₃ ] → [ A || S₁ ⊆ S₃ ]
⊆-trans {i} A S₁ S₂ S₃ p₁₂ p₂₃ a [S₁a] = p₂₃ a (p₁₂ a [S₁a])

⊆-refl' : ∀ {i} (A : Set i) (S₁ S₂ : A → Bool) → ([ A || S₁ ⊆ S₂ ]) × ([ A || S₂ ⊆ S₁ ]) → ([ A || S₁ ⊆ S₂ ]) × ([ A || S₂ ⊆ S₁ ])
⊆-refl' A S₁ S₂ [S₁≡S₂] = [S₁≡S₂]

⊆-antisym : ∀ {i} (A : Set i) (S₁ S₂ : A → Bool) → [ A || S₁ ⊆ S₂ ] → [ A || S₂ ⊆ S₁ ] → [ A || S₁ ⊆ S₂ ] × [ A || S₂ ⊆ S₁ ]
⊆-antisym {i} A S₁ S₂ [S₁⊆S₂] [S₂⊆S₁] = ([S₁⊆S₂] , [S₂⊆S₁])

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
  ≡-sym = λ x y p → (second p , first p) ;
  ≡-trans = λ x y z p₁ p₂ → ((⊆-trans A x y z (first p₁) (first p₂)) , (⊆-trans A z y x (second p₂) (second p₁))) ;
  _≤_ = [_||_⊆_] A ;
  ≤-refl = ⊆-refl' A ;
  ≤-trans = ⊆-trans A ;
  ≤-antisym = ⊆-antisym A ;
  _∧_ = [_||_∩_] A ;
  ∧-glb = λ x y → ((x∩y⊆x x y) , ((x∩y⊆y x y) , λ z → (z⊆x→z⊆y→z⊆x∩y x y z))) ;
  _∨_ = [_||_∪_] A ;
  ∨-lub = λ x y → ((x⊆x∪y x y) , ((y⊆x∪y x y) , λ z → (x⊆z→y⊆z→x∪y⊆z x y z)))
 
 }


{-
http://documents.kenyon.edu/math/SamTay.pdf
Proposition 2.1.3
-}


record AlgebraicLattice {i} {j} {k} : Set (((lsuc i) ⊔ (lsuc j)) ⊔ (lsuc k)) where
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
  ≡-refl : (x : carrier) → x ≡ x
  ≡-sym : (x y : carrier) → x ≡ y → y ≡ x
  ≡-trans : (x y z : carrier) → x ≡ y → y ≡ z → x ≡ z
  _∧_ : carrier → carrier → carrier
  _∨_ : carrier → carrier → carrier
  ∧-comm : (x y : carrier) → (x ∧ y) ≡ (y ∧ x)
  ∧-assoc : (x y z : carrier) → (x ∧ (y ∧ z)) ≡ ((x ∧ y) ∧ z)
  ∧∨-absorp : (x y : carrier) → (x ∧ (x ∨ y)) ≡ x
  ∨-comm : (x y : carrier) → (x ∨ y) ≡ (y ∨ x)
  ∨-assoc : (x y z : carrier) → (x ∨ (y ∨ z)) ≡ ((x ∨ y) ∨ z)
  ∨∧-absorp : (x y : carrier) → (x ∨ (x ∧ y)) ≡ x


record AlgebraicLattice'' {i} {j} : Set ((lsuc i) ⊔ (lsuc j)) where
 field
  carrier : Set i
  _≡_ : carrier → carrier → Set j
  ≡-equiv : isEquivalence _≡_
  _∧_ : carrier → carrier → carrier
  _∨_ : carrier → carrier → carrier
  ∧-comm : isCommutative {i} {i} {j} {carrier} {carrier} {_≡_} {≡-equiv} _∧_
  ∧-assoc : isAssociative {i} {j} {carrier} {_≡_} {≡-equiv} _∧_
  ∧∨-absorp : absorbs {i} {j} {carrier} {_≡_} {≡-equiv} _∧_ _∨_
  ∨-comm : isCommutative {i} {i} {j} {carrier} {carrier} {_≡_} {≡-equiv} _∨_
  ∨-assoc : isAssociative {i} {j} {carrier} {_≡_} {≡-equiv} _∨_
  ∨∧-absorp : absorbs {i} {j} {carrier} {_≡_} {≡-equiv} _∨_ _∧_

record isAlgebraicLattice {i} {j} (A : Set i) : Set ((lsuc i) ⊔ (lsuc j)) where
 field
  _≡_ : A → A → Set j
  ≡-equiv : isEquivalence _≡_
  _∧_ : A → A → A
  _∨_ : A → A → A
  ∧-comm : isCommutative {i} {i} {j} {A} {A} {_≡_} {≡-equiv} _∧_
  ∧-assoc : isAssociative {i} {j} {A} {_≡_} {≡-equiv} _∧_
  ∧∨-absorp : absorbs {i} {j} {A} {_≡_} {≡-equiv} _∧_ _∨_
  ∨-comm : isCommutative {i} {i} {j} {A} {A} {_≡_} {≡-equiv} _∨_
  ∨-assoc : isAssociative {i} {j} {A} {_≡_} {≡-equiv} _∨_
  ∨∧-absorp : absorbs {i} {j} {A} {_≡_} {≡-equiv} _∨_ _∧_

record isAlgebraicLattice' {i} {j} (A : Set i) (_≡_ : A → A → Set j) (≡-equiv : isEquivalence _≡_) : Set ((lsuc i) ⊔ (lsuc j)) where
 field
  _∧_ : A → A → A
  _∨_ : A → A → A
  ∧-comm : isCommutative {i} {i} {j} {A} {A} {_≡_} {≡-equiv} _∧_
  ∧-assoc : isAssociative {i} {j} {A} {_≡_} {≡-equiv} _∧_
  ∧∨-absorp : absorbs {i} {j} {A} {_≡_} {≡-equiv} _∧_ _∨_
  ∨-comm : isCommutative {i} {i} {j} {A} {A} {_≡_} {≡-equiv} _∨_
  ∨-assoc : isAssociative {i} {j} {A} {_≡_} {≡-equiv} _∨_
  ∨∧-absorp : absorbs {i} {j} {A} {_≡_} {≡-equiv} _∨_ _∧_

record isAlgebraicLattice'' {i} {j} (A : Set i) (_≡_ : A → A → Set j) (≡-equiv : isEquivalence _≡_) (_∧_ : A → A → A) (_∨_ : A → A → A) : Set ((lsuc i) ⊔ (lsuc j)) where
 field 
  ∧-comm : isCommutative {i} {i} {j} {A} {A} {_≡_} {≡-equiv} _∧_
  ∧-assoc : isAssociative {i} {j} {A} {_≡_} {≡-equiv} _∧_
  ∧∨-absorp : absorbs {i} {j} {A} {_≡_} {≡-equiv} _∧_ _∨_
  ∨-comm : isCommutative {i} {i} {j} {A} {A} {_≡_} {≡-equiv} _∨_
  ∨-assoc : isAssociative {i} {j} {A} {_≡_} {≡-equiv} _∨_
  ∨∧-absorp : absorbs {i} {j} {A} {_≡_} {≡-equiv} _∨_ _∧_


--Fix this to OrderLattice'
OrderLattice→AlgebraLattice : ∀{i j k} → OrderLattice {i} {j} {k} → AlgebraicLattice {i} {j} {k}
OrderLattice→AlgebraLattice {i} {j} {k} O =  
 record {
  carrier = carrier;
  _≤_ = _≤_;
  _≡_ = _≡_ ;
  ≡-refl = ≡-refl ;
  ≡-sym = ≡-sym ;
  ≡-trans = ≡-trans ;
  ≤-refl = ≤-refl ;
  ≤-trans = ≤-trans ;
  ≤-antisym = ≤-antisym ;
  _∧_ = _∧_ ;
  _∨_ = _∨_ ;
  ∧-comm = ∧-comm ;
  ∧-assoc = ∧-assoc ;
  ∧∨-absorp = ∧∨-absorp ;
  ∨-comm = ∨-comm ;
  ∨-assoc = ∨-assoc ;
  ∨∧-absorp = ∨∧-absorp
 } 
 where
  open OrderLattice O

  ∧-comm : (x y : carrier) → (x ∧ y) ≡ (y ∧ x)
  ∧-comm x y = ≤-antisym (x ∧ y) (y ∧ x) [x∧y≤y∧x] [y∧x≤x∧y]
   where
    [x∧y≤x] : (x ∧ y) ≤ x
    [x∧y≤x] = first (∧-glb x y)

    [x∧y≤y] : (x ∧ y) ≤ y
    [x∧y≤y] = first (second (∧-glb x y))

    [x∧y≤y∧x] : (x ∧ y) ≤ (y ∧ x)
    [x∧y≤y∧x] = (second (second (∧-glb y x))) (x ∧ y) ([x∧y≤y] , [x∧y≤x])

    [y∧x≤y] : (y ∧ x) ≤ y
    [y∧x≤y] = first (∧-glb y x)

    [y∧x≤x] : (y ∧ x) ≤ x
    [y∧x≤x] = first (second (∧-glb y x))

    [y∧x≤x∧y] : (y ∧ x) ≤ (x ∧ y)
    [y∧x≤x∧y] = (second (second (∧-glb x y))) (y ∧ x) ([y∧x≤x] , [y∧x≤y])

  ∧-assoc : (x y z : carrier) → (x ∧ (y ∧ z)) ≡ ((x ∧ y) ∧ z)
  ∧-assoc x y z = ≤-antisym (x ∧ (y ∧ z)) ((x ∧ y) ∧ z) [x∧[y∧z]≤[x∧y]∧z] [[x∧y]∧z≤x∧[y∧z]]
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
    [x∧[y∧z]≤y] = ≤-trans (x ∧ (y ∧ z)) (y ∧ z) y [x∧[y∧z]≤y∧z] [y∧z≤y]

    [x∧[y∧z]≤z] : (x ∧ (y ∧ z)) ≤ z
    [x∧[y∧z]≤z] = ≤-trans (x ∧ (y ∧ z)) (y ∧ z) z [x∧[y∧z]≤y∧z] [y∧z≤z]

    [x∧[y∧z]≤x∧y] : (x ∧ (y ∧ z)) ≤ (x ∧ y)
    [x∧[y∧z]≤x∧y] = (second (second (∧-glb x y))) (x ∧ (y ∧ z)) ([x∧[y∧z]≤x] , [x∧[y∧z]≤y] )

    [x∧[y∧z]≤[x∧y]∧z] : (x ∧ (y ∧ z)) ≤ ((x ∧ y) ∧ z)
    [x∧[y∧z]≤[x∧y]∧z] = (second (second (∧-glb (x ∧ y) z))) (x ∧ (y ∧ z)) ([x∧[y∧z]≤x∧y] , [x∧[y∧z]≤z] )

    [[x∧y]∧z≤x∧y] : ((x ∧ y) ∧ z) ≤ (x ∧ y)
    [[x∧y]∧z≤x∧y] = first (∧-glb (x ∧ y) z)

    [[x∧y]∧z≤z] : ((x ∧ y) ∧ z) ≤ z
    [[x∧y]∧z≤z] = first (second (∧-glb (x ∧ y) z))

    [x∧y≤x] : (x ∧ y) ≤ x
    [x∧y≤x] = first (∧-glb x y)

    [x∧y≤y] : (x ∧ y) ≤ y
    [x∧y≤y] = first (second (∧-glb x y))

    [[x∧y]∧z≤x] : ((x ∧ y) ∧ z) ≤ x
    [[x∧y]∧z≤x] = ≤-trans ((x ∧ y) ∧ z) (x ∧ y) x [[x∧y]∧z≤x∧y] [x∧y≤x]

    [[x∧y]∧z≤y] : ((x ∧ y) ∧ z) ≤ y
    [[x∧y]∧z≤y] = ≤-trans ((x ∧ y) ∧ z) (x ∧ y) y [[x∧y]∧z≤x∧y] [x∧y≤y] 

    [[x∧y]∧z≤y∧z] : ((x ∧ y) ∧ z) ≤ (y ∧ z)
    [[x∧y]∧z≤y∧z] = (second (second (∧-glb y z))) ((x ∧ y) ∧ z) ([[x∧y]∧z≤y] , [[x∧y]∧z≤z])

    [[x∧y]∧z≤x∧[y∧z]] : ((x ∧ y) ∧ z) ≤ (x ∧ (y ∧ z))
    [[x∧y]∧z≤x∧[y∧z]] = (second (second (∧-glb x (y ∧ z)))) ((x ∧ y) ∧ z) ([[x∧y]∧z≤x] , [[x∧y]∧z≤y∧z])

  ∨-comm : (x y : carrier) → (x ∨ y) ≡ (y ∨ x)
  ∨-comm x y = ≤-antisym (x ∨ y) (y ∨ x) [x∨y≤y∨x] [y∨x≤x∨y]
   where
    [x≤x∨y] : x ≤ (x ∨ y)
    [x≤x∨y] = first (∨-lub x y)
 
    [y≤x∨y] : y ≤ (x ∨ y)
    [y≤x∨y] = first (second (∨-lub x y))
 
    [y∨x≤x∨y] : (y ∨ x) ≤ (x ∨ y)
    [y∨x≤x∨y] = (second (second (∨-lub y x))) (x ∨ y) ([y≤x∨y] , [x≤x∨y])
   
    [y≤y∨x] : y ≤ (y ∨ x)
    [y≤y∨x] = first (∨-lub y x)

    [x≤y∨x] : x ≤ (y ∨ x)
    [x≤y∨x] = first (second (∨-lub y x))

    [x∨y≤y∨x] : (x ∨ y) ≤ (y ∨ x)
    [x∨y≤y∨x] = (second (second (∨-lub x y))) (y ∨ x) ([x≤y∨x] , [y≤y∨x])

  ∨-assoc : (x y z : carrier) → (x ∨ (y ∨ z)) ≡ ((x ∨ y) ∨ z)
  ∨-assoc x y z = ≤-antisym (x ∨ (y ∨ z)) ((x ∨ y) ∨ z) [x∨[y∨z]≤[x∨y]∨z] [[x∨y]∨z≤x∨[y∨z]]
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
    [y≤x∨[y∨z]] = ≤-trans y (y ∨ z) (x ∨ (y ∨ z)) [y≤y∨z] [y∨z≤x∨[y∨z]]

    [z≤x∨[y∨z]] : z ≤ (x ∨ (y ∨ z))
    [z≤x∨[y∨z]] = ≤-trans z (y ∨ z) (x ∨ (y ∨ z)) [z≤y∨z] [y∨z≤x∨[y∨z]]

    [x∨y≤x∨[y∨z]] : (x ∨ y) ≤ (x ∨ (y ∨ z))
    [x∨y≤x∨[y∨z]] = (second (second (∨-lub x y))) (x ∨ (y ∨ z)) ([x≤x∨[y∨z]] , [y≤x∨[y∨z]])
   
    [[x∨y]∨z≤x∨[y∨z]] : ((x ∨ y) ∨ z) ≤ (x ∨ (y ∨ z))
    [[x∨y]∨z≤x∨[y∨z]] = (second (second (∨-lub (x ∨ y) z))) (x ∨ (y ∨ z)) ([x∨y≤x∨[y∨z]] , [z≤x∨[y∨z]])

    [x∨y≤[x∨y]∨z] : (x ∨ y) ≤ ((x ∨ y) ∨ z)
    [x∨y≤[x∨y]∨z] = first (∨-lub (x ∨ y) z)
 
    [z≤[x∨y]∨z] : z ≤ ((x ∨ y) ∨ z)
    [z≤[x∨y]∨z] = first (second (∨-lub (x ∨ y) z))

    [x≤x∨y] : x ≤ (x ∨ y)
    [x≤x∨y] = first (∨-lub x y)
   
    [y≤x∨y] : y ≤ (x ∨ y)
    [y≤x∨y] = first (second (∨-lub x y))

    [x≤[x∨y]∨z] : x ≤ ((x ∨ y) ∨ z)
    [x≤[x∨y]∨z] = ≤-trans x (x ∨ y) ((x ∨ y) ∨ z) [x≤x∨y] [x∨y≤[x∨y]∨z]

    [y≤[x∨y]∨z] : y ≤ ((x ∨ y) ∨ z)
    [y≤[x∨y]∨z] = ≤-trans y (x ∨ y) ((x ∨ y) ∨ z) [y≤x∨y] [x∨y≤[x∨y]∨z]
    
    [y∨z≤[x∨y]∨z] : (y ∨ z) ≤ ((x ∨ y) ∨ z)
    [y∨z≤[x∨y]∨z] = (second (second (∨-lub y z))) ((x ∨ y) ∨ z) ([y≤[x∨y]∨z] , [z≤[x∨y]∨z])

    [x∨[y∨z]≤[x∨y]∨z] : (x ∨ (y ∨ z)) ≤ ((x ∨ y) ∨ z)
    [x∨[y∨z]≤[x∨y]∨z] = (second (second (∨-lub x (y ∨ z)))) ((x ∨ y) ∨ z) ([x≤[x∨y]∨z] , [y∨z≤[x∨y]∨z])

  ∧∨-absorp : (x y : carrier) → (x ∧ (x ∨ y)) ≡ x
  ∧∨-absorp x y = ≤-antisym (x ∧ (x ∨ y)) x [x∧[x∨y]≤x] [x≤x∧[x∨y]]
   where
    [x∧[x∨y]≤x] : (x ∧ (x ∨ y)) ≤ x
    [x∧[x∨y]≤x] = first (∧-glb x (x ∨ y))

    [x≤x] : x ≤ x
    [x≤x] = ≤-refl x

    [x≤x∨y] : x ≤ (x ∨ y)
    [x≤x∨y] = first (∨-lub x y)

    [x≤x∧[x∨y]] : x ≤ (x ∧ (x ∨ y))
    [x≤x∧[x∨y]] = (second (second (∧-glb x (x ∨ y)))) x ([x≤x] , [x≤x∨y])

  ∨∧-absorp : (x y : carrier) → (x ∨ (x ∧ y)) ≡ x
  ∨∧-absorp x y = ≤-antisym (x ∨ (x ∧ y)) x [x∨[x∧y]≤x] [x≤x∨[x∧y]]
   where
    [x≤x∨[x∧y]] : x ≤ (x ∨ (x ∧ y))
    [x≤x∨[x∧y]] = first (∨-lub x (x ∧ y))

    [x≤x] : x ≤ x
    [x≤x] = ≤-refl x

    [x∧y≤x] : (x ∧ y) ≤ x
    [x∧y≤x] = first (∧-glb x y)

    [x∨[x∧y]≤x] : (x ∨ (x ∧ y)) ≤ x
    [x∨[x∧y]≤x] = (second (second (∨-lub x (x ∧ y)))) x ([x≤x] , [x∧y≤x])

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
  ∧-comm x y = ≤-antisym (x ∧ y) (y ∧ x) [x∧y≤y∧x] [y∧x≤x∧y]
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
  ∧-assoc x y z = ≤-antisym (x ∧ (y ∧ z)) ((x ∧ y) ∧ z) [x∧[y∧z]≤[x∧y]∧z] [[x∧y]∧z≤x∧[y∧z]]
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
      [x∧[y∧z]≤y] = ≤-trans (x ∧ (y ∧ z)) (y ∧ z) y [x∧[y∧z]≤y∧z] [y∧z≤y]

      [x∧[y∧z]≤z] : (x ∧ (y ∧ z)) ≤ z
      [x∧[y∧z]≤z] = ≤-trans (x ∧ (y ∧ z)) (y ∧ z) z [x∧[y∧z]≤y∧z] [y∧z≤z]

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
      [[x∧y]∧z≤x] = ≤-trans ((x ∧ y) ∧ z) (x ∧ y) x [[x∧y]∧z≤x∧y] [x∧y≤x]

      [[x∧y]∧z≤y] : ((x ∧ y) ∧ z) ≤ y
      [[x∧y]∧z≤y] = ≤-trans ((x ∧ y) ∧ z) (x ∧ y) y [[x∧y]∧z≤x∧y] [x∧y≤y] 

      [[x∧y]∧z≤y∧z] : ((x ∧ y) ∧ z) ≤ (y ∧ z)
      [[x∧y]∧z≤y∧z] = (second (second (∧-glb y z))) ((x ∧ y) ∧ z) ([[x∧y]∧z≤y] , [[x∧y]∧z≤z])



  ∨-comm : (x y : carrier) → (x ∨ y) ≡ (y ∨ x)
  ∨-comm x y = ≤-antisym (x ∨ y) (y ∨ x) [x∨y≤y∨x] [y∨x≤x∨y]
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
  ∨-assoc x y z = ≤-antisym (x ∨ (y ∨ z)) ((x ∨ y) ∨ z) [x∨[y∨z]≤[x∨y]∨z] [[x∨y]∨z≤x∨[y∨z]]
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
      [y≤x∨[y∨z]] = ≤-trans y (y ∨ z) (x ∨ (y ∨ z)) [y≤y∨z] [y∨z≤x∨[y∨z]]

      [z≤x∨[y∨z]] : z ≤ (x ∨ (y ∨ z))
      [z≤x∨[y∨z]] = ≤-trans z (y ∨ z) (x ∨ (y ∨ z)) [z≤y∨z] [y∨z≤x∨[y∨z]]

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
      [x≤[x∨y]∨z] = ≤-trans x (x ∨ y) ((x ∨ y) ∨ z) [x≤x∨y] [x∨y≤[x∨y]∨z]

      [y≤[x∨y]∨z] : y ≤ ((x ∨ y) ∨ z)
      [y≤[x∨y]∨z] = ≤-trans y (x ∨ y) ((x ∨ y) ∨ z) [y≤x∨y] [x∨y≤[x∨y]∨z]
    
      [y∨z≤[x∨y]∨z] : (y ∨ z) ≤ ((x ∨ y) ∨ z)
      [y∨z≤[x∨y]∨z] = (second (second (∨-lub y z))) ((x ∨ y) ∨ z) ([y≤[x∨y]∨z] , [z≤[x∨y]∨z])

  ∧∨-absorp : (x y : carrier) → (x ∧ (x ∨ y)) ≡ x
  ∧∨-absorp x y = ≤-antisym (x ∧ (x ∨ y)) x [x∧[x∨y]≤x] [x≤x∧[x∨y]]
   where
    [x∧[x∨y]≤x] : (x ∧ (x ∨ y)) ≤ x
    [x∧[x∨y]≤x] = first (∧-glb x (x ∨ y))

    [x≤x∧[x∨y]] : x ≤ (x ∧ (x ∨ y))
    [x≤x∧[x∨y]] = (second (second (∧-glb x (x ∨ y)))) x ([x≤x] , [x≤x∨y])
     where
      [x≤x] : x ≤ x
      [x≤x] = first (≤-refl x x (≡-refl x))

      [x≤x∨y] : x ≤ (x ∨ y)
      [x≤x∨y] = first (∨-lub x y)
       

  ∨∧-absorp : (x y : carrier) → (x ∨ (x ∧ y)) ≡ x
  ∨∧-absorp x y = ≤-antisym (x ∨ (x ∧ y)) x [x∨[x∧y]≤x] [x≤x∨[x∧y]]
   where
    [x≤x∨[x∧y]] : x ≤ (x ∨ (x ∧ y))
    [x≤x∨[x∧y]] = first (∨-lub x (x ∧ y))

    [x∨[x∧y]≤x] : (x ∨ (x ∧ y)) ≤ x
    [x∨[x∧y]≤x] = (second (second (∨-lub x (x ∧ y)))) x ([x≤x] , [x∧y≤x])
     where
      [x≤x] : x ≤ x
      [x≤x] = first (≤-refl x x (≡-refl x))

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
    [b≤a] = second (≤-refl a b [a≡b])

    [c≤d] : c ≤ d
    [c≤d] = first (≤-refl c d [c≡d])

    [b≤d] : b ≤ d
    [b≤d] = ≤-trans b a d [b≤a] (≤-trans a c d [a≤c] [c≤d])

  ∧-cont : (a b c d : carrier) → (a ≡ b) → (c ≡ d) → (a ∧ c) ≡ (b ∧ d)
  ∧-cont a b c d [a≡b] [c≡d] = [a∧c]≡[b∧d]
   where
    [b∧d≤a∧c] : (b ∧ d) ≤ (a ∧ c)
    [b∧d≤a∧c] = (second (second (∧-glb a c))) (b ∧ d) ([b∧d≤a] , [b∧d≤c])
     where
      [b∧d≤a] : (b ∧ d) ≤ a
      [b∧d≤a] = ≤-trans (b ∧ d) b a [b∧d≤b] [b≤a]
       where
        [b≤a] : b ≤ a
        [b≤a] = second (≤-refl a b [a≡b])

        [b∧d≤b] : (b ∧ d) ≤ b
        [b∧d≤b] = first (∧-glb b d)

      [b∧d≤c] : (b ∧ d) ≤ c
      [b∧d≤c] = ≤-trans (b ∧ d) d c [b∧d≤d] [d≤c]
       where
        [d≤c] : d ≤ c
        [d≤c] = second (≤-refl c d [c≡d])

        [b∧d≤d] : (b ∧ d) ≤ d
        [b∧d≤d] = first (second (∧-glb b d))

    [a∧c≤b∧d] : (a ∧ c) ≤ (b ∧ d)
    [a∧c≤b∧d] = (second (second (∧-glb b d))) (a ∧ c ) ([a∧c≤b] , [a∧c≤d])
     where
      [a∧c≤b] : (a ∧ c) ≤ b
      [a∧c≤b] = ≤-trans (a ∧ c) a b [a∧c≤a] [a≤b]
       where
        [a≤b] : a ≤ b
        [a≤b] = first (≤-refl a b [a≡b])
 
        [a∧c≤a] : (a ∧ c) ≤ a
        [a∧c≤a] = first (∧-glb a c)

      [a∧c≤d] : (a ∧ c) ≤ d
      [a∧c≤d] = ≤-trans (a ∧ c) c d [a∧c≤c] [c≤d]
       where
        [c≤d] : c ≤ d
        [c≤d] = first (≤-refl c d [c≡d])

        [a∧c≤c] : (a ∧ c) ≤ c
        [a∧c≤c] = first (second (∧-glb a c))
      

    [a∧c]≡[b∧d] : (a ∧ c) ≡ (b ∧ d)
    [a∧c]≡[b∧d] = ≤-antisym (a ∧ c) (b ∧ d) [a∧c≤b∧d] [b∧d≤a∧c]

  ∨-cont : (a b c d : carrier) → (a ≡ b) → (c ≡ d) → (a ∨ c) ≡ (b ∨ d)
  ∨-cont a b c d [a≡b] [c≡d] = [a∨c]≡[b∨d]
   where
    [a∨c]≡[b∨d] : (a ∨ c) ≡ (b ∨ d)
    [a∨c]≡[b∨d] = ≤-antisym (a ∨ c) (b ∨ d) [a∨c≤b∨d] [b∨d≤a∨c]
     where
      [a∨c≤b∨d] : (a ∨ c) ≤ (b ∨ d)
      [a∨c≤b∨d] = (second (second (∨-lub a c))) (b ∨ d) ([a≤b∨d] , [c≤b∨d])
       where
        [a≤b] : a ≤ b
        [a≤b] = first (≤-refl a b [a≡b])

        [b≤b∨d] : b ≤ (b ∨ d)
        [b≤b∨d] = first (∨-lub b d)

        [a≤b∨d] : a ≤ (b ∨ d)
        [a≤b∨d] = ≤-trans a b (b ∨ d) [a≤b] [b≤b∨d]

        [c≤d] : c ≤ d
        [c≤d] = first (≤-refl c d [c≡d])
 
        [d≤b∨d] : d ≤ (b ∨ d)
        [d≤b∨d] = first (second (∨-lub b d))

        [c≤b∨d] : c ≤ (b ∨ d)
        [c≤b∨d] = ≤-trans c d (b ∨ d) [c≤d] [d≤b∨d]

      [b∨d≤a∨c] : (b ∨ d) ≤ (a ∨ c)
      [b∨d≤a∨c] = (second (second (∨-lub b d))) (a ∨ c) ([b≤a∨c] , [d≤a∨c])
       where
        [b≤a] : b ≤ a
        [b≤a] = second (≤-refl a b [a≡b])

        [a≤a∨c] : a ≤ (a ∨ c)
        [a≤a∨c] = first (∨-lub a c)

        [b≤a∨c] : b ≤ (a ∨ c)
        [b≤a∨c] = ≤-trans b a (a ∨ c) [b≤a] [a≤a∨c]

        [d≤c] : d ≤ c
        [d≤c] = second (≤-refl c d [c≡d])
 
        [c≤a∨c] : c ≤ (a ∨ c)
        [c≤a∨c] = first (second (∨-lub a c))

        [d≤a∨c] : d ≤ (a ∨ c)
        [d≤a∨c] = ≤-trans d c (a ∨ c) [d≤c] [c≤a∨c]
  

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

  ≡-sym' : {x y : carrier} → x ≡ y → y ≡ x
  ≡-sym' {x} {y} = ≡-sym x y

  ≡-trans' : {x y z : carrier} → x ≡ y → y ≡ z → x ≡ z
  ≡-trans' {x} {y} {z} = ≡-trans x y z

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
    [[a∧b]∨c]≡[[c∨a]∧[c∨b]] = ≡-trans' [[a∧b]∨c]≡[c∨[a∧b]] [c∨[a∧b]]≡[[c∨a]∧[c∨b]]



  [[a∧b]∨a]∧[[c∨a]∧[c∨b]]≡a∧[[c∨a]∧[c∨b]] : (((a ∧ b) ∨ a) ∧ ((c ∨ a) ∧ (c ∨ b))) ≡ (a ∧ ((c ∨ a) ∧ (c ∨ b)))
  [[a∧b]∨a]∧[[c∨a]∧[c∨b]]≡a∧[[c∨a]∧[c∨b]] = ∧-cont ((a ∧ b) ∨ a) a ((c ∨ a) ∧ (c ∨ b)) ((c ∨ a) ∧ (c ∨ b)) [[a∧b]∨a]≡a (≡-refl ((c ∨ a) ∧ (c ∨ b)))
   where
    [[a∧b]∨a]≡[a∨[a∧b]] : ((a ∧ b) ∨ a) ≡ (a ∨ (a ∧ b))
    [[a∧b]∨a]≡[a∨[a∧b]] = ∨-comm (a ∧ b) a

    [a∨[a∧b]]≡a : (a ∨ (a ∧ b)) ≡ a
    [a∨[a∧b]]≡a = ∨∧-absorp a b

    [[a∧b]∨a]≡a : ((a ∧ b) ∨ a) ≡ a
    [[a∧b]∨a]≡a = ≡-trans' [[a∧b]∨a]≡[a∨[a∧b]] [a∨[a∧b]]≡a


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
    [a∧[c∨a]]≡a = ≡-trans' [a∧[c∨a]]≡[a∧[a∨c]] [a∧[a∨c]]≡a


  a∧[c∨b]≡a∧[b∨c] : (a ∧ (c ∨ b)) ≡ (a ∧ (b ∨ c))
  a∧[c∨b]≡a∧[b∨c] = ∧-cont a a (c ∨ b) (b ∨ c) (≡-refl a) (∨-comm c b)

  proof : (a ∧ (b ∨ c)) ≡ ((a ∧ b) ∨ (a ∧ c))
  proof = ≡-sym' (≡-trans' [a∧b]∨[a∧c]≡[[a∧b]∨a]∧[[a∧b]∨c] 
                (≡-trans' [[a∧b]∨a]∧[[a∧b]∨c]≡[[a∧b]∨a]∧[[c∨a]∧[c∨b]]
                (≡-trans' [[a∧b]∨a]∧[[c∨a]∧[c∨b]]≡a∧[[c∨a]∧[c∨b]]
                (≡-trans' a∧[[c∨a]∧[c∨b]]≡[a∧[c∨a]]∧[c∨b]
                (≡-trans' [a∧[c∨a]]∧[c∨b]≡a∧[c∨b] a∧[c∨b]≡a∧[b∨c]
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

  ≡-sym' : {x y : carrier} → x ≡ y → y ≡ x
  ≡-sym' {x} {y} = ≡-sym x y

  ≡-trans' : {x y z : carrier} → x ≡ y → y ≡ z → x ≡ z
  ≡-trans' {x} {y} {z} = ≡-trans x y z

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
    [[a∨b]∧c]≡[[c∧a]∨[c∧b]] = ≡-trans' [[a∨b]∧c]≡[c∧[a∨b]] [c∧[a∨b]]≡[[c∧a]∨[c∧b]]



  [[a∨b]∧a]∨[[c∧a]∨[c∧b]]≡a∨[[c∧a]∨[c∧b]] : (((a ∨ b) ∧ a) ∨ ((c ∧ a) ∨ (c ∧ b))) ≡ (a ∨ ((c ∧ a) ∨ (c ∧ b)))
  [[a∨b]∧a]∨[[c∧a]∨[c∧b]]≡a∨[[c∧a]∨[c∧b]] = ∨-cont ((a ∨ b) ∧ a) a ((c ∧ a) ∨ (c ∧ b)) ((c ∧ a) ∨ (c ∧ b)) [[a∨b]∧a]≡a (≡-refl ((c ∧ a) ∨ (c ∧ b)))
   where
    [[a∨b]∧a]≡[a∧[a∨b]] : ((a ∨ b) ∧ a) ≡ (a ∧ (a ∨ b))
    [[a∨b]∧a]≡[a∧[a∨b]] = ∧-comm (a ∨ b) a

    [a∧[a∨b]]≡a : (a ∧ (a ∨ b)) ≡ a
    [a∧[a∨b]]≡a = ∧∨-absorp a b

    [[a∨b]∧a]≡a : ((a ∨ b) ∧ a) ≡ a
    [[a∨b]∧a]≡a = ≡-trans' [[a∨b]∧a]≡[a∧[a∨b]] [a∧[a∨b]]≡a


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
    [a∨[c∧a]]≡a = ≡-trans' [a∨[c∧a]]≡[a∨[a∧c]] [a∨[a∧c]]≡a


  a∨[c∧b]≡a∨[b∧c] : (a ∨ (c ∧ b)) ≡ (a ∨ (b ∧ c))
  a∨[c∧b]≡a∨[b∧c] = ∨-cont a a (c ∧ b) (b ∧ c) (≡-refl a) (∧-comm c b)

  proof : (a ∨ (b ∧ c)) ≡ ((a ∨ b) ∧ (a ∨ c))
  proof = ≡-sym' (≡-trans' [a∨b]∧[a∨c]≡[[a∨b]∧a]∨[[a∨b]∧c] 
                (≡-trans' [[a∨b]∧a]∨[[a∨b]∧c]≡[[a∨b]∧a]∨[[c∧a]∨[c∧b]]
                (≡-trans' [[a∨b]∧a]∨[[c∧a]∨[c∧b]]≡a∨[[c∧a]∨[c∧b]]
                (≡-trans' a∨[[c∧a]∨[c∧b]]≡[a∨[c∧a]]∨[c∧b]
                (≡-trans' [a∨[c∧a]]∨[c∧b]≡a∨[c∧b] a∨[c∧b]≡a∨[b∧c]
                )))))
  

