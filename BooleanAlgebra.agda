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

isCommutative : ∀ {i j k} {A : Set i} {B : Set j} {_≡_ : B → B → Set k} {p : isEquivalence _≡_} → (f : A → A → B) → Set (i ⊔ k)
isCommutative {i} {j} {k} {A} {B} {_≡_} {≡-equiv} f = (x y : A) → (f x y) ≡ (f y x)

isAssociative : ∀ {i j} {A : Set i} {_≡_ : A → A → Set j} {p : isEquivalence _≡_} → (f : A → A → A) → Set (i ⊔ j)
isAssociative {i} {j} {A} {_≡_} {≡-equiv} f = (x y z : A) → (f x (f y z)) ≡ (f (f x y) z)

absorbs : ∀ {i j} {A : Set i} {_≡_ : A → A → Set j} {p : isEquivalence _≡_} → (f : A → A → A) → (g : A → A → A) → Set (i ⊔ j)
absorbs {i} {j} {A} {_≡_}{≡-equiv} f g = (x y : A) → (f x (g x y)) ≡ x

distributesOver : ∀ {i j} {A : Set i} {_≡_ : A → A → Set j} {p : isEquivalence _≡_} → (f : A → A → A) → (g : A → A → A) → Set (i ⊔ j)
distributesOver {i} {j} {A} {_≡_} {≡-equiv} f g = (x y z : A) → (f x (g y z)) ≡ (g (f x y) (f x z)) 

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
  ∧-absorp : absorbs {i} {j} {carrier} {_≡_} {≡-equiv} _∧_ _∨_
  ∨-comm : isCommutative {i} {i} {j} {carrier} {carrier} {_≡_} {≡-equiv} _∨_
  ∨-assoc : isAssociative {i} {j} {carrier} {_≡_} {≡-equiv} _∨_
  ∨-absorp : absorbs {i} {j} {carrier} {_≡_} {≡-equiv} _∨_ _∧_

  

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


{-
http://documents.kenyon.edu/math/SamTay.pdf
Proposition 2.1.3
-}
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
 } where
  carrier : Set i
  carrier = OrderLattice.carrier O

  _≡_ : carrier → carrier → Set k
  _≡_ = OrderLattice._≡_ O

  ≡-refl : (x : carrier) → x ≡ x
  ≡-refl = OrderLattice.≡-refl O

  ≡-sym : (x y : carrier) → x ≡ y → y ≡ x
  ≡-sym = OrderLattice.≡-sym O

  ≡-trans : (x y z : carrier) → x ≡ y → y ≡ z → x ≡ z
  ≡-trans = OrderLattice.≡-trans O

  _≤_ : carrier → carrier → Set j
  _≤_ = OrderLattice._≤_ O

  ≤-refl : (x : carrier) → x ≤ x
  ≤-refl = OrderLattice.≤-refl O

  ≤-trans : (x y z : carrier) → x ≤ y → y ≤ z → x ≤ z
  ≤-trans = OrderLattice.≤-trans O

  ≤-antisym : (x y : carrier) → x ≤ y → y ≤ x → x ≡ y 
  ≤-antisym = OrderLattice.≤-antisym O

  _∧_ : carrier → carrier → carrier
  _∧_ = OrderLattice._∧_ O
 
  _∨_ : carrier → carrier → carrier
  _∨_ = OrderLattice._∨_ O

  ∧-glb : (x y : carrier) → ((x ∧ y) ≤ x) × (((x ∧ y) ≤ y) × ((z : carrier) → (z ≤ x) × (z ≤ y) → (z ≤ (x ∧ y))))
  ∧-glb = OrderLattice.∧-glb O

  ∨-lub : (x y : carrier) → (x ≤ (x ∨ y)) × ((y ≤ (x ∨ y)) × ((z : carrier) → (x ≤ z) × (y ≤ z) → (x ∨ y) ≤ z))
  ∨-lub = OrderLattice.∨-lub O

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

record BAlg : Set₁ where
 field
  carrier : Set
  _≤_ : carrier → carrier → Set
  _≡_ : carrier → carrier → Set
  
  _∨_ : carrier → carrier → carrier
  _∧_ : carrier → carrier → carrier
  
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

  -- wrong! we can't get this from A4. either the author made a mistake in 
  -- this proof or made a mistake in their definition of A4.
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

