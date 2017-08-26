module BooleanAlgebra where

open import Agda.Primitive

data _×_ {i} {j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
 _,_ : A → B → A × B

first : ∀ {i j} {A : Set i} {B : Set j} → A × B → A
first (a , b) = a

second : ∀ {i j} {A : Set i} {B : Set j} → A × B → B
second (a , b) = b

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
  
