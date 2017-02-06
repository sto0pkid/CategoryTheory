module Linear where

open import Agda.Primitive
--open import BaseLogic
open import OperationProperties
open import Data.Nat
open import Data.Vector
open import Data.PropositionalEquality

{-
Algebraic structure
Algebraic signature
Class inclusion

Magmas
Monoids
Groups
Ring
Commutative ring
Integral domain
Integrally closed domain
GCD domain
Unique factorization domain
Principal ideal domain
Euclidean domain
-}

record Field {α} : Set (lsuc α) where
 field
  F : Set α
  _+_ : F → F → F
  _*_ : F → F → F
  +-assoc : isAssociative _+_
  *-assoc : isAssociative _+_
  +-comm : isCommutative _*_
  *-comm : isCommutative _*_
  +-exid : hasIdentity _+_
  *-exid : hasIdentity _*_
  +-hasInv : hasInverses (record {M = F; _+_ = _+_; +-exid = +-exid})
  *-hasInv : hasInverses (record {M = F; _+_ = _*_; +-exid = *-exid})
  +*-distr : [in F ] _*_ distributesOver _+_
  

{-
Finite field
-}

{-
Modules

record VectorSpace (F : Field) : Set where
-}


additive : ∀ {α β} {A : Set α} {B : Set β} (f : A → B) → (+ : A → A → A) → (* : B → B → B) → Set (β ⊔ α)
additive {α} {β} {A} {B} f +' *' = (x y : A) → f (x + y) ≡ (f x) * (f y)
 where
  _+_ : A → A → A
  _+_ = +'

  _*_ : B → B → B
  _*_ = *'
{-
Notice that this is saying that the function f represents some kind of
functor from A to B.
-}

{-
homogeneous : ∀ {α β} {A : Set α} {B : Set β} (f : A → B) → (+ : A → A → A) 
-}

{-
 We can represent a system of linear equations by giving the coefficients
 for the LHS and the constant for the RHS.
 The system needs a type for the coefficients and a type for the variables.
 They don't necessarily have to be the same type, but there needs to be an
 operation that combines the scalar coefficients with elements of the type
 of the variables in order to form new elements of the type of the variables.

-}

record System {α β} : Set (lsuc (α ⊔ β)) where
 field
  numVars : Nat
  numEquations : Nat
  scalars : Set α
  vars : Set β
  _+_ : vars → vars → vars
  _*_ : scalars → vars → vars
  eqns : Vector (Vector scalars (suc numVars)) numEquations


{-
mean : {n : Nat} → Vector Rational n → Rational
mean {n} V = 
-}
