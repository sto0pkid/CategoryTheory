module ArithmeticDefinability where

open import Agda.Primitive
open import BaseLogic
open import Data.Nat
open import Data.Nat.Operations
open import Data.Nat.Relations
open import Data.Nat.Proofs
open import Data.Vector
open import Data.Vector.Operations
open import Data.Vector.Relations
open import Data.Bool
open import Data.Fin
open import Data.Fin.Operations
open import Data.Disjunction
open import Data.Product
open import Data.PropositionalEquality
open import Relations
{-
The input/output relations of the general recursive functions are definable in Robinson arithmetic:
-}
--http://www.cogsci.rpi.edu/~heuveb/teaching/Logic/CompLogic/Web/Presentations/Arithmetical%20Definability.pdf


{-
To talk about functions of arbitrary arities, we'll use functions on
finite vectors with a given length:
-}

{-
Let's make things simpler with non-empty vectors:
-}


--Make sure these are pulling from the right indices

AD-suc : Relation Nat 2
AD-suc = rel (λ vec → ∃ x ∈ Nat , (∃ y ∈ Nat , ( vec [ zero ]= x ∧ vec [ suc zero ]= y ∧ suc x ≡ y)))

AD-suc₁ : Relation₁ Nat 2
AD-suc₁ = λ vec → ∃ x ∈ Nat , (∃ y ∈ Nat , ( vec [ zero ]= x ∧ vec [ suc zero ]= y ∧ suc x ≡ y))

AD-pred : Nat → Nat → Set
AD-pred x y = (x ≡ 0 ∧ y ≡ 0) ∨ x ≡ (suc y)

AD-pred₁ : Relation₁ Nat 2
AD-pred₁ = λ vec → ∃ x ∈ Nat , (∃ y ∈ Nat , (vec [ zero ]= x ∧ vec [ suc zero ]= y ∧ x ≡ suc y))

AD-pred₁' : Relation₁ Nat 2
AD-pred₁' = λ vec → ∃ x ∈ Nat , (∃ y ∈ Nat , (vec [ zero ]= x ∧ vec [ suc zero ]= y ∧ AD-suc₁ (y ∷ x ∷ [])))

{-
AD-pred₂ : Relation Nat 2
AD-pred₂ = rel (λ vec → ∃ x ∈ Nat , (∃ y ∈ Nat , ( vec [ zero ]= x ∧ vec [ suc zero ]= y ∧ 
-}

AD-diff : Nat → Nat → Nat → Set
AD-diff x y z = (x ≤ y ∧ z ≡ 0) ∨ x ≡ y + z

AD-≤ : Relation₁ Nat 2
AD-≤ = λ vec → ∃ x ∈ Nat , (∃ y ∈ Nat , ( vec [ zero ]= x ∧ vec [ zero ]= y ∧ ∃ z ∈ Nat , ( x + z ≡ y )))


AD-diff₁ : Relation₁ Nat 3
AD-diff₁ = λ vec → ∃ x ∈ Nat , (∃ y ∈ Nat , (∃ z ∈ Nat , (vec [ zero ]= x ∧ vec [ suc zero ]= y ∧ vec [ suc (suc zero) ]= z ∧ ((AD-≤ (x ∷ y ∷ []) ∧ z ≡ 0) ∨ x ≡ y + z))))

{-
Page 7:
The modified quotient function quo(x,y) where
quo(x,y) = 0 for y = 0 and quo(x,y) = largest z such
that y * z < x, is defined by:
-}
AD-quo : Nat → Nat → Nat → Set
AD-quo x y z = (y ≡ 0 ∧ z ≡ 0) ∨ ∃ w ∈ Nat , (w < y ∧ y * z + w ≡ x)


{-
Page 7:
The modified remainder function rem(x,y), where
rem(x,y) = x for y = 0 and rem(x,y) = z such that z < y
and there is some w such that y * w + z = x, is 
defined by the formula:
-}

AD-rem : Nat → Nat → Nat → Set
AD-rem x y z = (y ≡ 0 ∧ z ≡ x) ∨ (z < y ∧ (∃ w ∈ Nat , (y * w + z ≡ x)))

{-
We can also define AD-rem in term of AD-quo:
-}

AD-rem₂ : Nat → Nat → Nat → Set
AD-rem₂ x y z = ∃ w ∈ Nat , (AD-quo x y w ∧ y * w + z ≡ x)




AD-zero₂ : Relation Nat 2
AD-zero₂ = rel (λ vec → ∃ y ∈ Nat , ( (vec [ suc zero ]= y) ∧ (y ≡ 0)))

AD-suc₂ : Relation Nat 2
AD-suc₂ = rel (λ vec → ∃ x ∈ Nat , (∃ y ∈ Nat , ((vec [ zero ]= x) ∧ (vec [ suc zero ]= y) ∧ y ≡ suc x)))

AD-id₂ : (n : Nat) → (i : Fin (suc n)) → Relation Nat (suc (suc n))
AD-id₂ n' i' = rel (λ vec → ∃ x ∈ Nat , (∃ y ∈ Nat , ((vec [ i ]= x) ∧ (vec [ n+1 ]= y) ∧ y ≡ x)))
 where
  i : Fin (suc (suc n'))
  i = raise 1 i'

  n+1 : Fin (suc (suc n'))
  n+1 = fromℕ (suc n')


--Fin (suc (suc n)) has n+2 elements. There will always be at least 2 elements, even when n=0.
--The convention is that the last element will be the output, and the first (n+1) elements will be the inputs.
--The indices start at 0, so the first element is vec[0], and the last element is vec[n+1].
--The input index should only cover the first (n+1) elements, so Fin (suc n).
--Later we can generalize this to include unary relations.



AD-comp : (k m : Nat) → (f : Relation Nat (suc (suc k))) → (gs : Vector (Relation Nat (suc (suc m))) (suc k)) → Relation {lzero} {lsuc lzero} Nat (suc (suc m))
AD-comp k m f gs = rel (λ vec →
  ∃ ys ∈ Vector Nat (suc k) , ( 
   ((i : Fin (suc k)) → 
      ∃ yi ∈ Nat , (
      ∃ gi ∈ Relation Nat (suc (suc m)) , (
         ys [ i ]= yi ∧ 
         gs [ i ]= gi ∧ 
         (get-rel gi) (Vector-coerce-length ((get-inputs m vec) ++ (yi ∷ [])) [𝕤[m+1]≡𝕤𝕤m])
      ))
   ) ∧ (get-rel f) (Vector-coerce-length (ys ++ ((get-output m vec) ∷ [])) [𝕤[k+1]≡𝕤𝕤k])
  )
 )
 where
  [m+1≡𝕤[m+0]] : m + 1 ≡ suc (m + 0)
  [m+1≡𝕤[m+0]] = x+𝕤y≡𝕤[x+y] m 0

  [m+0≡m] : m + 0 ≡ m
  [m+0≡m] = x+0≡x m

  [𝕤[m+0]≡𝕤m] : suc (m + 0) ≡ suc m
  [𝕤[m+0]≡𝕤m] = [x≡y]→[fx≡fy] suc (m + 0) m [m+0≡m]
 
  [m+1≡𝕤m] : m + 1 ≡ suc m
  [m+1≡𝕤m] = ≡-⇶ [m+1≡𝕤[m+0]] [𝕤[m+0]≡𝕤m]

  [𝕤[m+1]≡𝕤𝕤m] : suc (m + 1) ≡ suc (suc m)
  [𝕤[m+1]≡𝕤𝕤m] = [x≡y]→[fx≡fy] suc (m + 1) (suc m) [m+1≡𝕤m]

  [k+1≡𝕤[k+0]] : k + 1 ≡ suc (k + 0)
  [k+1≡𝕤[k+0]] = x+𝕤y≡𝕤[x+y] k 0

  [k+0≡k] : k + 0 ≡ k
  [k+0≡k] = x+0≡x k

  [𝕤[k+0]≡𝕤k] : suc (k + 0) ≡ suc k
  [𝕤[k+0]≡𝕤k] = [x≡y]→[fx≡fy] suc (k + 0) k [k+0≡k]

  [k+1≡𝕤k] : k + 1 ≡ suc k
  [k+1≡𝕤k] = ≡-⇶ [k+1≡𝕤[k+0]] [𝕤[k+0]≡𝕤k]

  [𝕤[k+1]≡𝕤𝕤k] : suc (k + 1) ≡ suc (suc k)
  [𝕤[k+1]≡𝕤𝕤k] = [x≡y]→[fx≡fy] suc (k + 1) (suc k) [k+1≡𝕤k]

-- We can do things more easily by specifying things in terms of +1 rather than 𝕤
-- With addition we have all sorts of results like commutativity, associativity, etc..
-- and it applies to all numbers, so we can make a general coercion, and if we keep
-- things in the same form then we shouldn't have to coerce as often.

{-
AD-prim : ... requires Chinese remainder theorem ...

-}

{-
 Next step would be proving that these actually define the general recursive functions somehow, instead of
 just claiming that they do and assuming it to be correct.
-}

{-
This N-ary relations problem is mainly syntactic. We can't fit all possible syntaxes into Agda syntax. But also, we shouldn't! Instead, we should model languages in Agda and use Agda to relate those languages to their semantic interpretations.
-}

{-
Right now we're doing it with vectors, and instead of using a function to just pull the value at an index,
we're using relations. This is no good because you have to prove what the value at an index is before you
can use it, so this just defers the repsonsibility of pulling the value at an index to the user of the
relations, rather than handling it in the relation.
-}

{-
Then we'll want to clean up the number theory.

One big issue is proving things equal. We know we can check Nats for equality, it should be decidable
to execute all the operations and then bring into some normal form and do an equality comparison, so
we should have a function which can do this.

Except this won't work for variables. It should still be decidable in most cases to check two symbolic
formulae for negation, so it seems once again we need to build our own language so that we can talk
about symbolic manipulations, then we can do the same concept as before except symbolically.
-}

{-
So the main issue is going to be building up formal language theory and relating the syntaxes to their
semantics and building up proof-scaffolding around this.
-}
