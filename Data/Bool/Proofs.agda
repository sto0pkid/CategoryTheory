module Data.Bool.Proofs where

open import BaseLogic using (_≠_ ; [x≡y]→[fx≡fy] ; ⊤≠⊥ ; ¬)
open import Data.False
open import Data.True
open import Data.PropositionalEquality
open import Data.Bool
open import Data.Bool.Operations
open import Data.Disjunction
open import Data.Product

𝕥≠𝕗 : true ≠ false
𝕥≠𝕗 [𝕥≡𝕗] = ☢ 
 where
  [𝕥≡𝕗]→[⊤≡⊥] : (true ≡ false) → (⊤ ≡ ⊥)
  [𝕥≡𝕗]→[⊤≡⊥] [𝕥≡𝕗] = [x≡y]→[fx≡fy] BoolProp true false [𝕥≡𝕗]

  [⊤≡⊥] : ⊤ ≡ ⊥
  [⊤≡⊥] = [𝕥≡𝕗]→[⊤≡⊥] [𝕥≡𝕗]

  ☢ : ⊥
  ☢ = ⊤≠⊥ [⊤≡⊥]

true≠false : true ≠ false
true≠false = 𝕥≠𝕗


b≡true→if[b]then[a₁]else[a₂]≡a₁ : ∀ {α} {A : Set α} → (a₁ a₂ : A) → (b : Bit) → b ≡ true → if b then a₁ else a₂ ≡ a₁
b≡true→if[b]then[a₁]else[a₂]≡a₁ {α} {A} a₁ a₂ true 𝕥≡𝕥 = refl
b≡true→if[b]then[a₁]else[a₂]≡a₁ {α} {A} a₁ a₂ false 𝕗≡𝕥 = ω (𝕥≠𝕗 (≡-↑↓ 𝕗≡𝕥))

b≡false→if[b]then[a₁]else[a₂]≡a₂ : ∀ {α} {A : Set α} → (a₁ a₂ : A) → (b : Bit) → b ≡ false → if b then a₁ else a₂ ≡ a₂
b≡false→if[b]then[a₁]else[a₂]≡a₂ {α} {A} a₁ a₂ true 𝕥≡𝕗 = ω (𝕥≠𝕗 𝕥≡𝕗)
b≡false→if[b]then[a₁]else[a₂]≡a₂ {α} {A} a₁ a₂ false 𝕗≡𝕗 = refl



true-or-x≡true : (b : Bool) → true or b ≡ true
true-or-x≡true true = refl
true-or-x≡true false = refl

x-or-true≡true : (b : Bool) → b or true ≡ true
x-or-true≡true true = refl
x-or-true≡true false = refl

false-or-x≡x : (b : Bool) → false or b ≡ b
false-or-x≡x true = refl
false-or-x≡x false = refl

x-or-false≡x : (b : Bool) → b or false ≡ b
x-or-false≡x true = refl
x-or-false≡x false = refl

or-comm : (b₁ b₂ : Bool) → b₁ or b₂ ≡ b₂ or b₁
or-comm true true = refl
or-comm true false = refl
or-comm false true = refl
or-comm false false = refl

true-and-x≡x : (b : Bool) → true and b ≡ b
true-and-x≡x true = refl
true-and-x≡x false = refl

x-and-true≡x : (b : Bool) → b and true ≡ b
x-and-true≡x true = refl
x-and-true≡x false = refl

false-and-x≡false : (b : Bool) → false and b ≡ false
false-and-x≡false true = refl
false-and-x≡false false = refl

x-and-false≡false : (b : Bool) → b and false ≡ false
x-and-false≡false true = refl
x-and-false≡false false = refl

and-comm : (b₁ b₂ : Bool) → b₁ and b₂ ≡ b₂ and b₁
and-comm true true = refl
and-comm true false = refl
and-comm false true = refl
and-comm false false = refl


∨-or-lemma : (a b : Bool) → (a ≡ true) ∨ (b ≡ true) → (a or b) ≡ true
∨-or-lemma a b (inl [a≡true]) = [a-or-b≡true]
 where
  or-b : Bool → Bool
  or-b x = x or b

  [a-or-b≡true-or-b] : (a or b) ≡ (true or b)
  [a-or-b≡true-or-b] = [x≡y]→[fx≡fy] or-b a true [a≡true]

  [a-or-b≡true] : (a or b) ≡ true
  [a-or-b≡true] = ≡-trans [a-or-b≡true-or-b] (true-or-x≡true b)
∨-or-lemma a b (inr [b≡true]) = [a-or-b≡true]
 where
  a-or : Bool → Bool
  a-or x = a or x

  [a-or-b≡a-or-true] : (a or b) ≡ (a or true)
  [a-or-b≡a-or-true] = [x≡y]→[fx≡fy] a-or b true [b≡true]

  [a-or-b≡true] : (a or b) ≡ true
  [a-or-b≡true] = ≡-trans [a-or-b≡a-or-true] (x-or-true≡true a)

or-∨-lemma : (a b : Bool) → (a or b) ≡ true → (a ≡ true) ∨ (b ≡ true)
or-∨-lemma true true [true-or-true≡true] = (inl refl)
or-∨-lemma true false [true-or-false≡true] = (inl refl)
or-∨-lemma false true [false-or-true≡true] = (inr refl)
or-∨-lemma false false [false-or-false≡true] = ω (true≠false (≡-sym [false-or-false≡true]))

∧-and-lemma : (a b : Bool) → (a ≡ true) ∧ (b ≡ true) → (a and b) ≡ true
∧-and-lemma a b ([a≡true] , [b≡true]) = [a-and-b≡true]
 where
  and-b : Bool → Bool
  and-b x = x and b

  [a-and-b≡true-and-b] : (a and b) ≡ (true and b)
  [a-and-b≡true-and-b] = [x≡y]→[fx≡fy] and-b a true [a≡true]
 
  true-and : Bool → Bool
  true-and x = true and x

  [true-and-b≡true-and-true] : (true and b) ≡ (true and true)
  [true-and-b≡true-and-true] = [x≡y]→[fx≡fy] true-and b true [b≡true]

  [true-and-true≡true] : (true and true) ≡ true
  [true-and-true≡true] = refl

  [a-and-b≡true] = ≡-trans [a-and-b≡true-and-b] (≡-trans [true-and-b≡true-and-true] [true-and-true≡true])

and-∧-lemma : (a b : Bool) → (a and b) ≡ true → (a ≡ true) ∧ (b ≡ true)
and-∧-lemma true true [true-and-true≡true] = (refl , refl)
and-∧-lemma true false [true-and-false≡true] = ω (true≠false (≡-sym [true-and-false≡true]))
and-∧-lemma false true [false-and-true≡true] = ω (true≠false (≡-sym [false-and-true≡true]))
and-∧-lemma false false [false-and-false≡true] = ω (true≠false (≡-sym [false-and-false≡true]))

¬-not-lemma : (a : Bool) → ¬ (a ≡ true) → (not a) ≡ true
¬-not-lemma true ¬[true≡true] = ω (¬[true≡true] refl)
¬-not-lemma false ¬[false≡true] = refl

not-¬-lemma : (a : Bool) → (not a) ≡ true → ¬ (a ≡ true)
not-¬-lemma true [false≡true] [true≡true] = true≠false (≡-sym [false≡true])
not-¬-lemma false [true≡true] [false≡true] = true≠false (≡-sym [false≡true])


