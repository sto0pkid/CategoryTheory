module TuringMachine where

open import Agda.Primitive
open import Data.PropositionalEquality

data ⊥ : Set where
ω : ∀ {α} {A : Set α} → ⊥ → A
ω ()


¬ : ∀ {i} → Set i → Set i
¬ A = A → ⊥

data ⊤ : Set where
 ● : ⊤

⊥→⊥ : ⊥ → ⊥
⊥→⊥ [⊥] = [⊥]

¬[⊤→⊥] : ¬ (⊤ → ⊥)
¬[⊤→⊥] [⊤→⊥] = [⊤→⊥] ●

⊥→⊤ : ⊥ → ⊤
⊥→⊤ [⊥] = ●

⊤→⊤ : ⊤ → ⊤
⊤→⊤ [⊤] = [⊤]

⊤→⊤₂ : ⊤ → ⊤
⊤→⊤₂ [⊤] = ●

⊤→⊤₃ : ⊤ → ⊤
⊤→⊤₃ ● = ●


[A≡B]→[A→B] : ∀ {i} {A : Set i} {B : Set i} → (A ≡ B) → A → B
[A≡B]→[A→B] {i} {A} {.A} refl a = a 

_≠_ : ∀ {i} {A : Set i} (x y : A) → Set i
x ≠ y = ¬ (x ≡ y)

⊤≠⊥ : ⊤ ≠ ⊥
⊤≠⊥ [⊤≡⊥] = [A≡B]→[A→B] [⊤≡⊥] ●

[x≡y]→[fx≡fy] : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → (x y : A) → x ≡ y → (f x) ≡ (f y)
[x≡y]→[fx≡fy] {i} {j} {A} {B} f x .x refl = refl

[f≡g]→[fx≡gx] : ∀ {i j} {A : Set i} {B : Set j} → (f g : A → B) → (f ≡ g) → (x : A) → f x ≡ g x
[f≡g]→[fx≡gx] {i} {j} {A} {B} f .f refl x = refl


record ∥_∥ {α} (A : Set α) : Set α where
 constructor squash
 field
  .x : A


data Bool : Set where
 true : Bool
 false : Bool

BoolToSet : Bool → Set
BoolToSet false = ⊥
BoolToSet true = ⊤


true≠false : true ≠ false
true≠false [true≡false] = ⊤≠⊥ ([x≡y]→[fx≡fy] BoolToSet true false [true≡false])



~_ : Bool → Bool
~ true = false
~ false = true

_&_ : Bool → Bool → Bool
true & true = true
true & false = false
false & true = false
false & false = false

_∥_ : Bool → Bool → Bool
true ∥ true = true
true ∥ false = true
false ∥ true = true
false ∥ false = false

a≠~a : {a : Bool} → a ≠ (~ a)
a≠~a {true} [true≡false] = true≠false [true≡false]
a≠~a {false} [false≡true] = true≠false (≡-sym [false≡true])
 

data Nat : Set where
 zero : Nat
 suc : Nat → Nat

data Fin : Nat → Set where
 zero : {n : Nat} → Fin (suc n)
 suc : {n : Nat} → Fin n → Fin (suc n)

infixr 2 _×_
data _×_ {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where
 _,_ : A → B → A × B

infixr 2 _∧_
_∧_ : ∀ {α β} (A : Set α) (B : Set β) → Set (α ⊔ β)
_∧_ = _×_

×-cons' : ∀ {α β} {A : Set α} {B : Set β} → B → A → A × B
×-cons' {α} {β} {A} {B} b a = (a , b)

∧-cons' : ∀ {α β} {A : Set α} {B : Set β} → B → A → A ∧ B
∧-cons' = ×-cons'


first : ∀ {α β} {A : Set α} {B : Set β} (P : A × B) → A
first (a , b) = a

second : ∀ {α β} {A : Set α} {B : Set β} (P : A × B) → B
second (a , b) = b


data ∃ {α β} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
 _,_ : (x : A) → B x → ∃ A B

syntax ∃ A (λ x → e) = ∃ x ∈ A , e

proj₁ : ∀ {α β} {A : Set α} {B : A → Set β} (P : ∃ x ∈ A , (B x)) → A
proj₁ (a , b) = a

π₁ : ∀ {α β} {A : Set α} {B : A → Set β} (P : ∃ x ∈ A , (B x)) → A
π₁ = proj₁

proj₂ : ∀ {α β} {A : Set α} {B : A →  Set β} (P : ∃ x ∈ A , (B x)) → B (proj₁ P)
proj₂ (a , b) = b 

π₂ : ∀ {α β} {A : Set α} {B : A →  Set β} (P : ∃ x ∈ A , (B x)) → B (proj₁ P)
π₂ = proj₂

{-
data _≡_ {i} {A : Set i} (x : A) : A → Set i where
 refl : x ≡ x
-}

_↔_ : ∀ {i j} → Set i → Set j → Set (i ⊔ j)
A ↔ B = (A → B) ∧ (B → A) 



_hasDecidableEquality : ∀ {i} → Set i → Set i
A hasDecidableEquality = ∃ eq ∈ (A → A → Bool) , ((a b : A) → (a ≡ b) ↔ (eq a b ≡ true))



_-_ : {A : Set} (S : A → Bool) (s : A → Bool) → (A → Bool)
(S - s) a = (S a) & (~ s a)

-- The subset over the domain A consisting of all the objects in A.
all : (A : Set) → A → Bool
all A a = true



<_> : {A : Set} → A → A hasDecidableEquality → A → Bool
< x > A-decEq a = (π₁ A-decEq) x a

_/_ : {A : Set} (S : A → Bool) (x : A) → A hasDecidableEquality → A → Bool
(S / x) A-has-decidable-equality a = (π₁ A-has-decidable-equality) x a

-- Over the domain of A, S₁ is a subset of S₂. 
[_||_⊆_] : (A : Set) → (S₁ S₂ : A → Bool) → Set
[ A || S₁ ⊆ S₂ ] = (x : A) → (S₁ x ≡ true) → (S₂ x ≡ true)

{-
∀ n , (Fin n) hasDecidableEquality
-}

-- https://en.wikipedia.org/wiki/Turing_machine#Formal_definition
{-
* Q is a finite, non-empty set of states
* Γ is a finite, non-empty set of tape alphabet symbols
* b ∈ Γ is the blank symbol (the only symbol allowed to occur on the tape infinitely often at any step during the computation)
* Σ ⊆ Γ \ {b} is the set of input symbols.
* δ : (Q \ F) x Γ → Q × Γ × {L,R} is a partial function called the transition function, where L is left shift, R is right shift. If δ is not defined on the current state and the current tape symbol, then the machine halts.
* q₀ ∈ Q is the initial state
* F ⊆ Q is the set of final or accepting states.
-}
-- Note: δ is actually a total function on (Q \ F) × Γ, which can be interpreted
-- as a partial function on Q × Γ, with the undefined states (which are members of F) representing halting.


record TM : Set where
 field
  Fin-has-decidable-equality : ∀ n → (Fin n) hasDecidableEquality
  states : Nat
  final-states : Fin states → Bool
  initial-state : Fin states
  alphabet : Nat
  blank-symbol : Fin alphabet
  input-symbols : ∃ s ∈ (Fin alphabet → Bool) , (∥ [ (Fin alphabet) ||  s ⊆ (((all (Fin alphabet)) / blank-symbol) (Fin-has-decidable-equality alphabet)) ] ∥)
  transition-function : ((∃ s ∈ (Fin states) , (∥ ((all (Fin states)) - final-states) s ≡ true ∥)) × (Fin alphabet)) → (Fin states) × (Fin alphabet) × Bool
 

{-
We know by now that the word "set" is more vague than one would first imagine. This definition of Turing machines is (most likely) expecting certain properties to hold for the sets being talked about, like, discreteness, finiteness, decidable equality, etc... Rather than leave it up to the user to provide their own set of states or set of alphabet symbols, we'll simply have them choose the number of states, `states`, and alphabet symbols, `alphabet`, and then just use `Fin states` or `Fin alphabet`, which has the desired properties.

Set logic is different from type logic, but they are related. A subset of a type is specified by functions to Set i or functions to Bool. In the case of Set i, a predicate is picking out members of the domain, and we can call this a set-membership predicate. In the case of functions to Bool, the function outputs true if the object is in the subset, false if it's not. These two are complementary: the former constitutes questions / propositions about set-membership, and the latter constitutes the decision procedures for these questions questions. We can reasonably assume that decidability of subset-membership is required in this definition of Turing-machines: we want to be able to tell whether or a state is in the set of final states or not, for example, and therefore I'm using the `A → Bool` version of subset definitions. In a more thorough treatment, one should use the propositional version of subsets, so as to be able to define a larger variety of (hypothetical) Turing machines.

 
-}

{-
Now we're going to make a function that will take our Turing machine descriptions in TM and execute them on a bitstring (or Nat, or whatever), so I figure I'd call that a universal turing machine (step). First, we'll translate the necessary tape operations into arithmetic operations, and then we can just have our tape be represented by a Nat.
-}

{-
utm-step : Nat → Nat
utm-step 
-}

{-
Once we have a utm step defined, we can iterate this as a stream, and then ask the halting problem.
Then we can ask whether the halting problem can be decided by a turing machine, and we should reach a contradiction.
-}

{-

-}

injection : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
injection {i} {j} {A} {B} f = (a₁ a₂ : A) → (f a₁ ≡ f a₂) → (a₁ ≡ a₂)

surjection : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
surjection {i} {j} {A} {B} f = (b : B) → ∃ a ∈ A , (f a ≡ b)

bijection : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
bijection {i} {j} {A} {B} f = (injection f) ∧ (surjection f)

bijective : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
bijective {i} {j} A B = ∃ f ∈ (A → B) , (bijection f)


A-cant-count-its-subsets : ∀ {i} {A : Set i} → (f : A → A → Bool) → ∃ d ∈ (A → Bool), (¬ (∃ a ∈ A , ((a' : A) → f a a' ≡ d a')))
A-cant-count-its-subsets {i} {A} f = (d , proof)
 where
  d : A → Bool
  d = λ x → ~ (f x x)

  proof : ¬ (∃ a ∈ A , ((a' : A) → f a a' ≡ d a'))
  proof (a , g) = ω p
   where
    [faa≡da] : f a a ≡ d a
    [faa≡da] = g a

    [da≡~faa] : d a ≡ ~ (f a a)
    [da≡~faa] = refl

    [faa≡~faa] : f a a ≡ ~ (f a a)
    [faa≡~faa] = ≡-trans [faa≡da] [da≡~faa]

    p : ⊥
    p = a≠~a [faa≡~faa]

no-surjection-A→[A→Bool] : ∀ {i} {A : Set i} → ¬ (∃ f ∈ (A → (A → Bool)) , (surjection f))
no-surjection-A→[A→Bool] {i} {A} (f , f-surjective) = [⊥]
 where
  d : A → Bool
  d = λ x → ~ (f x x)

  [∃a,fa≡d] : ∃ a ∈ A , (f a ≡ d)
  [∃a,fa≡d] = f-surjective d

  a : A
  a = π₁ [∃a,fa≡d]

  [faa≡da] : f a a ≡ d a
  [faa≡da] = [f≡g]→[fx≡gx] (f a) d (π₂ [∃a,fa≡d]) a

  [da≡~faa] : d a ≡ ~ (f a a)
  [da≡~faa] = refl

  [faa≡~faa] : f a a ≡ ~ (f a a)
  [faa≡~faa] = ≡-trans [faa≡da] [da≡~faa]

  [⊥] : ⊥
  [⊥] = a≠~a [faa≡~faa]


{-
We have to introduce the notion of bijections here so that we can talk about the cardinality of subsets.
-}
{-
diagonal : ∀ {i j} {A : Set i} {B : Set j} (prf : bijective B Bool) → (f : A → A → B) → ∃ d ∈ (A → B) , (¬ (∃ a ∈ A , ((a' : A) → f a a' ≡ d a')))
diagonal {i} {j} {A} {B} prf f =  
-}

diagonal : ∀ {i j} {A : Set i} {B : Set j} → (∃ neg ∈ (B → B) , ((b : B) → b ≠ (neg b))) → ¬ (∃ f ∈ (A → A → B) , (surjection f))
diagonal {i} {j} {A} {B} (neg , neg-has-no-fixed-points) (f , f-surjective) = [⊥]
 where
  d : A → B
  d = λ x → neg (f x x)

  [∃a,fa≡d] : ∃ a ∈ A , (f a ≡ d)
  [∃a,fa≡d] = f-surjective d

  a : A
  a = π₁ [∃a,fa≡d]

  [faa≡da] : f a a ≡ d a 
  [faa≡da] = [f≡g]→[fx≡gx] (f a) d (π₂ [∃a,fa≡d]) a

  [da≡neg[faa]] : d a ≡ neg (f a a)
  [da≡neg[faa]] = refl

  [faa≡neg[faa]] : f a a ≡ neg (f a a)
  [faa≡neg[faa]] = ≡-trans [faa≡da] [da≡neg[faa]]

  [⊥] : ⊥
  [⊥] = neg-has-no-fixed-points (f a a) [faa≡neg[faa]]

{-
What we really want to prove, essentially Lawvere's theorem, is that if there is a surjection A → (A → B) then every function B → B must have fixed points.
-}
lawvere : ∀ {i j} {A : Set i} {B : Set j} → (∃ f ∈ (A → A → B) , (surjection f)) → (g : B → B) → (∃ b ∈ B , (b ≡ g b)) 
lawvere {i} {j} {A} {B} (f , f-surjective) g = (f a a , [faa≡g[faa]])
 where
  d : A → B
  d = λ x → g (f x x)

  [∃a,fa≡d] : ∃ a ∈ A , (f a ≡ d)
  [∃a,fa≡d] = f-surjective d

  a : A
  a = π₁ [∃a,fa≡d]

  [faa≡da] : f a a ≡ d a
  [faa≡da] = [f≡g]→[fx≡gx] (f a) d (π₂ [∃a,fa≡d]) a

  [da≡g[faa]] : d a ≡ g (f a a)
  [da≡g[faa]] = refl

  [faa≡g[faa]] : f a a ≡ g (f a a)
  [faa≡g[faa]] = ≡-trans [faa≡da] [da≡g[faa]]


{-
Logical negation should have no fixed-points!
-}
