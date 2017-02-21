module Agatha where

open import BaseLogic
open import Data.PropositionalEquality
open import Data.Nat
open import Data.Fin
open import Data.Bool
open import Data.Bool.Operations
open import Data.Bool.Proofs
open import Data.Disjunction
open import Data.Product
open import Data.Vector
open import Data.False

-- http://math.chapman.edu/~jipsen/tptp/TPTP-v6.4.0/Problems/PUZ/PUZ001-1.p

{-
Someone who lives in Dreadbury Mansion killed Aunt Agatha.
Agatha, the butler, and Charles live in Dreadbury Mansion,
and are the only people who live therein. A killer always
hates his victim, and is never richer than his victim.
Charles hates no one that Aunt Agatha hates. Agatha hates
everyone except the butler. The butler hates everyone not
richer than Aunt Agatha. The butler hates everyone Aunt
Agatha hates. No one hates everyone. Agatha is not the
butler. Therefore : Agatha killed herself.

The statement "Agatha is not the butler" tells us that "Agatha",
"Charles" and "the butler" are just labels that could potentially
refer to the same person.

We can specify the set of labels as an inductive type because
we have all the information about the labels, but we can't specify
the set of people as an inductive type because we don't know
a priori what the members of this set are. 

So we say there exists some set of people, and an assignment of labels
to people. The set of people is just some finite set, Fin 1 or Fin 2 or
Fin 3. There's no way to have a single assignment of 3 labels to more
than 3 people, and we can prove that.

We can specify a relation between people as Person → Person → Bool
-}

{-

Agatha hates everyone except the butler, so:
 Agatha hates Charles
 Agatha hates Agatha.
 Agatha doesn't hate the butler
Charles hates no one that Agatha hates, so:
 Charles doesn't hate Charles
 Charles doesn't hate Agatha
The Butler hates everyone that Agatha hates, so:
 Butler hates Charles
 Butler hates Agatha
No one hates everyone, so:
 Butler doesn't hate Butler
  because no one hates everyone
   and Butler hates everyone besides the Butler
    because Butler hates everyone Agatha hates
     and Agatha hates everyone besides the Butler
Butler richer than Agatha
 because Butler hates everyone not richer than Agatha
  and Butler doesn't hate Butler

Extra rule: nobody is richer than themselves
Charles not richer than Charles
Agatha not richer than Agatha
Butler not richer than Butler
* need this rule for Agatha to qualify;
* without this rule, Agatha wouldn't be ruled out
  but she also wouldn't qualify.

ruled out: Charles
 because a killer always hates his victim
  and Charles doesn't hate Agatha
   because Charles hates no one that Agatha hates
    and Agatha hates Agatha
     because Agatha hates everyone except the butler
      and Agatha ≠ butler

Charles ≠ Agatha,
 because Charles hates no one that Agatha hates
  and equal objects satisfy the same logical properties

Charles ≠ Butler
 because Butler hates everyone that Agatha hates
  and Charles hates no one that Agatha hates
   
Agatha ≠ Butler

ruled out: Butler
 because a killer is never richer than his victim
  and Butler is richer than Agatha



Agatha : Person.
Charles : Person.
Butler : Person.
Dreadbury-Mansion : House.

-- Agatha, the butler, and Charles live in Dreadbury Mansion,
-- and are the only people who live therein.
Agatha lives-in Dreadbury-Mansion.
Charles lives-in Dreadbury-Mansion.
Butler lives-in Dreadbury-Mansion.

Agatha hates Charles.
Agatha hates Agatha.
¬ (Agatha hates Butler).
Butler hates Charles.
Butler hates Agatha.
¬ (Butler hates Butler).
¬ (Charles hates Charles).
¬ (Charles hates Agatha).
? (Charles hates Butler).

¬ (Agatha doesnt-hate Charles).
¬ (Agatha doesnt-hate Agatha).
Agatha doesnt-hate Butler.
¬ (Butler doesnt-hate Charles).
¬ (Butler doesnt-hate Agatha).
Butler doesnt-hate Butler.
Charles doesnt-hate Charles.
Charles doesnt-hate Agatha
? (Charles doesnt-hate Butler).

Agatha ≠ Charles.
Agatha ≠ Butler.
Butler ≠ Charles.

-}

{-
S
s

Charles
Agatha
Butler

-}

data PersonLabel : Set where
 Charles : PersonLabel
 Agatha : PersonLabel
 the-butler : PersonLabel

data HouseLabel : Set where
 Dreadbury-Mansion : HouseLabel


fin-assign : ∀ {i} {A : Set i} (f : PersonLabel → A) → 
  ∃ g ∈ (PersonLabel → Fin 3) , 
   (∃ h ∈ (Fin 3 → A) , 
     ((label : PersonLabel) → f label ≡ h (g label))
   )
fin-assign {i} {A} f = (g , (h , proof))
 where
  g : PersonLabel → Fin 3
  g Charles = zero
  g Agatha = suc zero
  g the-butler = suc (suc zero)

  h : Fin 3 → A
  h zero = f Charles
  h (suc zero) = f Agatha
  h (suc (suc x)) = f the-butler

  proof : (label : PersonLabel) → f label ≡ h (g label)
  proof Charles = refl
  proof Agatha = refl
  proof the-butler = refl

{-
 what should be the structure of our finite relations
-}

FinRel : {m n : Nat} → Set
FinRel {m} {n} = Fin m → Fin n → Bool

FinRel₂ : {m n : Nat} → Set
FinRel₂ {m} {n} = Fin m × Fin n → Bool

FinRel₂-compl : {m n : Nat} → FinRel₂ {m} {n} → FinRel₂ {m} {n}
FinRel₂-compl {m} {n} R = λ r → not (R r)

bool-LEM : (b : Bool) → b ≡ true ∨ b ≡ false
bool-LEM true = inl refl
bool-LEM false = inr refl

bool-DN : (a b : Bool) → a ≠ b → a ≡ not b
bool-DN true true [𝕥≠𝕥] = ω ☢
 where
  ☢ : ⊥
  ☢ = [𝕥≠𝕥] refl
bool-DN true false [𝕥≠𝕗] = refl
bool-DN false true [𝕗≠𝕥] = refl
bool-DN false false [𝕗≠𝕗] = ω ☢
 where
  ☢ : ⊥
  ☢ = [𝕗≠𝕗] refl

FinRel₂-LEM : ∀ {m n : Nat} → (R : FinRel₂ {m} {n}) → (r : Fin m × Fin n) → R r ≡ true ∨ R r ≡ false
FinRel₂-LEM {m} {n} R r = bool-LEM (R r)

FinRel₂-DN : ∀ {m n : Nat} → (R : FinRel₂ {m} {n}) → (r : Fin m × Fin n) → (b : Bool) → R r ≠ b → R r ≡ not b
FinRel₂-DN {m} {n} R r b [R-r≠b] = bool-DN (R r) b [R-r≠b]

Bool-conv : (a b : Bool) → (a ≡ true → b ≡ true) → b ≡ false → a ≡ false
Bool-conv true true [𝕥≡𝕥→𝕥≡𝕥] [𝕥≡𝕗] = ω ☢
 where
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]
Bool-conv true false [𝕥≡𝕥→𝕗≡𝕥] [𝕗≡𝕗] = ω ☢
 where
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 (≡-↑↓ ([𝕥≡𝕥→𝕗≡𝕥] refl))
Bool-conv false true [𝕗≡𝕥→𝕥≡𝕥] [𝕥≡𝕗] = refl
Bool-conv false false [𝕗≡𝕥→𝕗≡𝕥] [𝕗≡𝕗] = refl



Bool-conv₂ : (a b c d : Bool) → (a ≡ c → b ≡ d) → b ≡ not d → a ≡ not c
Bool-conv₂ true true true true [𝕥≡𝕥→𝕥≡𝕥] [𝕥≡𝕗] = ω ☢
 where
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]
Bool-conv₂ true true true false [𝕥≡𝕥→𝕥≡𝕗] [𝕥≡𝕥] = ω ☢
 where
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 ([𝕥≡𝕥→𝕥≡𝕗] refl)
Bool-conv₂ true true false true [𝕥≡𝕗→𝕥≡𝕥] [𝕥≡𝕗] = refl
Bool-conv₂ true true false false [𝕥≡𝕗→𝕥≡𝕗] [𝕥≡𝕥] = refl
Bool-conv₂ true false true true [𝕥≡𝕥→𝕗≡𝕥] [𝕗≡𝕗] = ω ☢
 where
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 (≡-↑↓ ([𝕥≡𝕥→𝕗≡𝕥] refl))
Bool-conv₂ true false true false [𝕥≡𝕥→𝕗≡𝕗] [𝕗≡𝕥] = ω ☢
 where
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 (≡-↑↓ [𝕗≡𝕥])
Bool-conv₂ true false false true [𝕥≡𝕗→𝕗≡𝕥] [𝕗≡𝕗] = refl
Bool-conv₂ true false false false [𝕥≡𝕗→𝕗≡𝕗] [𝕗≡𝕥] = refl
Bool-conv₂ false true true true [𝕗≡𝕥→𝕥≡𝕥] [𝕥≡𝕗] = refl
Bool-conv₂ false true true false [𝕗≡𝕥→𝕥≡𝕗] [𝕥≡𝕥] = refl
Bool-conv₂ false true false true [𝕗≡𝕗→𝕥≡𝕥] [𝕥≡𝕗] = ω ☢
 where
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 [𝕥≡𝕗]
Bool-conv₂ false true false false [𝕗≡𝕗→𝕥≡𝕗] [𝕥≡𝕥] = ω ☢
 where
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 ([𝕗≡𝕗→𝕥≡𝕗] refl)
Bool-conv₂ false false true true [𝕗≡𝕥→𝕗≡𝕥] [𝕗≡𝕗] = refl
Bool-conv₂ false false true false [𝕗≡𝕥→𝕗≡𝕗] [𝕗≡𝕥] = refl
Bool-conv₂ false false false true [𝕗≡𝕗→𝕗≡𝕥] [𝕗≡𝕗] = ω ☢
 where
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 (≡-↑↓ ([𝕗≡𝕗→𝕗≡𝕥] refl))
Bool-conv₂ false false false false [𝕗≡𝕗→𝕗≡𝕗] [𝕗≡𝕥] = ω ☢
 where
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 (≡-↑↓ [𝕗≡𝕥])

{-
∃ n ∈ Nat ,
∃ assign ∈ PersonLabel → Fin n ,
 assign Agatha ≠ assign the-butler 
∃ richer-than ∈ FinRel {n} {n} ,
∃ hates ∈ FinRel₂ {n} {n} , 
 ((person1 : Fin n) → ∃ person2 ∈ Fin m , (hates person1 person2 ≡ false)) ∧ 
 ((person : Fin n) → assign the-butler ≠ person → hates (assign Agatha) person ≡ true) ∧
 hates (assign Agatha) (assign the-butler) ≡ false ∧  
 ((person : Fin n) → hates (assign Agatha) person ≡ true → hates (assign Charles) person ≡ false) ∧ 
 ((person : Fin n) → hates (assign Agatha) person ≡ true → hates (assign the-butler) person ≡ true) ∧
 ((person : Fin n) → richer-than person (assign Agatha) ≡ false → hates (assign the-butler) person ≡ true)

-}

ValidRelations : (n : Nat) → (assign : PersonLabel → Fin n) → (richer-than : FinRel {n} {n}) → (hates : FinRel {n} {n}) → Set
ValidRelations n assign richer-than hates = 
 (assign Agatha ≠ assign the-butler) ∧
 ((person1 : Fin n) → ∃ person2 ∈ Fin n , (hates person1 person2 ≡ false)) ∧
 ((person : Fin n) → person ≠ assign the-butler → hates (assign Agatha) person ≡ true) ∧
 (hates (assign Agatha) (assign the-butler) ≡ false) ∧
 ((person : Fin n) → hates (assign Agatha) person ≡ true → hates (assign Charles) person ≡ false) ∧
 ((person : Fin n) → hates (assign Agatha) person ≡ true → hates (assign the-butler) person ≡ true) ∧
 ((person : Fin n) → richer-than person (assign Agatha) ≡ false → hates (assign the-butler) person ≡ true)

{-
The only way we know that the butler doesn't hate the butler is by the assumption that the only
people under consideration are those who live at Dreadbury Mansion.
Agatha hates Agatha, for sure, but the only way Agatha is a candidate is if Agatha is not richer
than Agatha. The rules don't tell us anything about this so we need an extra rule
-}


ValidRelations₂ : (n : Nat) → (assign : PersonLabel → Fin n) → (richer-than : FinRel {n} {n}) → (hates : FinRel {n} {n}) → Set
ValidRelations₂ n assign richer-than hates = 
 (assign Agatha ≠ assign the-butler) ∧
 ((person1 : Fin n) → ∃ person2 ∈ Fin n , (hates person1 person2 ≡ false)) ∧
 ((person : Fin n) → person ≠ assign the-butler → hates (assign Agatha) person ≡ true) ∧
 (hates (assign Agatha) (assign the-butler) ≡ false) ∧
 ((person : Fin n) → hates (assign Agatha) person ≡ true → hates (assign Charles) person ≡ false) ∧
 ((person : Fin n) → hates (assign Agatha) person ≡ true → hates (assign the-butler) person ≡ true) ∧
 ((person : Fin n) → richer-than person (assign Agatha) ≡ false → hates (assign the-butler) person ≡ true) ∧
 ((person : Fin n) → richer-than person person ≡ false)


ValidRelations₃ : (n : Nat) → (assign : PersonLabel → Fin n) → (lives-at-Dreadbury-Mansion : Fin n → Bool) → (richer-than : FinRel {n} {n}) → (hates : FinRel {n} {n}) → (could-have-killed : FinRel {n} {n}) → Set
ValidRelations₃ n assign lives-at-Dreadbury-Mansion richer-than hates could-have-killed =
 {-
  Somebody who lives in Dreadbury Mansion killed Aunt Agatha. 
 -} 
 ((person : Fin n) → lives-at-Dreadbury-Mansion person ≡ false → could-have-killed person (assign Agatha) ≡ false) ∧ 
 {-
  Agatha, the butler, and Charles live in Dreadbury Mansion, and are the only people
  who live therein.
 -}
 (lives-at-Dreadbury-Mansion (assign Agatha) ≡ true) ∧
 (lives-at-Dreadbury-Mansion (assign Charles) ≡ true) ∧
 (lives-at-Dreadbury-Mansion (assign the-butler) ≡ true) ∧
 ((person : Fin n) → person ≠ assign Agatha → person ≠ assign Charles → person ≠ assign the-butler → lives-at-Dreadbury-Mansion person ≡ false) ∧

 {-
  A killer always hates his victim, and is never richer than his victim.
 -}
 ((person1 person2 : Fin n) → hates person1 person2 ≡ false → could-have-killed person1 person2 ≡ false) ∧
 ((person1 person2 : Fin n) → richer-than person1 person2 ≡ true → could-have-killed person1 person2 ≡ false) ∧ 

 {-
  Charles hates no one that Aunt Agatha hates.
 -}
 ((person : Fin n) → hates (assign Agatha) person ≡ true → hates (assign Charles) person ≡ false) ∧

 {-
  Agatha hates everyone except the butler.
 -}
 ((person : Fin n) → person ≠ assign the-butler → hates (assign Agatha) person ≡ true) ∧
 (hates (assign Agatha) (assign the-butler) ≡ false) ∧

 {-
  The butler hates everyone not richer than Aunt Agatha.
 -}
 ((person : Fin n) → richer-than person (assign Agatha) ≡ false → hates (assign the-butler) person ≡ true) ∧ 

 {-
  The butler hates everyone Aunt Agatha hates.
 -}
 ((person : Fin n) → hates (assign Agatha) person ≡ true → hates (assign the-butler) person ≡ true) ∧
 
 {-
  No one hates everyone.
  Modified to: No one who lives at Dreadbury Mansion hates everyone who lives at Dreadbury Mansion.
 -}
 ((person1 : Fin n) → lives-at-Dreadbury-Mansion person1 ≡ true → ∃ person2 ∈ Fin n , ((lives-at-Dreadbury-Mansion person2 ≡ true) ∧ (hates person1 person2 ≡ false))) ∧

 {-
  Agatha is not the butler.
 -}
 (assign Agatha ≠ assign the-butler) ∧

 {-
  Extra axiom: no one is richer than themselves.
 -}
 ((person : Fin n) → richer-than person person ≡ false)


record World : Set where
 field
  population : Nat
  assign : PersonLabel → Fin population
  lives-at-Dreadbury-Mansion : Fin population → Bool
  _is-richer-than_ : FinRel {population} {population}
  _hates_ : FinRel {population} {population}
  _could-have-killed_ : FinRel {population} {population}

record PossibleWorld : Set where 
 field
  population : Nat 
  assign : PersonLabel → Fin population
  lives-at-Dreadbury-Mansion : Fin population → Bool 
  _is-richer-than_ : FinRel {population} {population}
  _hates_ : FinRel {population} {population}
  _could-have-killed_ : FinRel {population} {population}
  _killed_ : FinRel {population} {population}
  could-have-killed-Agatha : Fin population → Bool
   
  somebody-who-lives-in-Dreadbury-Mansion-killed-Aunt-Agatha : (person : Fin population) → lives-at-Dreadbury-Mansion person ≡ false → could-have-killed-Agatha person ≡ false 

  somebody-who-lives-in-Dreadbury-Mansion-killed-Aunt-Agatha₂ : ∃ person ∈ (Fin population) , (lives-at-Dreadbury-Mansion person ≡ true ∧ person killed (assign Agatha) ≡ true)

  Agathas-killer-must-have-been-able-to-kill-her : (person : Fin population) → person could-have-killed (assign Agatha) ≡ false → could-have-killed-Agatha person ≡ false

  Agatha-lives-in-Dreadbury-Mansion : lives-at-Dreadbury-Mansion (assign Agatha) ≡ true

  Charles-lives-in-Dreadbury-Mansion : lives-at-Dreadbury-Mansion (assign Charles) ≡ true

  the-butler-lives-in-Dreadbury-Mansion : lives-at-Dreadbury-Mansion (assign the-butler) ≡ true

  nobody-else-lives-in-Dreadbury-Mansion : (person : Fin population) → person ≠ assign Agatha → person ≠ assign Charles → person ≠ assign the-butler → lives-at-Dreadbury-Mansion person ≡ false

  Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein : (person : Fin population) → lives-at-Dreadbury-Mansion person ≡ true → person ≡ (assign Agatha) ∨ person ≡ (assign the-butler) ∨ person ≡ (assign Charles)

  a-killer-always-hates-his-victim : (person1 person2 : Fin population) → person1 hates person2 ≡ false → person1 could-have-killed person2 ≡ false

  a-killer-is-never-richer-than-his-victim : (person1 person2 : Fin population) → person1 is-richer-than person2 ≡ true → person1 could-have-killed person2 ≡ false

  a-killer-always-hates-his-victim-and-is-never-richer-than-his-victim : (person1 person2 : Fin population) → person1 hates person2 ≡ true → person1 is-richer-than person2 ≡ false → person1 could-have-killed person2 ≡ true

  a-killer-always-hates-his-victim₂ : (person1 person2 : Fin population) → person1 killed person2 ≡ true → person1 hates person2 ≡ true

  a-killer-is-never-richer-than-his-victim₂ : (person1 person2 : Fin population) → person1 killed person2 ≡ true → person1 is-richer-than person2 ≡ false

  Charles-hates-no-one-that-Aunt-Agatha-hates : (person : Fin population) → (assign Agatha) hates person ≡ true → (assign Charles) hates person ≡ false

  Agatha-hates-everyone-except-the-butler : (person : Fin population) → person ≠ assign the-butler → (assign Agatha) hates person ≡ true

  Agatha-doesnt-hate-the-butler : (assign Agatha) hates (assign the-butler) ≡ false

  the-butler-hates-everyone-not-richer-than-Aunt-Agatha : (person : Fin population) → person is-richer-than (assign Agatha) ≡ false → (assign the-butler) hates person ≡ true

  the-butler-hates-everyone-Aunt-Agatha-hates : (person : Fin population) → (assign Agatha) hates person ≡ true → (assign the-butler) hates person ≡ true
 
  no-one-hates-everyone : (person1 : Fin population) → lives-at-Dreadbury-Mansion person1 ≡ true → ∃ person2 ∈ Fin population , ((lives-at-Dreadbury-Mansion person2 ≡ true) ∧ (person1 hates person2 ≡ false))

  Agatha-is-not-the-butler : assign Agatha ≠ assign the-butler

  no-one-is-richer-than-themselves : (person : Fin population) → person is-richer-than person ≡ false

  Agathas-killer-lives-at-Dreadbury-Mansion : (person : Fin population) → person could-have-killed (assign Agatha) ≡ true → lives-at-Dreadbury-Mansion person ≡ true → could-have-killed-Agatha person ≡ true

  

 
{-
Now we want to prove that in any set of relations that satisfies ValidRelations₃, 
∃ person ∈ Fin n , (could-have-killed person (assign Agatha)) → person ≡ Agatha
-}

{-
Lemma: In every possible world, Agatha hates Agatha.
-}

the-butler-is-not-Agatha : (world : PossibleWorld) → ((PossibleWorld.assign world) the-butler) ≠ ((PossibleWorld.assign world) Agatha)
the-butler-is-not-Agatha world = ≠-↑↓ (PossibleWorld.Agatha-is-not-the-butler world)

Agatha-hates-Agatha : 
 (world : PossibleWorld) → (PossibleWorld._hates_ world) ((PossibleWorld.assign world) Agatha) ((PossibleWorld.assign world) Agatha) ≡ true
Agatha-hates-Agatha world = proof
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  _hates_ : FinRel {population} {population}
  _hates_ = PossibleWorld._hates_ world

  Agatha-hates-everyone-except-the-butler : (person : Fin population) → person ≠ assign the-butler → (assign Agatha) hates person ≡ true
  Agatha-hates-everyone-except-the-butler = PossibleWorld.Agatha-hates-everyone-except-the-butler world

  Agatha-is-not-the-butler : assign Agatha ≠ assign the-butler
  Agatha-is-not-the-butler = PossibleWorld.Agatha-is-not-the-butler world

  proof : (assign Agatha) hates (assign Agatha) ≡ true
  proof = Agatha-hates-everyone-except-the-butler (assign Agatha) Agatha-is-not-the-butler



the-butler-hates-everyone-except-the-butler : (world : PossibleWorld) → (person : Fin (PossibleWorld.population world)) → person ≠ (PossibleWorld.assign world) the-butler → (PossibleWorld._hates_ world) ((PossibleWorld.assign world) the-butler) person ≡ true
the-butler-hates-everyone-except-the-butler world = proof
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  _hates_ : FinRel {population} {population}
  _hates_ = PossibleWorld._hates_ world

  Agatha-hates-everyone-except-the-butler : (person : Fin population) → person ≠ assign the-butler → (assign Agatha) hates person ≡ true
  Agatha-hates-everyone-except-the-butler = PossibleWorld.Agatha-hates-everyone-except-the-butler world

  the-butler-hates-everyone-Aunt-Agatha-hates : (person : Fin population) → (assign Agatha) hates person ≡ true → (assign the-butler) hates person ≡ true
  the-butler-hates-everyone-Aunt-Agatha-hates = PossibleWorld.the-butler-hates-everyone-Aunt-Agatha-hates world
  
  proof : (person : Fin population) → person ≠ (assign the-butler) → (assign the-butler) hates person ≡ true
  proof person person-is-not-the-butler = the-butler-hates-everyone-Aunt-Agatha-hates person (Agatha-hates-everyone-except-the-butler person person-is-not-the-butler)

the-butler-hates-Agatha : (world : PossibleWorld) → (PossibleWorld._hates_ world) ((PossibleWorld.assign world) the-butler) ((PossibleWorld.assign world) Agatha) ≡ true
the-butler-hates-Agatha world = proof
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  _hates_ : FinRel {population} {population}
  _hates_ = PossibleWorld._hates_ world

  Agatha-is-not-the-butler : assign Agatha ≠ assign the-butler
  Agatha-is-not-the-butler = PossibleWorld.Agatha-is-not-the-butler world
  
  proof : (assign the-butler) hates (assign Agatha) ≡ true
  proof = the-butler-hates-everyone-except-the-butler world (assign Agatha) Agatha-is-not-the-butler 

Charles-doesnt-hate-Agatha :
 (world : PossibleWorld) → (PossibleWorld._hates_ world) ((PossibleWorld.assign world) Charles) ((PossibleWorld.assign world) Agatha) ≡ false
Charles-doesnt-hate-Agatha world = proof
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  _hates_ : FinRel {population} {population}
  _hates_ = PossibleWorld._hates_ world

  Charles-hates-no-one-that-Aunt-Agatha-hates : (person : Fin population) → (assign Agatha) hates person ≡ true → (assign Charles) hates person ≡ false
  Charles-hates-no-one-that-Aunt-Agatha-hates = PossibleWorld.Charles-hates-no-one-that-Aunt-Agatha-hates world

  proof : (assign Charles) hates (assign Agatha) ≡ false
  proof = Charles-hates-no-one-that-Aunt-Agatha-hates (assign Agatha) (Agatha-hates-Agatha world)


Charles-is-not-Agatha : (world : PossibleWorld) → ((PossibleWorld.assign world) Charles) ≠ ((PossibleWorld.assign world) Agatha)
Charles-is-not-Agatha world = proof
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  _hates_ : FinRel {population} {population}
  _hates_ = PossibleWorld._hates_ world

  proof : (assign Charles) ≠ (assign Agatha)
  proof Charles-is-Agatha = proof2
   where
    Agatha-hates-Agatha' : (assign Agatha) hates (assign Agatha) ≡ true
    Agatha-hates-Agatha' = Agatha-hates-Agatha world

    Charles-doesnt-hate-Agatha' : (assign Charles) hates (assign Agatha) ≡ false
    Charles-doesnt-hate-Agatha' = Charles-doesnt-hate-Agatha world
    
    hates-Agatha : Fin (population) → Bool
    hates-Agatha person = person hates (assign Agatha)

    Charles-hates-Agatha : (assign Charles) hates (assign Agatha) ≡ true
    Charles-hates-Agatha = ≡-⇶ ([x≡y]→[fx≡fy] hates-Agatha (assign Charles) (assign Agatha) Charles-is-Agatha) Agatha-hates-Agatha'

    proof2 : ⊥
    proof2 = 𝕥≠𝕗 (≡-⇶ (≡-↑↓ Charles-hates-Agatha) Charles-doesnt-hate-Agatha')

Agatha-is-not-Charles : (world : PossibleWorld) → ((PossibleWorld.assign world) Agatha) ≠ ((PossibleWorld.assign world) Charles)
Agatha-is-not-Charles world = ≠-↑↓ (Charles-is-not-Agatha world)

Charles-is-not-the-butler : (world : PossibleWorld) → ((PossibleWorld.assign world) Charles) ≠ ((PossibleWorld.assign world) the-butler)
Charles-is-not-the-butler world = proof
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  _hates_ : FinRel {population} {population}
  _hates_ = PossibleWorld._hates_ world

  proof : (assign Charles) ≠ (assign the-butler)
  proof Charles-is-the-butler = proof2
   where
    the-butler-hates-Agatha' : (assign the-butler) hates (assign Agatha) ≡ true
    the-butler-hates-Agatha' = the-butler-hates-Agatha world

    Charles-doesnt-hate-Agatha' : (assign Charles) hates (assign Agatha) ≡ false
    Charles-doesnt-hate-Agatha' = Charles-doesnt-hate-Agatha world

    hates-Agatha : (person : Fin population) → Bool
    hates-Agatha person = person hates (assign Agatha)

    Charles-hates-Agatha : (assign Charles) hates (assign Agatha) ≡ true
    Charles-hates-Agatha = ≡-⇶ ([x≡y]→[fx≡fy] hates-Agatha (assign Charles) (assign the-butler) Charles-is-the-butler) the-butler-hates-Agatha'

    proof2 : ⊥
    proof2 = 𝕥≠𝕗 (≡-⇶ (≡-↑↓ Charles-hates-Agatha) Charles-doesnt-hate-Agatha')

the-butler-is-not-Charles : (world : PossibleWorld) → ((PossibleWorld.assign world) the-butler) ≠ ((PossibleWorld.assign world) Charles)
the-butler-is-not-Charles world = ≠-↑↓ (Charles-is-not-the-butler world)

the-butler-hates-Charles : (world : PossibleWorld) → (PossibleWorld._hates_ world) ((PossibleWorld.assign world) the-butler) ((PossibleWorld.assign world) Charles) ≡ true
the-butler-hates-Charles world = proof
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  _hates_ : FinRel {population} {population}
  _hates_ = PossibleWorld._hates_ world
  
  proof : (assign the-butler) hates (assign Charles) ≡ true
  proof = the-butler-hates-everyone-except-the-butler world (assign Charles) (Charles-is-not-the-butler world)

Agatha-is-not-richer-than-Agatha : (world : PossibleWorld) → (PossibleWorld._is-richer-than_ world) ((PossibleWorld.assign world) Agatha) ((PossibleWorld.assign world) Agatha) ≡ false
Agatha-is-not-richer-than-Agatha world = (PossibleWorld.no-one-is-richer-than-themselves world) ((PossibleWorld.assign world) Agatha)

Agatha-could-have-killed-Agatha : (world : PossibleWorld) → (PossibleWorld._could-have-killed_ world) ((PossibleWorld.assign world) Agatha) ((PossibleWorld.assign world) Agatha) ≡ true
Agatha-could-have-killed-Agatha world = proof
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  _could-have-killed_ : FinRel {population} {population}
  _could-have-killed_ = PossibleWorld._could-have-killed_ world

  _hates_ : FinRel {population} {population}
  _hates_ = PossibleWorld._hates_ world

  _is-richer-than_ : FinRel {population} {population}
  _is-richer-than_ = PossibleWorld._is-richer-than_ world

  a-killer-always-hates-his-victim-and-is-never-richer-than-his-victim : (person1 person2 : Fin population) → person1 hates person2 ≡ true → person1 is-richer-than person2 ≡ false → person1 could-have-killed person2 ≡ true
  a-killer-always-hates-his-victim-and-is-never-richer-than-his-victim = PossibleWorld.a-killer-always-hates-his-victim-and-is-never-richer-than-his-victim world

  proof : (assign Agatha) could-have-killed (assign Agatha) ≡ true
  proof = a-killer-always-hates-his-victim-and-is-never-richer-than-his-victim (assign Agatha) (assign Agatha) (Agatha-hates-Agatha world) (Agatha-is-not-richer-than-Agatha world)

Agatha-could-have-killed-Agatha' : (world : PossibleWorld) → (PossibleWorld.could-have-killed-Agatha world) ((PossibleWorld.assign world) Agatha) ≡ true
Agatha-could-have-killed-Agatha' world = (PossibleWorld.Agathas-killer-lives-at-Dreadbury-Mansion world) ((PossibleWorld.assign world) Agatha) (Agatha-could-have-killed-Agatha world) (PossibleWorld.Agatha-lives-in-Dreadbury-Mansion world)


Butler-doesnt-hate-Butler₁ : (world : PossibleWorld) → (PossibleWorld._hates_ world) ((PossibleWorld.assign world) the-butler) ((PossibleWorld.assign world) the-butler) ≠ true
Butler-doesnt-hate-Butler₁ world = proof
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  lives-at-Dreadbury-Mansion : Fin population → Bool
  lives-at-Dreadbury-Mansion = PossibleWorld.lives-at-Dreadbury-Mansion world

  _hates_ : FinRel {population} {population}
  _hates_ = PossibleWorld._hates_ world
  
  no-one-hates-everyone : (person1 : Fin population) → lives-at-Dreadbury-Mansion person1 ≡ true → ∃ person2 ∈ Fin population , ((lives-at-Dreadbury-Mansion person2 ≡ true) ∧ (person1 hates person2 ≡ false))
  no-one-hates-everyone = PossibleWorld.no-one-hates-everyone world

  Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein : (person : Fin population) → lives-at-Dreadbury-Mansion person ≡ true → person ≡ (assign Agatha) ∨ person ≡ (assign the-butler) ∨ person ≡ (assign Charles)
  Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein = PossibleWorld.Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein world

  no-one-hates-Agatha-and-the-butler-and-Charles : (person1 : Fin population) → lives-at-Dreadbury-Mansion person1 ≡ true → ∃ person2 ∈ Fin population , ((person2 ≡ assign Agatha ∨ person2 ≡ assign the-butler ∨ person2 ≡ assign Charles) ∧ (person1 hates person2 ≡ false))
  no-one-hates-Agatha-and-the-butler-and-Charles person1 person1-lives-at-Dreadbury-Mansion = proof'
   where
    person1-doesnt-hate-someone : ∃ person2 ∈ Fin population , ((lives-at-Dreadbury-Mansion person2 ≡ true) ∧ (person1 hates person2 ≡ false))
    person1-doesnt-hate-someone = no-one-hates-everyone person1 person1-lives-at-Dreadbury-Mansion

    person2 : Fin population
    person2 = π₁ person1-doesnt-hate-someone

    person2-lives-at-Dreadbury-Mansion : lives-at-Dreadbury-Mansion person2 ≡ true
    person2-lives-at-Dreadbury-Mansion = first (π₂ person1-doesnt-hate-someone)

    person1-doesnt-hate-person2 : person1 hates person2 ≡ false
    person1-doesnt-hate-person2 = second (π₂ person1-doesnt-hate-someone)

    person2-is-Agatha-or-the-butler-or-Charles : person2 ≡ assign Agatha ∨ person2 ≡ assign the-butler ∨ person2 ≡ assign Charles
    person2-is-Agatha-or-the-butler-or-Charles = Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein person2 person2-lives-at-Dreadbury-Mansion

    proof' : ∃ person2 ∈ Fin population , ((person2 ≡ assign Agatha ∨ person2 ≡ assign the-butler ∨ person2 ≡ assign Charles) ∧ (person1 hates person2 ≡ false))
    proof' = (person2 , (person2-is-Agatha-or-the-butler-or-Charles , person1-doesnt-hate-person2))
 
  the-butler-lives-in-Dreadbury-Mansion : lives-at-Dreadbury-Mansion (assign the-butler) ≡ true
  the-butler-lives-in-Dreadbury-Mansion = PossibleWorld.the-butler-lives-in-Dreadbury-Mansion world

  the-butler-doesnt-hate-Agatha-and-the-butler-and-Charles : ∃ person2 ∈ Fin population , ((person2 ≡ assign Agatha ∨ person2 ≡ assign the-butler ∨ person2 ≡ assign Charles) ∧ ((assign the-butler) hates person2 ≡ false))
  the-butler-doesnt-hate-Agatha-and-the-butler-and-Charles = no-one-hates-Agatha-and-the-butler-and-Charles (assign the-butler) the-butler-lives-in-Dreadbury-Mansion

  the-butler-doesnt-hate-everyone : ∃ person ∈ Fin population , ((lives-at-Dreadbury-Mansion person ≡ true) ∧ ((assign the-butler) hates person ≡ false))
  the-butler-doesnt-hate-everyone = no-one-hates-everyone (assign the-butler) the-butler-lives-in-Dreadbury-Mansion

  person-the-butler-doesnt-hate : Fin population
  person-the-butler-doesnt-hate = π₁ the-butler-doesnt-hate-Agatha-and-the-butler-and-Charles

  person-the-butler-doesnt-hate-is-Agatha-or-the-butler-or-Charles : person-the-butler-doesnt-hate ≡ assign Agatha ∨ person-the-butler-doesnt-hate ≡ assign the-butler ∨ person-the-butler-doesnt-hate ≡ assign Charles
  person-the-butler-doesnt-hate-is-Agatha-or-the-butler-or-Charles = first (π₂ the-butler-doesnt-hate-Agatha-and-the-butler-and-Charles)

  the-butler-doesnt-hate-the-person-the-butler-doesnt-hate : (assign the-butler) hates person-the-butler-doesnt-hate ≡ false
  the-butler-doesnt-hate-the-person-the-butler-doesnt-hate = second (π₂ the-butler-doesnt-hate-Agatha-and-the-butler-and-Charles)

  person-the-butler-doesnt-hate' : Fin population
  person-the-butler-doesnt-hate' = π₁ the-butler-doesnt-hate-everyone

  person-the-butler-doesnt-hate-lives-at-Dreadbury-Mansion : lives-at-Dreadbury-Mansion person-the-butler-doesnt-hate' ≡ true
  person-the-butler-doesnt-hate-lives-at-Dreadbury-Mansion = first (π₂ the-butler-doesnt-hate-everyone)

  the-butler-doesnt-hate-the-person-the-butler-doesnt-hate' : (assign the-butler) hates person-the-butler-doesnt-hate' ≡ false
  the-butler-doesnt-hate-the-person-the-butler-doesnt-hate' = second (π₂ the-butler-doesnt-hate-everyone)

  proof : ((assign the-butler) hates (assign the-butler)) ≠ true
  proof the-butler-hates-the-butler = proof2
   where
    the-butler-hates-everyone : (person : Fin population) → lives-at-Dreadbury-Mansion person ≡ true → (assign the-butler) hates person ≡ true
    the-butler-hates-everyone person person-lives-at-Dreadbury-Mansion = proof3
     where
      person-is-Agatha-or-the-butler-or-Charles : person ≡ (assign Agatha) ∨ person ≡ (assign the-butler) ∨ person ≡ (assign Charles)
      person-is-Agatha-or-the-butler-or-Charles = Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein person person-lives-at-Dreadbury-Mansion
      
      the-butler-hates : Fin population → Bool
      the-butler-hates = _hates_ (assign the-butler)

      person-is-Agatha-or-the-butler-or-Charles-implies-the-butler-hates-person : (person ≡ (assign Agatha) ∨ person ≡ (assign the-butler) ∨ person ≡ (assign Charles)) → (assign the-butler) hates person ≡ true
      person-is-Agatha-or-the-butler-or-Charles-implies-the-butler-hates-person (inl person-is-Agatha) = the-butler-hates-person
       where
        the-butler-hates-person : (assign the-butler) hates person ≡ true
        the-butler-hates-person = ≡-⇶ ([x≡y]→[fx≡fy] the-butler-hates person (assign Agatha) person-is-Agatha) (the-butler-hates-Agatha world)
      person-is-Agatha-or-the-butler-or-Charles-implies-the-butler-hates-person (inr (inl person-is-the-butler)) = the-butler-hates-person
       where
        the-butler-hates-person : (assign the-butler) hates person ≡ true
        the-butler-hates-person = ≡-⇶ ([x≡y]→[fx≡fy] the-butler-hates person (assign the-butler) person-is-the-butler) the-butler-hates-the-butler
      person-is-Agatha-or-the-butler-or-Charles-implies-the-butler-hates-person (inr (inr person-is-Charles)) = the-butler-hates-person
       where
        the-butler-hates-person : (assign the-butler) hates person ≡ true
        the-butler-hates-person = ≡-⇶ ([x≡y]→[fx≡fy] the-butler-hates person (assign Charles) person-is-Charles) (the-butler-hates-Charles world)

      proof3 : (assign the-butler) hates person ≡ true
      proof3 = person-is-Agatha-or-the-butler-or-Charles-implies-the-butler-hates-person person-is-Agatha-or-the-butler-or-Charles

    the-butler-hates-the-person-the-butler-doesnt-hate : (assign the-butler) hates person-the-butler-doesnt-hate' ≡ true
    the-butler-hates-the-person-the-butler-doesnt-hate = the-butler-hates-everyone person-the-butler-doesnt-hate' person-the-butler-doesnt-hate-lives-at-Dreadbury-Mansion

    proof2 : ⊥
    proof2 = 𝕥≠𝕗 (≡-⇶ (≡-↑↓ the-butler-hates-the-person-the-butler-doesnt-hate) the-butler-doesnt-hate-the-person-the-butler-doesnt-hate')

Butler-doesnt-hate-Butler : 
 (world : PossibleWorld) → (PossibleWorld._hates_ world) ((PossibleWorld.assign world) the-butler) ((PossibleWorld.assign world) the-butler) ≡ false
Butler-doesnt-hate-Butler world = bool-DN ((PossibleWorld._hates_ world) ((PossibleWorld.assign world) the-butler) ((PossibleWorld.assign world) the-butler)) true (Butler-doesnt-hate-Butler₁ world)

Butler-is-richer-than-Agatha :
 (world : PossibleWorld) → (PossibleWorld._is-richer-than_ world) ((PossibleWorld.assign world) the-butler) ((PossibleWorld.assign world) Agatha) ≡ true
Butler-is-richer-than-Agatha world = proof
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  _hates_ : FinRel {population} {population}
  _hates_ = PossibleWorld._hates_ world

  _is-richer-than_ : FinRel {population} {population}
  _is-richer-than_ = PossibleWorld._is-richer-than_ world

  the-butler-hates-everyone-not-richer-than-Aunt-Agatha : (person : Fin population) → person is-richer-than (assign Agatha) ≡ false → (assign the-butler) hates person ≡ true
  the-butler-hates-everyone-not-richer-than-Aunt-Agatha = PossibleWorld.the-butler-hates-everyone-not-richer-than-Aunt-Agatha world

  proof : (assign the-butler) is-richer-than (assign Agatha) ≡ true
  proof = Bool-conv₂ ((assign the-butler) is-richer-than (assign Agatha)) ((assign the-butler) hates (assign the-butler)) false true (the-butler-hates-everyone-not-richer-than-Aunt-Agatha (assign the-butler)) (Butler-doesnt-hate-Butler world)

the-butler-couldnt-have-killed-Agatha : 
 (world : PossibleWorld) → (PossibleWorld._could-have-killed_ world) ((PossibleWorld.assign world) the-butler) ((PossibleWorld.assign world) Agatha) ≡ false
the-butler-couldnt-have-killed-Agatha world = proof
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  _is-richer-than_ : FinRel {population} {population}
  _is-richer-than_ = PossibleWorld._is-richer-than_ world

  _could-have-killed_ : FinRel {population} {population}
  _could-have-killed_ = PossibleWorld._could-have-killed_ world

  a-killer-is-never-richer-than-his-victim : (person1 person2 : Fin population) → person1 is-richer-than person2 ≡ true → person1 could-have-killed person2 ≡ false
  a-killer-is-never-richer-than-his-victim = PossibleWorld.a-killer-is-never-richer-than-his-victim world

  proof : (assign the-butler) could-have-killed (assign Agatha) ≡ false
  proof = a-killer-is-never-richer-than-his-victim (assign the-butler) (assign Agatha) (Butler-is-richer-than-Agatha world)

the-butler-couldnt-have-killed-Agatha' :
 (world : PossibleWorld) → (PossibleWorld.could-have-killed-Agatha world) ((PossibleWorld.assign world) the-butler) ≡ false
the-butler-couldnt-have-killed-Agatha' world = proof
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  _could-have-killed_ : FinRel {population} {population}
  _could-have-killed_ = PossibleWorld._could-have-killed_ world

  could-have-killed-Agatha : Fin population → Bool
  could-have-killed-Agatha = PossibleWorld.could-have-killed-Agatha world

  Agathas-killer-must-have-been-able-to-kill-her : (person : Fin population) → person could-have-killed (assign Agatha) ≡ false → could-have-killed-Agatha person ≡ false
  Agathas-killer-must-have-been-able-to-kill-her = PossibleWorld.Agathas-killer-must-have-been-able-to-kill-her world

  proof : could-have-killed-Agatha (assign the-butler) ≡ false
  proof = Agathas-killer-must-have-been-able-to-kill-her (assign the-butler) (the-butler-couldnt-have-killed-Agatha world)

Charles-couldnt-have-killed-Agatha : 
 (world : PossibleWorld) → (PossibleWorld._could-have-killed_ world) ((PossibleWorld.assign world) Charles) ((PossibleWorld.assign world) Agatha) ≡ false
Charles-couldnt-have-killed-Agatha world = proof
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  _hates_ : FinRel {population} {population}
  _hates_ = PossibleWorld._hates_ world

  _could-have-killed_ : FinRel {population} {population}
  _could-have-killed_ = PossibleWorld._could-have-killed_ world

  a-killer-always-hates-his-victim : (person1 person2 : Fin population) → person1 hates person2 ≡ false → person1 could-have-killed person2 ≡ false
  a-killer-always-hates-his-victim = PossibleWorld.a-killer-always-hates-his-victim world

  proof : (assign Charles) could-have-killed (assign Agatha) ≡ false
  proof = a-killer-always-hates-his-victim (assign Charles) (assign Agatha) (Charles-doesnt-hate-Agatha world)

Charles-couldnt-have-killed-Agatha' :
 (world : PossibleWorld) → (PossibleWorld.could-have-killed-Agatha world) ((PossibleWorld.assign world) Charles) ≡ false
Charles-couldnt-have-killed-Agatha' world = proof
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  _could-have-killed_ : FinRel {population} {population}
  _could-have-killed_ = PossibleWorld._could-have-killed_ world

  could-have-killed-Agatha : Fin population → Bool
  could-have-killed-Agatha = PossibleWorld.could-have-killed-Agatha world

  Agathas-killer-must-have-been-able-to-kill-her : (person : Fin population) → person could-have-killed (assign Agatha) ≡ false → could-have-killed-Agatha person ≡ false
  Agathas-killer-must-have-been-able-to-kill-her = PossibleWorld.Agathas-killer-must-have-been-able-to-kill-her world

  proof : could-have-killed-Agatha (assign Charles) ≡ false
  proof = Agathas-killer-must-have-been-able-to-kill-her (assign Charles) (Charles-couldnt-have-killed-Agatha world)

{-
Agatha-must-have-killed-Agatha :
 (world : PossibleWorld) → (PossibleWorld.could-have-killed-Agatha world) ((PossibleWorld.assign world) Agatha) ∧ ((person : Fin (PossibleWorld.population world)) → (PossibleWorld.could-have-killed-Agatha world) person → person ≡ Agatha)
Agatha-must-have-killed-Agatha world = ([Agatha-could-have-killed-Agatha] , [Agatha-is-the-only-one-who-could-have-killed-Agatha])
 where
  population : Nat
  population = PossibleWorld.population world
  
  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  could-have-killed-Agatha : Fin population → Bool
  could-have-killed-Agatha = PossibleWorld.could-have-killed-Agatha world

  [Agatha-could-have-killed-Agatha] : could-have-killed-Agatha (assign Agatha) ≡ true
  [Agatha-could-have-killed-Agatha] = Agatha-could-have-killed-Agatha' world

  [Agatha-is-the-only-one-who-could-have-killed-Agatha] : (person : Fin population) → could-have-killed-Agatha person ≡ true → person ≡ (assign Agatha)
  [Agatha-is-the-only-one-who-could-have-killed-Agatha] person 
-}

{-
Agatha-must-have-killed-Agatha₂ :
 (world : PossibleWorld) → (PossibleWorld.could-have-killed-Agatha world) ((PossibleWorld.assign world) Agatha) ∧ ((person : Fin (PossibleWorld.population world)) → person ≠ ((PossibleWorld.assign world) Agatha) → (PossibleWorld.could-have-killed-Agatha world) person ≡ false)
Agatha-must-have-killed-Agatha world = ([Agatha-could-have-killed-Agatha] , [no-one-else-could-have-killed-Agatha])
 where
  population : Nat
  population = PossibleWorld.population world
  
  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  could-have-killed-Agatha : Fin population → Bool
  could-have-killed-Agatha = PossibleWorld.could-have-killed-Agatha world

  [Agatha-could-have-killed-Agatha] : could-have-killed-Agatha (assign Agatha) ≡ true
  [Agatha-could-have-killed-Agatha] = Agatha-could-have-killed-Agatha' world

  [no-one-else-could-have-killed-Agatha] : (person : Fin population) → person ≠ (assign Agatha) → could-have-killed-Agatha person ≡ false
  [no-one-else-could-have-killed-Agatha] person person-is-not-Agatha = person-couldnt-have-killed-Agatha
   where
    person-couldnt-have-killed-Agatha
-}

{-
if-somebody-is-not-Agatha-then-they-must-be-Charles-or-the-butler-or-not-live-at-Dreadbury-Mansion : 
 (world : PossibleWorld) → (person : Fin (PossibleWorld.population world) → person ≠ ((PossibleWorld.assign world) Agatha) → (person ≡ ((PossibleWorld.assign world) Charles) ∨ person ≡ ((PossibleWorld.assign world) the-butler) ∨ (PossibleWorld.lives-at-Dreadbury-Mansion world) person ≡ false)
if-somebody-is-not-Agatha-then-they-must-be-Charles-or-the-butler-or-not-live-at-Dreadbury-Mansion world person person-is-not-Agatha = proof
 where
-}

Agathas-killer-is-Agatha-or-the-butler-or-Charles : (world : PossibleWorld) → (person : Fin (PossibleWorld.population world)) → (PossibleWorld.could-have-killed-Agatha world) person ≡ true → (person ≡ ((PossibleWorld.assign world) Agatha) ∨ person ≡ ((PossibleWorld.assign world) the-butler) ∨ person ≡ ((PossibleWorld.assign world) Charles))
Agathas-killer-is-Agatha-or-the-butler-or-Charles world person person-could-have-killed-Agatha = person-is-Agatha-or-the-butler-or-Charles
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  lives-at-Dreadbury-Mansion : Fin population → Bool
  lives-at-Dreadbury-Mansion = PossibleWorld.lives-at-Dreadbury-Mansion world

  could-have-killed-Agatha : Fin population → Bool
  could-have-killed-Agatha = PossibleWorld.could-have-killed-Agatha world

  somebody-who-lives-in-Dreadbury-Mansion-killed-Aunt-Agatha : (person : Fin population) → lives-at-Dreadbury-Mansion person ≡ false → could-have-killed-Agatha person ≡ false 
  somebody-who-lives-in-Dreadbury-Mansion-killed-Aunt-Agatha = PossibleWorld.somebody-who-lives-in-Dreadbury-Mansion-killed-Aunt-Agatha world

  Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein : (person : Fin population) → lives-at-Dreadbury-Mansion person ≡ true → person ≡ (assign Agatha) ∨ person ≡ (assign the-butler) ∨ person ≡ (assign Charles)
  Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein = PossibleWorld.Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein world

  person-lives-at-Dreadbury-Mansion : lives-at-Dreadbury-Mansion person ≡ true
  person-lives-at-Dreadbury-Mansion = Bool-conv₂ (lives-at-Dreadbury-Mansion person) (could-have-killed-Agatha person) false false (somebody-who-lives-in-Dreadbury-Mansion-killed-Aunt-Agatha person) person-could-have-killed-Agatha

  person-is-Agatha-or-the-butler-or-Charles : person ≡ (assign Agatha) ∨ person ≡ (assign the-butler) ∨ person ≡ (assign Charles)
  person-is-Agatha-or-the-butler-or-Charles = Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein person person-lives-at-Dreadbury-Mansion


process-of-elimination : ∀ {i j} {A : Set i} {B : Set j} → A ∨ B → ¬ A → B
process-of-elimination {i} {j} {A} {B} (inl a) ¬A = ω (¬A a)
process-of-elimination {i} {j} {A} {B} (inr b) ¬A = b

∨-sym : ∀ {i j} {A : Set i} {B : Set j} → A ∨ B → B ∨ A
∨-sym {i} {j} {A} {B} (inl a) = inr a
∨-sym {i} {j} {A} {B} (inr b) = inl b

∨-assoc : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → A ∨ (B ∨ C) → (A ∨ B) ∨ C
∨-assoc {i} {j} {k} {A} {B} {C} (inl a) = inl (inl a)
∨-assoc {i} {j} {k} {A} {B} {C} (inr (inl b)) = inl (inr b)
∨-assoc {i} {j} {k} {A} {B} {C} (inr (inr c)) = inr c

∨-assoc₂ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (A ∨ B) ∨ C → A ∨ (B ∨ C)
∨-assoc₂ {i} {j} {k} {A} {B} {C} (inl (inl a)) = inl a
∨-assoc₂ {i} {j} {k} {A} {B} {C} (inl (inr b)) = inr (inl b)
∨-assoc₂ {i} {j} {k} {A} {B} {C} (inr c) = inr (inr c)



Agathas-killer-is-the-butler-or-Charles-or-Agatha : (world : PossibleWorld) → (person : Fin (PossibleWorld.population world)) → (PossibleWorld.could-have-killed-Agatha world) person ≡ true → (person ≡ ((PossibleWorld.assign world) the-butler) ∨ person ≡ ((PossibleWorld.assign world) Charles) ∨ person ≡ ((PossibleWorld.assign world) Agatha))
Agathas-killer-is-the-butler-or-Charles-or-Agatha world person person-could-have-killed-Agatha = ∨-assoc₂ (∨-sym (Agathas-killer-is-Agatha-or-the-butler-or-Charles world person person-could-have-killed-Agatha))

Agathas-killer-is-not-the-butler : (world : PossibleWorld) → (person : Fin (PossibleWorld.population world)) → (PossibleWorld.could-have-killed-Agatha world) person ≡ true → person ≠ ((PossibleWorld.assign world) the-butler)
Agathas-killer-is-not-the-butler world person person-could-have-killed-Agatha person-is-the-butler = ω ☢
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  could-have-killed-Agatha : Fin population → Bool
  could-have-killed-Agatha = PossibleWorld.could-have-killed-Agatha world
 
  ☢ : ⊥
  ☢ = 𝕥≠𝕗 (≡-⇶ (≡-↑↓ person-could-have-killed-Agatha) (≡-⇶ ([x≡y]→[fx≡fy] could-have-killed-Agatha person (assign the-butler) person-is-the-butler) (the-butler-couldnt-have-killed-Agatha' world)))

Agathas-killer-is-not-Charles : (world : PossibleWorld) → (person : Fin (PossibleWorld.population world)) → (PossibleWorld.could-have-killed-Agatha world) person ≡ true → person ≠ ((PossibleWorld.assign world) Charles)
Agathas-killer-is-not-Charles world person person-could-have-killed-Agatha person-is-Charles = ω ☢
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  could-have-killed-Agatha : Fin population → Bool
  could-have-killed-Agatha = PossibleWorld.could-have-killed-Agatha world

  ☢ : ⊥
  ☢ = 𝕥≠𝕗 (≡-⇶ (≡-↑↓ person-could-have-killed-Agatha) (≡-⇶ ([x≡y]→[fx≡fy] could-have-killed-Agatha person (assign Charles) person-is-Charles) (Charles-couldnt-have-killed-Agatha' world)))


Agathas-killer-is-Charles-or-Agatha : (world : PossibleWorld) → (person : Fin (PossibleWorld.population world)) → (PossibleWorld.could-have-killed-Agatha world) person ≡ true → person ≡ ((PossibleWorld.assign world) Charles) ∨ person ≡ ((PossibleWorld.assign world) Agatha)
Agathas-killer-is-Charles-or-Agatha world person person-could-have-killed-Agatha = process-of-elimination (Agathas-killer-is-the-butler-or-Charles-or-Agatha world person person-could-have-killed-Agatha) (Agathas-killer-is-not-the-butler world person person-could-have-killed-Agatha)

Agathas-killer-is-Agatha : (world : PossibleWorld) → (person : Fin (PossibleWorld.population world)) → (PossibleWorld.could-have-killed-Agatha world) person ≡ true → person ≡ ((PossibleWorld.assign world) Agatha)
Agathas-killer-is-Agatha world person person-could-have-killed-Agatha = process-of-elimination (Agathas-killer-is-Charles-or-Agatha world person person-could-have-killed-Agatha) (Agathas-killer-is-not-Charles world person person-could-have-killed-Agatha)

{-

 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  lives-at-Dreadbury-Mansion : Fin population → Bool
  lives-at-Dreadbury-Mansion = PossibleWorld.lives-at-Dreadbury-Mansion world

  _hates_ : FinRel {population} {population}
  _hates_ = PossibleWorld._hates_ world
  
  no-one-hates-everyone : (person1 : Fin population) → lives-at-Dreadbury-Mansion person1 ≡ true → ∃ person2 ∈ Fin population , ((lives-at-Dreadbury-Mansion person2 ≡ true) ∧ (person1 hates person2 ≡ false))
  no-one-hates-everyone = PossibleWorld.no-one-hates-everyone world  

  Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein : (person : Fin population) → lives-at-Dreadbury-Mansion person ≡ true → person ≡ (assign Agatha) ∨ person ≡ (assign the-butler) ∨ person ≡ (assign Charles)
  Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein = PossibleWorld.Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein world

  
 
  proof
-}

{-
Agatha-hates-Agatha : (n : Nat) → (assign : PersonLabel → Fin n) → (lives-at-Dreadbury-Mansion : Fin n → Bool) → (richer-than : FinRel {n} {n}) → (hates : FinRel {n} {n}) → (could-have-killed : FinRel {n} {n}) → ValidRelations₃ n assign lives-at-Dreadbury-Mansion richer-than could-have-killed → hates (assign Agatha) (assign Agatha)
Agatha-hates-Agatha n assign lives-at-Dreadbury-Mansion richer-than hates could-have-killed
 (
-}
{-
Lemma: The butler doesn't hate the butler.
-}

{-
Problem : (n : Nat) → (assign : PersonLabel → Fin n) → (lives-at-Dreadbury-Mansion : Fin n → Bool) → (richer-than : FinRel {n} {n}) → (hates : FinRel {n} {n}) → (could-have-killed : FinRel {n} {n}) → ValidRelations₃ n assign lives-at-Dreadbury-Mansion richer-than could-have-killed → ∃ person ∈ Fin n , (could-have-killed person (assign Agatha)) → person ≡ Agatha
-}

{-
∃ n ∈ Nat , (
 ∃ f ∈ (PersonLabel → Fin n) , 
  ∃ hates ∈ (FinRel n) ,
   ∃ richerThan ∈ (FinRel n) ,
    f Agatha ≠ f the-butler
     
-}

data Person :  Set where
 Charles : Person
 Agatha : Person
 Butler : Person

data House : Set where
 Dreadbury-Mansion : House

data _lives-in_ : Person → House → Set where
 {-
  Agatha, the butler, and Charles live in Dreadbury Mansion.
 -}
 charles : Charles lives-in Dreadbury-Mansion
 agatha : Agatha lives-in Dreadbury-Mansion
 butler : Butler lives-in Dreadbury-Mansion


data _richer-than_ : Person → Person → Set where

data _not-richer-than_ : Person → Person → Set where

data _hates_ : Person → Person → Set where
 agatha-hates-everybody-but-the-butler : (x : Person) → (x ≠ Butler) → Agatha hates x
 butler-hates-everyone-agatha-hates : (x : Person) → Agatha hates x → Butler hates x

butler-hates-everybody-but-the-butler : (x : Person) → (x ≠ Butler) → Butler hates x
butler-hates-everybody-but-the-butler somebody somebody-is-not-the-butler = butler-hates-everyone-agatha-hates somebody (agatha-hates-everybody-but-the-butler somebody somebody-is-not-the-butler)

data _doesnt-hate_ : Person → Person → Set where
 {-
  Charles hates no one that Aunt Agatha hates.
 -}
 agatha-doesnt-hate-the-butler : Agatha doesnt-hate Butler
 charles-doesnt-hate-anybody-agatha-hates : (x : Person) → Agatha hates x → Charles doesnt-hate x
 

{-
for all x :  Person , exists y : Person , x doesnt-hate y
x hates y → ¬ ( x doesnt-hate y)
x doesnt-hate y → ¬ (x hates y)
-}

data was-killed : Person → Set where
 agatha : was-killed Agatha

data _could-have-killed_ : Person → Person → Set where
 cons : (x y : Person) → was-killed y →  x hates y → x not-richer-than y → x could-have-killed y


data _must-have-killed_ :  Person → Person → Set where
 cons : (x y : Person) → x could-have-killed y → ((z : Person) → z could-have-killed y → x ≡ z) → x must-have-killed y

data could-have-killed-Agatha : Person → Set where
 cons : (x : Person) → x could-have-killed Agatha → x lives-in Dreadbury-Mansion → could-have-killed-Agatha x

data must-have-killed-Agatha : Person → Set where
 cons : (x : Person) → could-have-killed-Agatha x → ((z : Person) → could-have-killed-Agatha z → x ≡ z) → must-have-killed-Agatha x


