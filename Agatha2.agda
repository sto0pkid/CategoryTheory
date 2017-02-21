module Agatha2 where

open import BaseLogic
open import Data.False
open import Data.Bool
open import Data.Bool.Operations
open import Data.Bool.Proofs
open import Data.Nat
open import Data.Fin
open import Data.PropositionalEquality
open import Data.Disjunction
open import Data.Product

FinRel : {m n : Nat} → Set
FinRel {m} {n} = Fin m → Fin n → Bool

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

data PersonLabel : Set where
 Charles : PersonLabel
 Agatha : PersonLabel
 the-butler : PersonLabel

record PossibleWorld : Set where 
 field
  population : Nat 
  assign : PersonLabel → Fin population
  lives-at-Dreadbury-Mansion : Fin population → Bool 
  _is-richer-than_ : FinRel {population} {population}
  _hates_ : FinRel {population} {population}
  _could-have-killed_ : FinRel {population} {population}
  could-have-killed-Agatha : Fin population → Bool

-- 1)   
  somebody-who-lives-in-Dreadbury-Mansion-killed-Aunt-Agatha : (person : Fin population) → lives-at-Dreadbury-Mansion person ≡ false → could-have-killed-Agatha person ≡ false 

-- 2)
  Agathas-killer-must-have-been-able-to-kill-her : (person : Fin population) → person could-have-killed (assign Agatha) ≡ false → could-have-killed-Agatha person ≡ false

-- 3)
  Agatha-lives-in-Dreadbury-Mansion : lives-at-Dreadbury-Mansion (assign Agatha) ≡ true

-- 4)
  Charles-lives-in-Dreadbury-Mansion : lives-at-Dreadbury-Mansion (assign Charles) ≡ true

-- 5)
  the-butler-lives-in-Dreadbury-Mansion : lives-at-Dreadbury-Mansion (assign the-butler) ≡ true

-- 6)
  Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein : (person : Fin population) → lives-at-Dreadbury-Mansion person ≡ true → person ≡ (assign Agatha) ∨ person ≡ (assign the-butler) ∨ person ≡ (assign Charles)

-- 7)
  a-killer-always-hates-his-victim : (person1 person2 : Fin population) → person1 hates person2 ≡ false → person1 could-have-killed person2 ≡ false

-- 8)
  a-killer-is-never-richer-than-his-victim : (person1 person2 : Fin population) → person1 is-richer-than person2 ≡ true → person1 could-have-killed person2 ≡ false

-- 9)
  a-killer-always-hates-his-victim-and-is-never-richer-than-his-victim : (person1 person2 : Fin population) → person1 hates person2 ≡ true → person1 is-richer-than person2 ≡ false → person1 could-have-killed person2 ≡ true

-- 10)
  Charles-hates-no-one-that-Aunt-Agatha-hates : (person : Fin population) → (assign Agatha) hates person ≡ true → (assign Charles) hates person ≡ false

-- 11)
  Agatha-hates-everyone-except-the-butler : (person : Fin population) → person ≠ assign the-butler → (assign Agatha) hates person ≡ true

-- 12)
  the-butler-hates-everyone-not-richer-than-Aunt-Agatha : (person : Fin population) → person is-richer-than (assign Agatha) ≡ false → (assign the-butler) hates person ≡ true

-- 13)
  the-butler-hates-everyone-Aunt-Agatha-hates : (person : Fin population) → (assign Agatha) hates person ≡ true → (assign the-butler) hates person ≡ true

-- 14) 
  no-one-hates-everyone : (person1 : Fin population) → lives-at-Dreadbury-Mansion person1 ≡ true → ∃ person2 ∈ Fin population , ((lives-at-Dreadbury-Mansion person2 ≡ true) ∧ (person1 hates person2 ≡ false))

-- 15)
  Agatha-is-not-the-butler : assign Agatha ≠ assign the-butler

-- 16)
  no-one-is-richer-than-themselves : (person : Fin population) → person is-richer-than person ≡ false

-- 17)
  Agathas-killer-lives-at-Dreadbury-Mansion : (person : Fin population) → person could-have-killed (assign Agatha) ≡ true → lives-at-Dreadbury-Mansion person ≡ true → could-have-killed-Agatha person ≡ true


Agatha-must-have-killed-herself : (world :  PossibleWorld) → (PossibleWorld.could-have-killed-Agatha world) ((PossibleWorld.assign world) Agatha) ≡ true ∧ ((person : Fin (PossibleWorld.population world)) → (PossibleWorld.could-have-killed-Agatha world) person ≡ true → person ≡ ((PossibleWorld.assign world) Agatha))
Agatha-must-have-killed-herself world = (Agatha-could-have-killed-Agatha , only-Agatha-could-have-killed-Agatha)
 where
  population : Nat
  population = PossibleWorld.population world

  assign : PersonLabel → Fin population
  assign = PossibleWorld.assign world

  _hates_ : FinRel {population} {population}
  _hates_ = PossibleWorld._hates_ world

  _is-richer-than_ : FinRel {population} {population}
  _is-richer-than_ = PossibleWorld._is-richer-than_ world

  _could-have-killed_ : FinRel {population} {population}
  _could-have-killed_ = PossibleWorld._could-have-killed_ world

  could-have-killed-Agatha : Fin population → Bool
  could-have-killed-Agatha = PossibleWorld.could-have-killed-Agatha world

  lives-at-Dreadbury-Mansion : Fin population → Bool
  lives-at-Dreadbury-Mansion = PossibleWorld.lives-at-Dreadbury-Mansion world

{-

-}
  Agatha' : Fin population
  Agatha' = assign Agatha

  the-butler' : Fin population
  the-butler' = assign the-butler

  Charles' : Fin population
  Charles' = assign Charles

{-

-}

-- 1)
  somebody-who-lives-in-Dreadbury-Mansion-killed-Aunt-Agatha : (person : Fin population) → lives-at-Dreadbury-Mansion person ≡ false → could-have-killed-Agatha person ≡ false 
  somebody-who-lives-in-Dreadbury-Mansion-killed-Aunt-Agatha = PossibleWorld.somebody-who-lives-in-Dreadbury-Mansion-killed-Aunt-Agatha world

-- 2)
  Agathas-killer-must-have-been-able-to-kill-her : (person : Fin population) → person could-have-killed (assign Agatha) ≡ false → could-have-killed-Agatha person ≡ false
  Agathas-killer-must-have-been-able-to-kill-her = PossibleWorld.Agathas-killer-must-have-been-able-to-kill-her world

-- 3)
  Agatha-lives-in-Dreadbury-Mansion : lives-at-Dreadbury-Mansion Agatha' ≡ true
  Agatha-lives-in-Dreadbury-Mansion = PossibleWorld.Agatha-lives-in-Dreadbury-Mansion world

-- 4)
  Charles-lives-in-Dreadbury-Mansion : lives-at-Dreadbury-Mansion Charles' ≡ true
  Charles-lives-in-Dreadbury-Mansion = PossibleWorld.Charles-lives-in-Dreadbury-Mansion world

-- 5)
  the-butler-lives-in-Dreadbury-Mansion : lives-at-Dreadbury-Mansion the-butler' ≡ true
  the-butler-lives-in-Dreadbury-Mansion = PossibleWorld.the-butler-lives-in-Dreadbury-Mansion world

-- 6)
  Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein : (person : Fin population) → lives-at-Dreadbury-Mansion person ≡ true → person ≡ (assign Agatha) ∨ person ≡ (assign the-butler) ∨ person ≡ (assign Charles)
  Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein = PossibleWorld.Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein world

-- 7)
  a-killer-always-hates-his-victim : (person1 person2 : Fin population) → person1 hates person2 ≡ false → person1 could-have-killed person2 ≡ false
  a-killer-always-hates-his-victim = PossibleWorld.a-killer-always-hates-his-victim world

-- 8)
  a-killer-is-never-richer-than-his-victim : (person1 person2 : Fin population) → person1 is-richer-than person2 ≡ true → person1 could-have-killed person2 ≡ false
  a-killer-is-never-richer-than-his-victim = PossibleWorld.a-killer-is-never-richer-than-his-victim world

-- 9)
  a-killer-always-hates-his-victim-and-is-never-richer-than-his-victim : (person1 person2 : Fin population) → person1 hates person2 ≡ true → person1 is-richer-than person2 ≡ false → person1 could-have-killed person2 ≡ true
  a-killer-always-hates-his-victim-and-is-never-richer-than-his-victim = PossibleWorld.a-killer-always-hates-his-victim-and-is-never-richer-than-his-victim world

-- 10)
  Charles-hates-no-one-that-Aunt-Agatha-hates : (person : Fin population) → (assign Agatha) hates person ≡ true → (assign Charles) hates person ≡ false
  Charles-hates-no-one-that-Aunt-Agatha-hates = PossibleWorld.Charles-hates-no-one-that-Aunt-Agatha-hates world

-- 11)
  Agatha-hates-everyone-except-the-butler : (person : Fin population) → person ≠ the-butler' → Agatha' hates person ≡ true
  Agatha-hates-everyone-except-the-butler = PossibleWorld.Agatha-hates-everyone-except-the-butler world

-- 12)
  the-butler-hates-everyone-not-richer-than-Aunt-Agatha : (person : Fin population) → person is-richer-than (assign Agatha) ≡ false → (assign the-butler) hates person ≡ true
  the-butler-hates-everyone-not-richer-than-Aunt-Agatha = PossibleWorld.the-butler-hates-everyone-not-richer-than-Aunt-Agatha world

-- 13)
  the-butler-hates-everyone-Aunt-Agatha-hates : (person : Fin population) → (assign Agatha) hates person ≡ true → (assign the-butler) hates person ≡ true
  the-butler-hates-everyone-Aunt-Agatha-hates = PossibleWorld.the-butler-hates-everyone-Aunt-Agatha-hates world

-- 14)
  no-one-hates-everyone : (person1 : Fin population) → lives-at-Dreadbury-Mansion person1 ≡ true → ∃ person2 ∈ Fin population , ((lives-at-Dreadbury-Mansion person2 ≡ true) ∧ (person1 hates person2 ≡ false))
  no-one-hates-everyone = PossibleWorld.no-one-hates-everyone world

-- 15)
  Agatha-is-not-the-butler : Agatha' ≠ the-butler'
  Agatha-is-not-the-butler = PossibleWorld.Agatha-is-not-the-butler world

-- 16)
  no-one-is-richer-than-themselves : (person : Fin population) → person is-richer-than person ≡ false
  no-one-is-richer-than-themselves = PossibleWorld.no-one-is-richer-than-themselves world

-- 17)
  Agathas-killer-lives-at-Dreadbury-Mansion : (person : Fin population) → person could-have-killed (assign Agatha) ≡ true → lives-at-Dreadbury-Mansion person ≡ true → could-have-killed-Agatha person ≡ true
  Agathas-killer-lives-at-Dreadbury-Mansion = PossibleWorld.Agathas-killer-lives-at-Dreadbury-Mansion world



  
{-
//
// Proofs
//
-}

  Agatha-hates-Agatha : Agatha' hates Agatha' ≡ true
  Agatha-hates-Agatha = Agatha-hates-everyone-except-the-butler Agatha' Agatha-is-not-the-butler

  the-butler-hates-Agatha : the-butler' hates Agatha' ≡ true
  the-butler-hates-Agatha = the-butler-hates-everyone-Aunt-Agatha-hates Agatha' Agatha-hates-Agatha

  Charles-doesnt-hate-Agatha : Charles' hates Agatha' ≡ false
  Charles-doesnt-hate-Agatha = Charles-hates-no-one-that-Aunt-Agatha-hates Agatha' Agatha-hates-Agatha

  Charles-is-not-the-butler : Charles' ≠ the-butler'
  Charles-is-not-the-butler Charles-is-the-butler = ω ☢
   where
    hates-Agatha : Fin population → Bool
    hates-Agatha person = person hates Agatha'

    ☢ : ⊥ 
    ☢ = 𝕥≠𝕗 (≡-⇶ (≡-↑↓ the-butler-hates-Agatha) (≡-⇶ ([x≡y]→[fx≡fy] hates-Agatha the-butler' Charles' (≡-↑↓ Charles-is-the-butler)) Charles-doesnt-hate-Agatha))

  Agatha-hates-Charles : Agatha' hates Charles' ≡ true
  Agatha-hates-Charles = Agatha-hates-everyone-except-the-butler Charles' Charles-is-not-the-butler

  the-butler-hates-Charles : the-butler' hates Charles' ≡ true
  the-butler-hates-Charles = the-butler-hates-everyone-Aunt-Agatha-hates Charles' Agatha-hates-Charles

  Agatha-is-not-richer-than-Agatha : Agatha' is-richer-than Agatha' ≡ false
  Agatha-is-not-richer-than-Agatha = no-one-is-richer-than-themselves Agatha'

  Agatha-could-have-killed-Agatha₁ : Agatha' could-have-killed Agatha' ≡ true
  Agatha-could-have-killed-Agatha₁ = a-killer-always-hates-his-victim-and-is-never-richer-than-his-victim Agatha' Agatha' Agatha-hates-Agatha Agatha-is-not-richer-than-Agatha 

  Agatha-could-have-killed-Agatha : could-have-killed-Agatha Agatha' ≡ true
  Agatha-could-have-killed-Agatha = Agathas-killer-lives-at-Dreadbury-Mansion Agatha' Agatha-could-have-killed-Agatha₁ Agatha-lives-in-Dreadbury-Mansion

  the-butler-doesnt-hate-everyone : ∃ person ∈ Fin population , ((lives-at-Dreadbury-Mansion person ≡ true) ∧ (the-butler' hates person ≡ false))
  the-butler-doesnt-hate-everyone = no-one-hates-everyone the-butler' the-butler-lives-in-Dreadbury-Mansion

  the-person-the-butler-doesnt-hate : Fin population
  the-person-the-butler-doesnt-hate = π₁ the-butler-doesnt-hate-everyone

  the-person-the-butler-doesnt-hate-lives-in-Dreadbury-Mansion : lives-at-Dreadbury-Mansion the-person-the-butler-doesnt-hate ≡ true
  the-person-the-butler-doesnt-hate-lives-in-Dreadbury-Mansion = first (π₂ the-butler-doesnt-hate-everyone)
  
  the-butler-doesnt-hate-the-person-the-butler-doesnt-hate : the-butler' hates the-person-the-butler-doesnt-hate ≡ false
  the-butler-doesnt-hate-the-person-the-butler-doesnt-hate = second (π₂ the-butler-doesnt-hate-everyone)

  the-person-the-butler-doesnt-hate-is-Agatha-or-the-butler-or-Charles : the-person-the-butler-doesnt-hate ≡ Agatha' ∨ the-person-the-butler-doesnt-hate ≡ the-butler' ∨ the-person-the-butler-doesnt-hate ≡ Charles'
  the-person-the-butler-doesnt-hate-is-Agatha-or-the-butler-or-Charles = Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein the-person-the-butler-doesnt-hate the-person-the-butler-doesnt-hate-lives-in-Dreadbury-Mansion


  the-butler-doesnt-hate-the-butler₁ : (the-butler' hates the-butler') ≠ true
  the-butler-doesnt-hate-the-butler₁ the-butler-hates-the-butler = ω ☢
   where
    the-butler-hates-everyone : (person : Fin population) → lives-at-Dreadbury-Mansion person ≡ true → the-butler' hates person ≡ true
    the-butler-hates-everyone person person-lives-at-Dreadbury-Mansion = proof
     where
      person-is-Agatha-or-the-butler-or-Charles : person ≡ Agatha' ∨ person ≡ the-butler' ∨ person ≡ Charles'
      person-is-Agatha-or-the-butler-or-Charles = Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein person person-lives-at-Dreadbury-Mansion

      the-butler-hates : Fin population → Bool
      the-butler-hates person = the-butler' hates person

      person-is-Agatha-or-the-butler-or-Charles-implies-the-butler-hates-person : (person ≡ Agatha' ∨ person ≡ the-butler' ∨ person ≡ Charles') → the-butler' hates person ≡ true
      person-is-Agatha-or-the-butler-or-Charles-implies-the-butler-hates-person (inl person-is-Agatha) = ≡-⇶ ([x≡y]→[fx≡fy] the-butler-hates person Agatha' person-is-Agatha) the-butler-hates-Agatha
      person-is-Agatha-or-the-butler-or-Charles-implies-the-butler-hates-person (inr (inl person-is-the-butler)) = ≡-⇶ ([x≡y]→[fx≡fy] the-butler-hates person the-butler' person-is-the-butler) the-butler-hates-the-butler
      person-is-Agatha-or-the-butler-or-Charles-implies-the-butler-hates-person (inr (inr person-is-Charles)) = ≡-⇶ ([x≡y]→[fx≡fy] the-butler-hates person Charles' person-is-Charles) the-butler-hates-Charles

      proof : the-butler' hates person ≡ true
      proof = person-is-Agatha-or-the-butler-or-Charles-implies-the-butler-hates-person person-is-Agatha-or-the-butler-or-Charles
  
    the-butler-hates-the-person-the-butler-doesnt-hate : the-butler' hates the-person-the-butler-doesnt-hate ≡ true
    the-butler-hates-the-person-the-butler-doesnt-hate = the-butler-hates-everyone the-person-the-butler-doesnt-hate the-person-the-butler-doesnt-hate-lives-in-Dreadbury-Mansion  
  
    ☢ : ⊥
    ☢ = 𝕥≠𝕗 (≡-⇶ (≡-↑↓ the-butler-hates-the-person-the-butler-doesnt-hate) the-butler-doesnt-hate-the-person-the-butler-doesnt-hate)


  the-butler-doesnt-hate-the-butler : the-butler' hates the-butler' ≡ false
  the-butler-doesnt-hate-the-butler = bool-DN (the-butler' hates the-butler') true the-butler-doesnt-hate-the-butler₁

  the-butler-is-richer-than-Agatha : the-butler' is-richer-than Agatha' ≡ true
  the-butler-is-richer-than-Agatha = Bool-conv₂ (the-butler' is-richer-than Agatha') (the-butler' hates the-butler') false true (the-butler-hates-everyone-not-richer-than-Aunt-Agatha the-butler') the-butler-doesnt-hate-the-butler

  the-butler-couldnt-have-killed-Agatha : the-butler' could-have-killed Agatha' ≡ false
  the-butler-couldnt-have-killed-Agatha = a-killer-is-never-richer-than-his-victim the-butler' Agatha' the-butler-is-richer-than-Agatha

  the-butler-couldnt-have-killed-Agatha' : could-have-killed-Agatha the-butler' ≡ false
  the-butler-couldnt-have-killed-Agatha' = Agathas-killer-must-have-been-able-to-kill-her the-butler' the-butler-couldnt-have-killed-Agatha

  Agathas-killer-is-not-the-butler : (person : Fin population) → could-have-killed-Agatha person ≡ true → person ≠ the-butler'
  Agathas-killer-is-not-the-butler person person-could-have-killed-Agatha person-is-the-butler = ω ☢
   where
    ☢ : ⊥
    ☢ = 𝕥≠𝕗 (≡-⇶ (≡-↑↓ person-could-have-killed-Agatha) (≡-⇶ ([x≡y]→[fx≡fy] could-have-killed-Agatha person the-butler' person-is-the-butler) the-butler-couldnt-have-killed-Agatha'))
 
  Charles-couldnt-have-killed-Agatha : Charles' could-have-killed Agatha' ≡ false
  Charles-couldnt-have-killed-Agatha = a-killer-always-hates-his-victim Charles' Agatha' Charles-doesnt-hate-Agatha

  Charles-couldnt-have-killed-Agatha' : could-have-killed-Agatha Charles' ≡ false
  Charles-couldnt-have-killed-Agatha' = Agathas-killer-must-have-been-able-to-kill-her Charles' Charles-couldnt-have-killed-Agatha

  Agathas-killer-is-not-Charles : (person : Fin population) → could-have-killed-Agatha person ≡ true → person ≠ Charles'
  Agathas-killer-is-not-Charles person person-could-have-killed-Agatha person-is-Charles = ω ☢
   where
    ☢ : ⊥
    ☢ = 𝕥≠𝕗 (≡-⇶ (≡-↑↓ person-could-have-killed-Agatha) (≡-⇶ ([x≡y]→[fx≡fy] could-have-killed-Agatha person Charles' person-is-Charles) Charles-couldnt-have-killed-Agatha'))

  only-Agatha-or-the-butler-or-Charles-could-have-killed-Agatha : (person : Fin population) → could-have-killed-Agatha person ≡ true → person ≡ Agatha' ∨ person ≡ the-butler' ∨ person ≡ Charles'
  only-Agatha-or-the-butler-or-Charles-could-have-killed-Agatha person person-could-have-killed-Agatha = proof
   where
    person-lives-in-Dreadbury-Mansion : lives-at-Dreadbury-Mansion person ≡ true
    person-lives-in-Dreadbury-Mansion = Bool-conv₂ (lives-at-Dreadbury-Mansion person) (could-have-killed-Agatha person) false false (somebody-who-lives-in-Dreadbury-Mansion-killed-Aunt-Agatha person) person-could-have-killed-Agatha

    proof : person ≡ Agatha' ∨ person ≡ the-butler' ∨ person ≡ Charles'
    proof = Agatha-the-butler-and-Charles-live-in-Dreadbury-Mansion-and-are-the-only-people-that-live-therein person person-lives-in-Dreadbury-Mansion

  only-the-butler-or-Charles-or-Agatha-could-have-killed-Agatha : (person : Fin population) → could-have-killed-Agatha person ≡ true → person ≡ the-butler' ∨ person ≡ Charles' ∨ person ≡ Agatha'
  only-the-butler-or-Charles-or-Agatha-could-have-killed-Agatha person person-could-have-killed-Agatha = ∨-assoc₂ (∨-sym (only-Agatha-or-the-butler-or-Charles-could-have-killed-Agatha person person-could-have-killed-Agatha))

  only-Charles-or-Agatha-could-have-killed-Agatha : (person : Fin population) → could-have-killed-Agatha person ≡ true → person ≡ Charles' ∨ person ≡ Agatha'
  only-Charles-or-Agatha-could-have-killed-Agatha person person-could-have-killed-Agatha = process-of-elimination (only-the-butler-or-Charles-or-Agatha-could-have-killed-Agatha person person-could-have-killed-Agatha) (Agathas-killer-is-not-the-butler person person-could-have-killed-Agatha)

  only-Agatha-could-have-killed-Agatha : (person : Fin population) → could-have-killed-Agatha person ≡ true → person ≡ Agatha'
  only-Agatha-could-have-killed-Agatha person person-could-have-killed-Agatha = process-of-elimination (only-Charles-or-Agatha-could-have-killed-Agatha person person-could-have-killed-Agatha) (Agathas-killer-is-not-Charles person person-could-have-killed-Agatha)


{-
Reasoning methods:

Transitivity of equality
symmetry of equality
Process of elimination
Liebniz inequality
Path transport
Equal functions applied to equal arguments give equal results
Type1 ≡ Type2 → Type1 → Type2
⊤≠⊥
Injectivity of inductive type constructors
"Threading" an inequality
𝕥≠𝕗 
-}
