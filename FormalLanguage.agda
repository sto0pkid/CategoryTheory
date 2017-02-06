module FormalLanguage where

open import Agda.Primitive
open import BaseLogic
open import Relations
open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.Vector
open import SetTheory

{- 
 A language is a set of strings.
 
 But what are "strings"?

 Strings are sequences of objects drawn from some "alphabet".
   
 But what is an "alphabet"?

 An alphabet is a set of characters.

 But what are "characters"?

 I don't really know what determines whether something is a "character" or not, but
 it seems one criteria (which is necessary for parsers) is that you should be able to
 determine whether or not two characters are equal.

 We don't really need to bring up anything regarding propositional equality, we can use
 an arbitrary equivance relation on the set of characters as long as we can decide whether
 or not two characters are in the same equivalence class.

 Under these definitions, an alphabet is then a set of objects, let's call it "glyph", equipped with
 an equivalence relation `glyph → glyph → Bool`. A set equipped with an equivalence relation is called
 a Setoid, so:
-}

record Setoid {i} : Set (lsuc i) where
 field
  elems : Set i
  equiv : ∃ r ∈ (elems → elems → Bool) , (isEquivalenceRelation r)

Alphabet : ∀ {i} → Set (lsuc i)
Alphabet = Setoid

{-
 Now a "character" is an equivalence class in this Setoid. How do we talk about equivalence classes?
 We can certainly talk about the equivalence class *of* a particular element in the Setoid.
-}

EquivClass : ∀ {i} (S : Setoid {i}) (x : Setoid.elems S) → Set i
EquivClass {i} S x = ∃ x' ∈ S-elems , ((x' == x) ≡ true)
 where
  S-elems : Set i
  S-elems = Setoid.elems S
 
  _==_ : S-elems → S-elems → Bool
  _==_ = π₁ (Setoid.equiv S)
{- 
 Can we define equivalence classes without doing it relative to
 a particular element?
 Should we?
-}

{-
 Back to "strings":

 A string is a sequence of characters drawn from an alphabet.

 But what is a "sequence"?

 We could define a "sequence" as a List. Doing so would, however, preclude the existence 
 of infinitely long strings in the language. If we wanted to include infinitely long strings, 
 we would instead define a "sequence" as a potentially finite, potentially infinite Stream.

 Let's stick with finite strings for now.
-}

String : ∀ {i} → (A : Alphabet {i}) → Set i
String A = List (Setoid.elems A)


{-
 Back to "languages" 
 A language is a set of strings over some alphabet.
 More precisely: it is a subset of the set of strings over some alphabet.
-}

Language : ∀ {i j} (A : Alphabet {i}) → Set (lsuc j ⊔ i)
Language {i} {j} A = Subset {i} {j} (String A)

  
{-
Now we should have a function that takes the decision function for propositional equality and returns
a proof that it define a Boolean equivalence relation.
-}




{-
ASCII : Alphabet
ASCII = record {elems = Vector Bit 8 ; equiv = BitVectorEq {8}}

-}

{-
Obviously this is a little much for a lot of practical purposes, so we should have
a simpler definition of an Alphabet as just a Set, rather than a Setoid where we have to
provide an equivalence relation and proof that it actually is an equivalence relation.
-}



{-
data Regex₂ (A : Alphabet) : Set where
 ⊘    : Regex₂ A
 ε    : Regex₂ A
 item : A → Regex₂ A
 _*   : Regex₂ A → Regex₂ A
 _||_ : Regex₂ A → Regex₂ A → Regex₂ A
 _&&_ : Regex₂ A → Regex₂ A → Regex₂ A
-}


-- Need our own Char & String types
-- Use the general definitions you were building up in Lang
--Set-theoretic descriptions:
--Let's make this real.

-- Empty language
-- ⊘        ≡ {}
lang-⊘ : ∀ {i} → (A : Alphabet {i}) → Subset {i} {lzero} (String A)
lang-⊘ A = EmptySet (String A)

{-
EmptySet : ∀ {α} (A : Set α) → Subset {α} {lzero} A
EmptySet {α} A = λ x → ⊥

-}

 -- Null language
 -- ε        ≡ {""}

lang-ε : ∀ {i} → (A : Alphabet {i}) → Subset {i} {i} (String A)
lang-ε A = λ s → s ≡ [] 


-- If x ∈ Char, then:
-- (char x) ≡ {x}
lang-char : ∀ {i} {A : Alphabet {i}} → (c : Setoid.elems A) → Subset {i} {i} (String A)
lang-char c = λ s → s ≡ (c ∷ []) 


-- L₁ || L₂ ≡ L₁ ∪ L₂
lang-union : ∀ {i j k} {A : Alphabet {i}} → Subset {i} {j} (String A) → Subset {i} {k} (String A) → Subset {i} {j ⊔ k} (String A)
lang-union L₁ L₂ = λ s → L₁ s ∨ L₂ s
-- or L₁ || L₂ = subsetUnion L₁ L₂


-- L₁ && L₂ ≡ {w₁w₂ | w₁ ∈ L₁ ∧ w₂ ∈ L₂}
lang-concat : ∀ {i j k} {A : Alphabet {i}} → Subset {i} {j} (String A) → Subset {i} {k} (String A) → Subset {i} {i ⊔ (j ⊔ k)} (String A)
lang-concat {i} {j} {k} {A} L₁ L₂ = λ s → ∃ w₁ ∈ (String A) , (∃ w₂ ∈ (String A) , ( [ w₁ ∈ L₁ ] ∧ [ w₂ ∈ L₂ ] ∧ (s ≡ Data.List._++_ w₁ w₂)))
 

 --When i ≠ 0,
 --L^i       ≡ L && L^(i-1)
rep : ∀ {i j} {A : Alphabet {i}} → Subset {i} {j} (String A) → Nat → Subset {i} {i ⊔ j} (String A)
rep {i} {j} {A} L zero = lang-ε A  
rep {i} {j} {A} L (suc n) = lang-concat {i} {j} {i ⊔ j} {A} L (rep {i} {j} {A} L n)

{-
 --What about L^0?
 --Notice that if the L ^ 0 were ⊘, then L ^ i would be empty for all i, because
 -- L && ⊘ ≡ ⊘, for all L, but L && ε ≡ L, for all L
 -- But note that we could also provide a different definition:
 -- L ^ zero = ⊘
 -- L ^ (suc zero) = L
 -- L ^ (suc (suc x)) = L && (L ^ (suc x))

 -- What about ⊘^0?
 -- If we're to assume that "" ∈ L*, for all L, then it must be the 
 -- case that ⊘^0 ≡ ε. 
 -- What if we want ⊘ ^ i ≡ ⊘, for all i, including 0?
 -- It would make sense that ⊘ ^ 0 ≡ ⊘, rather than ⊘ ^ 0 ≡ ε

 -- ⊘^0       ≡ ε
 -- ⊘^i       ≡ ⊘ , where i ≠ 0.

 --  L*       ≡ ⋃ {i ∈ [0,∞)} L^i
 rep : {A : Alphabet} → Subset (String A) → Subset (String A)
 rep L ≡ λ s → ∃ n ∈ Nat , ((L ^ n) s)
-}



{-
Rules to prove:
 -- Identity
 ε && L   ≡ L
 L && ε   ≡ L
 ⊘ || L   ≡ L
 
 -- Nilpotence
 ⊘ && L   ≡ ⊘
 L && ⊘   ≡ ⊘

 -- Idempotence
 L || L    ≡ L

 -- Symmetry
 L₁ || L₂ ≡ L₂ || L₁

 -- Distributivity
 L₁ && (L₂ || L₃) ≡ (L₁ && L₂) || (L₁ && L₃)
 (L₁ || L₂) && L₃ ≡ (L₁ && L₃) || (L₂ && L₃)

 -- Associativity
 (L₁ || L₂) || L₃ ≡ L₁ || (L₂ || L₃)
 (L₁ && L₂) && L₃ ≡ L₁ && (L₂ && L₃)
-}

{-
ε && L ≡ L

ε&&L≡L : (L : Subset String) → ε && L ≡ L
This probably won't work because of proof-relevance

What we need to do is irrelefy all the proofs of set-membership, so that there's only
one set-membership proof for each member in the set. Then, we probably can't use
propositional equality and probably need to make an extensional definition of equality
of subsets.

L₁ ≡ L₂ = (s : String) → (L₁ s → L₂ s) ∧ (L₂ s → L₁ s)

ε&&L≡L : (L : Subset String) → subsetExtEq (ε && L) L

L&&ε≡L : (L : Subset String) → subsetExtEq (L && ε) L

⊘∪L≡L : (L : Subset String) → subsetExtEq (⊘ ∪ L) L

⊘&&L≡⊘ : (L : Subset String) → subsetExtEq (⊘ && L) L

⊘&&L≡⊘ : (L : Subset String) → subsetExtEq (L && ⊘) L


-}


{-
 But why should regular expressions be limited to strings of Chars?
 Let's generalize to regular expressions over some set A
-}

{-
data Regex' (A : Set) : Set where
 ⊘    : Regex' A
 ε    : Regex' A
 item : A → Regex' A 
 _*   : Regex' A → Regex' A
 _||_ : Regex' A → Regex' A → Regex' A
 _&&_ : Regex' A → Regex' A → Regex' A
-}


{-
 This is a bit too general though. This is just an abstract data
 structure representing our regular expressions, but for these
 regular expressions to be useful we have to be able to use them
 to accept or reject Lists of objects in A. In order for that to
 work, we have to be able to compare items in the list to the items
 that the regular expression is expecting. For this to work, we
 need A to have decidable equality.
-}


{-
A language is regular iff. it can be described by a
formal regexp.
-}

{-
record DFA : Set where {
  Q : a finite set of states
  Σ : a finite set of symbols called the alphabet
  δ : Q × Σ → Q, the transition function
  q₀ ∈ Q : start state
  F ⊆ Q : the set of accepting states
}

-}

record DFA {i j} : Set ((lsuc i) ⊔ (lsuc j)) where
 field
  -- how to impose finiteness
  Q  : Set i
  Σ  : Set j
  δ  : Q × Σ → Q
  q₀ : Q
  -- this is a type-theoretic representation of a subset of Q
  F  : Q → Set

{-
 Moore machines vs. Mealy machines
-}

{-
Myhill-Nerode theorem
DFAs and regexps are equivalent
-}

{-
DFAs and NFAs are equivalent
-}

{-
 δ L = ε iff "" ∈ L
       ⊘ iff "" ∉ L

 Can we prove the following definition to be "correct"?
-}

{-
δ : {A : Alphabet} → Regex₂ A → Regex₂ A
δ ⊘ = ⊘
δ ε = ε
δ (item c) = ⊘
δ (L₁ || L₂) = (δ L₁) || (δ L₂)
δ (L₁ && L₂) = (δ L₁) && (δ L₂)
δ (L *) = ε
-}

{-
 δ' L = true  iff "" ∈ L
        false iff "" ∉ L

 Can we prove the following definition to be "correct"?
-}

{-
δ' : {A : Alphabet} → Regex₂ A → Bool
δ' ⊘ = false
δ' ε = true
δ' (item c) = false
δ' (L₁ || L₂) = (δ' L₁) or (δ' L₂)
δ' (L₁ && L₂) = (δ' L₁) and (δ' L₂)
δ' (L *) = true
-}


{-
D : {A : Alphabet} → (c : Setoid.elems A) → Regex₂ A → Regex₂ A
D c ⊘ = ⊘
D c ε = ⊘
D c (item x) = if (charEquality c x) then ε else ⊘
D c (L₁ || L₂) = (D c L₁) || (D c L₂)
D c (L *) = (D c L) && (L *)
D c (L₁ && L₂) = ((D c L₁) && L₂) || ((δ L₁) && (D c L₂))
-- i don't understand the && case

D'' : List Char → Regex → Regex
D'' [] r = r
D'' (c ∷ cs) r = D'' cs (D c r)

D' : Data.String.String → Regex → Regex
D' s r = D'' (primStringToList s) r
-}

{-
 Set-theoretically, the definition of the derivative is as such:
 D c L ≡ { w | cw ∈ L }

 How do we get from this to the definition given here?
 How would we "prove" that the derivative is defined "correctly"?
-}

{-
D₂ : Char → Regex → Regex
D₂ c ⊘ = ⊘
D₂ c ε = ⊘
D₂ c (char x) = if (charEquality c x) then ε else ⊘
D₂ c (L₁ || L₂) = (D c L₁) || (D c L₂)
D₂ c (L *) = (D c L) && (L *)
D₂ c (L₁ && L₂) = if (δ' L₁) then (((D₂ c L₁) && L₂) || (D₂ c L₂)) else ((D₂ c L₁) && L₂)
-}
{-

 Case 1: ⊘
 --------------------------------
 D c ⊘ = { w | cw ∈ ⊘ }

 D c {} = { w | cw ∈ {}}

 ∄ w ∈ String , cw ∈ ⊘

 So:
 D c ⊘ ≡ ⊘ 

-}

{-

 Case 2: ε
 ----------------------------------
 D c ε = { w | cw ∈ ⊘}

 D c ε = { w | cw ∈ {""}} 

 ∄ w ∈ String , cw ∈ ε

 So:
 D c ε ≡ ⊘

-}

{-

 Case 3: (char x)
 ------------------------------------------
 D c (char x) = {w | cw ∈ (char x)}

 If c ≠ x, then ∄ w ∈ String , cw ∈ (char x)
 If c = x, then cε ≡ c ∈ (char x)

-}

{-

 Case 4: L₁ || L₂
 ------------------------------------------
 D c (L₁ || L₂) = {w | cw ∈ (L₁ || L₂)}
                = {w | cw ∈ L₁ ∪ L₂}
                = {w | cw ∈ L₁} ∪ {w | cw ∈ L₂}
                = (D c L₁) ∪ (D c L₂)
                = (D c L₁) || (D c L₂)

-}

{-

 Case 5: L*
 ------------------------------------------
 D c L*  = {w | cw ∈ L*}
         = {w | cw ∈ ⋃ {i ∈ [0,∞)} L^i}
         = ⋃ {i ∈ [0,∞)} {w | cw ∈ L^i}
         = {w | cw ∈ ε} ∪ {⋃ {i ∈ [1,∞)} {w | cw ∈ L^i}}
         = ⊘ ∪ {⋃ {i ∈ [1,∞)} {w | cw ∈ L^i}}
         = ⋃ {i ∈ [1,∞)} {w | cw ∈ L^i}
         = ⋃ {i ∈ [1,∞)} {w | cw ∈ L && L^(i-1)}
 Assume L = ⊘, then
 D c L*  = ⋃ {i ∈ [1,∞)} {w | cw ∈ ⊘ && ⊘^(i-1)}
         = ⋃ {i ∈ [1,∞)} {w | cw ∈ ⊘}
         = ⋃ {i ∈ [1,∞)} ⊘
         = ⊘
 
 Assume L = ε, then
 D c L*  = ⋃ {i ∈ [1,∞)} {w | cw ∈ ε && ε^(i-1)}
         = ⋃ {i ∈ [1,∞)} {w | cw ∈ ε && ε}
         = ⋃ {i ∈ [1,∞)} {w | cw ∈ ε}
         = ⋃ {i ∈ [1,∞)} ⊘
         = ⊘

 Assume L non-empty and L ≠ ε, then we can split it
 into two cases, either "" ∈ L, or "" ∉ L.

 Case 1: Assume "" ∉ L, then
  D c L*  = ⋃ {i ∈ [1,∞)} {w | cw ∈ L && L^(i-1)}

  Since "" ∉ L, we know that if x ∈ && L^(i-1), it must
  have the form w₁x' where w₁ ≠ "" ∈ L, and x' ∈ L^(i-1).
  Since w₁ ≠ "", then there exists c' ∈ Char and k ∈ String
  such that w₁ = c'k, and w₁x' = c'kx'. We can split this
  up further into two cases:
  Case 1a: Assume c = c', then D c x = D c c'kx' = D c ckx = kx'
  Case 1b: Assume c ≠ c', then D c x = D c c'kx' = ⊘

 Case 2: Assume "" ∈ L, then
  L = ε ∪ L', where "" ∉ L.
  D c L* = ⋃ {i ∈ [1,∞)} {w | cw ∈ (ε ∪ L') && (ε ∪ L')^(i-1)}
         = ⋃ {i ∈ [1,∞)} {w | cw ∈ (ε && (ε ∪ L')^(i-1)) ∪ (L' && (ε ∪ L')^(i-1))}
         = ⋃ {i ∈ [1,∞)} {w | cw ∈ ((ε ∪ L')^(i-1)) ∪ (L' && (ε ∪ L')^(i-1))}

  (ε ∪ L')^i = ⋃ {j ∈ [0,i]} L'^j

  D c L* = ⋃ {i ∈ [1,∞)} {w | cw ∈ (⋃ {j ∈ [0,i]} L'^j) ∪ (L' && (⋃ {j ∈ [0,i]} L'^j))}
         = ⋃ {i ∈ [1,∞)} {w | cw ∈ (⋃ {j ∈ [0,i]} L'^j) ∪ (⋃ {j ∈ [0,i]} L' && L'^j)}
         = ⋃ {i ∈ [1,∞)} {w | cw ∈ (⋃ {j ∈ [0,i]} L'^j) ∪ (⋃ {j ∈ [0,i]} L'^(j+1))}
         = ⋃ {i ∈ [1,∞)} {w | cw ∈ (⋃ {j ∈ [0,i]} L'^j) ∪ (⋃ {j ∈ [1,i+1]} L'^j)}
         = ⋃ {i ∈ [1,∞)} {w | cw ∈ (⋃ {j ∈ [0,i]} L'^j) ∪ (⋃ {j ∈ [1,i]} L'^(j+1)) ∪ L'^(i+1)}

  We know that x ∪ x = x, so: 
  D c L* = ⋃ {i ∈ [1,∞)} {w | cw ∈ L'^0 ∪ (⋃ {j ∈ [1,i]} L'^j) ∪ (⋃ {j ∈ [1,i]} L'^j) ∪ L'^(i+1)}
         = ⋃ {i ∈ [1,∞)} {w | cw ∈ L'^0 ∪ (⋃ {j ∈ [1,i]} L'^j) ∪ L'^(i+1)}
         = ⋃ {i ∈ [1,∞)} {w | cw ∈ ⋃ {j ∈ [0,i+1]} L'^j}
         = ⋃ {i ∈ [1,∞)} {j ∈ [0,i+1]} {w | cw ∈ L'^j}
         = ⋃ {i ∈ [0,∞)} {w | cw ∈ L'^i}
         = {w | cw ∈ ε} ∪ (⋃ i ∈ [1,∞)} {w | cw ∈ L'^i}
         = ⊘ ∪ (⋃ i ∈ [1,∞)} {w | cw ∈ L'^i})
         = (⋃ i ∈ [1,∞)} {w | cw ∈ L' && L'^(i-1)}
         = (⋃ i ∈ [0,∞)} {w | cw ∈ L' && L'^i}
         = {w | cw ∈ L' && L'*}
  since we know that "" ∉ L', then {w | cw ∈ L' && L'*} = {w | cw ∈ L'} && L'*
  since L = ε ∪ L', we know that L'* = L*
  and {w | cw ∈ L'} = {w | cw ∈ L} = D c L, so:

  D c L* = (D c L) && L*
  
 Now we have to retroactively fit all the other cases to this form
 in order to get a general formula.
          
-}

{-

 Case 6: L₁ && L₂
 -------------------------------------------
 D c (L₁ && L₂) = {w | cw ∈ (L₁ && L₂)}
               L ≡ L₁ && L₂
 
 If we have w₁ ∈ L₁ and w₂ ∈ L₂, then w₁w₂ ∈ L₁ && L₂. How do we strip
 the first character off of this? What is the first character of w₁w₂?
 It will be the first character of w₁, except in the case that w₁ ≡ ε,
 in which case it will be the first character of w₂. 

 We can split the situation into two cases, the case where L₁ contains
 the empty string, and the case where it doesn't. (How can we homogenize
 the two cases?)

 If L₁ doesn't contain the empty string, then the first character in a
 word w₁w₂ ∈ L₁ && L₂, where w₁ ∈ L₁ and w₂ ∈ L₂ will come from w₁
           D c L ≡ (D c L₁) && L₂

 If L₁ does contain the empty string, then
              L₁ ≡ ε ∪ L₁' ,
 where L₁' doesn't contain the empty string. 

 Substituting this back into the definition for L:
               L ≡ (ε ∪ L₁') && L₂

 && distributes over ∪, so:
               L ≡ (ε && L₂) ∪ (L₁' && L₂)
 (but how do we know that we should do this?)
 
         ε && L₂ ≡ L₂
               L ≡ L₂ ∪ (L₁' && L₂)

 At this point we have L decomposed into a form where we know how to
 compute the D c L in terms of the subcomponents of L:
           D c L ≡ D c (L₂ ∪ (L₁' && L₂)

 We can apply the case for ∪:
           D c L ≡ (D c L₂) ∪ (D c (L₁' && L₂))
 D c L₂ is already simplified as far as possible/necessary, so we can
 move on to D c (L₁' && L₂).

 We know by definition that L₁' doesn't contain the empty string, and
 we've already derived the case for D c (X && Y) where X doesn't contain
 the empty string, so:
 D c (L₁' && L₂) ≡ (D c L₁) && L₂

 substituting this back into the definition for L, we finish the
 derivation for the case that L₁ contains the empty string. 
           D c L ≡ (D c L₂) ∪ ((D c L₁') && L₂)
  
-}

{-
testExpr : Regex
testExpr = (((char 'f') && (char 'o')) && (char 'o')) || (((char 'b') && (char 'a')) && (char 'r'))
-}

-- formal algebraic-structure definition of CFGs
{-
  not sure if this is quite suitable for defining derivative-parsing yet.
  both the terminal and non-terminal symbol sets should have decidable
  equality. They should also be non-empty, and the set of terminal symbols
  should contain a designated "empty string" symbol.

  not even sure if this is a fully proper definition of CFGs yet
  what about empty production rules? We'll need these for checking
  nullability after taking derivatives.
-}
record CFG {i j} : Set ((lsuc i) ⊔ (lsuc j)) where
 field
  -- non-terminal symbols
  V : Set i
  -- terminal symbols
  Σ : Set j
  -- production rules
  {- the outer List should really be a set rather than a List, i.e.
     1) no repeating elements
     2) order shouldn't matter at this level of abstraction
  -}
  R : List (V × (List (V ∪ Σ)))
  -- start-symbol.
  S : V

{-
 How this corresponds to regexes:
 you can have an empty grammar, which is the grammar with no
 production rules.

 you can have the grammar that accepts only the empty string
 if the only terminal symbol contained in the grammar is the 
 "empty-string terminal", ε, then the grammar only accepts the
 empty string. 

 the char constructor is replaced by the non-ε terminals

 the RHS of each production rule is a concatenation of the items in the list

 alternation is handled by having multiple production rules for a given
 non-terminal

 kleene star of the RHS of a production rule R → A corresponds to the
 rules: 
  R* → ε
  R* → A R*
-}

{-
 take the derivative with respect to a terminal symbol.
 the main tricky part is the left-recursion and nullability
-}

{-
To get a better understanding, we should provide the set-theoretic description
of CFGs and the meaning of the derivative when applied to these sets
-}


{-
 We can rule out left-recursion by forcing a terminal to come
 first on the RHS of a production rule. 
-}
record CFG-noLR {i j} : Set ((lsuc i) ⊔ (lsuc j)) where
 field
  V : Set i
  Σ : Set j
  R : List (V × (Σ × (List (V ∪ Σ))))
  S : V

{-
 This might be more restrictive than just non-left-recursive. For
 example there might be non-terminals which don't reference the
 non-terminal of the production-rule in question, so these could be
 allowed, but for that we'd have to traverse the graph generated by
 the CFG and determine whether the non-terminal ever gets referenced.
 By forcing a terminal to come first, we can avoid this graph-traversal
 check while still keeping a reasonable level of expressiveness.
-}


{-
 we also need to extend this to a parser instead of just a recognizer.
 Can't quite so easily define the derivative of parser combinators.

-}

{-
 After CFGs are handled, we can parse sem-web langs.
 It would be good to extend this to derivatives of parser-combinators
 though in order to finish up the theoretical side of parsing
-}

{-
 Can we make the derivative easier by first translating into Chomsky
 Normal Form to avoid the left-recursion issues, or will we run into
 issues with nullability even in that case?

 Nullability is trivial in CNF. In CNF, a language contains the empty
 string iff the production rule S → ε is present.

 How do we take the derivative of a CFG in CNF wrt a character c?
 If the CFG contains the rule S → ε, then remove it.
 If the CFG contains the rule S → x, where x is a terminal symbol,
  then remove it if c ≠ x and change it to S → ε if c ≡ x.
 If the CFG contains the rule S → AB, where A and B are non-terminals,
 then repeat the process with A instead of S.
-}

{-
 We should also be able to take the derivative of an automaton.
-}

{-
 Relation of CFGs to non-deterministic pushdown automata
-}

{-
 Chomsky Normal Form
 Backus-Naur Form
 Greibach Normal Form
-}

{-
 CYK algorithm
 Valiant's algorithm
 Early parser
-}

{-
Not all CFGs are good. The following grammar does not accept any
finite strings.
L → L ∘ x

Here it's modified to be able to accept a finite sequence of x's.
L → L ∘ x
L → ε

-}


{-

[1] Alexandre Agular, Bassel Mannaa
    "Regular Expressions in Agda"
    http://www.cse.chalmers.se/~bassel/report.pdf

[2] Sized Types; Agda Docs
    http://agda.readthedocs.io/en/latest/language/sized-types.html

[3] Dmitriy Traytel; Tobias Nipkow
    "Verified Decision Procedures for MSO on Words
    Based on Derivatives of Regular Expressions"
    https://www21.in.tum.de/~traytel/papers/jfp15-mso/mso.pdf

[4] Dmitriy Traytel
    "Formal Languages, Formally and Coinductively"
    https://arxiv.org/pdf/1611.09633.pdf

[5] Scott Owens, John Reppy, Aaron Turon
    "Regular-expression derivatives re-examined"
    https://www.cl.cam.ac.uk/~so294/documents/jfp09.pdf

[6] Haiming Chen
    "Derivatives of Regular Expressions"
    http://lcs.ios.ac.cn/~chm/papers/derivative-tr200910.pdf

[7] 
    NYC Haskell User's Group
    "Partial Derivatives of Regular Expressions"
    https://www.youtube.com/watch?v=QVdBPvOOjBA

[8] Might, Matthew; Darais, David; Spiewak, Daniel
    "Parsing with Derivatives"
    http://matt.might.net/papers/might2011derivatives.pdf

    Matthew Might explains the paper on video:
    https://www.youtube.com/watch?v=ZzsK8Am6dKU

[9] Firsov, Denis; Uustalo, Tarmo
    "Certified Normalization of Context-Free Grammars"

    Code:
    http://cs.ioc.ee/~denis/cert-norm/

    Paper:
    http://cs.ioc.ee/~denis/cert-norm/cfg-norm.pdf

[10] Firsov, Denis; Uustalo, Tarmo
     "Certified CYK parsing of context-free languages"
     http://cs.ioc.ee/~tarmo/papers/nwpt12-jlamp.pdf

[11] Younger, Daniel H.
     "Recognition and Parsing of Context-Free Languages in Time n³"
     http://ac.els-cdn.com/S001999586780007X/1-s2.0-S001999586780007X-main.pdf?_tid=7fd9ab1e-cc96-11e6-b64e-00000aacb35e&acdnat=1482885924_a614ff04651eedb0a4939386da93f45e

[12] Valiant, Leslie
     "General context-free recognition in less than cubic time"
     http://repository.cmu.edu/cgi/viewcontent.cgi?article=2751&context=compsci

[13] Chomsky, Noam
     "On Certain Formal Properties of Grammars"
     http://ac.els-cdn.com/S0019995859903626/1-s2.0-S0019995859903626-main.pdf?_tid=791917b4-cc97-11e6-b90d-00000aab0f02&acdnat=1482886342_e7ebc938aed5cf9420ca550e14a7201b

[14] Firsov, Denis; Uustalo, Tarmo
     "Certified Parsing of Regular Languages"
     http://cs.ioc.ee/~tarmo/papers/cpp13.pdf

[15] Danielsson, Nils Anders
     "Total Parser Combinators"
     http://www.cse.chalmers.se/~nad/publications/danielsson-parser-combinators.pdf

     Video: 
     https://vimeo.com/16541551

[16] Nolen, David
     "David Nolen on Parsing with Derivatives"
     http://paperswelove.org/2016/video/david-nolen-parsing-with-derivatives/

[17] Friedman, D.P.; Wise, D.S.
     "Cons should not evaluate its arguments"
     http://www.cs.indiana.edu/pub/techreports/TR44.pdf

[18] Rutten, J.J.M.M.
     "Automata and Coinduction (an exercise in coalgebra)"
     http://www.math.ucla.edu/~znorwood/290d.2.14s/papers/Rutten-v1.pdf     

[19] "Parsing with Derivatives", ESOP reviews 
     http://matt.might.net/papers/reviews/esop2010-derivatives.txt

[20] Rutten, J.J.M.M.
     "Behavioural differential equations: a coinductive calculus of
     streams, automata, and power series"
     http://homepages.cwi.nl/~janr/papers/files-of-papers/tcs308.pdf

[21] Chomsky, N; Schutzenberger M. P
     "The Algebraic Theory of Context-Free Languages"
     http://www-igm.univ-mlv.fr/~berstel/Mps/Travaux/A/1963-7ChomskyAlgebraic.pdf

[22] Publications of J.J.M.M. Rutten
     http://homepages.cwi.nl/~janr/papers/

[23] Hansen, Helle Hvid; Costa, David; Rutten, Jan
     "Synthesis of Mealy Machines Using Derivatives"
     http://homepages.cwi.nl/~janr/papers/files-of-papers/HCR06.pdf

[24] Abel, Andreas; Chapman, James
     "Normalization by Evaluation in the Delay Monad:
      An Extended Case Study for Coinduction via Copatterns and Sized Types"
     https://pdfs.semanticscholar.org/a714/8780d3c54fff800f6da558bfbb4ddc170d2a.pdf

[25] 
     "Parsing with derivatives: Introduction"
     https://maniagnosis.crsr.net/2012/04/parsing-with-derivatives-introduction.html

[26] Andersen, Leif
     "Parsing With Derivatives"
     http://leifandersen.net/papers/andersen2012parsing.pdf

[27] Might, Matthew; Adams, Michael D.; Hollenbeck, Celeste
     "On the Complexity and Performance of Parsing with Derivatives"
     https://arxiv.org/pdf/1604.04695v1.pdf

[28] Bernardy, Jean-Philippe; Jansson, Patrik
     "Certified Context-Free Parsing: A Formalisation of Valiant's Algorithm in Agda"
     http://www.cse.chalmers.se/~patrikj/papers/ValiantAgda_2014-07-03_preprint.pdf


-}
