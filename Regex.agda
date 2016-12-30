module Regex where

open import Agda.Primitive
open import BaseLogic
open import Data.Bool
open import Data.List
open import Data.String

{-
Formal language:
a set of strings
(over an alphabet)
-}




data Regex : Set where
 ⊘     : Regex                 -- empty language
 ε     : Regex                 -- language containing only the empty string
 char  : Char → Regex          -- language containing only the symbol "a"
 _*    : Regex → Regex         {- Kleene closure of a regexp e; the language
                                 obtained by concatenating strings from e zero or
                                 more times. -}
 _||_  : Regex → Regex → Regex -- union of two languages e₁ and e₂
 _&&_  : Regex → Regex → Regex {- language obtained by concatenation of a string
                                 of e₁ with a string of e₂ -}


{-
 But why should regular expressions be limited to strings of Chars?
 Let's generalize to regular expressions over some set A
-}

data Regex' (A : Set) : Set where
 ⊘    : Regex' A
 ε    : Regex' A
 item : A → Regex' A 
 _*   : Regex' A → Regex' A
 _||_ : Regex' A → Regex' A → Regex' A
 _&&_ : Regex' A → Regex' A → Regex' A



{-
 This is a bit too general though. This is just an abstract data
 structure representing our regular expressions, but for these
 regular expressions to be useful we have to be able to use them
 to accept or reject Lists of objects in A. In order for that to
 work, we have to be able to compare items in the list to the items
 that the regular expression is expecting. For this to work, we
 need A to have decidable equality!
-}

{-
data Regex'' (A : SetWithDecidableEquality) : Set where
 ⊘    : Regex'' A
 ε    : Regex'' A
 item : A → Regex'' A
 _*   : Regex'' A → Regex'' A
 _||_ : Regex'' A → Regex'' A → Regex'' A
 _&&_ : Regex'' A → Regex'' A → Regex'' A
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


{-
Myhill-Nerode theorem
DFAs and regexps are equivalent
-}

{-
DFAs and NFAs are equivalent
-}

δ : Regex → Regex
δ ⊘ = ⊘
δ ε = ε
δ (char c) = ⊘
δ (L₁ || L₂) = (δ L₁) || (δ L₂)
δ (L₁ && L₂) = (δ L₁) && (δ L₂)
δ (L *) = ε

δ' : Regex → Bool
δ' ⊘ = false
δ' ε = true
δ' (char c) = false
δ' (L₁ || L₂) = (δ' L₁) or (δ' L₂)
δ' (L₁ && L₂) = (δ' L₁) and (δ' L₂)
δ' (L *) = true



D : Char → Regex → Regex
D c ⊘ = ⊘
D c ε = ⊘
D c (char x) = if (charEquality c x) then ε else ⊘
D c (L₁ || L₂) = (D c L₁) || (D c L₂)
D c (L *) = (D c L) && (L *)
D c (L₁ && L₂) = ((D c L₁) && L₂) || ((δ L₁) && (D c L₂))
-- i don't understand the && case

D'' : List Char → Regex → Regex
D'' [] r = r
D'' (c ∷ cs) r = D'' cs (D c r)

D' : String → Regex → Regex
D' s r = D'' (primStringToList s) r

D₂ : Char → Regex → Regex
D₂ c ⊘ = ⊘
D₂ c ε = ⊘
D₂ c (char x) = if (charEquality c x) then ε else ⊘
D₂ c (L₁ || L₂) = (D c L₁) || (D c L₂)
D₂ c (L *) = (D c L) && (L *)
D₂ c (L₁ && L₂) = if (δ' L₁) then (((D₂ c L₁) && L₂) || (D₂ c L₂)) else ((D₂ c L₁) && L₂)
-- i still don't really understand the && case

testExpr : Regex
testExpr = (((char 'f') && (char 'o')) && (char 'o')) || (((char 'b') && (char 'a')) && (char 'r'))


-- formal algebraic-structure definition of CFGs
-- not sure if this is quite suitable for defining derivative-parsing yet.
record CFG {i j} : Set ((lsuc i) ⊔ (lsuc j)) where
 field
  -- non-terminal symbols
  V : Set i
  -- terminal symbols
  Σ : Set j
  -- production rules
  R : List (V × (List (V ∪ Σ)))
  -- start-symbol.
  S : V




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

[9] Firsov, Denis; Uustalo, Tarmo
    "Certified Normalization of Context-Free Grammars"
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

[16] Nolen, David
     "David Nolen on Parsing with Derivatives"
     http://paperswelove.org/2016/video/david-nolen-parsing-with-derivatives/

-}