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

Language : ∀ {i} (A : Alphabet {i}) → Set (lsuc lzero ⊔ i)
Language A = Subset (String A)

  
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
