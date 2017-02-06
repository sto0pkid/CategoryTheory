module Lang where

open import Agda.Primitive
--open import BaseLogic
open import Category

open import Data.List
open import Data.List.Operations
open import Data.Bool
open import Data.Bool.Operations
open import Data.Nat
open import Data.Maybe
open import Data.String
open import Data.Disjunction
open import Data.Product

{-

--http://www.cs.nott.ac.uk/~pszgmh/monparsing.pdf


-- Intuitively, a parser should take a string and produce some kind of tree:
Parser₁ : Set
Parser₁ = String → Tree

-- A parser might not consume the entire input though, so we might return the unconsumed suffix
-- of the string along with the resulting tree.
Parser₂ : Set
Parser₂ = String → Tree × String

-- A parser might also fail on its input string. Rather than just report a run-time error when
-- this happens, we choose to have parsers return a list of pairs rather than just a single pair
-- with the convention that the empty list denotes failure of the parser, and the singleton
-- list denotes success:
Parser₃ : Set
Parser₃ = String → List (Tree × String)
-}

-- Different parsers can potentially return different kinds of trees, so we should further
-- abstract on the specific type of trees:

Parser₄ : ∀ {i} → Set i → Set i
Parser₄ A = String → List ( A × String)

{-
 This works for the type of the parser, but for building total parser combinators we need
 to be able to structurally recurse on the input strings, and since Agda doesn't appear to
 support this directly and instead requires the input strings to be transformed into Lists
 of Chars first, we'll need to modify the parser type as such:
-}
Parser₄' : ∀ {i} → Set i → Set i
Parser₄' A = List Char → List (A × String)

{-
 Each parser can be constructed to accept Strings as input for convenience but then call a 
 "primed" version of itself on the List Char returned from "(primStringToList input)" in
 order to build the parsers in a structurally recursive form.
-}





-- "result" from Graham & Hutton's "Monadic Parser Combinators"
-- The three primitive parsers:
-- Always succeeds without consuming any input
{-
result : {A : Set} → A → String → List (A × String)
-}
result : {A : Set} → A → Parser₄ A
result v = λ inp → (v , inp) ∷ []

-- This is the same as "succeed" from [3]
-- Which is also the same as "succeed" from [4]
succeed : {A : Set} → A → Parser₄ A
succeed = result




-- "zero" from Graham & Hutton's "Monadic Parser Combinators"
-- shouldn't this be "{A : Set} → A → Parser₄ A" ?
-- Always fails, regardless of the input
zeroP : {A : Set} → Parser₄ A
zeroP = λ inp → []


-- This is the same as "fail" from [3]
-- And also the same as "fail" from [4]
fail : {A : Set} → Parser₄ A
fail = zeroP


{-
-- "satisfy" from [3]
-- which is the same as "satisfy" from [4]
-}

satisfy' : (P : Char → Bool) → List Char → List (Char × String)
satisfy' p [] = fail ""
satisfy' p (x ∷ xs) = if (p x) then (succeed {Char} x (primStringFromList xs)) else (fail (primStringFromList xs))

satisfy : (P : Char → Bool) → Parser₄ Char
satisfy p x = satisfy' p (primStringToList x) 



-- "item" from Graham & Hutton's "Monadic Parser Combinators"
-- Successfully consumes the first character if the input string is non-empty, and fails otherwise.
{-
item : String → List ( Char × String)
-}

item' : List Char → List ( Char × String)
item' [] = []
item' (x ∷ xs) = (x , (primStringFromList xs)) ∷ []

item : Parser₄ Char
item x = item' (primStringToList x)

any : Parser₄ Char
any = item






inString' : Char → List Char → Bool
inString' c [] = false
inString' c (x ∷ xs) = if (primStringEquality (primShowChar c) (primShowChar x)) then true else (inString' c xs)

inString : Char → String → Bool
inString c s = inString' c (primStringToList s)



digits : String
digits = "0123456789"

isDigit : Char → Bool
isDigit c = inString c digits

parseDigit : Parser₄ Char
parseDigit x = satisfy isDigit x




lcChars : String
lcChars = "abcdefghijklmnopqrstuvwxyz"

isLower : Char → Bool
isLower c = inString c lcChars

parseLower : Parser₄ Char
parseLower x = satisfy isLower x





ucChars : String
ucChars = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

isUpper : Char → Bool
isUpper c = inString c ucChars

parseUpper : Parser₄ Char
parseUpper x = satisfy isUpper x

{-
-- "literal" from [3]
literal : Parser₄ Char
-}

charEqual : Char → Char → Bool
charEqual c₁ c₂ = primStringEquality (primShowChar c₁) (primShowChar c₂)

parseChar : Char → Parser₄ Char
parseChar c x = satisfy (charEqual c) x

-- this is the same as "literal" from [4]
literal : Char → Parser₄ Char
literal = parseChar

fcomp : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} →
        (B → C) → (A → B) → A → C
fcomp g f x = g (f x)

{-
-- "alternative" combinator from Schirmer's [3]
-- this is the same as the "alt" combinator from [4]
-}

{-
 The "alt" combinator in [4] alternates two parsers of the same type.
 But the "then" combinator from [4] sequences two parsers of different types.
 So I've implemented ₁ and ₂ versions of the "alt" parser, for alternating
 parsers of the same type and different types, respectively.

 Due to the fact that the "then" combinator in [4] sequences parsers of two
 different types, but the "alt" combinator does not, leads me to assume
 that this is only because it's slightly more difficult to build the two-typed
 alternation than it is to build the singly-typed alternation, because you have
 to do unpackage things out of the A × String / B × String pairs, inl/inr them
 into (A ⊹ B) and then re-pair them with the String into (A ⊹ B) × String pairs
 in order to make it work.

 The singly-typed alternation combinator is definitely easier to understand and
 should be examined first before moving on to the generalized alternation 
 combinator.
-}

{-
 You can have exclusive alternation, which means that if the first parser
 succeeds then the second parser will not be used, and the only possibilities
 are to obtain either one result or no results.
-}
alt-exc₁ : ∀ {i} {A : Set i} → Parser₄ A → Parser₄ A → Parser₄ A
alt-exc₁ {i} {A} p1 p2 inp = if (not (isEmpty (p1 inp))) then (p1 inp) else (p2 inp)

alt-exc₂ : ∀ {i j} {A : Set i} {B : Set j} → Parser₄ A → Parser₄ B → Parser₄ (A ⊹ B)
alt-exc₂ {i} {j} {A} {B} p1 p2 inp = if (not (isEmpty (p1 inp))) then (list-inl {i} {j} {lzero} {A} {B} {String} (p1 inp)) else (list-inr {i} {j} {lzero} {A} {B} {String} (p2 inp))


{-
 The other option is to have inclusive alternation, which means that both
 parsers can be used, and if they both succeed (as in the case of an
 ambiguous grammar) then it is possible to have multiple results.
-}

alt-inc₁ : ∀ {i} {A : Set i} → Parser₄ A → Parser₄ A → Parser₄ A
alt-inc₁ {i} {A} p1 p2 inp = (p1 inp) ++ (p2 inp)

alt-inc₂ : ∀ {i j} {A : Set i} {B : Set j} → Parser₄ A → Parser₄ B → Parser₄ (A ⊹ B)
alt-inc₂ {i} {j} {A} {B} p1 p2 inp = _++_ {i ⊔ j} {(A ⊹ B) × String} (list-inl {i} {j} {lzero} {A} {B} {String} (p1 inp)) (list-inr {i} {j} {lzero} {A} {B} {String} (p2 inp)) 

{-
 Both the exclusive and inclusive alternation could be made to operate in parallel.
-}


{-
-- "next" combinator from [3]
-}

{-
-- "then" combinator from [4]
 [4] uses "list comprehension notation" to express the set of all pairs from each list
 [5] shows an implementation of this "allPairs" function

 We need something slightly more general than cartesian products of Lists though.
 For each element in the list produced by the first parser, we must call the second
 parser on the remaining input string.

 
-}


then : ∀ {i j} {A : Set i} {B : Set j} → Parser₄ A → Parser₄ B → Parser₄ (A × B)
then {i} {j} {A} {B} p1 p2 inp = concat (listmap (λ x → (listmap (λ y → (((first x) , (first y)) , (second y))) (p2 (second x)))) (p1 inp))



{-
-- Non-monadic sequencing combinator:
_seq'_ : {A B : Set} → Parser₄ A → Parser₄ B → Parser₄ (A × B)
p seq' q = λ inp → ((
-}

{-
-- "using" combinator from [3]
-- same as the "using" combinator from [4]
-}


using' : ∀ {i j} {A : Set i} {B : Set j} → Parser₄ A → (A → B) → Parser₄ B
using' {i} {j} {A} {B} p f inp = listmap (λ x → ((f (first x)) , (second x))) (p inp)

{-
-- "many" combinator from [4]

 the "many" combinator from [4] is not structurally recursive!
 "many p = ((p $then many p) $using cons) $alt (succeed [])"

 How to make it so? By structural recursion on the input string of course!
 This might not be entirely straight-forward, however, since a parser may
 consume multiple characters at a time, we might not be able to do structural
 recursion directly on the List constructors but might have to defer
 termination proofs to more general size-change arguments.
-}

{-
many' : ∀ {i} {A : Set i} → Parser₄ A → Parser₄' (List A)
many' {i} {A} p [] = ...?
many' {i} {A} p (x ∷ xs) = ...?

many : ∀ {i} {A : Set i} → Parser₄ A → Parser₄ (List A)
many {i} {A} p s = many' {i} {A} p (primStringToList s)
-}

{-
-- Monadic parser combinators

-}


data Reply {α} (A : Set α) : Set α where  
 error : Reply A
 ok : A → String → Reply A

data Consumed {α} (A : Set α) : Set α where
 consumed : Reply A → Consumed A
 empty : Reply A → Consumed A

Parser : ∀ {α} (A : Set α) → Set α
Parser A = String → Consumed A




{-

[1] Graham Hutton; Erik Meijer
    "Monadic Parser Combinators"
    http://www.cs.nott.ac.uk/~pszgmh/monparsing.pdf

[2] Philip Wadler;
    "How to Replace Failure by a List of Successes:
     A method for exception handling, backtracking, and pattern matching
     in lazy functional languages"
    https://rkrishnan.org/files/wadler-1985.pdf

    Defines:
     -- lit
     -- empty
     -- fail
     -- alt
     -- seq
     -- rep
     -- rep1
     -- alts
     -- seqs
     -- lits

[3] Stefanie Schirmer; DomCode; 
    "Parsers All the Way Down?"
    https://www.youtube.com/watch?v=oU2418-8_KI

[4] Graham Hutton
    "Higher Order Functions for Parsing"
    http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.63.3555&rep=rep1&type=pdf

   -- succeed
   -- fail
   -- satisfy
   -- literal
   -- alt (singly-typed ; inclusive)
   -- then
   -- using
   -- many
   -- some
   -- number
   -- word
   -- string
   -- xthen
   -- thenx
   -- nibble
   -- any
   -- symbol 
   -- offside
   -- into

[5] gallais
    on list-comprehensions in Agda:
    http://stackoverflow.com/questions/31394404/agda-forming-all-pairs-x-y-x-in-xs-y-in-ys
    https://gist.github.com/gallais/2e31c020937198a85529

[6] Nils Anders Danielsson
    "Total Parser Combinators" (in Agda)
    http://www.cse.chalmers.se/~nad/publications/danielsson-parser-combinators.pdf

[7] Agda Sized Types
    http://agda.readthedocs.io/en/latest/language/sized-types.html?highlight=sized%20types

[8] Alexandre Agular, Bassel Mannaa
    Regular Expressions in Agda
    http://www.cse.chalmers.se/~bassel/report.pdf



-}
