module Lang where

open import Agda.Primitive
open import BaseLogic

data List {α} (A : Set α) : Set α where
 [] : List A
 _∷_ : A → List A → List A

data CharLower : Set where
 a' : CharLower
 b' : CharLower
 c' : CharLower
 e' : CharLower
 f' : CharLower
 g' : CharLower
 h' : CharLower
 i' : CharLower
 j' : CharLower
 k' : CharLower
 l' : CharLower
 m' : CharLower
 n' : CharLower
 o' : CharLower
 p' : CharLower
 q' : CharLower
 r' : CharLower
 s' : CharLower
 t' : CharLower
 u' : CharLower
 v' : CharLower
 w' : CharLower
 x' : CharLower
 y' : CharLower
 z' : CharLower

data CharUpper : Set where
 A' : CharUpper
 B' : CharUpper
 C' : CharUpper
 D' : CharUpper
 E' : CharUpper
 F' : CharUpper
 G' : CharUpper
 H' : CharUpper
 I' : CharUpper
 J' : CharUpper
 K' : CharUpper
 L' : CharUpper
 M' : CharUpper
 N' : CharUpper
 O' : CharUpper
 P' : CharUpper
 Q' : CharUpper
 R' : CharUpper
 S' : CharUpper
 T' : CharUpper
 U' : CharUpper
 V' : CharUpper
 W' : CharUpper
 X' : CharUpper
 Y' : CharUpper
 Z' : CharUpper

data DecimalDigit : Set where
 0' : DecimalDigit
 1' : DecimalDigit
 2' : DecimalDigit
 3' : DecimalDigit
 4' : DecimalDigit
 5' : DecimalDigit
 6' : DecimalDigit
 7' : DecimalDigit
 8' : DecimalDigit
 9' : DecimalDigit

Char : Set
Char = CharLower ∨ CharUpper ∨ DecimalDigit

VarFirstChar : Set
VarFirstChar = CharLower ∨ CharUpper

String : Set
String = List Char


data Var : Set where
 cons1 : VarFirstChar → Var
 cons2 : VarFirstChar → String → Var


data Bound : Set where
 bind : Var → Bound

data Term : Set
data Lambda : Set where
 lam : Bound → Term → Term → Lambda

data Ty : Set where
 * : Ty

data Base : Set where
 tybase : Ty → Base
 varbase : Var → Base
 termbase : Term → Base

data App : Set where
 app : Base → Base → App

data Expr : Set where
 lapp : Bound → Term → Expr
 eapp : App → Expr

data Factor : Set where
 arr : Expr → Expr → Factor

data Term where
 tlam : Lambda → Term
 tfac : Factor → Term 

data Bool : Set where
 true : Bool
 false : Bool



{-
-- Bartosz Milewski:

Function take 1:
string log = "";

negate : Bool → Bool
negate true = false ; and also log+="not!"
negate false = true ; and also log+="not!"
-}

{-
Function take 2:
negate : (x : Bool) → (log : String) → Bool × String
negate true log = (false , log ++ "not!")
negate false log = (true , log ++ "not!")
-}

{-
Function take 3:
negate : (x : Bool) → Bool × String
negate true = (false , "not!")
negate false = (true , "not!")
-}

{-
Composition Take 1:
compose : (A → B) → (B → C) → (A → C)
compose f g x = g (f x)
-}

{-
Composition Take 2:
compose : (A → B × String) → (B → C × String) → (A → C × String)
compose f g x = (proj₁ (g (proj₁ (f x))) , (proj₂ (f x)) ++ (proj₂ (g (proj₁ (f x)))))

-}


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

Parser₄ : Set → Set
Parser₄ A = String → List ( A × String)



-- The three primitive parsers:
-- Always succeeds without consuming any input
result : {A : Set} → A → Parser₄ A
result v = λ inp → (v , inp) ∷ []


-- Always fails, regardless of the input
zero : {A : Set} → Parser₄ A
zero = λ inp → []


-- Successfully consumes the first character if the input string is non-empty, and fails otherwise.
item : Parser₄ Char
item [] = []
item (x ∷ xs) = (x , xs) ∷ []


{-
-- Non-monadic sequencing combinator:
_seq'_ : {A B : Set} → Parser₄ A → Parser₄ B → Parser₄ (A × B)
p seq' q = λ inp → ((
-}

{-
-- Monadic parser combinators

-}

