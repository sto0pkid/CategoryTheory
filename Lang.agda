module Lang where

open import Agda.Primitive
open import BaseLogic
open import Category

infixr 3 _∷_
data List {α} (A : Set α) : Set α where
 [] : List A
 _∷_ : A → List A → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL []    #-}
{-# BUILTIN CONS _∷_  #-}

infixr 3 _++_
_++_ : ∀ {α} {A : Set α} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

[]++xs≡xs : ∀ {α} {A : Set α} → (x : List A) → ([] ++ x) ≡ x
[]++xs≡xs x = refl x


[xs++[]≡xs]-ind : ∀ {α} {A : Set α} → (xs : List A) → ((xs ++ []) ≡ xs) → (x : A) → ((x ∷ xs) ++ []) ≡ (x ∷ xs)
[xs++[]≡xs]-ind {α} {A} xs [xs++[]≡xs] x = [x∷xs++[]≡x∷xs]
 where
  [x∷xs++[]]≡x∷[xs++[]] : ((x ∷ xs) ++ []) ≡ x ∷ (xs ++ [])
  [x∷xs++[]]≡x∷[xs++[]] = refl (x ∷ (xs ++ []))

  x∷_ : (l : List A) → Set α
  x∷ l = (x ∷ (xs ++ [])) ≡ (x ∷ l)

  x∷[xs++[]]≡x∷xs : (x ∷ (xs ++ [])) ≡ (x ∷ xs)
  x∷[xs++[]]≡x∷xs = [x≡y]→[Px→Py] x∷_ (xs ++ []) xs [xs++[]≡xs] (refl (x ∷ (xs ++ [])))

  [x∷xs++[]≡x∷xs] : ((x ∷ xs) ++ []) ≡ (x ∷ xs)
  [x∷xs++[]≡x∷xs] = ≡-⇶ [x∷xs++[]]≡x∷[xs++[]] x∷[xs++[]]≡x∷xs



xs++[]≡xs : ∀ {α} {A : Set α} → (xs : List A) → (xs ++ []) ≡ xs
xs++[]≡xs [] = refl []
xs++[]≡xs (x ∷ xs) = [xs++[]≡xs]-ind xs (xs++[]≡xs xs) x


listmap : ∀ {α β} {A : Set α} {B : Set β} (f : A → B) → List A → List B
listmap f [] = []
listmap f (x ∷ xs) = (f x) ∷ (listmap f xs) 



data Bool : Set where
 true : Bool
 false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

if_then_else : ∀ {α} {A : Set α} → Bool → A → A → A
if_then_else true x y = x
if_then_else false x y = y

data Nat : Set where
 zero : Nat
 suc : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

data Maybe {α} (A : Set α) : Set α where
 Nothing : Maybe A
 Just : A → Maybe A

postulate Char : Set
{-# BUILTIN CHAR Char #-}

postulate String : Set
{-# BUILTIN STRING String #-}

postulate primStringToList : String → List Char
postulate primStringFromList : List Char → String
postulate primStringAppend : String → String → String
postulate primStringEquality : String → String → Bool
postulate primShowString : String → String

notStr : String
notStr = "not!"


{-
-- Bartosz Milewski:
-- Category Theory for Programmers
-- Episode 3.2: Kliesli category

-- Logging, take 1:
string log = "";

negate₁ : Bool → Bool
negate₁ true = false ; and also log+="not!"
negate₁ false = true ; and also log+="not!"
-}

{-
 But this is not purely functional!

 It uses the global stateful variable "string log;"
 If we remove the global variable, then we break our negate₁ function

 Something is not right!
-}




-- Logging take 2:
negate₂ : (x : Bool) → (log : String) → Bool × String
negate₂ true log = (false , (primStringAppend log "not!"))
negate₂ false log = (true , (primStringAppend log "not!"))

{-
 Cool, now we can handle the logging without globals or state.
 Why does negate₂ know about appending strings?
 If we remove the _++_ definition then we break negate₂.

 Also, what happens when we want to memoize this function?
 Every time we call it with a different current log, we get
 a different result.

 Something is still not right!
-}





-- Logging, take 3:
negate₃ : (x : Bool) → Bool × String
negate₃ true = (false , notStr)
negate₃ false = (true , notStr)

{-
 Alright, that's cool.

 We've removed the dependency on _++_, and now we can
 reasonably memoize this function. 

 But this isn't appending to the log anymore!
 How do we recover that functionality?

 The log gets built up as different functions in the
 program are run. These functions are composed together
 to build the whole program. So maybe we can handle the
 log-append inside of our function composition!
-}

-- Here's our standard function composition:
-- Composition Take 1:
compose₁ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} → (A → B) → (B → C) → (A → C)
compose₁ f g x = g (f x)



--Composition Take 2:
compose₂ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} → (A → B × String) → (B → C × String) → (A → C × String)
compose₂ f g x = ((first (g (first (f x)))) , (primStringAppend (second (f x)) (second (g (first (f x))))))

someStr : String
someStr = second ((compose₂ negate₃ negate₃) true)

idLogger : ∀ {α} {A : Set α} → A → A × String
idLogger x = (x , "")

-- Now prove that we have a category!
kliesliCategory₀ : ∀ {α} → Category₀ {lsuc α} {α}
kliesliCategory₀ {α} = record {
  obj = Set α;
  hom = λ A B → (A → B × String);
  id = λ A → idLogger {α} { A };
  comp = λ g f → (compose₂ f g)
 }

π₁[idLogger-x]≡x : ∀ {α} {A : Set α} (x : A) → first (idLogger x) ≡ x
π₁[idLogger-x]≡x {α} {A} x = refl x

π₂[idLogger-x]≡[] : ∀ {α} {A : Set α} (x : A) → second (idLogger x) ≡ ""
π₂[idLogger-x]≡[] {α} {A} x = refl ""

p≡[π₁-p,π₂-p] : ∀ {α β} {A : Set α} {B : Set β} (p : A × B) → p ≡ (first p , second p)
p≡[π₁-p,π₂-p] {α} {β} {A} {B} (p1 , p2) = refl (p1 , p2)

{-
kliesliCategory : ∀ {α} → Category {lsuc α} {α}
kliesliCategory {α} = record {
  obj = Set α;
  hom = λ A B → (A → B × String);
  id = λ A → idLogger {α} {A};
  comp = λ g f → (compose₂ f g);
 
{-
  λ f → (λ x → ( first (idLogger (first (f x))) , (second (f x)) ++ (second (idLogger (first (f x))))))
   by : π₁[idLogger-x]≡x
  λ f → (λ x → ( first (f x) , (second (f x)) ++ (second (idLogger (first (f x))))) )
   by : π₂[idLogger-x]≡[]
  λ f → (λ x → ( first (f x) , (second (f x)) ++ []) )
   by : x++[]≡x
  λ f → (λ x → ( first (f x) , second (f x)))
   by : p≡[π₁-p,π₂-p]
  λ f → (λ x → f x)
   by : eta equivalence
  λ f → f
-}

  left-id = left-id-proof;
  right-id = right-id-proof;
  assoc = assoc-proof



 }
 where
{-
  π₂fx++[]≡π₂fx : {A B : Set α} → (f : A → B × String) → (x : A) → (second (f x) ++ []) ≡ second (f x)
  π₂fx++[]≡π₂fx f x = refl (second (f x))
-}

  left-id-proof : {A B : Set α} → (f : A → B × String) → compose₂ idLogger f ≡ f
  left-id-proof {A} {B} f x = left-id-proof'
   where
    π₁[f_]≡π₁fx : (b : B) → Set α
    π₁[f b ]≡π₁fx = (first (f b)) ≡ (first (f x))   
 
    π₁[f[π₁-idLogger-x]]≡π₁fx : (first (f (first (idLogger x)))) ≡ (first (f x))
    π₁[f[π₁-idLogger-x]]≡π₁fx = [x≡y]→[Px→Py] π₁[f_]≡π₁fx (first (idLogger x)) x π₁[idLogger-x]≡x (refl (first (f (first (idLogger x)))))

    --π₁[f[π₁[idLogger-x]]]
    left-id-proof'
  


  right-id-proof : {A B : Set α} → (f : A → B × String) → compose₂ f idLogger ≡ f
  right-id-proof {A} {B} f x = right-id-proof'
   where
    π₁[idLogger[π₁fx]]≡π₁fx : {A B : Set α} → (f : A → B × String) → (x : A) → first (idLogger (first (f x))) ≡ first (f x)
    π₁[idLogger[π₁fx]]≡π₁fx f x = refl (first (f x))

    π₂[idLogger[π₁fx]]≡[] : {A B : Set α} → (f : A → B × String) → (x : A) → second (idLogger (first (f x))) ≡ []
    π₂[idLogger[π₁fx]]≡[] f x = refl []

    π₂fx++[]≡π₂fx : ((second (f x)) ++ []) ≡ (second (f x))
    π₂fx++[]≡π₂fx = xs++[]≡xs (second (f x))

    π₂fx++_≡π₂fx : (x : List A) → Set α
    π₂fx++ l ≡π₂fx = ((second (f x)) ++ l) ≡ (second (f x))

    π₂fx++π₂[idLogger[π₁fx]]≡π₂fx : ((second (f x)) ++ (second (idLogger (first (f x))))) ≡ (second (f x))
    π₂fx++π₂[idLogger[π₁fx]]≡π₂fx = [x≡y]→[Px→Py] π₂fx++_≡π₂fx [] (second (idLogger (first (f x)))) (≡-↑↓ π₂[idLogger[π₁fx]]≡[]) π₂fx++[]≡π₂fx
   
    f∘idLogger-x≡[_,π₂fx++π₂[idLogger[π₁fx]]] : (b : B) → Set α
    f∘idLogger-x≡[ b ,π₂fx++π₂[idLogger[π₁fx]]] = compose₂ f idLogger ≡ (b , ((second (f x)) ++ (second (idLogger (first (f x))))))

    f∘idLogger-x≡[π₁fx,π₂fx++π₂[idLogger[π₁fx]]] : compose₂ f idLogger ≡ ((first (f x)) , ((second (f x)) ++ (second (idLogger (first (f x))))))
    f∘idLogger-x≡[π₁fx,π₂fx++π₂[idLogger[π₁fx]]] = 
     [x≡y]→[Px→Py] 
      f∘idLogger-x≡[_,π₂fx++π₂[idLogger[π₁fx]]] 

      (first (idLogger (first (f x)))) 
      (first (f x)) 
      π₁[idLogger[π₁fx]]≡π₁fx 
      (refl ((first (idLogger (first (f x)))) , ((second (f x)) ++ (second (idLogger (first (f x)))))))      

    f∘idLogger-x≡[π₁fx,_] : (s : String) → Set α
    f∘idLogger-x≡[π₁fx, s ] = compose₂ f idLogger ≡ ((first (f x)) , s)

    f∘idLogger-x≡[π₁fx,π₂fx] : compose₂ f idLogger ≡ ((first (f x)) , (second (f x)))
    f∘idLogger-x≡[π₁fx,π₂fx] = 
     [x≡y]→[Px→Py] 
      f∘idLogger-x≡[π₁fx,_] 
      ((second (f x)) ++ (second (idLogger (first (f x))))) 
      (second (f x)) 
      π₂fx++π₂[idLogger[π₁fx]]≡π₂fx

    f∘idLogger-x≡_ : (p : B × String) → Set α 
    f∘idLogger-x≡_ p = compose₂ f idLogger ≡ p

    right-id-proof' : compose₂ f idLogger ≡ f
    right-id-proof' = [x≡y]→[Px→Py] f∘idLogger-x≡_ ((first (f x)), (second (f x))) (f x) (≡-↑↓ (p≡[π₁-p,π₂-p] (f x))) f∘idLogger-x≡[π₁fx,π₂fx] 
    
  assoc-proof : {A B C D : Set α} → (f : A → B × String) → (g : B → C × String) → (h : C → D × String) → 
                compose₂ (compose₂ h g) f ≡ compose₂ h (compose₂ g f)
  assoc-proof = assoc-proof'
   where
    assoc-proof'
-}



-- Prove that this "logging" mechanism can be generalized to be able to use any
-- monoid, rather than just (String, _++_), and this will still form a category

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


-- "result" from Graham & Hutton's "Monadic Parser Combinators"
-- The three primitive parsers:
-- Always succeeds without consuming any input
{-
result : {A : Set} → A → String → List (A × String)
-}
result : {A : Set} → A → Parser₄ A
result v = λ inp → (v , inp) ∷ []

-- This is the same as "succeed" from Schirmer's "Parsers All the Way Down"
succeed : {A : Set} → A → Parser₄ A
succeed = result




-- "zero" from Graham & Hutton's "Monadic Parser Combinators"
-- shouldn't this be "{A : Set} → A → Parser₄ A" ?
-- Always fails, regardless of the input
{-
zeroP : {A : Set} → String → List (A × String)
-}
zeroP : {A : Set} → Parser₄ A
zeroP = λ inp → []

{-
zeroP' : {A : Set} → A → String → List (A × String)
-}
zeroP' : {A : Set} → A → Parser₄ A
zeroP' v = λ inp → []

-- This is the same as "fail" from Schirmer's "Parsers All the Way Down?"
fail : {A : Set} → Parser₄ A
fail = zeroP

fail' : {A : Set} → A → Parser₄ A
fail' = zeroP'


{-
-- "satisfy" from Schirmer's "Parsers All the Way Down?"
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


{-
-- "literal" from Schirmer's "Parsers All the Way Down?"
literal : Parser₄ Char
-}

{-
-- "alternative" combinator from Schirmer's "Parsers All the Way Down?"
-}

{-
-- "next" combinator from Schirmer's "Parsers All the Way Down?"
-}

{-
-- "using" combinator from Schirmer's "Parsers All the Way Down?"
-}

{-
-- Non-monadic sequencing combinator:
_seq'_ : {A B : Set} → Parser₄ A → Parser₄ B → Parser₄ (A × B)
p seq' q = λ inp → ((
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

[4] Bartosz Milewski, "Category Theory for Programmers"
    Episode 3.2: Kleisli category
    https://www.youtube.com/watch?v=i9CU4CuHADQ

-}
