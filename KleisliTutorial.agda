module KleisliTutorial where

open import Agda.Primitive
--open import BaseLogic
open import Category
open import Data.Bool
open import Data.String
open import Data.Product
open import Data.PropositionalEquality

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
negate₃ true = (false , "not!")
negate₃ false = (true , "not!")

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
π₁[idLogger-x]≡x {α} {A} x = refl

π₂[idLogger-x]≡[] : ∀ {α} {A : Set α} (x : A) → second (idLogger x) ≡ ""
π₂[idLogger-x]≡[] {α} {A} x = refl

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
REFERENCES:

[1] Bartosz Milewski, "Category Theory for Programmers"
    Episode 3.2: Kleisli category
    https://www.youtube.com/watch?v=i9CU4CuHADQ
-}
