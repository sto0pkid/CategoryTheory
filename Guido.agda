module Guido where

open import Data.Disjunction
open import Data.List
open import Data.Nat
open import Data.Bool
open import Data.Bool.Operations
open import Data.Product
open import Data.PropositionalEquality
open import BoolNat

{-
Chapter 5 will explain the meaning of inferencing in connection with RDF. Two aspects will be interwoven: the
theory of inferencing on RDF data and the specification of an inference engine, RDFEngine, in Haskell.
First a specification of a RDF graph will be given. Then inferencing on a RDF graph will be explained. A definition
will be given for rules, queries, solutions and proofs. After discussing substitution and unification, an inference
step will be defined and an explanation will be given of the data structure that is needed to perform a step. The
notion of subquerying will be explained and the proof format that is necessary for subquerying.
The explanations will be illustrated with examples and the relevant Haskell code.
RDFEngine possesses the characteristics of soundness, completeness, and monotonicity. This is demonstrated by a
series of lemmas.
-}


data Vare : Set where
 UVar : List Bool → Vare
 EVar : List Bool → Vare
 GVar : List Bool → Vare
 GEVar : List Bool → Vare

data URI : Set where
 cons : List Bool → URI

data IRI : Set where
 cons : List Bool → IRI

data Literal : Set where
 cons : List Bool → Literal



{-
S-5.2,pr-2,s-3:
A triple is composed of a subject, a property, and an object.
data Triple where
 _,_,_ : Subject → Property → Object → Triple
-}
data Triple : Set
data Subject : Set
data Property : Set
data Object : Set

record upto-S-5,2/pr-2/s-3 : Set₁ where
 field
  triple : Set
  subject : Set
  property : Set
  object : Set
  triple-component-subject : triple → subject
  triple-component-property : triple → property
  triple-component-object : triple → object
  triple-all-possible-components : (s : subject) → (p : property) → (o : object) → ∃ t ∈ triple , ((triple-component-subject t ≡ s) ∧ (triple-component-property t ≡ p) ∧ (triple-component-object t ≡ o))
  


{-
record Triple where
 field
  component-subject : Subject
  component-property : Property
  component-object : Object
-}

{-
S-5.2,pr-2,s-4:
A triplelist is a list of triples. 
-}
TripleList : Set
TripleList = List Triple

{-
S-5.2,pr-2,s-5:
Subject, property, and object can have as value a URI, a blank node, or a triplelist.
-}

data Subject where
 URI-cons : URI → Subject
 Var-cons : Vare → Subject
 TripleList-cons : TripleList → Subject

data Property where
 URI-cons : URI → Property
 Var-cons : Vare → Property
 TripleList-cons : TripleList → Property

data Object where
 URI-cons : URI → Object
 Var-cons : Vare → Object
 TripleList-cons : TripleList → Object

data Triple where
 _,_,_ : Subject → Property → Object → Triple

{-
S-5.2,pr-2,s-6:
An object can also be a literal.
-}

data Object₂ : Set where
 URI-cons : URI → Object₂
 Var-cons : Vare → Object₂
 TripleList-cons : TripleList → Object₂
 Literal-cons : Literal → Object₂

data Triple₂ : Set where
 _,_,_ : Subject → Property → Object₂ → Triple₂

TripleList₂ : Set
TripleList₂ = List Triple₂
 
{-
S-5.2,pr-2,s-7:
The property is also often called 'predicate'.
-}

Predicate : Set
Predicate = Property

data Triple₃ : Set where
 _,_,_ : Subject → Predicate → Object₂ → Triple₃

TripleList₃ : Set
TripleList₃ = List Triple₃
{-

-}

{-
A query is a triplelist.
-}
Query : Set
Query = TripleList

{-
The triples composing the query can contain variables. When the query does not contain variables, it is an RDF graph.
When it contains variables, it is not an RDF graph because variables are not defined in RDF and are thus an extension to
RDF.
-}
TripleList-containsVars-dec : List Triple → Bool
TripleList-containsVars-dec [] = false
TripleList-containsVars-dec ((Var-cons v , _ , _ ) ∷ rest) = true
TripleList-containsVars-dec ((_ , Var-cons v , _ ) ∷ rest) = true
TripleList-containsVars-dec ((_ ,  _ , Var-cons v ) ∷ rest) = true
TripleList-containsVars-dec (t ∷ rest) = TripleList-containsVars-dec rest

TripleList-isRDFGraph-dec : List Triple → Bool
TripleList-isRDFGraph-dec [] = true
TripleList-isRDFGraph-dec ((Var-cons v , _ , _ ) ∷ rest) = false
TripleList-isRDFGraph-dec ((_ , Var-cons v , _ ) ∷ rest) = false
TripleList-isRDFGraph-dec ((_ , _ , Var-cons v) ∷ rest) = false
TripleList-isRDFGraph-dec (t ∷ rest) = TripleList-isRDFGraph-dec rest

TripleList-isRDFGraph-dec' : List Triple → Bool
TripleList-isRDFGraph-dec' t = not (TripleList-containsVars-dec t)

{- 
When the inferencing in RDFEngine starts, the query becomes the goallist. The goallist is the tripleset that has to be
proved, i.e. matched against the RDF graph.
-}

record InfData : Set where
 field
  goallist : TripleList

{-
This process will be described in detail later. The answer to a query consists of one or more "solutions". In a solution the
variables of the query are replaced by URI's, if the query did have variables. If not, a solution is a confirmation that the
triples of the query are existing triples. I will give later a more precise definition of solutions.
-}


Substitution : Set
Substitution = Vare × (URI ⊹ Literal)

SubstitutionList : Set
SubstitutionList = List Substitution

data Solution : Set where
 answers : SubstitutionList → Solution
 confirmation : Bool → Solution


{-
A "variable" will be indicated with a question mark. For this chapter it is assumed that the variables are local universal
variables.
-}


{-
A grounded triple is a triple of which subject and property are URI's and the object is a URI or literal.
-}

Triple-isGrounded-dec : Triple₂ → Bool
Triple-isGrounded-dec (URI-cons s , URI-cons p , URI-cons o) = true
Triple-isGrounded-dec (URI-cons s , URI-cons p , Literal-cons o) = true
Triple-isGrounded-dec t = false

{-
A grounded triplelist contains only grounded triples.
-}
TripleList-isGrounded-dec : TripleList₂ → Bool
TripleList-isGrounded-dec [] = true
TripleList-isGrounded-dec (t ∷ ts) = if (Triple-isGrounded-dec t) then (TripleList-isGrounded-dec ts) else false

{-
A query can be grounded. In that case, an affirmation is sought that the triples in the query exist, but not
necessarily in the RDF graph: they can be deduced using the rules.
-}

{-
Triple-isRule-dec : Triple → Bool
Triple-isRule-dec (TripleList-cons tl₁ , p , TripleList-cons tl₂) = 
-}
