module Guido where

open import Data.Disjunction
open import Data.List
open import Data.Nat
open import Data.Bool
open import Data.Bool.Operations
open import Data.Product
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

String : Set
String = List Nat

data Vare : Set where
 UVar : String → Vare
 EVar : String → Vare
 GVar : String → Vare
 GEVar : String → Vare

data Triple : Set

TripleList : Set
TripleList = List Triple

data Resource : Set where
 URI-cons : String → Resource
 Literal-cons : String → Resource
 Var : Vare → Resource
 TripleList-cons : TripleList → Resource
 ResNil : Resource

Subject : Set
Subject = Resource

Object : Set
Object = Resource

Predicate : Set
Predicate = Resource

data Triple where
 _,_,_ : Subject → Predicate → Object → Triple


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
TripleList-containsVars-dec ((Var v , _ , _ ) ∷ rest) = true
TripleList-containsVars-dec ((_ , Var v , _ ) ∷ rest) = true
TripleList-containsVars-dec ((_ , _ , Var v ) ∷ rest) = true
TripleList-containsVars-dec (t ∷ rest) = TripleList-containsVars-dec rest

TripleList-isRDFGraph-dec : List Triple → Bool
TripleList-isRDFGraph-dec [] = true
TripleList-isRDFGraph-dec ((Var v , _ , _ ) ∷ rest) = false
TripleList-isRDFGraph-dec ((_ , Var v , _ ) ∷ rest) = false
TripleList-isRDFGraph-dec ((_ , _ , Var v) ∷ rest) = false
TripleList-isRDFGraph-dec ((_ , _ , _ ) ∷ rest) = TripleList-isRDFGraph-dec rest

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

data URI : Set where
 cons : String → URI

data Literal : Set where
 cons : String → Literal

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

Triple-isGrounded-dec : Triple → Bool
Triple-isGrounded-dec (URI-cons s , URI-cons p , URI-cons o) = true
Triple-isGrounded-dec (URI-cons s , URI-cons p , Literal-cons o) = true
Triple-isGrounded-dec t = false

{-
A grounded triplelist contains only grounded triples.
-}
TripleList-isGrounded-dec : TripleList → Bool
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
