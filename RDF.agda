module RDF where

open import Agda.Primitive
open import BaseLogic
open import Data.String
open import Data.List
open import Data.Bool
open import SetTheory


{-
The RDF model-theoretic semantics:
https://www.w3.org/TR/rdf-mt/
RDF 1.1:
https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/
-}

_∘_ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} (g : B → C) (f : A → B) → A → C
_∘_ {i} {j} {k} {A} {B} {C} g f a = g (f a)


{-
   if (S a) then 
    <would like to have a proof here that S a ≡ true> 
   else
    <would like to have a proof here that S a ≡ false>

  Because we'd like to conditionally call functions that may require
  a proof of S a ≡ true in one branch and S a ≡ false in the other.

  To do this we can use `with` and `inspect`.
-}

data Singleton {α} {A : Set α} (x : A) : Set α where
 _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {α} {A : Set α} (x : A) → Singleton x
inspect x = x with≡ refl x


{-
RDF 1.1 Concepts
https://www.w3.org/TR/rdf11-concepts/
-}



{-
Literal values
-}

LV : Set
LV = String

URIRef : Set
URIRef = String

IRI : Set
IRI = String

RDFName : Set
RDFName = IRI ⊹ LV

{-
Blank nodes??
-}

RDFVocabulary : Set₁
RDFVocabulary = Powerset URIRef

RDFVocabulary' : Set
RDFVocabulary' = Powerset' URIRef




{-
Section 1.3
...
A simple interpretation I of a vocabulary V is defined by:

1. A non-empty set IR of resources, called the domain or universe of I
2. A mapping IEXT from IR into the powerset of IR × (IR union LV) i.e. the set
   of sets of pairs <x,y> with x in IR and y in IR or LV
3. A mapping IS from V into IR
-}

record SimpleInterpretation (V : RDFVocabulary) : Set₁ where
 field
  IR : Set
  IS : (∃ w ∈ URIRef , ∥ V w ∥) → IR
  IEXT : IR → Powerset (IR × (IR ⊹ LV))


record SimpleInterpretation' (V : RDFVocabulary') : Set₁ where
 field
  IR : Set
  IS : (∃ w ∈ URIRef , ∥ (V w) ≡ true ∥) → IR
  IEXT : IR → Powerset' (IR × (IR ⊹ LV))

record GroundRDFTriple : Set where
 field
  s : URIRef
  p : URIRef
  o : URIRef ⊹ LV 

-- This won't do, because it allows repeated triples and is not order-independent
GroundRDFGraph : Set
GroundRDFGraph = List GroundRDFTriple

-- This works but graph-membership is not necessarily decidable
GroundRDFGraph' : Set₁
GroundRDFGraph' = Powerset GroundRDFTriple

-- This works and graph-membership is decidable.
GroundRDFGraph'' : Set
GroundRDFGraph'' = Powerset' GroundRDFTriple


EmptyGroundRDFGraph : GroundRDFGraph
EmptyGroundRDFGraph = []

EmptyGroundRDFGraph'' : GroundRDFGraph''
EmptyGroundRDFGraph'' = EmptySet' GroundRDFTriple


Denotation-Literal : {V : RDFVocabulary} (I : SimpleInterpretation V) → LV → LV
Denotation-Literal {V} I lv = lv

Denotation-Literal' : {V : RDFVocabulary'} (I : SimpleInterpretation' V) → LV → LV
Denotation-Literal' {V} I lv = lv




Denotation-URIRef : {V : RDFVocabulary} (I : SimpleInterpretation V) → (u : URIRef) → (v : V u) → SimpleInterpretation.IR I
Denotation-URIRef {V} I u v = (SimpleInterpretation.IS I) (u , squash v)

Denotation-URIRef' : {V : RDFVocabulary'} (I : SimpleInterpretation' V) → (u : URIRef) → (v : (V u) ≡ true) → SimpleInterpretation'.IR I
Denotation-URIRef' {V} I u v = (SimpleInterpretation'.IS I) (u , squash v)


-- How does this desugar?
Denotation-URIRef'' : {V : RDFVocabulary'} (I : SimpleInterpretation' V) → (u : URIRef) → (SimpleInterpretation'.IR I) ⊹ Bool
Denotation-URIRef'' {V} I uri with inspect (V uri) 
...                              | true  with≡ eq = inl ((SimpleInterpretation'.IS I) (uri , squash eq))
...                              | false with≡ eq = inr false


Denotation-GroundObject' : {V : RDFVocabulary'} (I : SimpleInterpretation' V) → (o : URIRef ⊹ LV) → ((SimpleInterpretation'.IR I) ⊹ Bool) ⊹ LV
Denotation-GroundObject' {V} I (inl uri) = inl (Denotation-URIRef'' I uri)
Denotation-GroundObject' {V} I (inr lv)  = inr (Denotation-Literal' I lv)


-- true if <I(s),I(o)> ∈ IEXT(I(p))
-- false otherwise
Denotation-Triple : {V : RDFVocabulary'} (I : SimpleInterpretation' V) → (t : GroundRDFTriple) → Bool
Denotation-Triple {V} I t with (Denotation-URIRef'' I (GroundRDFTriple.s t)) | (Denotation-URIRef'' I (GroundRDFTriple.p t)) | (Denotation-GroundObject' I (GroundRDFTriple.o t))
...                          | (inl s)         | (inl p)     | (inl (inl o))  = ((SimpleInterpretation'.IEXT I) p) (s , (inl o))
...                          | (inl s)         | (inl p)     | (inl (inr o))  = false
...                          | (inl s)         | (inl p)     | (inr o)        = ((SimpleInterpretation'.IEXT I) p) (s , (inr o))
...                          | (inr s)         | _           | _              = false
...                          | _               | (inr p)     | _              = false

Denotation-Graph : {V : RDFVocabulary'} (I : SimpleInterpretation' V) → (g : GroundRDFGraph) → Bool
Denotation-Graph {V} I []       = true
Denotation-Graph {V} I (t ∷ ts) = (Denotation-Triple I t) and (Denotation-Graph I ts)

