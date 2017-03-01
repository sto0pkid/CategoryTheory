module RDF where

open import Agda.Primitive
--open import BaseLogic
open import Inspection
open import Data.String
open import Data.List
open import Data.Bool
open import Data.Bool.Operations
open import SetTheory
open import Data.Disjunction
open import Data.Product
open import Data.Irrelevance
open import Data.PropositionalEquality

{-
ASCII
UTF-8
UTF-16
UTF-32

Unicode version 9.0.0
http://www.unicode.org/versions/Unicode9.0.0/

URI : RFC 3986
http://www.rfc-base.org/txt/rfc-3986.txt

IRI : RFC 3987
http://www.rfc-base.org/txt/rfc-3987.txt

Language tags: BCP47
https://tools.ietf.org/html/bcp47

-}

{-
The RDF model-theoretic semantics:
https://www.w3.org/TR/rdf-mt/
RDF 1.1:
https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/
-}



{-
RDF 1.1 Concepts
RDF11-CONCEPTS
https://www.w3.org/TR/rdf11-concepts/
-}

{-
RDF Schema
RDF11-SCHEMA
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

module RDF10-Concepts where
 RDFVocabulary : Set₁
 RDFVocabulary = Powerset URIRef

 RDFVocabulary' : Set
 RDFVocabulary' = Powerset' URIRef

module RDF11-Concepts where
 RDFVocabulary : Set₁
 RDFVocabulary = Powerset IRI

 RDFVocabulary' : Set
 RDFVocabulary' = Powerset' IRI

module RDF11-ModelTheory where
 RDFVocabulary : Set₁
 RDFVocabulary = Powerset RDFName
  
 RDFVocabulary' : Set
 RDFVocabulary' = Powerset' RDFName

{-
Blank nodes??
-}

{-
 RDF Vocabulary according to "RDF 1.1 Concepts":
 https://www.w3.org/TR/rdf11-concepts/
 Section 1.4:
 "An RDF vocabulary is a collection of IRIs intended for use in RDF graphs."
-}
RDFVocabulary₁ : Set₁
RDFVocabulary₁ = Powerset URIRef

RDFVocabulary₂ : Set
RDFVocabulary₂ = Powerset' URIRef

RDFVocabulary₃ : Set₁
RDFVocabulary₃ = Powerset IRI

RDFVocabulary₄ : Set
RDFVocabulary₄ = Powerset' IRI

RDFVocabulary₅ : Set₁
RDFVocabulary₅ = Powerset RDFName

RDFVocabulary₆ : Set
RDFVocabulary₆ = Powerset' RDFName



{-
Section 1.3
...
A simple interpretation I of a vocabulary V is defined by:

1. A non-empty set IR of resources, called the domain or universe of I
2. A mapping IEXT from IR into the powerset of IR × (IR union LV) i.e. the set
   of sets of pairs <x,y> with x in IR and y in IR or LV
3. A mapping IS from V into IR
-}

record SimpleInterpretation (V : RDFVocabulary₁) : Set₁ where
 field
  IR : Set
  IS : (∃ w ∈ URIRef , ∥ V w ∥) → IR
  IEXT : IR → Powerset (IR × (IR ⊹ LV))


record SimpleInterpretation' (V : RDFVocabulary₂) : Set₁ where
 field
  IR : Set
  IS : (∃ w ∈ URIRef , ∥ (V w) ≡ true ∥) → IR
  IEXT : IR → Powerset' (IR × (IR ⊹ LV))

record SimpleInterpretation'' (V : RDFVocabulary₆) : Set₁ where
 field
  IR : Set
  IS : (∃ w ∈ RDFName , ∥ (V w) ≡ true ∥) → IR
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


Denotation-Literal : {V : RDFVocabulary₁} (I : SimpleInterpretation V) → LV → LV
Denotation-Literal {V} I lv = lv

Denotation-Literal' : {V : RDFVocabulary₂} (I : SimpleInterpretation' V) → LV → LV
Denotation-Literal' {V} I lv = lv




Denotation-URIRef : {V : RDFVocabulary₁} (I : SimpleInterpretation V) → (u : URIRef) → (v : V u) → SimpleInterpretation.IR I
Denotation-URIRef {V} I u v = (SimpleInterpretation.IS I) (u , squash v)

Denotation-URIRef' : {V : RDFVocabulary₂} (I : SimpleInterpretation' V) → (u : URIRef) → (v : (V u) ≡ true) → SimpleInterpretation'.IR I
Denotation-URIRef' {V} I u v = (SimpleInterpretation'.IS I) (u , squash v)


-- How does this desugar?
Denotation-URIRef'' : {V : RDFVocabulary₂} (I : SimpleInterpretation' V) → (u : URIRef) → (SimpleInterpretation'.IR I) ⊹ Bool
Denotation-URIRef'' {V} I uri with inspect (V uri) 
...                              | true  with≡ eq = inl ((SimpleInterpretation'.IS I) (uri , squash eq))
...                              | false with≡ eq = inr false


Denotation-GroundObject' : {V : RDFVocabulary₂} (I : SimpleInterpretation' V) → (o : URIRef ⊹ LV) → ((SimpleInterpretation'.IR I) ⊹ Bool) ⊹ LV
Denotation-GroundObject' {V} I (inl uri) = inl (Denotation-URIRef'' I uri)
Denotation-GroundObject' {V} I (inr lv)  = inr (Denotation-Literal' I lv)


-- true if <I(s),I(o)> ∈ IEXT(I(p))
-- false otherwise
Denotation-Triple : {V : RDFVocabulary₂} (I : SimpleInterpretation' V) → (t : GroundRDFTriple) → Bool
Denotation-Triple {V} I t with (Denotation-URIRef'' I (GroundRDFTriple.s t)) | (Denotation-URIRef'' I (GroundRDFTriple.p t)) | (Denotation-GroundObject' I (GroundRDFTriple.o t))
...                          | (inl s)         | (inl p)     | (inl (inl o))  = ((SimpleInterpretation'.IEXT I) p) (s , (inl o))
...                          | (inl s)         | (inl p)     | (inl (inr o))  = false
...                          | (inl s)         | (inl p)     | (inr o)        = ((SimpleInterpretation'.IEXT I) p) (s , (inr o))
...                          | (inr s)         | _           | _              = false
...                          | _               | (inr p)     | _              = false

Denotation-Graph : {V : RDFVocabulary₂} (I : SimpleInterpretation' V) → (g : GroundRDFGraph) → Bool
Denotation-Graph {V} I []       = true
Denotation-Graph {V} I (t ∷ ts) = (Denotation-Triple I t) and (Denotation-Graph I ts)

