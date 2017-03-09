module RDF11MT where

open import Agda.Primitive
open import BaseLogic
open import Data.Disjunction
open import Data.Product
open import Data.PropositionalEquality
open import SetTheory

{-
record hmm : Set₃ where
 field
  triple : Set
  subject : Set
  predicate : Set
  object : Set
  triple-def : triple ≡ subject × predicate × object
  graph : Set₁
  graph-def : graph ≡ Subset {lzero} {lzero} triple
  Resource : Set
  IRI : Set
  Literal : Set
  blank-node : Set
  node : Set
  node-def : node ≡ IRI ⊹ (Literal ⊹ blank-node)
  subject-def : subject ≡ IRI ⊹ blank-node
  predicate-def : predicate ≡ IRI
  object-def : object ≡ IRI ⊹ (Literal ⊹ blank-node)
  denotation-IRI : IRI → Resource
  denotation-Literal : Literal → Resource
  referent : IRI → Resource
  referent-def : referent ≡ denotation-IRI
  literal-value : Literal → Resource
  literal-value-def : literal-value ≡ denotation-Literal
  Datatype : Set
  literal-datatype : Literal → Datatype
  language-tagged-strings : Subset {lzero} {lzero} Literal
  vocabulary : Set₁
  vocabulary-def : vocabulary ≡ Subset {lzero} {lzero} IRI
  dataset : Set₂
  dataset-def : dataset ≡ Subset {lsuc lzero} {lsuc lzero} graph
  statement : Set₁
  statement-def : statement ≡ Set
  
  Entails : (A B : graph) → Set
  Equivalent : (A B : graph) → Set
  Equivalent-def : Equivalent ≡ (λ A → (λ B → (Entails A B) × (Entails B A)))
  Inconsistency : (A : graph) → Set
  Inconsistency 
-}

record RDF11Concepts : Set₃ where
 field 
  triple : Set
  subject : Set
  predicate : Set
  object : Set
  Resource : Set
  -- Unicode; RFC 3987
  -- is actually not a Set but instead the Subset of Unicode strings satisfying the requirements in RFC 3987
  IRI : Set
  denotation-IRI : IRI → Resource
  referent : IRI → Resource
  referent-def : referent ≡ denotation-IRI

  -- is not a Set but instead the Subset of Unicode strings satisfying the definition in RDF11Concepts section 3.3 Literals
  literal : Set
  denotation-literal : literal → Resource
  literal-value : literal → Resource
  literal-value-def : literal-value ≡ denotation-literal
  -- Unicode String; Normal Form C
  lexical-form : Set
  data-type-IRI : Subset {lzero} {lzero} IRI
  datatype : Set
  lexical-space : datatype → Set
  value-space : datatype → Set
  lexical-to-value-mapping : (dt : datatype) → (lexical-space dt) → (value-space dt)
  -- section 2.2.9 of [BCP47]
  language-tag : Set
  literal-def : literal ≡  (lexical-form × (∃ dt ∈ IRI , (data-type-IRI dt))) ⊹ (lexical-form × (∃ dt ∈ IRI , (data-type-IRI dt)) × language-tag)
  XMLSchema#String : ∃ iri ∈ IRI , (data-type-IRI iri) 
  simple-literal : Set
  simple-literal-def : simple-literal ≡ lexical-form

  -- note how Agda doesn't know that simple-literal ≡ lexical-form. maybe we can use coercion?
  lexical-form-to-literal : lexical-form →  (lexical-form × (∃ dt ∈ IRI , (data-type-IRI dt))) ⊹ (lexical-form × (∃ dt ∈ IRI , (data-type-IRI dt)) × language-tag)
  lexical-form-to-literal-def : lexical-form-to-literal ≡ λ lex → (inl (lex , XMLSchema#String))
  language-tagged-string : Subset' literal
  --language-tagged-string-def : language-tagged-string ≡ λ (inl lit) → false ; (inr lit) → true

  -- we can interpret blank-nodes as a Set rather than a Subset of Unicode strings.
  -- the particular Subset of Unicode strings that correspond to blank-nodes is defined locally per RDF concrete-syntax, not
  -- globally across all RDF applications like IRIs and Literals are.
  -- "Blank nodes are disjoint from IRIs and literals. Otherwise, the set of possible blank nodes is arbitrary. RDF makes no reference to any internal structure of blank nodes."
  -- we might want to attribute some more properties to blank-nodes though; for example, the Set should probably be infinite, but only countably so, and it
  -- might be desirable to distinguish between bnodes.
  blank-node : Set
  subject-def : subject ≡ IRI ⊹ blank-node
  predicate-def : predicate ≡ IRI
  object-def : subject ≡ IRI ⊹ (literal ⊹ blank-node)

  triple-subject : triple → subject
  triple-predicate : triple → predicate
  triple-object : triple → object

  graph : Set₁
  graph-def : graph ≡ Subset {lzero} {lzero} triple
  --should probably have an abstract definition of edge-labeled/node-labeled graphs
  --so that we can map between triple-sets and abstract graphs, as is done in RDF11Concepts

  term : Set
  term-def : term ≡ IRI ⊹ (literal ⊹ blank-node)

  nodes : graph → Set
  --Agda doesn't know that `graph ≡ Subset {lzero} {lzero} triple`, so it can't recognize `g` as a function
  --maybe we can apply coercion
  --nodes-def : nodes ≡ (λ g → ∃ node ∈ term , (∃ t ∈ triple , ((g t) × (((triple-subject t) ≡ node) ⊹ ((triple-object t) ≡ node)))))

  nodes' : Subset {lzero} {lzero} triple → Set
  
  --This still doesn't work because of lack of coherence between `term` and `subject`/`predicate`/`object`:
  -- term !=< subject of type Set when checking that the expression `node` has type `subject.
  --nodes'-def : nodes' ≡ (λ g → ∃ node ∈ term , (∃ t ∈ triple , ((g t) × (((triple-subject t) ≡ node) ⊹ ((triple-object t) ≡ node)))))

  -- RFC3987: Simple String Comparison ("character-by-character", not "bit-by-bit" or "byte-by-byte")
  IRI-equality : IRI → IRI → Set
  lexical-form-equality : lexical-form → lexical-form → Set
  language-tag-equality : language-tag → language-tag → Set
  literal-term-equality : literal → literal → Set
  -- note that we can't enforce the coherence between `lexical-form-equality`, `language-tag-equality` and `literal-term-equality`
  -- needs something like the extensible types from GuidoLiterate

  IRIs-disjoint-from-literals : IRI ≠ literal
  IRIs-disjoint-from-blank-nodes : IRI ≠ blank-node
  literals-disjoint-from-blank-nodes : literal ≠ blank-node
  -- propositional inequality isn't the right notion of disjointness here
  -- each of these is going to be a subset of Unicode strings; we want to make sure those subsets are disjoints using
  -- a notion of disjoint subsets of a the type of Unicode strings

  --skolem-IRIs
  {-
  graph-isomorphism : graph → graph → Set
  graph-isomorphism 
  -}

  dataset : Set₂
  dataset-def : dataset ≡ Subset {lsuc lzero} {lsuc lzero} graph
  default-graph : dataset → graph

  --Once again, Agda doesn't know that dataset ≡ Subset {lsuc lzero} {lsuc lzero} graph
  --named-graphs : (d : dataset) → ∃ S ∈ (Subset {lsuc lzero} {lsuc lzero} graph) , ( [ graph || S ⊂ d ])

  {-
  Dataset comparison
  -} 
