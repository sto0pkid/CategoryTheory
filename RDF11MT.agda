module RDF11MT where

open import Agda.Primitive
open import BaseLogic
open import Data.Disjunction
open import Data.Product
open import Data.PropositionalEquality
open import SetTheory

record RDF11Concepts : Set₃ where
 field 
  triple : Set
  subject : Set
  predicate : Set
  object : Set

  {-
  why don't we say "triple-def : triple ≡ subject × predicate × object" ?
  because this ascribes too much specifics to the representation of triples.
  this formal specification should be as abstract as possible. we shouldn't require
  any specific representation unless it's actually called for in some standards docs.
  we don't care what specific representation you use to store your triples, we only
  care that you can handle all the required behaviors for triples:


  you need to have a constructor function that takes an s, p, o and returns a triple.
  this is essentially the "intro rule" for triples.

  you have projection functions that take a triple and return it's subject or
  its predicate or its object. these are essentially the "elim rules" for triples.

  your intros and elims need to be in "logical harmony", meaning:
  1) if i have an s, p, o and cons- it into a triple, t, then i should be able to
      project the s, p, o back out of it.
  2) if i have a triple t, and project some s, p, o out of it, i should be able to
      cons- these back into the same triple t.
  -}

  Resource : Set

  Unicode-String : Set
  US-ASCII-String : Set
  --US-ASCII is a subset of Unicode, for some appropriate notion of "subset". need to
  -- properly define that notion.


  -- is the subset of Unicode strings satisfying the requirements in RFC 3987
  IRI : Subset {lzero} {lzero} Unicode-String
  denotation-IRI : (∃ s ∈ Unicode-String , (IRI s)) → Resource
  referent : (∃ s ∈ Unicode-String , (IRI s)) → Resource
  referent-def : referent ≡ denotation-IRI

  -- is not a Set but instead the Subset of Unicode strings satisfying the definition in RDF11Concepts section 3.3 Literals
  -- actually literals aren't defined in section 3.3 as a subset of Unicode strings, they're instead defined as complex objects
  -- composed of a 'lexical form', a 'data-type IRI' and optionally a  'language-tag'.
  literal : Set
  denotation-literal : literal → Resource
  literal-value : literal → Resource
  literal-value-def : literal-value ≡ denotation-literal
  literal-syntax : Subset {lzero} {lzero} Unicode-String

  -- Unicode String; Normal Form C
  lexical-form : Subset {lzero} {lzero} Unicode-String
  data-type-IRI : ∃ S ∈ (Subset {lzero} {lzero} Unicode-String) , ( [ Unicode-String || S ⊆ IRI ] )
  datatype : Set
  lexical-space : datatype → Set
  value-space : datatype → Set

  -- this isn't quite how they define it, though it's semantically equivalent to how they define it, and simpler.
  -- they even mention the equivalence. we should use their version though, just for the sake of having
  -- this formalization correspond as directly as possible to what's being described in the RDF 11 Concepts doc.
  lexical-to-value-mapping : (dt : datatype) → (lexical-space dt) → (value-space dt)

  -- section 2.2.9 of [BCP47]
  --language-tags apparently use US-ASCII rather than Unicode ?
  {-"Although [RFC5234] refers to octets, the language tags described in
   this document are sequences of characters from the US-ASCII [ISO646]
   repertoire."
  -}
  language-tag : Subset {lzero} {lzero} US-ASCII-String
  --literal-def : literal ≡  (lexical-form × (∃ dt ∈ IRI , (data-type-IRI dt))) ⊹ (lexical-form × (∃ dt ∈ IRI , (data-type-IRI dt)) × language-tag)
  literal-def : literal ≡ ((∃ lex ∈ Unicode-String , (lexical-form lex)) × (∃ dt-iri ∈ Unicode-String , ((π₁ data-type-IRI) dt-iri))) ⊹ ((∃ lex ∈ Unicode-String , (lexical-form lex)) × (∃ dt-iri ∈ Unicode-String , ((π₁ data-type-IRI) dt-iri)) × (∃ tag ∈ US-ASCII-String , (language-tag tag)))
  XMLSchema#String : ∃ s ∈ Unicode-String , ((π₁ data-type-IRI) s) 
  simple-literal : Subset {lzero} {lzero} Unicode-String
  simple-literal-def : simple-literal ≡ lexical-form

  -- note how Agda doesn't know that simple-literal ≡ lexical-form. maybe we can use coercion?
  lexical-form-to-literal : (∃ lex ∈ Unicode-String , (lexical-form lex)) →  ((∃ lex ∈ Unicode-String , (lexical-form lex)) × (∃ dt ∈ Unicode-String , ((π₁ data-type-IRI) dt))) ⊹ ((∃ lex ∈ Unicode-String , (lexical-form lex)) × (∃ dt ∈ Unicode-String , ((π₁ data-type-IRI) dt)) × (∃ tag ∈ US-ASCII-String , (language-tag tag)))
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
  blank-node-syntax : Subset {lzero} {lzero} Unicode-String

  {-
  subject-def : subject ≡ IRI ⊹ blank-node
  predicate-def : predicate ≡ IRI
  object-def : subject ≡ IRI ⊹ (literal ⊹ blank-node)
  -}
  -- what's the right notion of "or" to use here?
  -- seems to be a subset-union of these syntactic forms of Unicode strings in a given concrete syntax.
  -- this would imply that subject/predicate/object need to be defined as syntactic forms as well.
  subject-syntax : Subset {lzero} {lzero} Unicode-String
  subject-syntax-def : subject-syntax ≡ subsetUnion IRI blank-node-syntax

  predicate-syntax : Subset {lzero} {lzero} Unicode-String
  predicate-syntax-def : predicate-syntax ≡ IRI

  object-syntax : Subset {lzero} {lzero} Unicode-String
  object-syntax-def : object-syntax ≡ subsetUnion IRI (subsetUnion literal-syntax blank-node-syntax)

  {-
  An alternative interpretation is that the resource denoted by a subject can be the resource denoted by
  some IRI, or the resource denoted by some blank-node.
  -}

  {-
  triple-subject : triple → subject
  triple-predicate : triple → predicate
  triple-object : triple → object
  -}
  -- needed to change this up so that we can define `graph-nodes'-def` below..
  triple-subject : triple → ∃ s ∈ Unicode-String , (subject-syntax s)
  triple-predicate : triple → ∃ p ∈ Unicode-String , (predicate-syntax p)
  triple-object : triple → ∃ o ∈ Unicode-String , (object-syntax o)

  graph : Set₁
  graph-def : graph ≡ Subset {lzero} {lzero} triple
  --should probably have an abstract definition of edge-labeled/node-labeled graphs
  --so that we can map between triple-sets and abstract graphs, as is done in RDF11Concepts

  {-
  term : Set
  term-def : term ≡ IRI ⊹ (literal ⊹ blank-node)
  -}
  term : Subset {lzero} {lzero} Unicode-String
  term-def : term ≡ subsetUnion IRI (subsetUnion literal-syntax blank-node-syntax)

  graph-nodes : graph → Set
  --Agda doesn't know that `graph ≡ Subset {lzero} {lzero} triple`, so it can't recognize `g` as a function
  --maybe we can apply coercion
  --nodes-def : nodes ≡ (λ g → ∃ node ∈ term , (∃ t ∈ triple , ((g t) × (((triple-subject t) ≡ node) ⊹ ((triple-object t) ≡ node)))))

  graph-nodes' : Subset {lzero} {lzero} triple → Set
  
  --This still doesn't work because of lack of coherence between `term` and `subject`/`predicate`/`object`:
  -- term !=< subject of type Set when checking that the expression `node` has type `subject.
  graph-nodes'-def : graph-nodes' ≡ (λ g → (∃ node ∈ Unicode-String , ((term node) × (∃ t ∈ triple , ((g t) × (((π₁ (triple-subject t)) ≡ node) ⊹ ((π₁ (triple-object t)) ≡ node)))))))

  -- RFC3987: Simple String Comparison ("character-by-character", not "bit-by-bit" or "byte-by-byte")
  IRI-Simple-String-Comparison : (∃ iri₁ ∈ Unicode-String , (IRI iri₁)) → (∃ iri₂ ∈ Unicode-String , (IRI iri₂)) → Set
  lexical-form-equality : (∃ lex₁ ∈ Unicode-String , (lexical-form lex₁)) → (∃ lex₂ ∈ Unicode-String , (lexical-form lex₂)) → Set
  language-tag-equality : (∃ tag₁ ∈ US-ASCII-String , (language-tag tag₁)) → (∃ tag₂ ∈ US-ASCII-String , (language-tag tag₂)) → Set
  literal-term-equality : literal → literal → Set
  -- note that we can't enforce the coherence between `lexical-form-equality`, `language-tag-equality` and `literal-term-equality`
  -- why exactly can't we do that?
  -- needs something like the extensible types from GuidoLiterate

  {-
  IRIs-disjoint-from-literals : IRI ≠ literal
  IRIs-disjoint-from-blank-nodes : IRI ≠ blank-node
  literals-disjoint-from-blank-nodes : literal ≠ blank-node
  -}
  -- propositional inequality isn't the right notion of disjointness here
  -- each of these is going to be a subset of Unicode strings; we want to make sure those subsets are disjoints using
  -- a notion of disjoint subsets of a the type of Unicode strings

  -- Still not right.
  -- IRIs are a subset of Unicode strings
  -- blank-nodes are an abstract set
  -- literals are complex objects
  -- I think what is meant here is that the syntactic forms for expressing these in a concrete syntax are each disjoint,
  -- i.e. the set of labels that represent IRIs is disjoint from the set of labels representing blank-nodes and both
  -- are disjoint from the set of labels that represent literals.
  -- Need to bring in the relation between the abstract & concrete syntax in order to formalize that (assuming it's
  -- even the right interpretation of the specs..)
  IRIs-disjoint-from-literals : (s : Unicode-String) → ¬ ((subsetIntersection IRI literal-syntax) s)
  IRIs-disjoint-from-blank-nodes : (s : Unicode-String) → ¬ ((subsetIntersection IRI blank-node-syntax) s)
  literals-disjoint-from-blank-nodes : (s : Unicode-String) → ¬ ((subsetIntersection literal-syntax blank-node-syntax) s)

  {-
  An alternative interpretation is to say that the subset of resources denoted by IRIs is disjoint from the subset of resources
  denoted by literals / blank-nodes.
  -}

  --skolem-IRIs: an optional mapping from blank nodes to IRIs
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
