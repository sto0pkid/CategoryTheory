module GuidoLiterate where

open import Agda.Primitive
open import BaseLogic
open import Data.Bool
open import Data.Bool.Proofs
open import Data.Disjunction
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.PropositionalEquality
open import Data.False
open import Data.True
open import Functions


record Start : Set₁ where
 field
  dummy : ⊤

start-interp : Start
start-interp =
 record {
  dummy = ●
 }

{-
S-5.2,pr-2,s-3:
A triple is composed of a subject, a property, and an object.
-}
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

upto-S-5,2/pr-2/s-3-interp : upto-S-5,2/pr-2/s-3
upto-S-5,2/pr-2/s-3-interp =
 record {
  triple = Nat × (Nat × Nat) ;
  subject = Nat ;
  property = Nat ;
  object = Nat ;
  triple-component-subject = first ;
  triple-component-property = first ∘ second ;
  triple-component-object = second ∘ second ;
  triple-all-possible-components = λ s → (λ p → (λ o → ((s , (p , o)) , (refl , (refl , refl)))))
 }
 
{-
S-5.2,pr-2,s-4:
A triplelist is a list of triples.
-}
record upto-S-5,2/pr-2/s-4 : Set₁ where
 field
  triple : Set
  subject : Set
  property : Set
  object : Set
  triple-component-subject : triple → subject
  triple-component-property : triple → property
  triple-component-object : triple → object
  triple-all-possible-components : (s : subject) → (p : property) → (o : object) → ∃ t ∈ triple , ((triple-component-subject t ≡ s) ∧ (triple-component-property t ≡ p) ∧ (triple-component-object t ≡ o))
  triplelist : Set
  triplelist-def : triplelist ≡ List triple

upto-S-5,2/pr-2/s-4-interp : upto-S-5,2/pr-2/s-4
upto-S-5,2/pr-2/s-4-interp =
 record {
  triple = Nat × (Nat × Nat) ;
  subject = Nat ;
  property = Nat ;
  object = Nat ;
  triple-component-subject = first ;
  triple-component-property = first ∘ second ;
  triple-component-object = second ∘ second ;
  triple-all-possible-components = λ s → (λ p → (λ o → ((s , (p , o)) , (refl , (refl , refl))))) ;
  triplelist = List (Nat × (Nat × Nat)) ;
  triplelist-def = refl
 }

 
{-
S-5.2,pr-2,s-5:
Subject, property, and object can have as value a URI, a blank node, or a triplelist.
-}
record upto-S-5,2/pr-2/s-5 : Set₁ where
 field
  triple : Set
  subject : Set
  property : Set
  object : Set
  triple-component-subject : triple → subject
  triple-component-property : triple → property
  triple-component-object : triple → object
  triple-all-possible-components : (s : subject) → (p : property) → (o : object) → ∃ t ∈ triple , ((triple-component-subject t ≡ s) ∧ (triple-component-property t ≡ p) ∧ (triple-component-object t ≡ o))
  triplelist : Set
  triplelist-def : triplelist ≡ List triple
  URI : Set
  blank-node : Set
  subject-def : subject ≡ (URI ⊹ (blank-node ⊹ triplelist))
  property-def : property ≡ (URI ⊹ (blank-node ⊹ triplelist))
  object-def : object ≡ (URI ⊹ (blank-node ⊹ triplelist))



data triple-interp : Set

triplelist-interp : Set
triplelist-interp = List triple-interp

URI-interp : Set
URI-interp = Nat

blank-node-interp : Set
blank-node-interp = Nat

subject-interp : Set
subject-interp = URI-interp ⊹ (blank-node-interp ⊹ triplelist-interp)

property-interp : Set
property-interp = URI-interp ⊹ (blank-node-interp ⊹ triplelist-interp)

object-interp : Set
object-interp = URI-interp ⊹ (blank-node-interp ⊹ triplelist-interp)

data triple-interp where
 _,_,_ : subject-interp → property-interp → object-interp → triple-interp

triple-component-subject-interp : triple-interp → subject-interp
triple-component-subject-interp (s , _ , _ ) = s

triple-component-property-interp : triple-interp → property-interp
triple-component-property-interp (_ , p , _ ) = p

triple-component-object-interp : triple-interp → object-interp
triple-component-object-interp (_ , _ , o) = o

upto-S-5,2/pr-2/s-5-interp : upto-S-5,2/pr-2/s-5
upto-S-5,2/pr-2/s-5-interp = 
 record {
  triple = triple-interp ;
  subject = subject-interp ;
  property = property-interp ;
  object = object-interp ;
  triple-component-subject = triple-component-subject-interp ;
  triple-component-property = triple-component-property-interp ;
  triple-component-object = triple-component-object-interp ;
  triple-all-possible-components = λ s → (λ p → (λ o → ((s , p , o) , (refl , (refl , refl))))) ;
  triplelist = triplelist-interp ;
  triplelist-def = refl ;
  URI = URI-interp ;
  blank-node = blank-node-interp ;
  subject-def = refl ;
  property-def = refl ;
  object-def = refl 
 }


{-
S-5.2,pr-2,s-6:
An object can also be a literal.
-}
record upto-S-5,2/pr-2/s-6 : Set₁ where
 field
  triple : Set
  subject : Set
  property : Set
  object : Set
  triple-component-subject : triple → subject
  triple-component-property : triple → property
  triple-component-object : triple → object
  triple-all-possible-components : (s : subject) → (p : property) → (o : object) → ∃ t ∈ triple , ((triple-component-subject t ≡ s) ∧ (triple-component-property t ≡ p) ∧ (triple-component-object t ≡ o))
  triplelist : Set
  triplelist-def : triplelist ≡ List triple
  URI : Set
  blank-node : Set
  subject-def : subject ≡ (URI ⊹ (blank-node ⊹ triplelist))
  property-def : property ≡ (URI ⊹ (blank-node ⊹ triplelist))
  object-def : object ≡ (URI ⊹ (blank-node ⊹ triplelist))
  literal : Set
  object-def₂ : object ≡ (URI ⊹ (blank-node ⊹ (triplelist ⊹ literal)))
  
{-
This last modification renders the world unsatisfiable, because
`object-def : object ≡ (URI ⊹ (blank-node ⊹ triplelist))` is inconsistent with
`object-def₂ : object ≡ (URI ⊹ (blank-node ⊹ (triplelist ⊹ literal)))`

The problem is that _≡_ is too strict of a statement to use here: it does not allow
for extensibility and defeasibility of definitions. How can we capture the extensibility
and defeasibility of definitions?

"Subject can have URI as a value" could mean that for every URI, there's a corresponding
  subject, you can determine whether a subject has a URI as a value, and if a subject has
a URI as a value then you can retrieve that URI. No two URIs correspond to the same
subject. 

subject-type-label : Set
subject-type-interpretation : subject-type-label → Set
subject-val-type : subject → subject-type-label

subject-URI-type-label : ∃ label ∈ subject-type-label , (subject-type-interpretation label ≡ URI)
subject-URI-cons : URI → subject
subject-URI-cons-inj : injective subject-URI-cons
subject-get-URI-val : (s : subject) → subject-type-interpretation (subject-val-type s) ≡ URI → URI

subject-blank-node-type-label : ∃ label ∈ subject-type-label , (subject-type-interpretation label ≡ blank-node)
subject-blank-node-cons : blank-node → subject
subject-blank-node-cons-inj : injective subject-blank-node-cons
subject-get-blank-node-val : (s : subject) → subject-type-interpretation (subject-val-type s) ≡ blank-node → blank-node

subject-triplelist-type-label : ∃ label ∈ subject-triplelist-label , (subject-type-interpretation label ≡ triplelist)
subject-triplelist-cons : triplelist → subject
subject-triplelist-cons-inj : injective subject-triplelist-cons
subject-get-triplelist-val : (s : subject) → subject-type-interpretation (subject-val-type s) ≡ triplelist → triplelist


-}

{-
injective : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → Set (i ⊔ j)
injective {i} {j} {A} {B} f = (a1 a2 : A) → (f a1) ≡ (f a2) → a1 ≡ a2
-}

record ExtensibleType : Set₁ where
 field
  carrier : Set
  type-label : Set
  val-type : carrier → type-label
  type-interpretation : type-label → Set
  get-val : (x : carrier) → type-interpretation (val-type x)

record TypeExtension (T : ExtensibleType) (A : Set) : Set₁ where
 field
  type-label : ∃ label ∈ (ExtensibleType.type-label T) , ((ExtensibleType.type-interpretation T) label ≡ A)
  cons : A → (ExtensibleType.carrier T)
  cons-inj : injective cons
  cons-type : (a : A) → (ExtensibleType.type-interpretation T) ((ExtensibleType.val-type T) (cons a)) ≡ A
  get-val : (x : (ExtensibleType.carrier T)) → (ExtensibleType.type-interpretation T) ((ExtensibleType.val-type T) x) ≡ A → A 
  get-val-harmony-elim : (x : (ExtensibleType.carrier T)) → (p : ((ExtensibleType.type-interpretation T) ((ExtensibleType.val-type T) x) ≡ A)) → x ≡ cons (get-val x p)
  get-val-harmony-intro : (a : A) → get-val (cons a) (cons-type a) ≡ a


data List₂ (E : ExtensibleType) : Set where
 [] : List₂ E
 _∷_ : (ExtensibleType.carrier E) → List₂ E → List₂ E
{-
So why would we want to use these? Because we want to be able to operate under the following assumptions:
1) Every sentence describes a modification to a set of constraints describing a set of possible worlds.
2) No untruths are being spoken.
3) A set of multiple partial definitions of a concept must be able to exist together consistently.
-}

{-
Sentence 1:
A triple is composed of a subject, a property, and an object.
-}

record upto-S1-1 : Set₁ where
 field 
  triple : ExtensibleType
  subject : ExtensibleType
  property : ExtensibleType
  object : ExtensibleType
  triple-component-subject : ExtensibleType.carrier triple → ExtensibleType.carrier subject
  triple-component-property : ExtensibleType.carrier triple → ExtensibleType.carrier property
  triple-component-object : ExtensibleType.carrier triple → ExtensibleType.carrier object
  triple-all-possible-components : (s : (ExtensibleType.carrier subject)) → (p : (ExtensibleType.carrier property)) → (o : (ExtensibleType.carrier object)) → ∃ t ∈ (ExtensibleType.carrier triple) , ((triple-component-subject t ≡ s) ∧ (triple-component-property t ≡ p) ∧ (triple-component-object t ≡ o))


upto-S1-1-interp : upto-S1-1
upto-S1-1-interp =
 record {
  triple = record {
   carrier = Nat × (Nat × Nat) ;
   type-label = ⊤ ;
   val-type = λ t → ● ;
   type-interpretation = λ label → Nat × (Nat × Nat) ;
   get-val = λ t → t
  } ;
  subject = record {
   carrier = Nat ;
   type-label = ⊤ ;
   val-type = λ s → ● ;
   type-interpretation = λ label → Nat ;
   get-val = λ s → s
  } ;
  property = record {
   carrier = Nat ;
   type-label = ⊤ ;
   val-type = λ p → ● ;
   type-interpretation = λ label → Nat ;
   get-val = λ p → p
  } ;
  object = record {
   carrier = Nat ;
   type-label = ⊤ ;
   val-type = λ o → ● ;
   type-interpretation = λ label → Nat ;
   get-val = λ o → o
  } ;
  triple-component-subject = first ;
  triple-component-property = first ∘ second ;
  triple-component-object = second ∘ second ;
  triple-all-possible-components = λ s → (λ p → (λ o → ((s , (p , o)) , (refl , (refl , refl)))))
 }

{-
Sentence 2:
A triplelist is a list of triples.
-}

record upto-S2-1 : Set₁ where
 field 
  triple : ExtensibleType
  subject : ExtensibleType
  property : ExtensibleType
  object : ExtensibleType
  triple-component-subject : ExtensibleType.carrier triple → ExtensibleType.carrier subject
  triple-component-property : ExtensibleType.carrier triple → ExtensibleType.carrier property
  triple-component-object : ExtensibleType.carrier triple → ExtensibleType.carrier object
  triple-all-possible-components : (s : (ExtensibleType.carrier subject)) → (p : (ExtensibleType.carrier property)) → (o : (ExtensibleType.carrier object)) → ∃ t ∈ (ExtensibleType.carrier triple) , ((triple-component-subject t ≡ s) ∧ (triple-component-property t ≡ p) ∧ (triple-component-object t ≡ o))
  triplelist : ExtensibleType
  triplelist-def : TypeExtension triplelist (List (Nat × (Nat × Nat)))

upto-S2-1-interp : upto-S2-1
upto-S2-1-interp =
 record {
    triple = record {
   carrier = Nat × (Nat × Nat) ;
   type-label = ⊤ ;
   val-type = λ t → ● ;
   type-interpretation = λ label → Nat × (Nat × Nat) ;
   get-val = λ t → t
  } ;
  subject = record {
   carrier = Nat ;
   type-label = ⊤ ;
   val-type = λ s → ● ;
   type-interpretation = λ label → Nat ;
   get-val = λ s → s
  } ;
  property = record {
   carrier = Nat ;
   type-label = ⊤ ;
   val-type = λ p → ● ;
   type-interpretation = λ label → Nat ;
   get-val = λ p → p
  } ;
  object = record {
   carrier = Nat ;
   type-label = ⊤ ;
   val-type = λ o → ● ;
   type-interpretation = λ label → Nat ;
   get-val = λ o → o
  } ;
  triple-component-subject = first ;
  triple-component-property = first ∘ second ;
  triple-component-object = second ∘ second ;
  triple-all-possible-components = λ s → (λ p → (λ o → ((s , (p , o)) , (refl , (refl , refl))))) ;
  triplelist = record {
   carrier = List (Nat × (Nat × Nat)) ;
   type-label = ⊤ ;
   val-type = λ tl → ● ;
   type-interpretation = λ label → List (Nat × (Nat × Nat)) ;
   get-val = λ tl → tl
  } ;
  triplelist-def = record {
   type-label = (● , refl) ;
   cons = λ tl → tl ;
   cons-inj = λ a1 → (λ a2 → (λ [fa1≡fa2] → [fa1≡fa2])) ;
   cons-type = λ tl → refl ;
   get-val = λ tl → (λ right-type → tl) ;
   get-val-harmony-elim = λ tl → (λ right-type → refl) ;
   get-val-harmony-intro = λ tl → refl
  }
 }

{-
Sentence 3: 
Subject, property, and object can have as value a URI, a blank node, or a triplelist.
-}

record upto-S3-1 : Set₁ where
 field 
  triple : ExtensibleType
  subject : ExtensibleType
  property : ExtensibleType
  object : ExtensibleType
  triple-component-subject : ExtensibleType.carrier triple → ExtensibleType.carrier subject
  triple-component-property : ExtensibleType.carrier triple → ExtensibleType.carrier property
  triple-component-object : ExtensibleType.carrier triple → ExtensibleType.carrier object
  triple-all-possible-components : (s : (ExtensibleType.carrier subject)) → (p : (ExtensibleType.carrier property)) → (o : (ExtensibleType.carrier object)) → ∃ t ∈ (ExtensibleType.carrier triple) , ((triple-component-subject t ≡ s) ∧ (triple-component-property t ≡ p) ∧ (triple-component-object t ≡ o))
  triplelist : ExtensibleType
  triplelist-def : TypeExtension triplelist (List (ExtensibleType.carrier triple))
  URI : ExtensibleType
  blank-node : ExtensibleType
  subject-def₁ : TypeExtension subject (ExtensibleType.carrier URI)
  subject-def₂ : TypeExtension subject (ExtensibleType.carrier blank-node)
  subject-def₃ : TypeExtension subject (ExtensibleType.carrier triplelist)
  property-def₁ : TypeExtension property (ExtensibleType.carrier URI)
  property-def₂ : TypeExtension property (ExtensibleType.carrier blank-node)
  property-def₃ : TypeExtension property (ExtensibleType.carrier triplelist)
  object-def₁ : TypeExtension object (ExtensibleType.carrier URI)
  object-def₂ : TypeExtension object (ExtensibleType.carrier blank-node)
  object-def₃ : TypeExtension object (ExtensibleType.carrier triplelist)

data triple-interp₂ : Set

triplelist-interp₂ : Set
triplelist-interp₂ = List triple-interp₂

URI-interp₂ : Set
URI-interp₂ = Nat

blank-node-interp₂ : Set
blank-node-interp₂ = Nat

subject-interp₂ : Set
subject-interp₂ = URI-interp₂ ⊹ (blank-node-interp₂ ⊹ triplelist-interp₂)

property-interp₂ : Set
property-interp₂ = URI-interp₂ ⊹ (blank-node-interp₂ ⊹ triplelist-interp₂)

object-interp₂ : Set
object-interp₂ = URI-interp₂ ⊹ (blank-node-interp₂ ⊹ triplelist-interp₂)

data triple-interp₂ where
 _,_,_ : subject-interp₂ → property-interp₂ → object-interp₂ → triple-interp₂

triple-component-subject-interp₂ : triple-interp₂ → subject-interp₂
triple-component-subject-interp₂ (s , _ , _ ) = s

triple-component-property-interp₂ : triple-interp₂ → property-interp₂
triple-component-property-interp₂ (_ , p , _ ) = p

triple-component-object-interp₂ : triple-interp₂ → object-interp₂
triple-component-object-interp₂ (_ , _ , o) = o

data resource-type-labels : Set where
 uri : resource-type-labels
 bnode : resource-type-labels
 triplelist : resource-type-labels

is-uri : resource-type-labels → Bool
is-uri uri = true
is-uri bnode = false
is-uri triplelist = false

is-bnode : resource-type-labels → Bool
is-bnode uri = false
is-bnode bnode = true
is-bnode triplelist = false

is-triplelist : resource-type-labels → Bool
is-triplelist uri = false
is-triplelist bnode = false
is-triplelist triplelist = true

uri≠bnode : uri ≠ bnode
uri≠bnode [uri≡bnode] = true≠false ([x≡y]→[fx≡fy] is-uri uri bnode [uri≡bnode])

uri≠triplelist : uri ≠ triplelist
uri≠triplelist [uri≡triplelist] = true≠false ([x≡y]→[fx≡fy] is-uri uri triplelist [uri≡triplelist])

bnode≠triplelist : bnode ≠ triplelist
bnode≠triplelist [bnode≡triplelist] = true≠false ([x≡y]→[fx≡fy] is-bnode bnode triplelist [bnode≡triplelist])

resource-type-labels-interp : resource-type-labels → Set
resource-type-labels-interp uri = URI-interp₂
resource-type-labels-interp bnode = blank-node-interp₂
resource-type-labels-interp triplelist = triplelist-interp₂

subject-type-label-interp : subject-interp₂ → resource-type-labels
subject-type-label-interp (inl v) = uri
subject-type-label-interp (inr (inl v)) = bnode
subject-type-label-interp (inr (inr v)) = triplelist

subject-get-val : (s : subject-interp₂) → (resource-type-labels-interp (subject-type-label-interp s))
subject-get-val (inl v) = v
subject-get-val (inr (inl v)) = v
subject-get-val (inr (inr v)) = v

subject-get-uri : (s : subject-interp₂) → (subject-type-label-interp s ≡ uri) → URI-interp₂
subject-get-uri (inl v) [s-label≡uri] = v
subject-get-uri (inr (inl v)) [s-label≡uri] = ω ((≠-sym uri≠bnode) [s-label≡uri])
subject-get-uri (inr (inr v)) [s-label≡uri] = ω ((≠-sym uri≠triplelist) [s-label≡uri])

property-type-label-interp : property-interp₂ → resource-type-labels
property-type-label-interp (inl v) = uri
property-type-label-interp (inr (inl v)) = bnode
property-type-label-interp (inr (inr v)) = triplelist

property-get-val : (p : property-interp₂) → (resource-type-labels-interp (property-type-label-interp p))
property-get-val (inl v) = v
property-get-val (inr (inl v)) = v
property-get-val (inr (inr v)) = v

object-type-label-interp : object-interp₂ → resource-type-labels
object-type-label-interp (inl v) = uri
object-type-label-interp (inr (inl v)) = bnode
object-type-label-interp (inr (inr v)) = triplelist

object-get-val : (o : object-interp₂) → (resource-type-labels-interp (object-type-label-interp o))
object-get-val (inl v) = v
object-get-val (inr (inl v)) = v
object-get-val (inr (inr v)) = v

inl-inj : ∀ {i j} {A : Set i} {B : Set j} → injective {i} {i ⊔ j} {A} {A ⊹ B} inl 
inl-inj {i} {j} {A} {B} a .a refl = refl

inr-inj : ∀ {i j} {A : Set i} {B : Set j} → injective {j} {i ⊔ j} {B} {A ⊹ B} inr
inr-inj {i} {j} {A} {B} b .b refl = refl

inr∘inl-inj : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → injective {j} {i ⊔ (j ⊔ k)} {B} {A ⊹ (B ⊹ C)} (inr ∘ inl)
inr∘inl-inj {i} {j} {k} {A} {B} {C} b .b refl = refl

inr∘inr-inj : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → injective {k} {i ⊔ (j ⊔ k)} {C} {A ⊹ (B ⊹ C)} (inr ∘ inr)
inr∘inr-inj {i} {j} {k} {A} {B} {C} c .c refl = refl



upto-S3-1-interp : upto-S3-1
upto-S3-1-interp =
 record {
  triple = record {
   carrier = triple-interp₂ ;
   type-label = ⊤ ;
   val-type = λ t → ● ;
   type-interpretation = λ label → triple-interp₂ ;
   get-val = λ t → t
  } ;
  subject = record {
   carrier = subject-interp₂ ;
   type-label = resource-type-labels ;
   val-type = subject-type-label-interp ;
   type-interpretation = resource-type-labels-interp ;
   get-val = subject-get-val
  } ;
  property = record {
   carrier = property-interp₂ ;
   type-label = resource-type-labels ;
   val-type = property-type-label-interp ;
   type-interpretation = resource-type-labels-interp ;
   get-val = property-get-val 
  } ;
  object = record {
   carrier = object-interp₂ ;
   type-label = resource-type-labels ;
   val-type = object-type-label-interp ;
   type-interpretation = resource-type-labels-interp ;
   get-val = object-get-val
  } ;
  triple-component-subject = triple-component-subject-interp₂ ;
  triple-component-property = triple-component-property-interp₂ ;
  triple-component-object = triple-component-object-interp₂ ;
  triple-all-possible-components = λ s → (λ p → (λ o → ((s , p , o) , (refl , (refl , refl))))) ;
  triplelist = record {
   carrier = triplelist-interp₂ ;
   type-label = ⊤ ;
   val-type = λ tl → ● ;
   type-interpretation = λ label → triplelist-interp₂ ;
   get-val = λ tl → tl
  } ;

{-
record TypeExtension (T : ExtensibleType) (A : Set) : Set₁ where
 field
  type-label : ∃ label ∈ (ExtensibleType.type-label T) , ((ExtensibleType.type-interpretation T) label ≡ A)
  cons : A → (ExtensibleType.carrier T)
  cons-inj : injective cons
  cons-type : (a : A) → (ExtensibleType.type-interpretation T) ((ExtensibleType.val-type T) (cons a)) ≡ A
  get-val : (x : (ExtensibleType.carrier T)) → (ExtensibleType.type-interpretation T) ((ExtensibleType.val-type T) x) ≡ A → A 
  get-val-harmony-elim : (x : (ExtensibleType.carrier T)) → (p : ((ExtensibleType.type-interpretation T) ((ExtensibleType.val-type T) x) ≡ A)) → x ≡ cons (get-val x p)
  get-val-harmony-intro : (a : A) → get-val (cons a) (cons-type a) ≡ a
-}

  triplelist-def = record {
   type-label = (● , refl) ;
   cons = λ tl → tl ;
   cons-inj = λ a1 → (λ a2 → (λ [fa1≡fa2] → [fa1≡fa2])) ;
   cons-type = λ tl → refl ;
   get-val = λ tl → (λ right-type → tl) ;
   get-val-harmony-elim = λ tl → (λ right-type → refl) ;
   get-val-harmony-intro = λ tl → refl
  } ;
  URI = record {
   carrier = URI-interp₂ ;
   type-label = ⊤ ;
   val-type = λ uri → ● ;
   type-interpretation = λ label → URI-interp₂ ;
   get-val = λ uri → uri 
  } ;
  blank-node = record {
   carrier = blank-node-interp₂ ;
   type-label = ⊤ ;
   val-type = λ bnode → ● ;
   type-interpretation = λ label → blank-node-interp₂ ;
   get-val = λ bnode → bnode
  } ;
  subject-def₁ = record {
   type-label = (uri , refl) ;
   cons = inl ;
   cons-inj = inl-inj ;
   cons-type = λ s → refl ;
   get-val = subject-get-uri ;
   get-val-harmony-elim = λ s → (λ right-type → refl) ;
   get-val-harmony-intro = λ s → refl
  }
  {-
  subject-def₂ : TypeExtension subject blank-node
  subject-def₃ : TypeExtension subject triplelist
  property-def₁ : TypeExtension property URI
  property-def₂ : TypeExtension property blank-node
  property-def₃ : TypeExtension property triplelist
  object-def₁ : TypeExtension object URI
  object-def₂ : TypeExtension object blank-node
  object-def₃ : TypeExtension object triplelist
-}
 }

