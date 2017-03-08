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
open import Data.Fin
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

disjunct-return : ∀ {i} {A B : Set i} → A ⊹ B → Set i
disjunct-return {i} {A} {B} (inl a) = A
disjunct-return {i} {A} {B} (inr b) = B

disjunct-getval : ∀ {i} {A B : Set i} → (d : A ⊹ B) → disjunct-return d
disjunct-getval {i} {A} {B} (inl a) = a
disjunct-getval {i} {A} {B} (inr b) = b


-- These two record types allow you to make an extensible disjunction of types
record ExtensibleType : Set₁ where
 field
  -- this is the underlying set
  carrier : Set

  -- this is a set of labels for indicating what kind of value an object in carrier has
  type-label : Set

  -- this takes an object in carrier and tells us what kind of value it is
  val-type : carrier → type-label

  -- this takes a label and tells us the type it refers to
  type-interpretation : type-label → Set
  
  -- this takes an object in carrier and returns its value
  get-val : (x : carrier) → type-interpretation (val-type x)

record TypeExtension (T : ExtensibleType) (A : Set) : Set₁ where
 field
  -- adds a constraint to T saying that there must be a label for values
  -- of type A, and this label must be interpreted by T as indicating the
  -- type A.
  type-label : ∃ label ∈ (ExtensibleType.type-label T) , ((ExtensibleType.type-interpretation T) label ≡ A)

  -- we need to be able to take objects of type A and construct objects
  -- of type T from them
  cons : A → (ExtensibleType.carrier T)

  -- if the constructor function is injective then we can construct a
  -- distinct object of type T for every distinct object of type A
  cons-inj : injective cons

  -- if we construct an object (cons a) of type T from an object a of type
  -- A, then we must be able to recognize (cons a) as having a value of type A.
  cons-type : (a : A) → (ExtensibleType.type-interpretation T) ((ExtensibleType.val-type T) (cons a)) ≡ A

  -- this function should extract the value from an object of type T which has a value of type A
  get-val : (x : (ExtensibleType.carrier T)) → (ExtensibleType.type-interpretation T) ((ExtensibleType.val-type T) x) ≡ A → A

  -- if we have an object x of type T, extract its value, and then construct a new object x' from this extracted value, then
  -- we should have that x == x'
  get-val-harmony-elim : (x : (ExtensibleType.carrier T)) → (p : ((ExtensibleType.type-interpretation T) ((ExtensibleType.val-type T) x)) ≡ A) → x ≡ cons (get-val x p)

  -- if we have an object a of type A and use it to construct an object of type T, and then extract the value from this
  -- object, then we should get out the same value that we put in.
  get-val-harmony-intro : (a : A) → get-val (cons a) (cons-type a) ≡ a



record TypeExtension₂ (T : ExtensibleType) (A : Set) : Set₁ where
 field
  type-label : ∃ label ∈ (ExtensibleType.type-label T) , ((ExtensibleType.type-interpretation T) label ≡ A)
  cons : A → (ExtensibleType.carrier T)
  cons-inj : injective cons
  cons-type : (a : A) → ((ExtensibleType.val-type T) (cons a)) ≡ (π₁ type-label)
  get-val : (x : (ExtensibleType.carrier T)) → ((ExtensibleType.val-type T) x) ≡ (π₁ type-label) → A
  get-val-harmony-elim : (x : (ExtensibleType.carrier T)) → (p : ((ExtensibleType.val-type T) x) ≡ (π₁ type-label)) → x ≡ cons (get-val x p)
  get-val-harmony-intro : (a : A) → get-val (cons a) (cons-type a) ≡ a

type-coerce : ∀ {i} {A B : Set i} → A ≡ B → A → B
type-coerce {i} {A} {.A} refl a = a



record TypeExtension₃ (T : ExtensibleType) (A : Set) : Set₁ where
 field
  type-label : ∃ label ∈ (ExtensibleType.type-label T), ((ExtensibleType.type-interpretation T) label ≡ A)
  cons : A → (ExtensibleType.carrier T)
  cons-inj : injective cons
  cons-type : (a : A) → ((ExtensibleType.val-type T) (cons a)) ≡ (π₁ type-label)
  get-val : (x : (ExtensibleType.carrier T)) → ((ExtensibleType.val-type T) x) ≡ (π₁ type-label) → A
  get-val-harmony-elim : (x : ExtensibleType.carrier T) → (p : ((ExtensibleType.val-type T) x) ≡ (π₁ type-label)) → x ≡ cons (get-val x p)
  get-val-harmony-intro : (a : A) → get-val (cons a) (cons-type a) ≡ a
  get-val-coherence : (x : (ExtensibleType.carrier T)) → (p : ((ExtensibleType.val-type T) x) ≡ (π₁ type-label)) → (type-coerce (π₂ type-label) (type-coerce ([x≡y]→[fx≡fy] (ExtensibleType.type-interpretation T) ((ExtensibleType.val-type T) x) (π₁ type-label) p) ((ExtensibleType.get-val T) x))) ≡  (get-val x p)

--type-interpretation (val-type x)
--(p : ((ExtensibleType.val-type T) x) ≡ (π₁ type-label))
--[x≡y]→[fx≡fy] (ExtensibleType.type-interpretation T) ((ExtensibleType.val-type T) x) (π₁ type-label) p

-- having a separate get-val function for each TypeExtension probably isn't necessary; really we should probably just be
-- adding constraints to the definition of get-val in ExtensibleType


{-
Need conjunctive extensions as well. If we alternate conjunction and disjunction, does it matter which one comes first?
A conjunction can be interpreted as just one of the options of a disjunction.
A disjunction can be interpreted as just one of the components of a conjunction.
So it seems it doesn't matter: if you assume one of them comes first, then the other could have actually came first without
changing anything.
It seems reasonable to take conjunctions as the outer-most layer, since this corresponds to specifications being
a conjunction of statements.

Each component of the conjunction needs:
1) A projection function to extract that value
2) Logical harmony rules; trickier than the disjunctive case because you can't express
    the logical harmony in isolation from the other components. 
3) For every combination of component objects, there should be an object of type T which
    has those components.
4) Needs a cons function; takes an object from each component type and returns an object of type T
    The cons function should be injective
5) projᵢ (cons(..., aᵢ ,...)) = aᵢ, forall i, aᵢ
6) cons (... , projᵢ(x), ....) = x, forall x

There's a set of component types.
The components will be labeled, so this is like a record type.
There will be a set of labels to store these.
There will be an interpretation function that takes a label and returns the type of the component
 corresponding to that label.
Have a general projection function that takes a label and returns the specific projection function
 which projects the record onto the component corresponding to that label.
There will be a general cons function that takes a product of all the component types and returns
 an object of type T (it should be injective).
To add a component, we'll create a type-extension that takes T as a parameter.
The type-extension should assert the existence of a label corresponding to this component
It should also assert that the interpretation function returns the correct type when supplied with this label.


The extensible disjunctions allow us to handle cases like: "An object can be a URI. An object can also be a literal."
 * Relation between disjunction and "being"
The extensible conjunctions allow us to handle cases like "A triple has a subject. A triple also has an object."
 * Relation between conjunction and "having"

There are many situations where an object can be multiple different things (meaning it can have different types), 
but not simultaneously. This is a mutually exclusive disjunction of possibilities. There are also situations where an 
object can be multiple different  things simultaneously. This is still not a conjunction: we don't interpret the object 
as being a tuple where each component is an instance of the object for each different type it can have.

On the other hand, an object can *have* multiple different components simultaneously. This is a conjunction.
From this perspective, it seems reasonable to have disjunction be the outer-most layer when giving the
description of an object.
-}



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
  triplelist-def : TypeExtension₂ triplelist (List (ExtensibleType.carrier triple))
  URI : ExtensibleType
  blank-node : ExtensibleType
  subject-def₁ : TypeExtension₂ subject (ExtensibleType.carrier URI)
  subject-def₂ : TypeExtension₂ subject (ExtensibleType.carrier blank-node)
  subject-def₃ : TypeExtension₂ subject (ExtensibleType.carrier triplelist)
  property-def₁ : TypeExtension₂ property (ExtensibleType.carrier URI)
  property-def₂ : TypeExtension₂ property (ExtensibleType.carrier blank-node)
  property-def₃ : TypeExtension₂ property (ExtensibleType.carrier triplelist)
  object-def₁ : TypeExtension₂ object (ExtensibleType.carrier URI)
  object-def₂ : TypeExtension₂ object (ExtensibleType.carrier blank-node)
  object-def₃ : TypeExtension₂ object (ExtensibleType.carrier triplelist)

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
 uri-label : resource-type-labels
 bnode-label : resource-type-labels
 triplelist-label : resource-type-labels

is-uri : resource-type-labels → Bool
is-uri uri-label = true
is-uri bnode-label = false
is-uri triplelist-label = false

is-bnode : resource-type-labels → Bool
is-bnode uri-label = false
is-bnode bnode-label = true
is-bnode triplelist-label = false

is-triplelist : resource-type-labels → Bool
is-triplelist uri-label = false
is-triplelist bnode-label = false
is-triplelist triplelist-label = true

uri≠bnode : uri-label ≠ bnode-label
uri≠bnode [uri≡bnode] = true≠false ([x≡y]→[fx≡fy] is-uri uri-label bnode-label [uri≡bnode])

uri≠triplelist : uri-label ≠ triplelist-label
uri≠triplelist [uri≡triplelist] = true≠false ([x≡y]→[fx≡fy] is-uri uri-label triplelist-label [uri≡triplelist])

bnode≠triplelist : bnode-label ≠ triplelist-label
bnode≠triplelist [bnode≡triplelist] = true≠false ([x≡y]→[fx≡fy] is-bnode bnode-label triplelist-label [bnode≡triplelist])

URI-interp₂≡bnode-interp₂ : URI-interp₂ ≡ blank-node-interp₂
URI-interp₂≡bnode-interp₂ = refl

coerce-type : ∀ {i} {A B : Set i} → A → A ≡ B → B
coerce-type {i} {A} {.A} a refl = a

resource-type-labels-interp : resource-type-labels → Set
resource-type-labels-interp uri-label = URI-interp₂
resource-type-labels-interp bnode-label = blank-node-interp₂
resource-type-labels-interp triplelist-label = triplelist-interp₂

subject-type-label-interp : subject-interp₂ → resource-type-labels
subject-type-label-interp (inl v) = uri-label
subject-type-label-interp (inr (inl v)) = bnode-label
subject-type-label-interp (inr (inr v)) = triplelist-label

subject-get-val : (s : subject-interp₂) → (resource-type-labels-interp (subject-type-label-interp s))
subject-get-val (inl v) = v
subject-get-val (inr (inl v)) = v
subject-get-val (inr (inr v)) = v

{-
subject-get-uri : (s : subject-interp₂) → (resource-type-labels-interp (subject-type-label-interp s)) ≡ URI-interp₂ → URI-interp₂
subject-get-uri (inl v) [s-label≡uri] = v
subject-get-uri (inr (inl v)) [s-label≡uri] = coerce-type v URI-interp₂≡bnode-interp₂
subject-get-uri (inr (inr v)) [s-label≡uri] = ω ((≠-sym uri≠triplelist) [s-label≡uri])
-}
subject-get-uri₂ : (s : subject-interp₂) → (subject-type-label-interp s) ≡ uri-label → URI-interp₂
subject-get-uri₂ (inl v) [s-label≡uri] = v
subject-get-uri₂ (inr (inl v)) [s-label≡uri] = ω ((≠-sym uri≠bnode) [s-label≡uri])
subject-get-uri₂ (inr (inr v)) [s-label≡uri] = ω ((≠-sym uri≠triplelist) [s-label≡uri])

subject-uri-elim-harmony : (s : subject-interp₂) → (p : (subject-type-label-interp s) ≡ uri-label) → s ≡ inl (subject-get-uri₂ s p)
subject-uri-elim-harmony (inl v) [s-label≡uri] = refl
subject-uri-elim-harmony (inr (inl v)) [s-label≡uri] = ω ((≠-sym uri≠bnode) [s-label≡uri])
subject-uri-elim-harmony (inr (inr v)) [s-label≡uri] = ω ((≠-sym uri≠triplelist) [s-label≡uri])

subject-get-bnode₂ : (s : subject-interp₂) → (subject-type-label-interp s) ≡ bnode-label → blank-node-interp₂
subject-get-bnode₂ (inl v) [s-label≡bnode] = ω (uri≠bnode [s-label≡bnode])
subject-get-bnode₂ (inr (inl v)) [s-label≡bnode] = v
subject-get-bnode₂ (inr (inr v)) [s-label≡bnode] = ω ((≠-sym bnode≠triplelist) [s-label≡bnode])

subject-bnode-elim-harmony : (s : subject-interp₂) → (p : (subject-type-label-interp s) ≡ bnode-label) → s ≡ (inr ∘ inl) (subject-get-bnode₂ s p)
subject-bnode-elim-harmony (inl v) [s-label≡bnode] = ω (uri≠bnode [s-label≡bnode])
subject-bnode-elim-harmony (inr (inl v)) [s-label≡bnode] = refl
subject-bnode-elim-harmony (inr (inr v)) [s-label≡bnode] = ω ((≠-sym bnode≠triplelist) [s-label≡bnode])

subject-get-triplelist₂ : (s : subject-interp₂) → (subject-type-label-interp s) ≡ triplelist-label → triplelist-interp₂
subject-get-triplelist₂ (inl v) [s-label≡triplelist] = ω (uri≠triplelist [s-label≡triplelist])
subject-get-triplelist₂ (inr (inl v)) [s-label≡triplelist] = ω (bnode≠triplelist [s-label≡triplelist])
subject-get-triplelist₂ (inr (inr v)) [s-label≡triplelist] = v

subject-triplelist-elim-harmony : (s : subject-interp₂) → (p : (subject-type-label-interp s) ≡ triplelist-label) → s ≡ (inr ∘ inr) (subject-get-triplelist₂ s p)
subject-triplelist-elim-harmony (inl v) [s-label≡triplelist] = ω (uri≠triplelist [s-label≡triplelist])
subject-triplelist-elim-harmony (inr (inl v)) [s-label≡triplelist] = ω (bnode≠triplelist [s-label≡triplelist])
subject-triplelist-elim-harmony (inr (inr v)) [s-label≡triplelist] = refl

property-type-label-interp : property-interp₂ → resource-type-labels
property-type-label-interp (inl v) = uri-label
property-type-label-interp (inr (inl v)) = bnode-label
property-type-label-interp (inr (inr v)) = triplelist-label

property-get-val : (p : property-interp₂) → (resource-type-labels-interp (property-type-label-interp p))
property-get-val (inl v) = v
property-get-val (inr (inl v)) = v
property-get-val (inr (inr v)) = v

property-get-uri₂ : (p : property-interp₂) → (property-type-label-interp p) ≡ uri-label → URI-interp₂
property-get-uri₂ (inl v) [p-label≡uri] = v
property-get-uri₂ (inr (inl v)) [p-label≡uri] = ω ((≠-sym uri≠bnode) [p-label≡uri])
property-get-uri₂ (inr (inr v)) [p-label≡uri] = ω ((≠-sym uri≠triplelist) [p-label≡uri])

property-uri-elim-harmony : (p : property-interp₂) → (eq : (property-type-label-interp p) ≡ uri-label) → p ≡ inl (property-get-uri₂ p eq)
property-uri-elim-harmony (inl v) [p-label≡uri] = refl
property-uri-elim-harmony (inr (inl v)) [p-label≡uri] = ω ((≠-sym uri≠bnode) [p-label≡uri])
property-uri-elim-harmony (inr (inr v)) [p-label≡uri] = ω ((≠-sym uri≠triplelist) [p-label≡uri])

property-get-bnode₂ : (p : property-interp₂) → (property-type-label-interp p) ≡ bnode-label → blank-node-interp₂
property-get-bnode₂ (inl v) [p-label≡bnode] = ω (uri≠bnode [p-label≡bnode])
property-get-bnode₂ (inr (inl v)) [p-label≡bnode] = v
property-get-bnode₂ (inr (inr v)) [p-label≡bnode] = ω ((≠-sym bnode≠triplelist) [p-label≡bnode])

property-bnode-elim-harmony : (p : property-interp₂) → (eq : (property-type-label-interp p) ≡ bnode-label) → p ≡ (inr ∘ inl) (property-get-bnode₂ p eq)
property-bnode-elim-harmony (inl v) [p-label≡bnode] = ω (uri≠bnode [p-label≡bnode])
property-bnode-elim-harmony (inr (inl v)) [p-label≡bnode] = refl
property-bnode-elim-harmony (inr (inr v)) [p-label≡bnode] = ω ((≠-sym bnode≠triplelist) [p-label≡bnode])

property-get-triplelist₂ : (p : property-interp₂) → (property-type-label-interp p) ≡ triplelist-label → triplelist-interp₂
property-get-triplelist₂ (inl v) [p-label≡triplelist] = ω (uri≠triplelist [p-label≡triplelist])
property-get-triplelist₂ (inr (inl v)) [p-label≡triplelist] = ω (bnode≠triplelist [p-label≡triplelist])
property-get-triplelist₂ (inr (inr v)) [p-label≡triplelist] = v

property-triplelist-elim-harmony : (p : property-interp₂) → (eq : (property-type-label-interp p) ≡ triplelist-label) → p ≡ (inr ∘ inr) (property-get-triplelist₂ p eq)
property-triplelist-elim-harmony (inl v) [p-label≡triplelist] = ω (uri≠triplelist [p-label≡triplelist])
property-triplelist-elim-harmony (inr (inl v)) [p-label≡triplelist] = ω (bnode≠triplelist [p-label≡triplelist])
property-triplelist-elim-harmony (inr (inr v)) [p-label≡triplelist] = refl



object-type-label-interp : object-interp₂ → resource-type-labels
object-type-label-interp (inl v) = uri-label
object-type-label-interp (inr (inl v)) = bnode-label
object-type-label-interp (inr (inr v)) = triplelist-label

object-get-val : (o : object-interp₂) → (resource-type-labels-interp (object-type-label-interp o))
object-get-val (inl v) = v
object-get-val (inr (inl v)) = v
object-get-val (inr (inr v)) = v

object-get-uri₂ : (o : object-interp₂) → (object-type-label-interp o) ≡ uri-label → URI-interp₂
object-get-uri₂ (inl v) [o-label≡uri] = v
object-get-uri₂ (inr (inl v)) [o-label≡uri] = ω ((≠-sym uri≠bnode) [o-label≡uri])
object-get-uri₂ (inr (inr v)) [o-label≡uri] = ω ((≠-sym uri≠triplelist) [o-label≡uri])

object-uri-elim-harmony : (o : object-interp₂) → (eq : (object-type-label-interp o) ≡ uri-label) → o ≡ inl (object-get-uri₂ o eq)
object-uri-elim-harmony (inl v) [o-label≡uri] = refl
object-uri-elim-harmony (inr (inl v)) [o-label≡uri] = ω ((≠-sym uri≠bnode) [o-label≡uri])
object-uri-elim-harmony (inr (inr v)) [o-label≡uri] = ω ((≠-sym uri≠triplelist) [o-label≡uri])

object-get-bnode₂ : (o : object-interp₂) → (object-type-label-interp o) ≡ bnode-label → blank-node-interp₂
object-get-bnode₂ (inl v) [o-label≡bnode] = ω (uri≠bnode [o-label≡bnode])
object-get-bnode₂ (inr (inl v)) [o-label≡bnode] = v
object-get-bnode₂ (inr (inr v)) [o-label≡bnode] = ω ((≠-sym bnode≠triplelist) [o-label≡bnode])

object-bnode-elim-harmony : (o : object-interp₂) → (eq : (object-type-label-interp o) ≡ bnode-label) → o ≡ (inr ∘ inl) (object-get-bnode₂ o eq)
object-bnode-elim-harmony (inl v) [o-label≡bnode] = ω (uri≠bnode [o-label≡bnode])
object-bnode-elim-harmony (inr (inl v)) [o-label≡bnode] = refl
object-bnode-elim-harmony (inr (inr v)) [o-label≡bnode] = ω ((≠-sym bnode≠triplelist) [o-label≡bnode])

object-get-triplelist₂ : (o : object-interp₂) → (object-type-label-interp o) ≡ triplelist-label → triplelist-interp₂
object-get-triplelist₂ (inl v) [o-label≡triplelist] = ω (uri≠triplelist [o-label≡triplelist])
object-get-triplelist₂ (inr (inl v)) [o-label≡triplelist] = ω (bnode≠triplelist [o-label≡triplelist])
object-get-triplelist₂ (inr (inr v)) [o-label≡triplelist] = v

object-triplelist-elim-harmony : (o : object-interp₂) → ( eq : (object-type-label-interp o) ≡ triplelist-label) → o ≡ (inr ∘ inr) (object-get-triplelist₂ o eq)
object-triplelist-elim-harmony (inl v) [o-label≡triplelist] = ω (uri≠triplelist [o-label≡triplelist])
object-triplelist-elim-harmony (inr (inl v)) [o-label≡triplelist] = ω (bnode≠triplelist [o-label≡triplelist])
object-triplelist-elim-harmony (inr (inr v)) [o-label≡triplelist] = refl


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
   type-label = (uri-label , refl) ;
   cons = inl ;
   cons-inj = inl-inj ;
   cons-type = λ s → refl ;
   get-val = subject-get-uri₂ ;
   get-val-harmony-elim = subject-uri-elim-harmony ;
   get-val-harmony-intro = λ s → refl
  } ;
  subject-def₂ = record {
   type-label = (bnode-label , refl) ;
   cons = inr ∘ inl ;
   cons-inj = inr∘inl-inj ;
   cons-type = λ s → refl ;
   get-val = subject-get-bnode₂ ;
   get-val-harmony-elim = subject-bnode-elim-harmony ;
   get-val-harmony-intro = λ s → refl
  } ;
  subject-def₃ = record {
   type-label = (triplelist-label , refl) ;
   cons = inr ∘ inr ;
   cons-inj = inr∘inr-inj ;
   cons-type = λ s → refl ;
   get-val = subject-get-triplelist₂ ;
   get-val-harmony-elim = subject-triplelist-elim-harmony ;
   get-val-harmony-intro = λ s → refl
  } ;
  property-def₁ = record {
   type-label = (uri-label , refl) ;
   cons = inl ;
   cons-inj = inl-inj ;
   cons-type = λ p → refl ;
   get-val = property-get-uri₂ ;
   get-val-harmony-elim = property-uri-elim-harmony ;
   get-val-harmony-intro = λ s → refl 
  } ;
  property-def₂ = record {
   type-label = (bnode-label , refl) ;
   cons = inr ∘ inl ;
   cons-inj = inr∘inl-inj ;
   cons-type = λ p → refl ;
   get-val = property-get-bnode₂ ;
   get-val-harmony-elim = property-bnode-elim-harmony ;
   get-val-harmony-intro = λ p → refl 
  } ;
  property-def₃ = record {
   type-label = (triplelist-label , refl) ;
   cons = inr ∘ inr ;
   cons-inj = inr∘inr-inj ;
   cons-type = λ p → refl ;
   get-val = property-get-triplelist₂ ;
   get-val-harmony-elim = property-triplelist-elim-harmony ;
   get-val-harmony-intro = λ p → refl 
  } ;
  object-def₁ = record {
   type-label = (uri-label , refl) ;
   cons = inl ;
   cons-inj = inl-inj ;
   cons-type = λ o → refl ;
   get-val = object-get-uri₂ ;
   get-val-harmony-elim = object-uri-elim-harmony ;
   get-val-harmony-intro = λ o → refl 
  } ;
  object-def₂ = record {
   type-label = (bnode-label , refl) ;
   cons = inr ∘ inl ;
   cons-inj = inr∘inl-inj ;
   cons-type = λ o → refl ;
   get-val = object-get-bnode₂ ;
   get-val-harmony-elim = object-bnode-elim-harmony ;
   get-val-harmony-intro = λ o → refl 
  } ;
  object-def₃ = record {
   type-label = (triplelist-label , refl) ;
   cons = inr ∘ inr ;
   cons-inj = inr∘inr-inj ;
   cons-type = λ o → refl ;
   get-val = object-get-triplelist₂ ;
   get-val-harmony-elim = object-triplelist-elim-harmony ;
   get-val-harmony-intro = λ o → refl 
  }
 }


{-
Sentence 4:
An object can also be a literal.
-}

record upto-S4-1 : Set₁ where
 field 
  triple : ExtensibleType
  subject : ExtensibleType
  property : ExtensibleType
  object : ExtensibleType
  triple-component-subject : ExtensibleType.carrier triple → ExtensibleType.carrier subject
  triple-component-property : ExtensibleType.carrier triple → ExtensibleType.carrier property
  triple-component-object : ExtensibleType.carrier triple → ExtensibleType.carrier object
  triple-all-possible-components : (s : (ExtensibleType.carrier subject)) → (p : (ExtensibleType.carrier property)) → (o : (ExtensibleType.carrier object)) → ∃ t ∈ (ExtensibleType.carrier triple) , ((triple-component-subject t ≡ s) ∧ (triple-component-property t ≡ p) ∧ (triple-component-object t  ≡ o))


  triplelist : ExtensibleType
  triplelist-def : TypeExtension₂ triplelist (List (ExtensibleType.carrier triple))


  URI : ExtensibleType
  blank-node : ExtensibleType
  subject-def₁ : TypeExtension₂ subject (ExtensibleType.carrier URI)
  subject-def₂ : TypeExtension₂ subject (ExtensibleType.carrier blank-node)
  subject-def₃ : TypeExtension₂ subject (ExtensibleType.carrier triplelist)
  property-def₁ : TypeExtension₂ property (ExtensibleType.carrier URI)
  property-def₂ : TypeExtension₂ property (ExtensibleType.carrier blank-node)
  property-def₃ : TypeExtension₂ property (ExtensibleType.carrier triplelist)
  object-def₁ : TypeExtension₂ object (ExtensibleType.carrier URI)
  object-def₂ : TypeExtension₂ object (ExtensibleType.carrier blank-node)
  object-def₃ : TypeExtension₂ object (ExtensibleType.carrier triplelist)


  literal : ExtensibleType
  object-def₄ : TypeExtension₂ object (ExtensibleType.carrier literal)


data triple-interp₃ : Set

URI-interp₃ : Set
URI-interp₃ = Nat

blank-node-interp₃ : Set
blank-node-interp₃ = Nat

literal-interp₃ : Set
literal-interp₃ = Nat

triplelist-interp₃ : Set
triplelist-interp₃ = List triple-interp₃

subject-interp₃ : Set
subject-interp₃ = URI-interp₃ ⊹ (blank-node-interp₃ ⊹ triplelist-interp₃)

property-interp₃ : Set
property-interp₃ = URI-interp₃ ⊹ (blank-node-interp₃ ⊹ triplelist-interp₃)

object-interp₃ : Set
object-interp₃ = URI-interp₃ ⊹ (blank-node-interp₃ ⊹ (triplelist-interp₃ ⊹ literal-interp₃))

data triple-interp₃ where
 _,_,_ : subject-interp₃ → property-interp₃ → object-interp₃ → triple-interp₃

triple-component-subject-interp₃ : triple-interp₃ → subject-interp₃
triple-component-subject-interp₃ (s , _ , _) = s

triple-component-property-interp₃ : triple-interp₃ → property-interp₃
triple-component-property-interp₃ (_ , p , _) = p

triple-component-object-interp₃ : triple-interp₃ → object-interp₃
triple-component-object-interp₃ (_ , _ , o) = o

simple-ext-type : Set → ExtensibleType
simple-ext-type A =
 record {
  carrier = A ;
  type-label = ⊤ ;
  val-type = λ a → ● ;
  type-interpretation = λ label → A ;
  get-val = λ a → a
 }

{-
is-uri₃ : Fin 4 → Bool
is-uri₃ zero = true
is-uri₃ (suc zero) = false
is-uri₃ (suc (suc zero)) = false
is-uri₃ (suc (suc (suc zero))) = false
-}

{-
upto-S4-1-interp : upto-S4-1
upto-S4-1-interp =
 record {
  triple = simple-ext-type triple-interp₃ ;

  subject = record {
   carrier = subject-interp₃ ;
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

  triplelist = simple-ext-type triplelist-interp₃ ; 

  triplelist-def = record {
   type-label = (● , refl) ;
   cons = λ tl → tl ;
   cons-inj = λ a1 → (λ a2 → (λ [fa1≡fa2] → [fa1≡fa2])) ;
   cons-type = λ tl → refl ;
   get-val = λ tl → (λ right-type → tl) ;
   get-val-harmony-elim = λ tl → (λ right-type → refl) ;
   get-val-harmony-intro = λ tl → refl
  } ;

  URI = simple-ext-type URI-interp₃ ; 
  blank-node = simple-ext-type blank-node-interp₃ ; 

  subject-def₁ = record {
   type-label = (uri-label , refl) ;
   cons = inl ;
   cons-inj = inl-inj ;
   cons-type = λ s → refl ;
   get-val = subject-get-uri₂ ;
   get-val-harmony-elim = subject-uri-elim-harmony ;
   get-val-harmony-intro = λ s → refl
  } ;
  subject-def₂ = record {
   type-label = (bnode-label , refl) ;
   cons = inr ∘ inl ;
   cons-inj = inr∘inl-inj ;
   cons-type = λ s → refl ;
   get-val = subject-get-bnode₂ ;
   get-val-harmony-elim = subject-bnode-elim-harmony ;
   get-val-harmony-intro = λ s → refl
  } ;
  subject-def₃ = record {
   type-label = (triplelist-label , refl) ;
   cons = inr ∘ inr ;
   cons-inj = inr∘inr-inj ;
   cons-type = λ s → refl ;
   get-val = subject-get-triplelist₂ ;
   get-val-harmony-elim = subject-triplelist-elim-harmony ;
   get-val-harmony-intro = λ s → refl
  } ;
  property-def₁ = record {
   type-label = (uri-label , refl) ;
   cons = inl ;
   cons-inj = inl-inj ;
   cons-type = λ p → refl ;
   get-val = property-get-uri₂ ;
   get-val-harmony-elim = property-uri-elim-harmony ;
   get-val-harmony-intro = λ s → refl 
  } ;
  property-def₂ = record {
   type-label = (bnode-label , refl) ;
   cons = inr ∘ inl ;
   cons-inj = inr∘inl-inj ;
   cons-type = λ p → refl ;
   get-val = property-get-bnode₂ ;
   get-val-harmony-elim = property-bnode-elim-harmony ;
   get-val-harmony-intro = λ p → refl 
  } ;
  property-def₃ = record {
   type-label = (triplelist-label , refl) ;
   cons = inr ∘ inr ;
   cons-inj = inr∘inr-inj ;
   cons-type = λ p → refl ;
   get-val = property-get-triplelist₂ ;
   get-val-harmony-elim = property-triplelist-elim-harmony ;
   get-val-harmony-intro = λ p → refl 
  } ;
  object-def₁ = record {
   type-label = (uri-label , refl) ;
   cons = inl ;
   cons-inj = inl-inj ;
   cons-type = λ o → refl ;
   get-val = object-get-uri₂ ;
   get-val-harmony-elim = object-uri-elim-harmony ;
   get-val-harmony-intro = λ o → refl 
  } ;
  object-def₂ = record {
   type-label = (bnode-label , refl) ;
   cons = inr ∘ inl ;
   cons-inj = inr∘inl-inj ;
   cons-type = λ o → refl ;
   get-val = object-get-bnode₂ ;
   get-val-harmony-elim = object-bnode-elim-harmony ;
   get-val-harmony-intro = λ o → refl 
  } ;
  object-def₃ = record {
   type-label = (triplelist-label , refl) ;
   cons = inr ∘ inr ;
   cons-inj = inr∘inr-inj ;
   cons-type = λ o → refl ;
   get-val = object-get-triplelist₂ ;
   get-val-harmony-elim = object-triplelist-elim-harmony ;
   get-val-harmony-intro = λ o → refl 
  } ;
 }
-}

