module Trees where

open import Data.List
open import Data.List.Operations
open import Data.Nat
open import Data.Nat.Operations

data SimpleTree : Set where
 leaf : SimpleTree
 node : SimpleTree → SimpleTree → SimpleTree

flatten-SimpleTree : ∀ {i} {B : Set i} → B → (B → B → B) → SimpleTree → B
flatten-SimpleTree b f leaf = b
flatten-SimpleTree b f (node l r) = f (flatten-SimpleTree b f l) (flatten-SimpleTree b f r)

SimpleTree:size : SimpleTree → Nat
SimpleTree:size leaf = 1
SimpleTree:size (node l r) = 1 + (SimpleTree:size l) + (SimpleTree:size r)

SimpleTree:#leaves : SimpleTree → Nat
SimpleTree:#leaves leaf = 1
SimpleTree:#leaves (node l r) = 1 + (SimpleTree:#leaves l) + (SimpleTree:#leaves r)

SimpleTree:#internal : SimpleTree → Nat
SimpleTree:#internal leaf = 0
SimpleTree:#internal (node l r) = 1 + (SimpleTree:#internal l) + (SimpleTree:#internal r)

data SimpleNTree : Set where
 leaf : SimpleNTree
 node : List SimpleNTree → SimpleNTree

data Tree {i} (A : Set i) : Set i where
 leaf : A → Tree A
 node : Tree A → Tree A → Tree A

map-tree : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → Tree A → Tree B
map-tree f (leaf a) = (leaf (f a))
map-tree f (node l r) = (node (map-tree f l) (map-tree f r))

flatten-Tree : ∀ {i j} {A : Set i} {B : Set j} → (f : B → B → B) → (g : A → B) → Tree A → B
flatten-Tree {i} {j} {A} {B} f g (leaf a) = g a
flatten-Tree {i} {j} {A} {B} f g (node l r) = f (flatten-Tree f g l) (flatten-Tree f g r)

Tree:size : ∀ {i} {A : Set i} → Tree A → Nat
Tree:size (leaf a) = 1
Tree:size (node l r) = 1 + (Tree:size l) + (Tree:size r)

Tree:#leaves : ∀ {i} {A : Set i} → Tree A → Nat
Tree:#leaves (leaf a) = 1
Tree:#leaves (node l r) = (Tree:#leaves l) + (Tree:#leaves r)

Tree:#internal : ∀ {i} {A : Set i} → Tree A → Nat
Tree:#internal (leaf a) = 0
Tree:#internal (node l r) = 1 + (Tree:#internal l) + (Tree:#internal r)


data NTree {i} (A : Set i) : Set i where
 leaf : A → NTree A
 node : List (NTree A) → NTree A

{-
--Fails termination check
map-NTree : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → NTree A → NTree B
map-NTree f (leaf a) = (leaf (f a))
map-NTree f (node children) = node (map (map-NTree f) children)

-}

data Tree' {i} (A : Set i) : Set i where
 leaf : A → Tree' A
 node : A → Tree' A → Tree' A → Tree' A

map-Tree' : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → Tree' A → Tree' B
map-Tree' f (leaf a) = leaf (f a)
map-Tree' f (node a l r) = node (f a) (map-Tree' f l) (map-Tree' f r)

flatten-Tree' : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B → B → B) → (g : A → B) → Tree' A → B
flatten-Tree' {i} {j} {A} {B} f g (leaf a) = g a
flatten-Tree' {i} {j} {A} {B} f g (node a l r) = f a (flatten-Tree' f g l) (flatten-Tree' f g r) 

Tree':size : ∀ {i} {A : Set i} → Tree' A → Nat
Tree':size (leaf a) = 1
Tree':size (node a l r) = 1 + (Tree':size l) + (Tree':size r)

Tree':#leaves : ∀ {i} {A : Set i} → Tree' A → Nat
Tree':#leaves (leaf a) = 1
Tree':#leaves (node a l r) = (Tree':#leaves l) + (Tree':#leaves r)

Tree':#internal : ∀ {i} {A : Set i} → Tree' A → Nat
Tree':#internal (leaf a) = 0
Tree':#internal (node a l r) = 1 + (Tree':#internal l) + (Tree':#internal r)


data NTree' {i} (A : Set i) : Set i where
 leaf : A → NTree' A
 node : A → List (NTree' A) → NTree' A


