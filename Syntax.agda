module Syntax where

record something : Set₁ where
 field
  func-field : {A : Set} → A → A

my-func1 : {A : Set} → A → A
my-func1 = λ x → x

{-
-- bad
my-func2 : {A : Set} → A → A
my-func2 = λ A x → x
-}

my-func3 : {A : Set} → A → A
my-func3 = λ {A} x → x

my-rec1 : something
my-rec1 = 
 record {
  func-field = λ x → x
 }

{-
-- bad
my-rec2 : something
my-rec2 =
 record {
  func-field = λ A x → x 
 }
-}

my-rec3 : something
my-rec3 =
 record {
  func-field = λ {A} x → x
 }

{-
-- bad where clause
my-rec4 : something
my-rec4 =
 record {
  func-field = id
   where
    id : {A : Set} → A → A
    id {A} = λ x → x
 }
-}

-- good where clause
my-rec4 : something
my-rec4 =
 record {
  func-field = id
 }
 where
  id : {A : Set} → A → A
  id {A} = λ x → x


