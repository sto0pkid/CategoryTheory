data Nat : Type
 0 : Nat
 suc : Nat -> Nat
 
data LambdaVar : Type
 V : Nat -> LambdaVar
 
data LambdaTerm : Type
 Var : LambdaVar -> LambdaTerm
 App : LambdaTerm -> LambdaTerm -> LambdaTerm
 Abs : LambdaVar -> LambdaTerm -> LambdaTerm
 
data List (A : Type) : Type
 [] : List A
 _::_ : A -> List A -> List A
 
data Bool : Type
 true : Bool
 false : Bool
 
if_then_else_ : {A : Type} -> Bool -> A -> A -> A
if true then x else y = x
if false then x else y = y
 
_and_ : Bool -> Bool -> Bool
true and true = true
true and false = false
false and true = false
false and false = false
 
_or_ : Bool -> Bool -> Bool
true or true = true
true or false = false
false or true = false
false or false = false
 
Nat-eq : Nat -> Nat -> Bool
Nat-eq 0 0 = true
Nat-eq (suc x) 0 = false
Nat-eq 0 (suc y) = false
Nat-eq (suc x) (suc y) = Nat-eq x y
 
LambdaVar-eq : LambdaVar -> LambdaVar -> Bool
LambdaVar-eq (V x) (V y) = Nat-eq x y
 
list-in : List LambdaVar -> LambdaVar -> Bool
list-in [] v = false
list-in (l :: ls) v = if (LambdaVar-eq l v) then true else (list-in ls v)
 
list-union : List LambdaVar -> List LambdaVar -> List LambdaVar
list-union [] rs = rs
list-union (l :: ls) rs = if (list-in rs l) then (list-union ls rs) else (l :: (list-union ls rs))
 
remove_from_ : LambdaVar -> List LambdaVar -> List LambdaVar
remove x from [] = []
remove x from (l :: ls) = if (Lambdavar-eq x l) then (remove x from ls) else (l :: (remove x from ls))
 
FV-helper : LambdaTerm -> List LambdaVar -> List LambdaVar
FV-helper (Var x) r = x :: r
FV-helper (App t s) r = list-union (FV-helper t r) (FV-helper t r)
FV-helper (Abs x e) r = remove x from (FV-helper e r)
 
FV : LambdaTerm -> List LambdaVar
FV t = FV-helper t []
 
Vars-helper : LambdaTerm -> List LambdaVar -> List LambdaVar
Vars-helper (Var x) r = x :: r
Vars-helper (App t s) r = list-union (FV-helper t r) (FV-helper s r)
Vars-helper (Abs x e) r = list-union (Vars-helper
 
Vars : LambdaTerm -> List LambdaVar
Vars (Var x) = x :: r
Vars (App t s) = list-union (Vars t) (Vars s)
Vars (Abs x e) = list-union (x :: []) (Vars e)
 
_gte_ : Nat -> Nat -> Bool
0 gte 0 = true
(suc x) gte 0 = true
0 gte (suc y) = false
(suc x) gte (suc y) = x gte y
 
maxVar : LambdaTerm -> Nat
maxVar (Var (V n)) = n
maxVar (App t s) = if ((maxVar t) gte (maxVar s)) then (maxVar t) else (maxVar s)
maxVar (Abs (V n) e) = if (n gte (maxVar e)) then n else (maxVar e)
 
freshVar : LambdaTerm -> LambdaVar
freshVar t = V (suc (maxVar t))
 
subst-helper : LambdaTerm -> LambdaVar -> LambdaTerm -> LambdaTerm -> LambdaTerm
subst-helper (Var x) v r t = if (LambdaVar-eq x v) then r else (Var x)
subst-helper (App f x) v r t = App (subst f v r t) (subst x v r t)
subst-helper (Abs x e) v r t = if (LambdaVar-eq x v) then (Abs x e) else (if (list-in (FV r) x) then (Abs (freshVar t) (subst (subst e x (freshVar t) t) v r t)) else (Abs x (subst e v r t))
 
subst : LambdaTerm -> LambdaVar -> LambdaTerm -> LambdaTerm
subst t v r = subst-helper t v r t
 
LambdaTerm-syn-eq : LambdaTerm -> LambdaTerm -> Bool
LambdaTerm-syn-eq (Var x) (Var y) = LambdaVar-eq x y
LambdaTerm-syn-eq (Var x) (App t s) = false
LambdaTerm-syn-eq (Var x) (Abs v e) = false
LambdaTerm-syn-eq (App t s) (Var y) = false
LambdaTerm-syn-eq (App t s) (App q r) = (LambdaTerm-syn-eq t q) and (LambdaTerm-syn-eq s r)
LambdaTerm-syn-eq (App t s) (Abs v e) = false
LambdaTerm-syn-eq (Abs v e) (Var y) = false
LambdaTerm-syn-eq (Abs v e) (App q r) = false
LambdaTerm-syn-eq (Abs v e) (Abs w f) = (LambdaVar-eq v w) and (LambdaTerm-syn-eq e f)
 
data _==_ {A : Type} (x : A) : A -> Type
 refl : x == x
 
data True : Type
 () : True
 
data False : Type
 omega : {A: Type} -> _|_ -> A
 
True-implies-True : True -> True
True-implies-True () = ()
 
False-implies-True : False -> True
False-implies-True evil = omega evil
 
False-implies-False : False -> False
False-implies-False evil = evil
 
[True-implies-False]-implies-False : (True -> False) -> False
[True-implies-False]-implies-False f = f ()
 
A==B-implies-A-implies-B : {A B : Type} -> A == B -> A -> B
A==B-implies-A-implies-B {A} {.A} refl a = a
 
_=/=_ : {A : Type} -> (a b : A) -> Type
a =/= b = (a == b) -> False
 
True=/=False : True =/= False
True=/=False [True==False] = A==B-implies-A-implies-B [True==False] ()
 
bool-to-Type : Bool -> Type
bool-to-Type true = True
bool-to-Type false = False
 
x==y-implies-fx==fy : {A B : Type} (f : A -> B) (x y : A) -> (x == y) -> (f x) == (f y)
x==y-implies-fx==fy {A B} f x .x refl = refl
 
true=/=false : true =/= false
true=/=false [true==false] = True=/=False (x==y-implies-fx==fy bool-to-Type true false [true==false])
 
==-sym : {A : Type} {x y : A} -> x == y -> y == x
==-sym {A} {x} {.x} refl = refl
 
==-trans : {A : Type} {x y z : A} -> x == y -> y == z -> x == z
==-trans {A} {x} {.x} {.x} refl refl = refl
 
Nat-eq-refl-ind : (x : Nat) -> Nat-eq x x == true -> Nat-eq (suc x) (suc x) == true
 
Nat-eq-refl : (x : Nat) -> Nat-eq x x == true
Nat-eq-refl 0 = refl
Nat-eq-refl (suc n) = Nat-eq-refl-ind x (Nat-eq-refl n)
 
LambdaVar-eq-refl : (x : LambdaVar) -> LambdaVar-eq x x == true
LambdaVar-eq-refl 0 = refl
LambdaVar-eq-refl (suc n) = proof
 where
  p1 : LambdaVar-eq (suc n) (suc n) == Nat-eq (suc n) (suc n)
  p1 = refl
 
  p2 : Nat-eq (suc n) (suc n) == true
  p2 = Nat-eq-refl (suc n)
 
  proof = ==-trans p1 p2
 
LambdaVar-eq-x-y-implies-LambdaTerm-eq-x-y : (x y : LambdaVar) -> LambdaVar-eq x y == true -> LambdaTerm-syn-eq (Var x) (Var y) == true
LambdaVar-eq-x-y-implies-LambdaTerm-eq-x-y x y [x==y] = ==-trans (==-sym [x==y]) refl
 
 
 
## Your proposition & proof stuff:
 
#list-in (Vars (Var x)) x == list-in (x :: []) x
x-in-x : (x : LambdaVar) -> (list-in (Vars (Var x)) x) == true
x-in-x x = refl
 
x-in-x' : (v x : LambdaVar) -> (LambdaVar-eq v x == true) -> (list-in (Vars (Var v)) x) == true
x-in-x' v x [v==x] = proof
 where
    p1 : list-in (Vars (Var v)) x == list-in (v :: []) x
    p1 = refl
 
    p2 : list-in (v :: []) x == if (LambdaVar-eq v x) then true else (list-in [] x)
    p2 = refl
 
    helper : Bool -> Bool
    helper b = if b then true else (list-in [] x)
 
    p3 : if (LambdaVar-eq v x) then true else (list-in [] x) == if true then true else (list-in [] x)
    p3 = [x==y]-implies-[fx==fy] helper (LambdaVar-eq v x) true [v==x]
 
    p4 : if true then true else (list-in [] x) == true
    p4 = refl
 
    proof = ==-trans p1 (==-trans p2 (==-trans p3 p4))
 
x-not-in-y : (v x : LambdaVar) -> (LambdaVar-eq v x == false) -> (list-in (Vars (Var v)) x) == false
x-not-in-y v x [v=/=x] == proof
 where
    p1 : list-in (Vars (Var v)) x == list-in (v :: []) x
    p1 = refl
 
    p2 : list-in (v :: []) x == if (LambdaVar-eq v x) then true else (list-in [] x)
    p2 = refl
 
    helper : Bool -> Bool
    helper b = if b then true else (list-in [] x)
 
    p3 : if (LambdaVar-eq v x) then true else (list-in [] x) == if false then true else (list-in [] x)
    p3 = [x==y]-implies-[fx==fy] helper (LambdaVar-eq v x) false [v=/=x]
 
    p4 : if false then true else (list-in [] x) == false
    p4 = refl
 
    proof = ==-trans p1 (==-trans p2 (==-trans p3 p4))
 
 
y[x:=r]=y : (x y : LambdaVar) -> (r : LambdaTerm) -> (LambdaVar-eq x y == false) -> subst (Var y) x r == (Var y)
y[x:=r]=y x y r [x=/=y] = proof
 where
    p1 : subst (Var y) x r == subst-helper (Var y) x r (Var y)
    p1 = refl
 
    p2 : subst-helper (Var y) x r (Var y) == if (LambdaVar-eq y x) then r else (Var y)
    p2 = refl
 
    helper : Bool -> Bool
    helper b = if b then r else (Var y)
 
    p3 : if (LambdaVar-eq y x) then r else (Var y) == if false then r else (Var y)
    p3 = [x==y]-implies-[fx==fy] helper (LambdaVar-eq y x) false [x=/=y]
 
    p4 : if false then r else (Var y) == (Var y)
    p4 = refl
 
    proof = ==-trans p1 (==-trans p2 (==-trans p3 p4))
 
 
P : LambdaVar -> LambdaTerm -> LambdaTerm -> Type
P x N M = (list-in (Vars M) x == false) -> ((LambdaTerm-syn-eq (subst M x N) M) == true)
 
induct : (t s N : LambdaTerm) -> (x : LambdaVar) -> P x t N -> P x s N -> P x (App t s) N
induct t s N x PxtN PxsN = ...
 
f : (M N : LambdaTerm) -> (x : LambdaVar) -> P x N M
f (Var v) N x x-not-in-M = if (LambdaVar-eq v x) then x-case else y-case
 where
  x-case : (LambdaVar-eq v x == true) -> P x N M
  x-case [v==x] = omega (true=/=false [true==false])
    where
        [true==false] : true == false
        [true==false] = subproof
            where
                p1 : list-in (Vars (Var v)) x == false
                p1 = x-not-in-M
 
                p2 : true == list-in (Vars (Var v)) x
                p2 = ==-sym (x-in-x' v x)
 
                subproof = ==-trans p2 p1
 
  y-case : (LambdaVar-eq v x == false) -> P x N M
  y-case [v=/=x] = subproof
    where
        p1a : (subst (Var v) x N) == (Var v)
        p1a = y[x:=r]=y x v N [v=/=x]
 
        helper : LambdaTerm -> Bool
        helper t = LambdaTerm-syn-eq t (Var v)
 
        p1 : (LambdaTerm-syn-eq (subst (Var v) x N) (Var v)) == (LambdaTerm-syn-eq (Var v) (Var v))
        p1 = [x==y]-implies-[fx==fy] helper (subst (Var v) x N) (Var v) p1a
 
        p2 : (LambdaTerm-syn-eq (Var v) (Var v)) == LambdaVar-eq v v
        p2 = refl
 
        p3 : LambdaVar-eq v v == true
        p3 = LambdaVar-eq-refl v
 
        subproof = ==-trans p1 (==-trans p2 p3)
 
 
f (App t s) N x = induct t s N x (koo'sTheorem t N x) (koo'sTheorem s N x)
f (Abs v e) N x = ...
