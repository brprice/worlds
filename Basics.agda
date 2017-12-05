module Basics where

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

sym : forall {l}{X : Set l}{x y : X} -> x == y -> y == x
sym refl = refl

trans : forall {l}{X : Set l}{x y z : X} -> x == y -> y == z -> x == z
trans refl refl = refl

cong : forall {l}{X : Set l}{m}{Y : Set m}
    -> (f : X -> Y)
    -> {x1 x2 : X} -> x1 == x2
    -> f x1 == f x2
cong f refl = refl

subst : {A : Set}(B : A -> Set){x y : A} -> x == y -> B x -> B y
subst B refl b = b

_-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k} ->
        (f : {a : A}(b : B a) -> C a b)(g : (a : A) -> B a)(a : A) -> C a (g a)
(f - g) x = f (g x)

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

_+N_ : Nat -> Nat -> Nat
n +N ze = n
n +N su m = su (n +N m)
infixr 30 _+N_

+Nassoc : forall x y z -> x +N y +N z == (x +N y) +N z
+Nassoc x y ze = refl
+Nassoc x y (su z) = cong su (+Nassoc x y z)

data Fin : Nat -> Set where
  ze : forall {n} -> Fin (su n)
  su : forall {n} -> Fin n -> Fin (su n)

suInj : {n : Nat}{i j : Fin n} -> Fin.su i == su j -> i == j
suInj refl = refl


record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 4 _,_ _*_
open Sg public

record One : Set where
  constructor <>

data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

data Zero : Set where
naughty : forall {l}{X : Set l} -> Zero -> X
naughty ()

the : forall {l}(X : Set l) -> X -> X
the X x = x

¬ : Set -> Set
¬ X = X -> Zero


-- Inspect idiom
data Unit : Set where it : Unit

Hidden : Set -> Set
Hidden A = Unit -> A

data Reveal_is_ {A : Set}(h : Hidden A)(a : A) : Set where
  [_] : h it == a -> Reveal _ is a

inspect : {A : Set}{B : A -> Set} -> (f : (a : A) -> B a) -> (a : A) -> Reveal (\{it -> f a}) is (f a)
inspect f a = [ refl ]
