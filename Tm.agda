module Tm {Q : Set} where
-- Q has to be an implicit argument, as agda gets confused if it is explicit
-- See : https://github.com/agda/agda/issues/2668

open import Basics
open import OPE
open import Dir

data Tm (n : Nat) : Dir -> Set where

  star : Tm n chk
  pi   : Q -> Tm n chk -> Tm (su n) chk -> Tm n chk
  lam  : Tm (su n) chk -> Tm n chk
  [_]  : Tm n syn -> Tm n chk

  var  : Fin n -> Tm n syn
  _$_  : Tm n syn -> Tm n chk -> Tm n syn
  _::_ : Tm n chk -> Tm n chk -> Tm n syn

infix 30 _$_ _::_

record Act (A : Nat -> Nat -> Set) : Set where
  field
    actV : forall {n m} -> A n m -> Fin n -> Tm m syn
    actW : forall {n m} -> A n m -> A (su n) (su m)

  act : forall {n m d} -> A n m -> Tm n d -> Tm m d
  act a star = star
  act a (pi q S T) = pi q (act a S) (act (actW a) T)
  act a (lam t) = lam (act (actW a) t)
  act a [ e ] = [ act a e ]
  act a (var i) = actV a i
  act a (f $ s) = act a f $ act a s
  act a (t :: T) = act a t :: act a T

THIN : Act _<=_
THIN = record { actV = \ th x -> var (thin th x) ; actW = os }

module Th = Act THIN

record ActId {A : Nat -> Nat -> Set}(AA : Act A)(ai : forall {n} -> A n n) : Set where
  field
    actVId : forall {n}(i : Fin n) -> Act.actV AA ai i == var i
    actWId : forall n -> Act.actW AA (ai {n}) == ai {su n}

  actId : forall {d n}(t : Tm n d) -> Act.act AA ai t == t
  actId star = refl
  actId {n = n} (pi q S T) rewrite actId S | actWId n | actId T = refl
  actId {n = n} (lam t) rewrite actWId n | actId t = refl
  actId [ e ] rewrite actId e = refl
  actId (var i) = actVId i
  actId (f $ s) rewrite actId f | actId s = refl
  actId (t :: T) rewrite actId t | actId T = refl

THINID : ActId THIN oi
THINID = record { actVId = help ; actWId = \ n -> refl } where
  help : forall {n} (i : Fin n) -> var (thin oi i) == var i
  help i rewrite oiQ i = refl

record ActCo {A B C : Nat -> Nat -> Set}
             (AA : Act A)(AB : Act B)(AC : Act C)
             (abc : forall {n m l} -> A m l -> B n m -> C n l) : Set where
  field
    actVCo : forall {n m l}(a : A m l)(b : B n m)(i : Fin n) ->
               Act.act AA a (Act.actV AB b i) == Act.actV AC (abc a b) i
    actWCo : forall {n m l}(a : A m l)(b : B n m) ->
               abc (Act.actW AA a) (Act.actW AB b) == Act.actW AC (abc a b)
  actCo : forall {d n m l}(a : A m l)(b : B n m)(t : Tm n d) ->
          Act.act AA a (Act.act AB b t) == Act.act AC (abc a b) t
  actCo a b star = refl
  actCo a b (pi q S T)
    rewrite actCo a b S
          | actCo (Act.actW AA a) (Act.actW AB b) T
          | actWCo a b
          = refl
  actCo a b (lam t)
    rewrite actCo (Act.actW AA a) (Act.actW AB b) t
          | actWCo a b
          = refl
  actCo a b [ e ] rewrite actCo a b e = refl
  actCo a b (var i) = actVCo a b i
  actCo a b (f $ s) rewrite actCo a b f | actCo a b s = refl
  actCo a b (t :: T) rewrite actCo a b t | actCo a b T = refl

THINTHINTHIN : ActCo THIN THIN THIN _-<-_
THINTHINTHIN = record { actVCo = help ; actWCo = \ _ _ -> refl } where
  help : forall {n m l} (a : m <= l) (b : n <= m) (i : Fin n) ->
          var (thin a (thin b i)) == var (thin (a -<- b) i)
  help th ph i rewrite thinCo th ph i = refl

lemma : forall {n m}(th : n <= m)(t : Tm n syn) ->
            Th.act (os th) (Th.act (o' oi) t) ==
            Th.act (o' th) t
lemma th t
  rewrite ActCo.actCo THINTHINTHIN (os th) (o' oi) t
        | th -<-oiQ
        = refl

lemma' : forall {n m}(th : n <= m)(t : Tm n syn) ->
            Th.act (o' oi) (Th.act th t) ==
            Th.act (o' th) t
lemma' th t
  rewrite ActCo.actCo THINTHINTHIN (o' oi) th t
        | oi-<-Q th
        = refl

thinUnderStar : {n m : Nat}(th : n <= m)(t : Tm n chk)
             -> star == Th.act th t
             -> t == star
thinUnderStar th star refl = refl
thinUnderStar th (pi _ _ _) ()
thinUnderStar th (lam _) ()
thinUnderStar th [ _ ] ()

thinUnderPi : {n m : Nat}(th : n <= m)(R : Tm n chk)
           -> forall {q S T}
           -> pi q S T == Th.act th R
           -> Sg _ \S' ->
              Sg _ \T' ->
              R == pi q S' T' * S == Th.act th S' * T == Th.act (os th) T'
thinUnderPi th star ()
thinUnderPi th (pi x S' T') refl = S' , T' , refl , refl , refl
thinUnderPi th (lam R) ()
thinUnderPi th [ R ] ()

thinUnderLam : {n m : Nat}(th : n <= m)(t : Tm n chk)
            -> forall {s}
            -> lam s == Th.act th t
            -> Sg _ \s' ->
               t == lam s' * s == Th.act (os th) s'
thinUnderLam th star ()
thinUnderLam th (pi _ _ _) ()
thinUnderLam th (lam t) refl = t , refl , refl
thinUnderLam th [ _ ] ()

thinUnderEmb : {n m : Nat}(th : n <= m)(t : Tm n chk)
            -> forall {e}
            -> [ e ] == Th.act th t
            -> Sg _ \e' ->
               t == [ e' ] * e == Th.act th e'
thinUnderEmb th star ()
thinUnderEmb th (pi _ _ _) ()
thinUnderEmb th (lam _) ()
thinUnderEmb th [ e ] refl = e , refl , refl

thinUnderVar : {n m : Nat}(th : n <= m)(e : Tm n syn)
            -> forall {i}
            -> var i == Th.act th e
            -> Sg _ \j ->
               e == var j * i == thin th j
thinUnderVar th (var x) refl = x , refl , refl
thinUnderVar th (_ $ _) ()
thinUnderVar th (_ :: _) ()

thinUnderApp : {n m : Nat}(th : n <= m)(e : Tm n syn)
            -> forall {f s}
            -> f $ s == Th.act th e
            -> Sg _ \f' ->
               Sg _ \s' ->
               e == f' $ s' * f == Th.act th f' * s == Th.act th s'
thinUnderApp th (var _) ()
thinUnderApp th (f $ s) refl = f , s , refl , refl , refl
thinUnderApp th (_ :: _) ()

thinUnderAnn : {n m : Nat}(th : n <= m)(e : Tm n syn)
            -> forall {t T}
            -> t :: T == Th.act th e
            -> Sg _ \t' ->
               Sg _ \T' ->
               e == t' :: T' * t == Th.act th t' * T == Th.act th T'
thinUnderAnn th (var _) ()
thinUnderAnn th (_ $ _) ()
thinUnderAnn th (t :: T) refl = t , T , refl , refl , refl

-- Thinning is an injection
thinActInj : {n m : Nat}(th : n <= m)
          {d : Dir}(s t : Tm n d)
       -> Th.act th s == Th.act th t -> s == t
thinActInj th star t p = sym (thinUnderStar th t p)
thinActInj th (pi q S T) t p with thinUnderPi th t p
... | S' , T' , refl , thS=thS' , thT=thT'
  rewrite thinActInj _ S S' thS=thS' | thinActInj _ T T' thT=thT'
  = refl
thinActInj th (lam s) t p with thinUnderLam th t p
... | t' , refl , ths=tht' rewrite thinActInj _ s t' ths=tht'
  = refl
thinActInj th [ e ] t p with thinUnderEmb th t p
... | t' , refl , the=tht' rewrite thinActInj _ e t' the=tht'
  = refl
thinActInj th (var x) t p with thinUnderVar th t p
... | y , refl , thx=thy rewrite thinInj th thx=thy
  = refl
thinActInj th (f $ s) t p with thinUnderApp th t p
... | f' , s' , refl , thf=thf' , ths=ths'
  rewrite thinActInj _ f f' thf=thf' | thinActInj _ s s' ths=ths'
  = refl
thinActInj th (s :: S) t p with thinUnderAnn th t p
... | s' , S' , refl , ths=ths' , thS=thS'
  rewrite thinActInj _ s s' ths=ths' | thinActInj _ S S' thS=thS'
  = refl
