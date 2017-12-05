module Er where

open import Basics
open import OPE
open import Env

------------------------------------------------------------------------------
----- Syntax of the erasure --------------------------------------------------
------------------------------------------------------------------------------
data Er n : Set where
  star : Er n
  pi   : Er n -> Er (su n) -> Er n
  erpi : Er (su n) -> Er n
  arr  : Er n -> Er n -> Er n
  lam  : Er (su n) -> Er n

  var  : Fin n -> Er n
  _$_  : Er n -> Er n -> Er n
infix 30 _$_

thinEr : forall {m n} -> m <= n -> Er m -> Er n
thinEr th star = star
thinEr th (pi S T) = pi (thinEr th S) (thinEr (os th) T)
thinEr th (erpi T) = erpi (thinEr (os th) T)
thinEr th (arr S T) = arr (thinEr th S) (thinEr th T)
thinEr th (lam t) = lam (thinEr (os th) t)
thinEr th (var x) = var (thin th x)
thinEr th (f $ s) = thinEr th f $ thinEr th s

thinErId : forall {n} -> (t : Er n) -> thinEr oi t == t
thinErId star = refl
thinErId (pi S T) rewrite thinErId S | thinErId T = refl
thinErId (erpi T) rewrite thinErId T = refl
thinErId (arr S T) rewrite thinErId S | thinErId T = refl
thinErId (lam t) rewrite thinErId t = refl
thinErId (var x) rewrite oiQ x = refl
thinErId (f $ s) rewrite thinErId f | thinErId s = refl

-- Weaken an environment of erased terms
wkEnvEr : forall {m n} -> Env (Er m) n -> Env (Er (su m)) (su n)
wkEnvEr erz = env (thinEr (o' oi)) erz -, var ze

-- Substitution for erased terms
substEr : forall {m n} -> Env (Er m) n -> Er n -> Er m
substEr erz star = star
substEr erz (pi S T) = pi (substEr erz S) (substEr (wkEnvEr erz) T)
substEr erz (erpi T) = erpi (substEr (wkEnvEr erz) T)
substEr erz (arr S T) = arr (substEr erz S) (substEr erz T)
substEr erz (lam t) = lam (substEr (wkEnvEr erz) t)
substEr erz (var i) = erz ! i
substEr erz (f $ s) = substEr erz f $ substEr erz s

-- Identity substitution
siE : forall {n} -> Env (Er n) n
siE {ze} = []
siE {su n} = wkEnvEr siE

siEQ : forall {n}(i : Fin n) -> (siE ! i) == var i
siEQ ze = refl
siEQ (su i) rewrite env!Q (thinEr (o' oi)) siE i | siEQ i | oiQ i = refl

substErId : forall {n} -> (t : Er n) -> substEr siE t == t
substErId star = refl
substErId (pi S T) rewrite substErId S | substErId T = refl
substErId (erpi T) rewrite substErId T = refl
substErId (arr S T) rewrite substErId S | substErId T = refl
substErId (lam t) rewrite substErId t = refl
substErId (var x) = siEQ x
substErId (f $ s) rewrite substErId f | substErId s = refl

-- Erasure reductions, single step
data _~>E_ {n} : Er n -> Er n -> Set where
  piL   : forall {S S'} -> S ~>E S' -> forall T -> pi S T ~>E pi S' T
  piR   : forall S {T T'} -> T ~>E T' -> pi S T ~>E pi S T'
  erpi  : forall {T T'} -> T ~>E T' -> erpi T ~>E erpi T'
  arrL  : forall {S S'} -> S ~>E S' -> forall T -> arr S T ~>E arr S' T
  arrR  : forall S {T T'} -> T ~>E T' -> arr S T ~>E arr S T'
  lam   : forall {t t'} -> t ~>E t' -> lam t ~>E lam t'
  _$L_  : forall {f f'} -> f ~>E f' -> forall s -> f $ s ~>E f' $ s
  _$R_  : forall f {s s'} -> s ~>E s' -> f $ s ~>E f $ s'
  beta  : forall {t s} -> lam t $ s ~>E substEr (siE -, s) t
