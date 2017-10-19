module RedNorm {Q : Set} where

open import Basics
open import Star
open import OPE
open import Dir
open import Tm {Q}
open import Env
open import Subst {Q}

data _~>_ {n} : {d : Dir} -> Tm n d -> Tm n d -> Set where
  piL   : forall q {S S'} -> S ~> S' -> forall T -> pi q S T ~> pi q S' T
  piR   : forall q S {T T'} -> T ~> T' -> pi q S T ~> pi q S T'
  lam   : forall {t t'} -> t ~> t' -> lam t ~> lam t'
  [_]   : forall {e e'} -> e ~> e' -> [ e ] ~> [ e' ]
  _$L_  : forall {f f'} -> f ~> f' -> forall s -> (f $ s) ~> (f' $ s)
  _$R_  : forall f {s s'} -> s ~> s' -> (f $ s) ~> (f $ s')
  _::L_ : forall {t t'} -> t ~> t' -> forall T -> (t :: T) ~> (t' :: T)
  _::R_ : forall t {T T'} -> T ~> T' -> (t :: T) ~> (t :: T')
  beta  : forall {q t S T s} ->
            ((lam t :: pi q S T) $ s) ~> Sb.act (si -, (s :: S)) (t :: T)
  upsi  : forall {t T} -> [ t :: T ] ~> t

_~>*_ : forall {n d} -> Tm n d -> Tm n d -> Set
s ~>* t = Star _~>_ s t

data Nm (n : Nat) : Dir -> Set where
  star : Nm n chk
  pi   : Q -> Nm n chk -> Nm (su n) chk -> Nm n chk
  lam  : Nm (su n) chk -> Nm n chk
  [_]  : Nm n syn -> Nm n chk
  var  : Fin n -> Nm n syn
  _$_  : Nm n syn -> Nm n chk -> Nm n syn
  [_]::Pi_!_>_:$_ :
    Nm n syn -> Q -> Nm n chk -> Nm (su n) chk -> Nm n chk -> Nm n syn

fog : forall {n d} -> Nm n d -> Tm n d
fog star = star
fog (pi q S T) = pi q (fog S) (fog T)
fog (lam t) = lam (fog t)
fog [ e ] = [ fog e ]
fog (var i) = var i
fog (f $ s) = fog f $ fog s
fog ([ f ]::Pi q ! S > T :$ s) = ([ fog f ] :: pi q (fog S) (fog T)) $ fog s

nmNoRed : forall {n d} s {t t' : Tm n d} -> t ~> t' -> t == fog s -> Zero
nmNoRed star () refl
nmNoRed (pi q S T) (piL r SS' .(fog T)) refl = naughty (nmNoRed S SS' refl) 
nmNoRed (pi q S T) (piR r .(fog S) TT') refl = naughty (nmNoRed T TT' refl)
nmNoRed (lam t) (lam tt') refl = naughty (nmNoRed t tt' refl)
nmNoRed [ s ] (piL q tt' T) ()
nmNoRed [ s ] (piR q S tt') ()
nmNoRed [ s ] (lam tt') ()
nmNoRed [ e ] [ ee' ] refl = naughty (nmNoRed e ee' refl) 
nmNoRed [ var i ] upsi ()
nmNoRed [ f $ s ] upsi ()
nmNoRed [ [ e ]::Pi q ! S > T₁ :$ s ] upsi ()
nmNoRed (var i) () refl
nmNoRed (f $ s) (ff' $L .(fog s)) refl = naughty (nmNoRed f ff' refl)
nmNoRed (f $ s) (.(fog f) $R ss') refl = naughty (nmNoRed s ss' refl)
nmNoRed (f $ s) (tt' ::L T) ()
nmNoRed (f $ s) (t ::R tt') ()
nmNoRed (var _ $ s) beta ()
nmNoRed ((_ $ _) $ _) beta ()
nmNoRed (([ _ ]::Pi _ ! _ > _ :$ _) $ _) beta ()
nmNoRed ([ e ]::Pi q ! S > T :$ s)
  ((ee' ::L .(pi q (fog S) (fog T))) $L .(fog s)) refl
  = naughty (nmNoRed [ e ] ee' refl)
nmNoRed ([ e ]::Pi q ! S > T :$ s) ((.([ fog e ]) ::R FF') $L .(fog s)) refl
  = naughty (nmNoRed (pi q S T) FF' refl)
nmNoRed ([ e ]::Pi q ! S > T :$ s)
  (.([ fog e ] :: pi q (fog S) (fog T)) $R ss') refl
  = naughty (nmNoRed s ss' refl)
nmNoRed ([ _ ]::Pi _ ! _ > _ :$ _) (tt' ::L T) ()
nmNoRed ([ _ ]::Pi _ ! _ > _ :$ _) (t ::R tt') ()
nmNoRed ([ _ ]::Pi _ ! _ > _ :$ _) beta ()
