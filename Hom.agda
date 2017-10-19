-- World homomorphisms

module Hom where

open import Basics
open import OPE
open import Env

open import WorldSystem
open WorldSystem.WorldSystem

unJust= : {A : Set}{x y : A} -> Just x == Just y -> x == y
unJust= refl = refl

record WorldHom (qw1 qw2 : WorldSystem) : Set where
  field
    FW : W qw1 -> W qw2
    FQ : {s : Sort} -> Q qw1 s  -> Q qw2 s

    pres<< : forall {u v} -> _<<_ qw1 u v -> _<<_ qw2 (FW u) (FW v)
    presTyW : forall {w} -> tyW qw1 w -> tyW qw2 (FW w)
    presAct : forall {s}{q : Q qw1 s}{w qw} -> _#_ qw1 q w ~ qw -> _#_ qw2 (FQ q) (FW w) ~ FW qw
    presSt : FQ (st qw1) == st qw2
    presUnst : forall {sw' w} -> unst qw1 sw' ~ w -> unst qw2 (FW sw') ~ FW w

  presStAct : forall w -> FW (st-act qw1 w) == st-act qw2 (FW w)
  presStAct w with presAct (st-pr qw1 w)
  ... | p rewrite presSt | st-pr qw2 (FW w) = sym (unJust= p)

  presAct? : forall {s}(q : One + Q qw1 s){w qw}
          -> _#?_ qw1 q w ~ qw
          -> _#?_ qw2 (either {C = \_ -> One + Q qw2 s} (\r -> inl r) (\r -> inr (FQ r)) q) (FW w) ~ FW qw
  presAct? (inl _) refl = refl
  presAct? (inr r) qw = presAct qw

  pres&Unst& : forall q r w {quw'}
           -> _#_ qw1 (snd (_&unst&_ qw1 q r)) w ~ quw'
           -> forall {rw'} -> _#?_ qw1 r w ~ rw'
           -> _#_ qw2 (FQ (snd (_&unst&_ qw1 q r))) (FW w)
           == _#_ qw2 (snd (_&unst&_ qw2 (FQ q) (either (\x -> inl x) (\r' -> inr (FQ r')) r))) (FW w)
  pres&Unst& q r w p {rw'} rw
    rewrite presAct p
          | &unst&-action qw2 (FQ q) (either (\x -> inl x) (\r' -> inr (FQ r')) r) (FW w)
          | presAct? r rw
          | &unst&-action qw1 q r w
          | rw
    with unst qw1 rw' | inspect (unst qw1) rw'
  pres&Unst& q r w () {rw'} rw | Nothing | _
  pres&Unst& q r w p {rw'} rw | Just uw' | [ uw ] rewrite presUnst uw | presAct p = refl

import Subst
open Subst using (si)
open import Dir
import Tm
import Typing
open import Par
open import RedNorm

module _ (qw1 qw2 : WorldSystem)(Hom : WorldHom qw1 qw2) where
  open WorldHom Hom

  open Subst {Q qw1 Real} renaming (module Sb to Sb1) using ()
  open Subst {Q qw2 Real} renaming (module Sb to Sb2) using ()
  open Tm {Q qw1 Real} renaming (Tm to Tm1) using ()
  open Tm {Q qw2 Real} renaming (Tm to Tm2) using ()
  open Tm
  open Typing {qw1} renaming (Cx to Cx1) using ()
  open Typing {qw2} renaming (Cx to Cx2) using ()
  open Typing

  F : forall {n}{d} -> Tm1 n d -> Tm2 n d
  F star = star
  F (pi q S T) = pi (FQ q) (F S) (F T)
  F (lam t) = lam (F t)
  F [ t ] = [ F t ]
  F (var x) = var x
  F (f $ t) = F f $ F t
  F (t :: T) = F t :: F T

  FThinQ : forall {n m}(th : n <= m){d}(t : Tm1 n d) -> F (Th.act th t) == Th.act th (F t)
  FThinQ th star = refl
  FThinQ th (pi q S T) rewrite FThinQ th S | FThinQ (os th) T = refl
  FThinQ th (lam t) rewrite FThinQ (os th) t = refl
  FThinQ th [ t ] rewrite FThinQ th t = refl
  FThinQ th (var x) = refl
  FThinQ th (f $ s) rewrite FThinQ th f | FThinQ th s = refl
  FThinQ th (t :: T) rewrite FThinQ th t | FThinQ th T = refl

  FCx : forall {n} -> Cx1 n -> Cx2 n
  FCx [] = []
  FCx (Ga -, (w , S)) = FCx Ga -, (FW w , F S)

  FCxWQ : forall {n}(Ga : Cx n) i -> cxW (FCx Ga) i == FW (cxW Ga i)
  FCxWQ [] ()
  FCxWQ (Ga -, (w , S)) ze = refl
  FCxWQ (Ga -, (w , S)) (su i) = FCxWQ Ga i

  FCxTyQ : forall {n}(Ga : Cx n) i -> cxTy (FCx Ga) i == F (cxTy Ga i)
  FCxTyQ [] ()
  FCxTyQ (Ga -, (w , S)) ze = sym (FThinQ (o' oi) S)
  FCxTyQ (Ga -, (w , S)) (su i) rewrite FCxTyQ Ga i = sym (FThinQ (o' oi) (cxTy Ga i))

  envFWkQ : forall {n m}(ez : Env (Tm1 m syn) n)
     -> env F (env (Th.act (o' oi)) ez) == env (Th.act (o' oi)) (env F ez)
  envFWkQ [] = refl
  envFWkQ (ez -, e) rewrite envFWkQ ez | FThinQ (o' oi) e = refl

  envFsiQ : forall n -> env {n} F si == si
  envFsiQ ze = refl
  envFsiQ (su n) rewrite envFWkQ {n} si | envFsiQ n = refl

  homPresSubst : forall {n m}(ez : Env (Tm1 m syn) n){d}(t : Tm1 n d)
              -> F (Sb1.act ez t) == Sb2.act (env F ez) (F t)
  homPresSubst ez star = refl
  homPresSubst ez (pi x S T)
    rewrite homPresSubst ez S | homPresSubst (Sb1.actW ez) T
          | envFWkQ ez
    = refl
  homPresSubst ez (lam t)
    rewrite homPresSubst (Sb1.actW ez) t
          | envFWkQ ez
    = refl
  homPresSubst ez [ t ] rewrite homPresSubst ez t = refl
  homPresSubst ez (var x) = sym (env!Q F ez x)
  homPresSubst ez (f $ s) rewrite homPresSubst ez f | homPresSubst ez s
    = refl
  homPresSubst ez (t :: T) rewrite homPresSubst ez t | homPresSubst ez T
    = refl

  homPresComp : forall {n d}{s t : Tm1 n d} -> s ~> t -> F s ~> F t
  homPresComp (piL q red T) = piL (FQ q) (homPresComp red) (F T)
  homPresComp (piR q S red) = piR (FQ q) (F S) (homPresComp red)
  homPresComp (lam red) = lam (homPresComp red)
  homPresComp [ red ] = [ homPresComp red ]
  homPresComp (red $L s) = homPresComp red $L F s
  homPresComp (f $R red) = F f $R homPresComp red
  homPresComp (red ::L T) = homPresComp red ::L F T
  homPresComp (t ::R red) = F t ::R homPresComp red
  homPresComp {n} (beta {q}{t}{S}{T}{s})
    rewrite homPresSubst (si -, s :: S) (t :: T)
          | envFsiQ n
    = beta {q = FQ q}{F t}{F S}{F T}{F s}
  homPresComp upsi = upsi

  homPresPar : forall {n d}{s t : Tm1 n d} -> s ~>> t -> F s ~>> F t
  homPresPar star = star
  homPresPar (pi q SS' TT') = pi (FQ q) (homPresPar SS') (homPresPar TT')
  homPresPar (lam red) = lam (homPresPar red)
  homPresPar [ red ] = [ homPresPar red ]
  homPresPar (var i) = var i
  homPresPar (ff' $ ss') = homPresPar ff' $ homPresPar ss'
  homPresPar (tt' :: TT') = homPresPar tt' :: homPresPar TT'
  homPresPar {n} (beta {t' = t'}{S' = S'}{T' = T'}{s' = s'} tt' SS' TT' ss')
    rewrite homPresSubst (si -, s' :: S') (t' :: T')
          | envFsiQ n
    = beta (homPresPar tt') (homPresPar SS') (homPresPar TT') (homPresPar ss')
  homPresPar (upsi red) = upsi (homPresPar red)

  homPresCHK : forall {n}{Ga : Cx1 n}{w}{T t : Tm1 n chk}
            -> CHK Ga w T t -> CHK (FCx Ga) (FW w) (F T) (F t)
  homPresSYN : forall {n}{Ga : Cx1 n}{w}{e : Tm1 n syn}{S : Tm1 n chk}
            -> SYN Ga w e S -> SYN (FCx Ga) (FW w) (F e) (F S)
  homPresCHK (pre TS St) = pre (homPresPar TS) (homPresCHK St)
  homPresCHK (star tyW) = star (presTyW tyW)
  homPresCHK {w = w} (pi {q}{quw'} tyW quw *S *T) with homPresCHK *S | presAct quw
  ... | *FS | Fquw rewrite presStAct quw'
                         | pres&Unst& q (inl <>) w quw refl
    = pi (presTyW tyW) Fquw *FS (homPresCHK *T)
  homPresCHK (lam qw Tt) = lam (presAct qw) (homPresCHK Tt)
  homPresCHK ([ eS ] refl) = [ homPresSYN eS ] refl
  homPresSYN (post eS ST) = post (homPresSYN eS) (homPresPar ST)
  homPresSYN {Ga = Ga} (var i u<w) with pres<< u<w
  ... | Fu<Fw rewrite sym (FCxTyQ Ga i) | sym (FCxWQ Ga i)
    = var i Fu<Fw
  homPresSYN {n}(_$~_~$_ {s = s}{S}{T} fST qw Ss)
    rewrite homPresSubst (si -, s :: S) T | envFsiQ n
    = homPresSYN fST $~ presAct qw ~$ homPresCHK Ss
  homPresSYN {w = w} (*S :~: Ss) with homPresCHK *S
  ... | *FS rewrite presStAct w = *FS :~: homPresCHK Ss

  homPresValid : forall {n}{Ga : Cx1 n} -> VALID Ga -> VALID (FCx Ga)
  homPresValid emp = emp
  homPresValid (ext {w = w} valid *S) with homPresCHK *S
  ... | *FS rewrite presStAct w = ext (homPresValid valid) *FS
