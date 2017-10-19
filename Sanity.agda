open import WorldSystem

module Sanity {QW : WorldSystem} where

open WorldSystem.WorldSystem QW

open import Basics
open import Star
open import OPE
open import Dir
open import Tm {Q Real}
open import Env
open import Subst {Q Real}
open import Typing {QW}
open import Preservation {QW}

sanityVar : forall {n}{Ga : Cx n} ->
            VALID Ga -> (i : Fin n) ->
            CHK Ga (st-act (cxW Ga i)) star (cxTy Ga i)
sanityVar {Ga = Ga -, (_ , _)}(ext valid *S) ze = thinCHK (o' oi) (idThinC Ga) *S
sanityVar {Ga = Ga -, (_ , _)}(ext valid _) (su i) = thinCHK (o' oi) (idThinC Ga) (sanityVar valid i)

sanity : forall {n Ga w e}{S : Tm n chk} -> VALID Ga -> SYN Ga w e S -> CHK Ga (st-act w) star S
sanity valid (post eS' S'S) = presCHK (!~>>*refl _) [] S'S (sanity valid eS')
sanity valid (var i u<w) = subsumeCHK _ (st-op u<w) (sanityVar valid i)
sanity valid (_$~_~$_ {s = s}{S} fST qw Ss) with piInvSt qw (sanity valid fST)
... | *S , *T = substCHK (si -, (s :: S)) (zeMor *S Ss []) *T
sanity valid (T :~: Tt) = T
