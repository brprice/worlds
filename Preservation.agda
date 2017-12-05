open import WorldSystem

module Preservation {QW : WorldSystem} where

open WorldSystem.WorldSystem QW

open import Basics
open import OPE
open import Star
open import Env
open import Dir
open import Tm {Q Real}
open import Subst {Q Real}
open import Par {Q Real}
open import Dev {Q Real}
open import Typing {QW}

-- Lift parallel reduction to contexts
_!~>>*_ : forall {n} -> Cx n -> Cx n -> Set
[] !~>>* [] = One
(Ga -, (u , S)) !~>>* (De -, (v , T)) = (Ga !~>>* De) * u == v * (S ~>>* T)

!~>>*refl : forall {n} -> (Ga : Cx n) -> Ga !~>>* Ga
!~>>*refl [] = <>
!~>>*refl (Ga -, (w , S)) = !~>>*refl Ga , refl , []

zeMor : forall {n}{Ga : Cx n}{w s S S'} ->
        CHK Ga (st-act w) star S -> CHK Ga w S s -> S ~>>* S' ->
        CxMor Ga (Ga -, (w , S')) (si -, (s :: S))
zeMor {n}{Ga}{w}{s}{S}{S'} *S Ss SS'
  rewrite ActId.actId SUBSTID S'
        = idCxMor Ga , post* (*S :~: Ss) SS'

presCxWTy : forall {n}{Ga De : Cx n} ->
  Ga !~>>* De -> (i : Fin n) ->
  cxW Ga i == cxW De i * cxTy Ga i ~>>* cxTy De i
presCxWTy {Ga = Ga -, (u , S)} {De -, (v , T)} (Ga~>*De , u=v , S~>*T) ze
  = u=v , starm (Th.act (o' oi)) (parThin (o' oi)) S~>*T
presCxWTy {Ga = Ga -, _} {De -, _} (Ga~>*De , _ , _) (su i)
  with presCxWTy Ga~>*De i
... | u=v , S~>*T = u=v , starm (Th.act (o' oi)) (parThin (o' oi)) S~>*T

presCxW : forall {n}{Ga De : Cx n} ->
  Ga !~>>* De -> (i : Fin n) ->
  cxW Ga i == cxW De i
presCxW Ga~>*De i = fst (presCxWTy Ga~>*De i)

presCxTy : forall {n}{Ga Ga' : Cx n} ->
  Ga !~>>* Ga' -> (i : Fin n) -> cxTy Ga i ~>>* cxTy Ga' i
presCxTy Ga~>*De i = snd (presCxWTy Ga~>*De i)

presCHK : forall {n}{Ga Ga' : Cx n}{w}{T T' : Tm n chk}{t t' : Tm n chk} ->
  Ga !~>>* Ga' -> T ~>>* T' -> t ~>> t' ->
  CHK Ga w T t -> CHK Ga' w T' t'

presSYN : forall {n}{Ga Ga' : Cx n}{w}{e e' : Tm n syn}{S : Tm n chk} ->
  Ga !~>>* Ga' -> e ~>> e' ->
  SYN Ga w e S -> Sg (Tm n chk) \ S' -> (S ~>>* S') * SYN Ga' w e' S'
presCHK rGa rT0 rt (pre rT1 Tt) with confluence rT0 (rT1 ,- [])
... | _ , rT2 , rT3 = pre* rT2 (presCHK rGa rT3 rt Tt)
presCHK rGa rT star (star tyW) with starInvRed rT
presCHK rGa rT star (star tyW) | refl = star tyW
presCHK rGa rT (pi _ SS' TT') (pi tyW quw S T) with starInvRed rT
presCHK rGa rT (pi _ SS' TT') (pi tyW quw S T) | refl
  = pi tyW quw (presCHK rGa [] SS' S) (presCHK (rGa , refl , (SS' ,- [])) [] TT' T)
presCHK rGa rT (lam rt) (lam qw Tt) with piInvRed rT
presCHK rGa rT (lam rt) (lam qw Tt) | S , T , refl , SS' , TT'
  = lam qw (presCHK (rGa , refl , SS') TT' rt Tt)
presCHK rGa rT [ re ] ([ e ] refl) with presSYN rGa re e
... | S' , SS' , e'S' with confluence rT SS'
... | Sw , T'Sw , S'Sw = pre* T'Sw ([ post* e'S' S'Sw ] refl)
presCHK {n} rGa rT (upsi rt) ([ e ] refl) = help rGa rT rt e where
  help : forall {t t' T U V : Tm n chk}{Ga Ga' w} ->
           Ga !~>>* Ga' -> U ~>>* V -> t ~>> t' -> SYN Ga w (t :: T) U ->
           CHK Ga' w V t'
  help rGa UV tt' (post tTS SU) = help rGa (SU ,- UV) tt' tTS
  help rGa UV tt' (T :~: t) = presCHK rGa UV tt' t

presSYN rGa re (post eS S0S') with presSYN rGa re eS
... | _ , S0S1 , eS1 with confluence S0S1 (S0S' ,- [])
... | _ , S1Sw , S'Sw = _ , S'Sw , post* eS1 S1Sw
presSYN rGa (var .i) (var i u<v) rewrite presCxW rGa i = _ , presCxTy rGa i , var i u<v
presSYN rGa (rf $ rs) (fST $~ qw ~$ Ss) with presSYN rGa rf fST
... | _ , STS'T' , f'S'T' with piInvRed STS'T'
presSYN rGa (rf $ rs) (fST $~ qw ~$ Ss)
  | .(pi _ S' T') , STS'T' , f'S'T'
  | (S' , T' , refl , SS' , TT')
  with presCHK rGa SS' rs Ss
... | S's'
  =  _ , substStab (rs ,- []) SS' TT' , (f'S'T' $~ qw ~$ S's')
presSYN rGa (beta {S = S}{S'}{T}{T'}{s}{s'} tt' SS' TT' ss')
  (_$~_~$_ {S = Si}{Ti} fST q-w Sis)
  with annInv fST
... | *piST , piSTlamt , piSTpiSiTi
  with lamInv piSTlamt | piInvRed piSTpiSiTi
... | qw1' , q-w1 , Sc , Tc , SSc , TTc , Tct | .Si , .Ti , refl , SSi , TTi
  with piInvSt q-w *piST
... | *S , *T
  with consensus S (S' ,- Si ,- Sc ,- []) ((SS' ,- []) , SSi , SSc , <>)
     | consensus T (T' ,- Ti ,- Tc ,- []) ((TT' ,- []) , TTi , TTc , <>)
...  | Sw , SSw , S'Sw , SiSw , ScSw , <>
     | Tw , TTw , T'Tw , TiTw , TcTw , <>
  with presCHK rGa [] SS' *S | presCHK rGa SiSw ss' Sis
     | presCHK (rGa , refl , SSw) [] TT' *T  | presCHK (rGa , refl , ScSw) TcTw tt' Tct
...  | hS | hs | hT | ht
  rewrite #functional q-w1 q-w
    = let zada = zeMor hS (pre* S'Sw hs) S'Sw
      in  Sb.act (si -, (s' :: Sw)) Tw
          , substStab (ss' ,- []) SiSw TiTw
          , post* (substCHK (si -, (s' :: S')) zada hT
                   :~: substCHK (si -, (s' :: S')) zada (pre* T'Tw ht))
              (substStab [] S'Sw T'Tw)
presSYN rGa (rt :: rT) (T :~: t) =
  _ , (rT ,- []) , (presCHK rGa [] rT T :~: presCHK rGa (rT ,- []) rt t)

presVALID : forall {n}{Ga Ga' : Cx n} -> Ga !~>>* Ga' -> VALID Ga -> VALID Ga'
presVALID {Ga' = []} rGa emp = emp
presVALID {Ga' = Ga' -, (w , S)} (rGa , refl , SS') (ext valid *S)
  = ext (presVALID rGa valid)
        (starLiftPres (\S → CHK Ga' (st-act w) star S)
                      (\SS' *S -> presCHK (!~>>*refl _) [] SS' *S)
                      SS'
                      (presCHK rGa [] (parRefl _) *S))


presCHK* : forall {n}{Ga Ga' : Cx n}{w}{T T' : Tm n chk}{t t' : Tm n chk} ->
  Ga !~>>* Ga' -> T ~>>* T' -> t ~>>* t' ->
  CHK Ga w T t -> CHK Ga' w T' t'
presCHK* rGa rT [] Tt = presCHK rGa rT (parRefl _) Tt
presCHK* rGa rT (rt ,- rts) Tt = presCHK* (!~>>*refl _) [] rts (presCHK rGa rT rt Tt)

presSYN* : forall {n}{Ga Ga' : Cx n}{w}{e e' : Tm n syn}{S : Tm n chk} ->
  Ga !~>>* Ga' -> e ~>>* e' ->
  SYN Ga w e S -> Sg (Tm n chk) \ S' -> (S ~>>* S') * SYN Ga' w e' S'
presSYN* rGa [] eS = presSYN rGa (parRefl _) eS
presSYN* rGa (re ,- res) eS with presSYN rGa re eS
... | S' , SS' , e'S' with presSYN* (!~>>*refl _) res e'S'
... | S'' , S'S'' , e''S'' = S'' , (SS' ++ S'S'') , e''S''
