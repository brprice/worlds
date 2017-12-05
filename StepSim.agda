open import WorldSystem
import ErasureSet

module StepSim {QW : WorldSystem}{E : ErasureSet.ErasureSet {QW}} where

open WorldSystem.WorldSystem QW
open ErasureSet {QW}
open ErasureSet.ErasureSet E

open import Basics
open import OPE
open import Star
open import Dir
open import Tm {Q Real}
open import Env
open import Subst {Q Real}
open import RedNorm {Q Real}
open import Par {Q Real}
open import Dev {Q Real}
open import Typing {QW}
open import Preservation {QW}
open import Er
open import Erasure {QW}{E}

------------------------------------------------------------------------------
----- Step simulation A ------------------------------------------------------
------------------------------------------------------------------------------
{-
We prove that if an unerased term takes a single reduction step s ~> t
then the erasure of s takes 0 or 1 step to become the erasure of t
-}

data Reflexive {A : Set}(R : A -> A -> Set) : A -> A -> Set where
  refl : {a : A} -> Reflexive R a a
  rel : {a b : A} -> R a b -> Reflexive R a b

-- M for Maybe
-- This is "0 or 1 steps"
_~>M_ : forall {n} -> Er n -> Er n -> Set
s ~>M t = Reflexive _~>E_ s t

-- lift implications to Reflexive
-- (M for Maybe)
liftM : {A B : Set}
     -> (f : A -> B)
     -> {R : A -> A -> Set}{S : B -> B -> Set}
     -> ({a b : A} -> R a b -> S (f a) (f b))
     -> {a b : A} -> Reflexive R a b
     -> Reflexive S (f a) (f b)
liftM f g refl = refl
liftM f g (rel aRb) = rel (g aRb)

-- Inversion lemma for (lam t :: pi q S T), just combining those for _::_, lam and pi
-- This covers the two cases where qw is erased or not
annLamPiErInvComb : forall {n}{Ga : Cx n}{l}{uner : Unerased Ga l}{w keepW t q S T r A B d}
                 -> SYNEr Ga uner w keepW (lam t :: pi q S T) (pi r A B) d
                 -> q == r
                  * Sg _ \qw' ->
                    q # w ~ qw'
                  * S ~>>* A
                  * T ~>>* B
                  * CHK Ga (st-act qw') star S
                  * CHK (Ga -, (qw' , S)) (st-act w) star T
                  * Sg _ \S'' ->
                    S ~>>* S'' * Sg _ \T'' ->
                    T ~>>* T''
                  * (  (Sg (er? qw' == keep) \keQW ->
                        Sg _ \e ->
                        d == lam e
                      * CHKEr (Ga -, (qw' , S'')) (kee uner keQW) w keepW T'' t e)
                    + (Sg (er? qw' == delete) \deQW ->
                       CHKEr (Ga -, (qw' , S'')) (del uner deQW) w keepW T'' t d)
                    )
annLamPiErInvComb ltSTABd
  with annInvEr ltSTABd
... | *ST , STtd , ST~>AB
  with lamInvEr STtd
... | S'' , S~>S'' , T'' , T~>T'' , qw' , qw , rest
  with piInvSt qw *ST | piInvRed ST~>AB
... | *S , *T | _ , _ , refl , S~>A , T~>B
  = refl , qw' , qw , S~>A , T~>B , *S , *T , S'' , S~>S'' , T'' , T~>T'' , rest

-- The case where qw is not erased
annLamPiErInvKe : forall {r w qw'} -> r # w ~ qw' -> (keQW : er? qw' == keep)
               -> forall {n}{Ga : Cx n}{l}{uner : Unerased Ga l}{keepW t q S T A B d}
               -> SYNEr Ga uner w keepW (lam t :: pi q S T) (pi r A B) d
               -> q == r
                * S ~>>* A
                * T ~>>* B
                * CHK Ga (st-act qw') star S
                * CHK (Ga -, (qw' , S)) (st-act w) star T
                * Sg _ \S'' ->
                  S ~>>* S'' * Sg _ \T'' ->
                  T ~>>* T''
                * Sg _ \e ->
                  d == lam e
                * CHKEr (Ga -, (qw' , S'')) (kee uner keQW) w keepW T'' t e
annLamPiErInvKe qw keQW ltSTAd with annLamPiErInvComb ltSTAd
... | refl , qw'2 , qw2 , S~>A , T~>B , *S , *T , S'' , S~>S'' , T'' , T~>T'' , inr (deQW , T''td)
  rewrite #functional qw qw2
  = naughty (erXorKp deQW keQW)
... | refl , qw'2 , qw2 , S~>A , T~>B , *S , *T , S'' , S~>S'' , T'' , T~>T'' , inl (keQW2 , e , d=lame , T''te)
  rewrite #functional qw qw2 | uip keQW keQW2
  = refl , S~>A , T~>B , *S , *T , S'' , S~>S'' , T'' , T~>T'' , e , d=lame , T''te

-- The case where qw is erased
annLamPiErInvDe : forall {r w qw'} -> r # w ~ qw' -> (deQW : er? qw' == delete)
               -> forall {n}{Ga : Cx n}{l}{uner : Unerased Ga l}{keepW t q S T A B d}
               -> SYNEr Ga uner w keepW (lam t :: pi q S T) (pi r A B) d
               -> q == r
                * S ~>>* A
                * T ~>>* B
                * CHK Ga (st-act qw') star S
                * CHK (Ga -, (qw' , S)) (st-act w) star T
                * Sg _ \S'' ->
                  S ~>>* S'' * Sg _ \T'' ->
                  T ~>>* T''
                * CHKEr (Ga -, (qw' , S'')) (del uner deQW) w keepW T'' t d
annLamPiErInvDe qw deQW ltSTAd with annLamPiErInvComb ltSTAd
... | refl , qw'2 , qw2 , S~>A , T~>B , *S , *T , S'' , S~>S'' , T'' , T~>T'' , inr (deQW2 , T''td)
  rewrite #functional qw qw2 | uip deQW deQW2
  = refl , S~>A , T~>B , *S , *T , S'' , S~>S'' , T'' , T~>T'' , T''td
... | refl , qw'2 , qw2 , S~>A , T~>B , *S , *T , S'' , S~>S'' , T'' , T~>T'' , inl (keQW , e , d=lame , T''te)
  rewrite #functional qw qw2
  = naughty (erXorKp deQW keQW)


zeMorEr : forall {n}{Ga : Cx n}{l}{uner : Unerased Ga l}{w S}
       -> CHK Ga (st-act w) star S
       -> forall {keepW s s'} -> CHKEr Ga uner w keepW S s s'
       -> forall {S'} -> S ~>>* S'
       -> CxMorEr Ga uner (Ga -, (w , S')) (kee uner keepW) (si -, (s :: S)) (siE -, s')
zeMorEr {uner = uner} *S Sss' {S'} S~>S'
  rewrite ActId.actId SUBSTID S'
  = idCxMorEr uner , postEr* (*S :~: Sss') S~>S'


stepSimACHK : forall {n}{t t'}
           -> t ~> t'
           -> forall {Ga : Cx n}{l}{uner : Unerased Ga l}
           -> forall {w keepW}{T s}
           -> CHKEr Ga uner w keepW T t s
           -> Sg _ \s' -> s ~>M s' * CHKEr Ga uner w keepW T t' s'
stepSimASYN : forall {n}{e e'}
           -> e ~> e'
           -> forall {Ga : Cx n}{l}{uner : Unerased Ga l}
           -> forall {w keepW}{S d}
           -> SYNEr Ga uner w keepW e S d
           -> Sg _ \S' -> S ~>>* S' * Sg _ \d' -> d ~>M d' * SYNEr Ga uner w keepW e' S' d'
stepSimACHK t~>t' (pre T~>T' Tts)
  with stepSimACHK t~>t' Tts
... | s' , s~>s' , T't's' = s' , s~>s' , pre T~>T' T't's'
stepSimACHK () (star tyW)
stepSimACHK (piL q S~>R T) (piEE tyW quw deQUW deSQUW *S *TT')
  with presCHK (!~>>*refl _) [] (redPar S~>R) *S
     | presCHKErCxTy (!~>>*refl _ , refl , ~>To~>>* S~>R) [] *TT'
... | *R | R-*TT' = _ , refl , piEE tyW quw deQUW deSQUW *R R-*TT'
stepSimACHK (piR q S T~>R) (piEE tyW quw deQUW deSQUW *S *TT')
  with stepSimACHK T~>R *TT'
... | R' , T'~>R' , *RR' = R' , T'~>R' , piEE tyW quw deQUW deSQUW *S *RR'
stepSimACHK (piL q S~>R T) (piArr tyW quw deQUW keSQUW *SS' *TT')
  with stepSimACHK S~>R *SS'
     | presCHKErCxTy (!~>>*refl _ , refl , ~>To~>>* S~>R) [] *TT'
... | R' , S'~>R' , *RR' | R-*TT'
  = arr R' _ , liftM (\x -> arr x _) (\x -> arrL x _) S'~>R' , piArr tyW quw deQUW keSQUW *RR' R-*TT'
stepSimACHK (piR q S T~>R) (piArr {S' = S'} tyW quw deQUW keSQUW *SS' *TT')
  with stepSimACHK T~>R *TT'
... | R' , T'~>R' , *RR' = arr S' R' , liftM (arr S') (arrR S') T'~>R' , piArr tyW quw deQUW keSQUW *SS' *RR'
stepSimACHK (piL q S~>R T) (piE tyW quw keQUW deSQUW *S *TT')
  with presCHK (!~>>*refl _) [] (redPar S~>R) *S
     | presCHKErCxTy (!~>>*refl _ , refl , ~>To~>>* S~>R) [] *TT'
... | *R | R-*TT' = erpi _ , refl , piE tyW quw keQUW deSQUW *R R-*TT'
stepSimACHK (piR q S T~>R) (piE tyW quw keQUW deSQUW *S *TT')
  with stepSimACHK T~>R *TT'
... | R' , T'~>R' , *RR' = erpi R' , liftM erpi erpi T'~>R' , piE tyW quw keQUW deSQUW *S *RR'
stepSimACHK (piL q S~>R T) (pi tyW quw keQUW keSQUW *SS' *TT')
  with stepSimACHK S~>R *SS'
     | presCHKErCxTy (!~>>*refl _ , refl , ~>To~>>* S~>R) [] *TT'
... | R' , S'~>R' , *RR' | R-*TT'
  = pi R' _ , liftM (\x -> pi x _) (\x -> piL x _) S'~>R' , pi tyW quw keQUW keSQUW *RR' R-*TT'
stepSimACHK (piR q S T~>R) (pi {S' = S'} tyW quw keQUW keSQUW *SS' *TT')
  with stepSimACHK T~>R *TT'
... | R' , T'~>R' , *RR' = pi S' R' , liftM (pi S') (piR S') T'~>R' , pi tyW quw keQUW keSQUW *SS' *RR'
stepSimACHK (lam t~>t') (lamE qw deQW Tts)
  with stepSimACHK t~>t' Tts
... | s' , s~>s' , Tt's' = s' , s~>s' , lamE qw deQW Tt's'
stepSimACHK (lam t~>t') (lam qw keQW Tts)
  with stepSimACHK t~>t' Tts
... | s' , s~>s' , Tt's' = lam s' , liftM Er.lam (_~>E_.lam) s~>s' , lam qw keQW Tt's'
stepSimACHK [ e~>e' ] ([ eSd ] refl)
  with stepSimASYN e~>e' eSd
... | S' , S~>S' , d' , d~>d' , e'S'd' = d' , d~>d' , preEr* S~>S' ([ e'S'd' ] refl)
stepSimACHK upsi {s = s} ([ tTSs ] refl)
  with annInvEr tTSs
... | *T , Tts , T~>S
  with eraseCHK _ _ (presCHK (!~>>*refl _) T~>S (parRefl _) (forgetCHKEr Tts))
... | s' , Sts'
  rewrite thinErInj (eraseUniqCHK equiv!Refl _ _ (~>>*ToEquiv T~>S) Tts Sts')
   = s' , refl , Sts'

stepSimASYN t~>t' (post eSd S~>S')
  with stepSimASYN t~>t' eSd
... | S'' , S~>S'' , d' , d~>d' , e'S''d'
  with confluence (S~>S' ,- []) S~>S''
... | Sc , S'~>Sc , S''~>Sc = Sc , S'~>Sc , d' , d~>d' , postEr* e'S''d' S''~>Sc
stepSimASYN () (var i u<w)
stepSimASYN (f~>f' $L s) (appE fSTd qw deQW Ss)
  with stepSimASYN f~>f' fSTd
... | ST' , ST~>ST' , d' , d~>d' , f'ST'd'
  with piInvRed ST~>ST'
... | S' , T' , refl , S~>S' , T~>T'
  with presCHK (!~>>*refl _) S~>S' (parRefl s) Ss
... | S's
  = Sb.act (si -, (s :: S')) T'
  , substStab [] S~>S' T~>T'
  , d' , d~>d' , appE f'ST'd' qw deQW S's
stepSimASYN (_$R_ f s~>s') (appE {T = T} fSTd qw deQW Ss)
  with presCHK (!~>>*refl _) [] (redPar s~>s') Ss
... | Ss'
  = _ , substStab {T = T} (~>To~>>* s~>s') [] []
  , _ , refl , appE fSTd qw deQW Ss'
stepSimASYN (beta {S = S}{T}{s}) {Ga}{_}{uner} (appE {S = S'}{T'}{f' = d} fSTd qw deQW S's)
  with annLamPiErInvDe qw deQW fSTd
... | refl , S~>S' , T~>T' , *S , *T , S'' , S~>S'' , T'' , T~>T'' , T''td
  with preEr* T~>T'' T''td
     | presCHK (!~>>*refl Ga , refl , S~>S'') [] (parRefl T) *T :~: preEr* T~>T'' T''td
... | Ttd | tTTd
  with substSYNEr (del uner deQW) uner (si -, (s :: S))
                  (zeMor *S (pre* S~>S' S's) S~>S'')
                  siE (idCxMorEr uner) tTTd
... | tT[sS]T[sS]d rewrite substErId d
  = Sb.act (si -, (s :: S')) T' , [] , d , refl , postEr* tT[sS]T[sS]d (substStab [] S~>S' T~>T')
stepSimASYN (f~>f' $L s) (fSTd $~ qw ^ keQW ~$ Sst)
  with stepSimASYN f~>f' fSTd
... | ST' , ST~>ST' , d' , d~>d' , f'ST'd'
  with piInvRed ST~>ST'
... | S' , T' , refl , S~>S' , T~>T'
  with presCHKErCxTy (!~>>*refl _) S~>S' Sst
... | S'st
  = _ , substStab [] S~>S' T~>T'
  , _ , liftM (_$ _) (_$L _) d~>d' , f'ST'd' $~ qw ^ keQW ~$ S'st
stepSimASYN (_$R_ f s~>s') (_$~_^_~$_ {T = T} fSTd qw keQW Sst)
  with stepSimACHK s~>s' Sst
... | t' , t~>t' , Ss't'
  = _ , substStab {T = T} (~>To~>>* s~>s') [] []
  , _ , liftM (_ $_) (_ $R_) t~>t' , fSTd $~ qw ^ keQW ~$ Ss't'
stepSimASYN (beta {S = S}{T}{s}) {Ga}{_}{uner} (_$~_^_~$_ {S = S'}{T'}{s' = e} fSTlamd qw keQW S'se)
  with annLamPiErInvKe qw keQW fSTlamd
... | refl , S~>S' , T~>T' , *S , *T , S'' , S~>S'' , T'' , T~>T'' , d , refl , T''td
  with preEr* T~>T'' T''td
     | presCHK (!~>>*refl Ga , refl , S~>S'') [] (parRefl T) *T :~: preEr* T~>T'' T''td
     | preEr* S~>S' S'se
... | Ttd | tTTd | Sse
  with substSYNEr (kee uner keQW) uner
                  (si -, (s :: S)) (zeMor *S (forgetCHKEr Sse) S~>S'')
                  (siE -, e) (zeMorEr *S Sse S~>S'') tTTd
... | tT[sS]T[sS]d
  = Sb.act (si -, (s :: S')) T' , [] , substEr (siE -, e) d , rel beta , postEr* tT[sS]T[sS]d (substStab [] S~>S' T~>T')
stepSimASYN (s~>s' ::L S) (*S :~: Sst)
  with stepSimACHK s~>s' Sst
... | t' , t~>t' , Ss't' = S , [] , t' , t~>t' , *S :~: Ss't'
stepSimASYN (s ::R S~>S') (*S :~: Sst)
  with presCHK (!~>>*refl _) [] (redPar S~>S') *S
... | *S' = _ , ~>To~>>* S~>S' , _ , refl , *S' :~: presCHKErCxTy (!~>>*refl _) (~>To~>>* S~>S') Sst


------------------------------------------------------------------------------
----- Erasures and Lambdas ---------------------------------------------------
------------------------------------------------------------------------------
-- We need that if the erasure of a term is a lambda, then the original
-- term computes to a string of erased lambdas plus one unerased one

-- a pi with n erased arguments and one non-erased
nPi : W -> Nat -> Nat -> Set
nPi w m ze = Sg (Q Real) \q -> Sg _ \qw' ->
             q # w ~ qw' * er? qw' == keep * Tm m chk * Tm (su m) chk
nPi w m (su n) = Sg (Q Real) \q -> Sg _ \qw' ->
                 q # w ~ qw' * er? qw' == delete * Tm m chk * nPi w (su m) n

nPiToTy : forall {w m} n -> nPi w m n -> Tm m chk
nPiToTy ze (q , qw' , qw , keQW , S , T) = pi q S T
nPiToTy (su n) (q , qw' , qw , deQW , S , rest) = pi q S (nPiToTy n rest)

-- a lambda with n erased bound variables and one non-erased
nLam : Nat -> Nat -> Set
nLam m ze = Tm (su m) chk
nLam m (su n) = nLam (su m) n

nLamToTm : forall {m} n -> nLam m n -> Tm m chk
nLamToTm ze t = lam t
nLamToTm (su n) t = lam (nLamToTm n t)

-- substitution for nPi
substnPi : forall {m1 m2} -> Env (Tm m2 syn) m1 -> forall {w} n -> nPi w m1 n -> nPi w m2 n
substnPi ez ze (q , qw' , qw , keQW , S , T)
  = q , qw' , qw , keQW , Sb.act ez S , Sb.act (Sb.actW ez) T
substnPi ez (su n) (q , qw' , qw , keQW , S , rest)
  = q , qw' , qw , keQW , Sb.act ez S , substnPi (Sb.actW ez) n rest

-- substitution for nPi is actually substitution when interpreted
substnPiQ : forall {m1 m2}(ez : Env (Tm m2 syn) m1)
         -> forall {w} n (p : nPi w m1 n)
         -> Sb.act ez (nPiToTy n p) == nPiToTy n (substnPi ez n p)
substnPiQ ez ze (q , qw' , qw , keQW , S , T) = refl
substnPiQ ez (su n) (q , qw' , qw , keQW , S , rest)
  rewrite substnPiQ (Sb.actW ez) n rest = refl

-- substitution for nLam
substnLam : forall {m1 m2} -> Env (Tm m2 syn) m1 -> forall n -> nLam m1 n -> nLam m2 n
substnLam ez ze l = Sb.act (Sb.actW ez) l
substnLam ez (su n) l = substnLam (Sb.actW ez) n l

-- substitution for nLam is actually substitution when interpreted
substnLamQ : forall {m1 m2}(ez : Env (Tm m2 syn) m1)
         -> forall n (l : nLam m1 n)
         -> Sb.act ez (nLamToTm n l) == nLamToTm n (substnLam ez n l)
substnLamQ ez ze t = refl
substnLamQ ez (su n) t
  rewrite substnLamQ (Sb.actW ez) n t = refl

-- star will never be a pi
stNoRednPi : forall {w m} n {p : nPi w m n} -> star ~>>* nPiToTy n p -> Zero
stNoRednPi ze rs with starInvRed rs
... | ()
stNoRednPi (su n) rs with starInvRed rs
... | ()

-- We will need that some nPi have at least one erased argument
-- this type captures those nPi w m (su n)
data sunPi {w m} q : (n : Nat) -> nPi w m n -> Set where
  mkSunPi : forall n' qw' qw deQW S T
         -> sunPi q (su n') (q , qw' , qw , deQW , S , T)

-- In particular, if a pi with an erased argument reduces to an nPi
-- then said nPi will have an erased argument
dePi~>nPi : forall {q w qw'}
         -> q # w ~ qw'
         -> (deQW : er? qw' == delete)
         -> forall {m} n {p : nPi w m n}{S T} -> pi q S T ~>>* nPiToTy n p
         -> sunPi q n p
dePi~>nPi qw1 deQW ze {q , qw'2 , qw2 , keQW , S' , T'} ST~>p
  with piInvRed ST~>p
... | _ , _ , refl , _ , _
  rewrite #functional qw1 qw2
  = naughty (erXorKp deQW keQW)
dePi~>nPi qw1 deQW1 (su n) {q , qw'2 , qw2 , deQW2 , S' , p'} ST~>p
  with piInvRed ST~>p
... | _ , _ , refl , _ , _
    rewrite #functional qw1 qw2
  = mkSunPi n qw'2 qw2 deQW2 S' p'

-- If a pi with an unerased argument reduces to an nPi
-- then said nPi will have zero erased arguments
kePi~>nPi : forall {q w qw'}
         -> q # w ~ qw'
         -> er? qw' == keep
         -> forall n {m}{S : Tm m chk}{T ST'} -> pi q S T ~>>* nPiToTy {w} n ST'
         -> n == ze
kePi~>nPi qw keQW ze ST~>ST' = refl
kePi~>nPi qw1 keQW (su n) {ST' = q , qw' , qw2 , deQW , S' , T'} ST~>ST'
  with piInvRed ST~>ST'
... | .S' , .(nPiToTy n T') , refl , S~>S' , T~>T'
  rewrite #functional qw1 qw2
  = naughty (erXorKp deQW keQW)

-- reducts of nPi are themselves nPi, one step version
nPiInvRed1 : forall {w m} n {S : nPi w m n}{T} -> nPiToTy n S ~>> T -> Sg (nPi w m n) \T' -> T == nPiToTy n T'
nPiInvRed1 ze {.q , qw' , qw , deQW , S , T}(pi q {S' = S'}{T' = T'} S~>S' T~>T')
  = (q , qw' , qw , deQW , S' , T') , refl
nPiInvRed1 (su n) {.q , qw' , qw , deQW , S , rest}(pi q {S' = S'}{T' = T'} S~>S' T~>T')
  with nPiInvRed1 n T~>T'
... | nPiT' , refl
  = (q , qw' , qw , deQW , S' , nPiT') , refl

-- reducts of nPi are themselves nPi, multistep version
nPiInvRed : forall {w m} n {S : nPi w m n}{T} -> nPiToTy n S ~>>* T -> Sg (nPi w m n) \T' -> T == nPiToTy n T'
nPiInvRed n [] = _ , refl
nPiInvRed n (S~>T ,- T~>R)
  with nPiInvRed1 n S~>T
... | nPiT , refl = nPiInvRed n T~>R

-- If a term erases to a lambda, it computes to a(n annotated) string of lambdas
-- only the last of which survives erasure
erToLamCHK : forall {m}{Ga : Cx m}{l}{uner : Unerased Ga l}
          -> forall {w keepW T t s}
          -> CHKEr Ga uner w keepW T t (lam s)
          -> Sg Nat \n ->
             Sg (nPi w m n) \T' ->
             T ~>>* nPiToTy n T'
           * Sg (nLam m n) \t' ->
             t ~>>* nLamToTm n t'
           * CHKEr Ga uner w keepW (nPiToTy n T') (nLamToTm n t') (lam s)
erToLamSYN : forall {m}{Ga : Cx m}{l}{uner : Unerased Ga l}
          -> forall {w keepW e S s}
          -> SYNEr Ga uner w keepW e S (lam s)
          -> Sg Nat \n ->
             Sg (nPi w m n) \S' ->
             S ~>>* nPiToTy n S'
           * Sg (nLam m n) \t' ->
             e ~>>* nLamToTm n t' :: nPiToTy n S'
           * SYNEr Ga uner w keepW
                   (nLamToTm n t' :: nPiToTy n S') (nPiToTy n S') (lam s)
erToLamCHK (pre T~>T' T'tls)
  with erToLamCHK T'tls
... | n , T'' , T'~>T'' , t' , t~>t' , T''t'ls
  = n , T'' , (T~>T' ,- T'~>T'') , t' , t~>t' , T''t'ls
erToLamCHK (piEE tyW quw deQUW deSQUW *S *Tls)
  with erToLamCHK *Tls
... | n , npi , *~>npi , nlam , T~>nlam , npiNlamls
  = naughty (stNoRednPi n *~>npi)
erToLamCHK (lamE qw deQW Ttls)
  with erToLamCHK Ttls
... | n , T' , T~>T' , t' , t~>t' , T't'ls
  = su n , (_ , _ , qw , deQW , _ , T') , pi* [] T~>T' , t' , lam* t~>t' , lamE qw deQW T't'ls
erToLamCHK (lam qw keQW Tts) = ze , (_ , _ , qw , keQW , _ , _) , [] , _ , [] , lam qw keQW Tts
erToLamCHK ([ eSls ] refl)
  with erToLamSYN eSls
... | n , S' , S~>S' , t' , e~>t':S' , t'S'S'ls
  with annInvEr t'S'S'ls
... | _ , S't'ls , _
  = n , S' , S~>S' , t' , ([ e~>t':S' ]* ++ (upsi (parRefl _) ,- [])) , S't'ls
erToLamSYN (post eSls S~>T)
  with erToLamSYN eSls
... | n , S' , S~>S' , t' , e~>t':S' , t'S'S'ls
  with confluence (S~>T ,- []) S~>S' | annInvEr t'S'S'ls
... | R , T~>R , S'~>R | *S' , S't'ls , _
  with nPiInvRed n S'~>R
... | nPiR , refl
  = n , nPiR , T~>R , t' , (e~>t':S' ++ ([] ::* S'~>R)) , presCHK* (!~>>*refl _) [] S'~>R *S' :~: presCHKErCxTy (!~>>*refl _) S'~>R S't'ls
erToLamSYN {uner = uner}{s = s'} (appE {s = s} fSTls' qw deQW Ss)
  with erToLamSYN fSTls'
... | n , ST' , ST~>ST' , f' , f~>f':ST' , f'ST'ST'ls'
  with dePi~>nPi qw deQW n ST~>ST'
... | mkSunPi n' qw' qw2 deQW2 S' T'
  with piInvRed ST~>ST'
... | _ , _ , refl , S~>S' , T~>T'
  with annLamPiErInvDe qw deQW f'ST'ST'ls'
... | _ , _ , _ , *S' , *T' , S'' , S'~>S'' , T'' , T'~>T'' , T''f'ls'
  with presCHK (!~>>*refl _) S~>S' (parRefl s) Ss | preEr* T'~>T'' T''f'ls'
... | S's | T'f'ls'
  with substSYNEr (del uner deQW) uner (si -, (s :: S')) (zeMor *S' S's S'~>S'') siE (idCxMorEr uner)
                  (presCHK (!~>>*refl _ , refl , S'~>S'') [] (parRefl _) *T' :~: T'f'ls')
... | f'[sS']T'[sS']T'[sS'][sS']ls'
  with substStab {s = s} [] S~>S' T~>T'
     | (f~>f':ST' $* [])
       ++ (beta (parRefl (nLamToTm n' f')) (parRefl S')
                (parRefl (nPiToTy n' T')) (parRefl s)
           ,- [])
... | T[sS]~>T'[sS'] | fs~>f'[sS']
  rewrite substErId s' | substnPiQ (si -, (s :: S')) n' T' | substnLamQ (si -, (s :: S')) n' f'
  = n' , substnPi (si -, (s :: S')) n' T' , T[sS]~>T'[sS']
  , substnLam (si -, (s :: S')) n' f' , fs~>f'[sS']
  , f'[sS']T'[sS']T'[sS'][sS']ls'
erToLamSYN (*T :~: Ttls)
  with erToLamCHK Ttls
... | n , T' , T~>T' , t' , t~>t' , T't'ls
  = n , T' , T~>T' , t' , (t~>t' ::* T~>T') , presCHK* (!~>>*refl _) [] T~>T' *T :~: T't'ls


------------------------------------------------------------------------------
----- Step Simulation B ------------------------------------------------------
------------------------------------------------------------------------------
-- We prove that if s erases to e which takes a single reduction step e ~> d
-- then the s takes 1 or more steps to t where t erases to d

-- "1 or more"
data Trans {A : Set}(R : A -> A -> Set) : A -> A -> Set where
  rel : {a b : A} -> R a b -> Trans R a b
  _-,_ : {a b : A} -> R a b -> {c : A} -> Trans R b c -> Trans R a c

-- any number of steps followed by one or more is one or more
_*+++_ : {A : Set}{R : A -> A -> Set}{a b c : A} -> Star R a b -> Trans R b c -> Trans R a c
[] *+++ b~>c = b~>c
(a~>b ,- b~>b') *+++ b'~>c = a~>b -, (b~>b' *+++ b'~>c)

-- lift implications to Trans
lift+ : {A B : Set}
     -> (f : A -> B)
     -> {R : A -> A -> Set}{S : B -> B -> Set}
     -> ({a b : A} -> R a b -> S (f a) (f b))
     -> {a b : A} -> Trans R a b
     -> Trans S (f a) (f b)
lift+ f g (rel aRb) = rel (g aRb)
lift+ f g (aRb -, bR+c) = g aRb -, lift+ f g bR+c

_~>+_ : forall {n d} -> Tm n d -> Tm n d -> Set
s ~>+ t = Trans _~>_ s t

~>+To~>>* : forall {n d}{s t : Tm n d} -> s ~>+ t -> s ~>>* t
~>+To~>>* (rel s~>t) = ~>To~>>* s~>t
~>+To~>>* (s~>t -, t~>r) = redPar s~>t ,- ~>+To~>>* t~>r


stepSimBCHK : forall {l}{s s'}
           -> s ~>E s'
           -> forall {n}{Ga : Cx n}{uner : Unerased Ga l}
           -> forall {w keepW}{T t}
           -> CHKEr Ga uner w keepW T t s
           -> Sg _ \t' -> t ~>+ t' * CHKEr Ga uner w keepW T t' s'
stepSimBSYN : forall {l}{d d'}
           -> d ~>E d'
           -> forall {n}{Ga : Cx n}{uner : Unerased Ga l}
           -> forall {w keepW}{e S}
           -> SYNEr Ga uner w keepW e S d
           -> Sg _ \e' -> e ~>+ e'
            * Sg _ \S' -> S ~>>* S'
            * SYNEr Ga uner w keepW e' S' d'
stepSimBCHK s~>s' (pre T~>T' Tts)
  with stepSimBCHK s~>s' Tts
... | t' , t~>t' , T't's' = t' , t~>t' , pre T~>T' T't's'
stepSimBCHK () (star tyW)
stepSimBCHK B~>B' (piEE tyW quw deQUW deSQUW *S *TB)
  with stepSimBCHK B~>B' *TB
... | T' , T~>T' , *T'B'
  = _ , lift+ (pi _ _) (piR _ _) T~>T' , piEE tyW quw deQUW deSQUW *S *T'B'
stepSimBCHK (arrL A~>A' B) (piArr tyW quw deQUW keSQUW *SA *TB)
  with stepSimBCHK A~>A' *SA
... | S' , S~>S' , *S'A'
  = _ , lift+ (\x -> pi _ x _) (\r -> piL _ r _) S~>S'
  , piArr tyW quw deQUW keSQUW *S'A'
          (presCHKErCxTy (!~>>*refl _ , refl , ~>+To~>>* S~>S') [] *TB)
stepSimBCHK (arrR A B~>B') (piArr tyW quw deQUW keSQUW *SA *TB)
  with stepSimBCHK B~>B' *TB
... | T' , T~>T' , *T'B'
  = _ , lift+ (pi _ _) (piR _ _) T~>T' , piArr tyW quw deQUW keSQUW *SA *T'B'
stepSimBCHK (erpi B~>B') (piE tyW quw keQUW deSQUW *S *TB)
  with stepSimBCHK B~>B' *TB
... | T' , T~>T' , *T'B'
  = _ , lift+ (pi _ _) (piR _ _) T~>T' , piE tyW quw keQUW deSQUW *S *T'B'
stepSimBCHK (piL A~>A' B) (pi tyW quw keQUW keSQUW *SA *TB)
  with stepSimBCHK A~>A' *SA
... | S' , S~>S' , *S'A'
  = _ , lift+ (\x -> pi _ x _) (\r -> piL _ r _) S~>S'
  , pi tyW quw keQUW keSQUW *S'A'
       (presCHKErCxTy (!~>>*refl _ , refl , ~>+To~>>* S~>S') [] *TB)
stepSimBCHK (piR A B~>B') (pi tyW quw keQUW keSQUW *SA *TB)
  with stepSimBCHK B~>B' *TB
... | T' , T~>T' , *T'B'
  = _ , lift+ (pi _ _) (piR _ _) T~>T' , pi tyW quw keQUW keSQUW *SA *T'B'
stepSimBCHK s~>s' (lamE qw deQW Tts)
  with stepSimBCHK s~>s' Tts
... | t' , t~>t' , Tt's' = lam t' , lift+ lam lam t~>t' , lamE qw deQW Tt's'
stepSimBCHK (lam s~>s') (lam qw keQW Tts)
  with stepSimBCHK s~>s' Tts
... | t' , t~>t' , Tt's' = lam t' , lift+ lam lam t~>t' , lam qw keQW Tt's'
stepSimBCHK d~>d' ([ eSd ] refl)
  with stepSimBSYN d~>d' eSd
... | e' , e~>e' , S' , S~>S' , e'S'd'
  = [ e' ] , lift+ [_] [_] e~>e' , preEr* S~>S' ([ e'S'd' ] refl)

stepSimBSYN d~>d' (post eSd S~>S')
  with stepSimBSYN d~>d' eSd
... | e' , e~>e' , S'' , S~>S'' , e'S''d'
  with confluence (S~>S' ,- []) S~>S''
... | Sc , S'~>Sc , S''~>Sc
  = e' , e~>e' , Sc , S'~>Sc , postEr* e'S''d' S''~>Sc
stepSimBSYN () (var i u<w)
stepSimBSYN d~>d' (appE {s = s} fSTd qw deQW Ss)
  with stepSimBSYN d~>d' fSTd
... | f' , f~>f' , ST' , ST~>ST' , f'ST'd'
  with piInvRed ST~>ST'
... | S' , T' , refl , S~>S' , T~>T'
  = f' $ s , lift+ (_$ _) (_$L _) f~>f'
  , Sb.act (si -, (s :: S')) T' , substStab [] S~>S' T~>T'
  , appE f'ST'd' qw deQW (presCHK (!~>>*refl _) S~>S' (parRefl _) Ss)
stepSimBSYN (d~>d' $L e) (_$~_^_~$_ {s = s} fSTd qw keQW Sse)
  with stepSimBSYN d~>d' fSTd
... | f' , f~>f' , ST' , ST~>ST' , f'ST'd'
  with piInvRed ST~>ST'
... | S' , T' , refl , S~>S' , T~>T'
  = f' $ s , lift+ (_$ _) (_$L _) f~>f'
  , Sb.act (si -, (s :: S')) T' , substStab [] S~>S' T~>T'
  , f'ST'd' $~ qw ^ keQW ~$ presCHKErCxTy (!~>>*refl _) S~>S' Sse
stepSimBSYN (d $R e~>e') (_$~_^_~$_ {f = f}{S = S}{T = T} fSTd qw keQW Sse)
  with stepSimBCHK e~>e' Sse
... | s' , s~>s' , Ss'e'
  = f $ s' , lift+ (f $_) (f $R_) s~>s'
  , Sb.act (si -, (s' :: S)) T , substStab {T = T} (~>+To~>>* s~>s') [] []
  , fSTd $~ qw ^ keQW ~$ Ss'e'
stepSimBSYN beta (_$~_^_~$_ {s = s}{s' = e} fSTld qw keQW Sse)
  with erToLamSYN fSTld
... | n , ST' , ST~>ST' , t , f~>ltST' , ltST'ST'ld
  with kePi~>nPi qw keQW n ST~>ST' | piInvRed ST~>ST'
... | refl | S' , T' , refl , S~>S' , T~>T'
  with annLamPiErInvKe qw keQW ltST'ST'ld
... | _ , _ , _ , *S' , *T' , S'' , S'~>S'' , T'' , T'~>T'' , _ , refl , T''tld
  with presCHK* (!~>>*refl _ , refl , S'~>S'') [] [] *T' :~: preEr* T'~>T'' T''tld
     | presCHKErCxTy (!~>>*refl _) S~>S' Sse
... | tT'T'ld | S'se
  = Sb.act (si -, s :: S') (t :: T') , (parsReds (f~>ltST' $* []) *+++ rel beta)
  , Sb.act (si -, s :: S') T' , substStab [] S~>S' T~>T'
  , substSYNEr (kee _ keQW) _
               (si -, s :: S') (zeMor *S' (forgetCHKEr S'se) S'~>S'')
               (siE -, e) (zeMorEr *S' S'se S'~>S'')
               tT'T'ld
stepSimBSYN d~>d' (_:~:_ {T = S} *S Ssd)
  with stepSimBCHK d~>d' Ssd
... | s' , s~>s' , Ss'd'
  = s' :: S , lift+ (_:: S) (_::L S) s~>s' , S , [] , *S :~: Ss'd'
