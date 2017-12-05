open import WorldSystem
import ErasureSet

module Erasure {QW : WorldSystem}{E : ErasureSet.ErasureSet {QW}} where

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
open import Par {Q Real}
open import Dev {Q Real}
open import Typing {QW}
open import Preservation {QW}
open import Er


------------------------------------------------------------------------------
----- Defining equivalent terms and contexts, and helpers --------------------
------------------------------------------------------------------------------
data Equiv {n d}(S T : Tm n d) : Set where
  _~>>*<<~_ : {R : Tm n d} -> S ~>>* R -> T ~>>* R -> Equiv S T
infix 10 _~>>*<<~_

-- Lift to contexts
data Equiv! : forall {n}(Ga1 Ga2 : Cx n) -> Set where
  [] : Equiv! [] []
  CxEqv : forall {n Ga1 Ga2 w1 w2 S1 S2}
       -> Equiv! {n} Ga1 Ga2 -> Equiv S1 S2
       -> Equiv! (Ga1 -, (w1 , S1)) (Ga2 -, (w2 , S2))

~>>*ToEquiv : forall {n d}{s t : Tm n d} -> s ~>>* t -> Equiv s t
~>>*ToEquiv s~>t = s~>t ~>>*<<~ []

!~>>*ToEquiv : forall {n}{Ga Ga' : Cx n} -> Ga !~>>* Ga' -> Equiv! Ga Ga'
!~>>*ToEquiv {Ga = []}{[]} <> = []
!~>>*ToEquiv {Ga = Ga -, (u , S)} {Ga' -, (v , T)} (Ga~>Ga' , u=v , S~>T)
  = CxEqv (!~>>*ToEquiv Ga~>Ga') (~>>*ToEquiv S~>T)


equivRefl : forall {n d}{S : Tm n d} -> Equiv S S
equivRefl = ~>>*ToEquiv []

equiv!Refl : forall {n}{Ga : Cx n} -> Equiv! Ga Ga
equiv!Refl = !~>>*ToEquiv (!~>>*refl _)

piSplitEquiv : forall {n q r S T S' T'}
            -> Equiv {n} (pi q S T) (pi r S' T')
            -> Equiv S S' * Equiv T T'
piSplitEquiv ([] ~>>*<<~ ST2R)
  with piInvRed ST2R
... | S' , T' , refl , SS' , TT' = [] ~>>*<<~ SS' , [] ~>>*<<~ TT'
piSplitEquiv ((pi q S1S1' T1T1' ,- ST1'R) ~>>*<<~ ST2R)
  with piSplitEquiv (ST1'R ~>>*<<~ ST2R)
... |  S1'R ~>>*<<~ S2R , T1'R ~>>*<<~ T2R = (S1S1' ,- S1'R) ~>>*<<~ S2R , (T1T1' ,- T1'R) ~>>*<<~ T2R

piEquivSameQ : forall {n q r S T S' T'}
            -> Equiv {n} (pi q S T) (pi r S' T')
            -> q == r
piEquivSameQ (STR ~>>*<<~ ST'R)
  with piInvRed STR | piInvRed ST'R
... | _ , _ , refl , _ , _ | _ , _ , refl , _ , _ = refl

piEquivSameW : forall {n q r S T S' T'}
            -> Equiv {n} (pi q S T) (pi r S' T')
            -> forall {w qw} -> q # w ~ qw
            -> forall {rw} -> r # w ~ rw
            -> qw == rw
piEquivSameW eqv qw rw rewrite piEquivSameQ eqv = #functional qw rw

thinEquiv : forall {n m}(th : n <= m)
         -> forall {d S T} -> Equiv {n}{d} S T
         -> Equiv (Th.act th S) (Th.act th T)
thinEquiv th (SR ~>>*<<~ TR) = parsThin th SR ~>>*<<~ parsThin th TR

substEquiv : forall {n S S'} -> Equiv {n} S S'
          -> forall {d T}{T' : Tm _ d} -> Equiv T T'
          -> forall s
          -> Equiv (Sb.act (si -, (s :: S)) T) (Sb.act (si -, (s :: S')) T')
substEquiv (SR ~>>*<<~ S'R) (TR ~>>*<<~ T'R) s
  = substStab [] SR TR ~>>*<<~ substStab [] S'R T'R

cxEquiv : forall {n}{Ga1 Ga2 : Cx n} -> Equiv! Ga1 Ga2
       -> forall i -> Equiv (cxTy Ga1 i) (cxTy Ga2 i)
cxEquiv (CxEqv Ga1eqvGa2 S1eqvS2) ze = thinEquiv (o' oi) S1eqvS2
cxEquiv (CxEqv Ga1eqvGa2 S1eqvS2) (su i) = thinEquiv (o' oi) (cxEquiv Ga1eqvGa2 i)


-- We care about the number of context entries in worlds which do not get erased.
-- This enables us to have a de Bruijn representation of erased terms which, by
-- construction, has the property that every variable mentioned is either bound or
-- in the context at an unerased world.
data Unerased : {m : Nat} -> Cx m -> Nat -> Set where
  [] : Unerased [] ze
  kee : forall {m Ga n w}{S : Tm m chk} -> Unerased Ga n -> er? w == keep -> Unerased (Ga -, (w , S)) (su n)
  del : forall {m Ga n w}{S : Tm m chk} -> Unerased Ga n -> er? w == delete -> Unerased (Ga -, (w , S)) n

-- de Bruijn indices in the erased term thin to give the index of the variable in the original context
unerThin : forall {n}{Ga : Cx n}{m} -> Unerased Ga m -> m <= n
unerThin [] = oz
unerThin (kee uner _) = os (unerThin uner)
unerThin (del uner _) = o' (unerThin uner)

-- indices of variables that are not erased indeed have a index in the shorter
-- context of just those variables which are not erased.
eraseVar : forall {n} -> {Ga : Cx n}
        -> forall {m} -> Unerased Ga m
        -> (i : Fin n) -> er? (cxW Ga i) == keep
        -> Fin m
eraseVar (kee left keew) ze keepi = ze
eraseVar (del left delw) ze keepi = naughty (erXorKp delw keepi)
eraseVar (kee left x) (su i) keepi = su (eraseVar left i keepi)
eraseVar (del left x) (su i) keepi = eraseVar left i keepi

-- unerThin hits only variables that are not erased
unerThinKeep : forall {n}{Ga : Cx n}{m}
            -> (uner : Unerased Ga m)(i : Fin m)
            -> er? (cxW Ga (thin (unerThin uner) i)) == keep
unerThinKeep [] ()
unerThinKeep (del uner de) i = unerThinKeep uner i
unerThinKeep (kee uner ke) ze = ke
unerThinKeep (kee uner ke) (su i) = unerThinKeep uner i

-- erasing a variable and thinning it back into
-- the original context are inverses
thinErase : forall {n} -> {Ga : Cx n}
         -> forall {m} -> (uner : Unerased Ga m)
         -> (i : Fin n) -> (keepi : er? (cxW Ga i) == keep)
         -> thin (unerThin uner) (eraseVar uner i keepi) == i
thinErase [] () keepi
thinErase (kee uner ke) ze keepi = refl
thinErase (kee uner ke) (su i) keepi = cong su (thinErase uner i keepi)
thinErase (del uner de) ze keepi = naughty (erXorKp de keepi)
thinErase (del uner de) (su i) keepi = cong su (thinErase uner i keepi)

eraseThin : forall {n} -> {Ga : Cx n}
         -> forall {m} -> (uner : Unerased Ga m)
         -> (i : Fin m)
         -> eraseVar uner (thin (unerThin uner) i) (unerThinKeep uner i) == i
eraseThin [] ()
eraseThin (kee uner ke) ze = refl
eraseThin (kee uner ke) (su i) = cong su (eraseThin uner i)
eraseThin (del uner de) i = eraseThin uner i


------------------------------------------------------------------------------
----- The judgements are extended with an erasure output ---------------------
------------------------------------------------------------------------------
data CHKEr {n}(Ga : Cx n){m}(uner : Unerased Ga m)(w : W)(keepW : er? w == keep) : Tm n chk -> Tm n chk -> Er m -> Set
data SYNEr {n}(Ga : Cx n){m}(uner : Unerased Ga m)(w : W)(keepW : er? w == keep) : Tm n syn -> Tm n chk -> Er m -> Set

data CHKEr {n} Ga {m} uner w keepW where

  pre  : forall {T T' t t'} ->
         T ~>> T' -> CHKEr Ga uner w keepW T' t t' ->
         CHKEr Ga uner w keepW T t t'

  star : tyW w -> CHKEr Ga uner w keepW star star star

  piEE : forall {q quw S T T'} ->
         tyW w -> snd (q &unst& inl <>) # w ~ quw ->
         (erQUW : er? quw == delete) -> (erSQUW : er? (st-act quw) == delete) ->
         CHK Ga (st-act quw) star S ->
         CHKEr (Ga -, (quw , S)) (del uner erQUW) w keepW star T T' ->
         CHKEr Ga uner w keepW star (pi q S T) T'

  piArr : forall {q quw S S' T T'} ->
          tyW w -> snd (q &unst& inl <>) # w ~ quw ->
          (erQUW : er? quw == delete) -> (keepSQUW : er? (st-act quw) == keep) ->
          CHKEr Ga uner (st-act quw) keepSQUW star S S' ->
          CHKEr (Ga -, (quw , S)) (del uner erQUW) w keepW star T T' ->
          CHKEr Ga uner w keepW star (pi q S T) (arr S' T')

  piE : forall {q quw S T T'} ->
        tyW w -> snd (q &unst& inl <>) # w ~ quw ->
        (keepQUW : er? quw == keep) -> (erSQUW : er? (st-act quw) == delete) ->
        CHK Ga (st-act quw) star S ->
        CHKEr (Ga -, (quw , S)) (kee uner keepQUW) w keepW star T T' ->
        CHKEr Ga uner w keepW star (pi q S T) (erpi T')

  pi  : forall {q quw S S' T T'} ->
        tyW w -> snd (q &unst& inl <>) # w ~ quw ->
        (keepQUW : er? quw == keep) -> (keepSQUW : er? (st-act quw) == keep) ->
        CHKEr Ga uner (st-act quw) keepSQUW star S S' ->
        CHKEr (Ga -, (quw , S)) (kee uner keepQUW) w keepW star T T' ->
        CHKEr Ga uner w keepW star (pi q S T) (pi S' T')

  lamE : forall {q qw S T t t'} ->
         q # w ~ qw ->
         (erQW : er? qw == delete) ->
         CHKEr (Ga -, (qw , S)) (del uner erQW) w keepW T t t' ->
         CHKEr Ga uner w keepW (pi q S T) (lam t) t'

  lam  : forall {q qw S T t t'} ->
         q # w ~ qw ->
         (keepQW : er? qw == keep) ->
         CHKEr (Ga -, (qw , S)) (kee uner keepQW) w keepW T t t' ->
         CHKEr Ga uner w keepW (pi q S T) (lam t) (lam t')

  [_]  : forall {e S T e'} ->
         SYNEr Ga uner w keepW e S e' -> S == T ->
         CHKEr Ga uner w keepW T [ e ] e'

data SYNEr {n} Ga {m} uner w keepW where

  post : forall {e S S' e'} ->
         SYNEr Ga uner w keepW e S e' -> S ~>> S' ->
         SYNEr Ga uner w keepW e S' e'

  var  : forall i ->
         (u<w : cxW Ga i << w) ->
         SYNEr Ga uner w keepW (var i) (cxTy Ga i) (var (eraseVar uner i (downsetKeep u<w keepW)))

  appE : forall {q qw f s S T f'} ->
         SYNEr Ga uner w keepW f (pi q S T) f' ->
         q # w ~ qw ->
         (erQW : er? qw == delete) ->
         CHK Ga qw S s ->
         SYNEr Ga uner w keepW (f $ s) (Sb.act (si -, (s :: S)) T) f'

  _$~_^_~$_  : forall {q qw f s S T f' s'} ->
               SYNEr Ga uner w keepW f (pi q S T) f' ->
               q # w ~ qw ->
               (keepQW : er? qw == keep) ->
               CHKEr Ga uner qw keepQW S s s' ->
               SYNEr Ga uner w keepW (f $ s) (Sb.act (si -, (s :: S)) T) (f' $ s')

  _:~:_ : forall {t T t'} ->
          CHK Ga (st-act w) star T ->
          CHKEr Ga uner w keepW T t t' ->
          SYNEr Ga uner w keepW (t :: T) T t'

-- We have elaborated the rules, so if a CHKEr holds, then the corresponding CHK does
-- and similarly for SYN
forgetCHKEr : forall {n Ga m uner w keepW T t t'}
           -> CHKEr {n} Ga {m} uner w keepW T t t'
           -> CHK Ga w T t
forgetSYNEr : forall {n Ga m uner w keepW e S e'}
           -> SYNEr {n} Ga {m} uner w keepW e S e'
           -> SYN Ga w e S
forgetCHKEr (pre S~>T Ttt') = pre S~>T (forgetCHKEr Ttt')
forgetCHKEr (star tyW) = star tyW
forgetCHKEr (piEE tyW quw deQUW deSQUW *S *TT') = pi tyW quw *S (forgetCHKEr *TT')
forgetCHKEr (piArr tyW quw deQUW keSQUW *SS' *TT') = pi tyW quw (forgetCHKEr *SS') (forgetCHKEr *TT')
forgetCHKEr (piE tyW quw keQUW deSQUW *S *TT') = pi tyW quw *S (forgetCHKEr *TT')
forgetCHKEr (pi tyW quw keQUW keSQUW *SS' *TT') = pi tyW quw (forgetCHKEr *SS') (forgetCHKEr *TT')
forgetCHKEr (lamE qw erQW Ttt') = lam qw (forgetCHKEr Ttt')
forgetCHKEr (lam qw keQW Ttt') = lam qw (forgetCHKEr Ttt')
forgetCHKEr ([ eSe' ] S=T) = [ forgetSYNEr eSe' ] S=T

forgetSYNEr (post eSe' S~>T) = post (forgetSYNEr eSe') S~>T
forgetSYNEr (var i u<w) = var i u<w
forgetSYNEr (appE fSTf' qw erQW Ss) = forgetSYNEr fSTf' $~ qw ~$ Ss
forgetSYNEr (fSTf' $~ qw ^ keQW ~$ Sss') = forgetSYNEr fSTf' $~ qw ~$ forgetCHKEr Sss'
forgetSYNEr (*T :~: Ttt') = *T :~: forgetCHKEr Ttt'


------------------------------------------------------------------------------
----- Every typing derivation elaborates to one with erasure -----------------
------------------------------------------------------------------------------
-- also, all contexts have a certain number of variables in worlds which are not erased
eraseCx : forall {n} -> (Ga : Cx n) -> Sg _ (Unerased Ga)
eraseCx [] = ze , []
eraseCx (Ga -, (w , S)) with eraseCx Ga
... | n , erGa with caseEr w (\ke -> kee erGa ke) (\de -> del erGa de)
... | keep , f , g = su n , g
... | delete , f , g = n , g

eraseCHK : forall {n Ga m}
       -> (uner : Unerased Ga m)
       -> forall {w} keepW {T t}
       -> CHK {n} Ga w T t
       -> Sg _ (CHKEr Ga uner w keepW T t)
eraseSYN : forall {n Ga m}
       -> (uner : Unerased Ga m)
       -> forall {w} keepW {e S}
       -> SYN {n} Ga w e S
       -> Sg _ (SYNEr Ga uner w keepW e S)
eraseCHK uner keepW (pre S~>T Tt) with eraseCHK uner keepW Tt
... | t' , p = t' , pre S~>T p
eraseCHK uner keepW (star tyW) = star , star tyW
eraseCHK uner keepW (pi {quw = quw'} tyW quw *S *T)
  with caseEr (st-act quw') (\ke -> eraseCHK uner ke *S) (\de -> <>)
     | caseEr quw' (\ke -> eraseCHK (kee uner ke) keepW *T)
                   (\de -> eraseCHK (del uner de) keepW *T)
... | keep , keepSQUW , S' , *SS' | keep , keepQUW , T' , *TT' = pi S' T' , pi tyW quw keepQUW keepSQUW *SS' *TT'
... | keep , keepSQUW , S' , *SS' | delete , delQUW , T' , *TT' = arr S' T' , piArr tyW quw delQUW keepSQUW *SS' *TT'
... | delete , delSQUW , <> | keep , keepQUW , T' , *TT' = erpi T' , piE tyW quw keepQUW delSQUW *S *TT'
... | delete , delSQUW , <> | delete , delQUW , T' , *TT' = T' , piEE tyW quw delQUW delSQUW *S *TT'
eraseCHK uner keepW (lam {qw = qw'} qw Tt)
  with caseEr qw' (\ke -> eraseCHK (kee uner ke) keepW Tt)
                  (\de -> eraseCHK (del uner de) keepW Tt)
... | keep , keepQW , t' , Ttt' = lam t' , lam qw keepQW Ttt'
... | delete , delQW , t' , Ttt' = t' , lamE qw delQW Ttt'
eraseCHK uner keepW ([ eS ] S=T) with eraseSYN uner keepW eS
... | e' , eSe' = e' , [ eSe' ] S=T

eraseSYN uner keepW (post eS S~>T) with eraseSYN uner keepW eS
... | e' , eSe' = e' , post eSe' S~>T
eraseSYN uner keepW (var i p) = var _ , var i p
eraseSYN uner keepW (_$~_~$_ {qw = qw'} fST qw Ss)
  with eraseSYN uner keepW fST
     | caseEr qw' (\ke -> eraseCHK uner ke Ss) (\de -> <>)
... | f' , fSTf' | keep , keeQW , s' , Sss' = f' $ s' , fSTf' $~ qw ^ keeQW ~$ Sss'
... | f' , fSTf' | delete , delQW , <> = f' , appE fSTf' qw delQW Ss
eraseSYN uner keepW (*T :~: Tt) with eraseCHK uner keepW Tt
... | t' , Ttt' = t' , *T :~: Ttt'


------------------------------------------------------------------------------
----- Erasures are unique ----------------------------------------------------
------------------------------------------------------------------------------
-- We wish to show erasures are unique and depend only on the
-- original term and the fact it is well typed (but not the proof).
-- We allow the context and input type (if any) to vary to equivalent
-- ones and also show the output type (if any) varys only to an
-- equivalent one.
-- Equivalent for types means convertible.
-- We have a choice for contexts: we need the two to be the same length
-- and the types appearing to be pairwise equivalent.
-- However, should we require the worlds to be pairwise equal?
-- If we do, the uniqueness result is easier to state, since we can
-- just show the two erasures (both of the type Cx m for some m) are equal.
-- (and in this case, we don't need unerThin and friends)
-- If we don't (which is the choice we make here), the erasures live in
-- different contexts (since the number of worlds in the context that are
-- erased may differ), and so the de Bruijn indices for the same variable differ.
-- Thus, we need to view the terms in the original context, which we do by
-- thinning with unerThin.


-- We will show that thinning is injective, which we need for going under
-- a erased binder (adding an o' to a thinning) when proving erasures
-- are unique
piInj : forall {n}{A C : Er n}{B D} -> Er.pi A B == pi C D -> A == C * B == D
piInj refl = refl , refl

erpiInj : forall {n}{B D : Er (su n)} -> Er.Er.erpi B == erpi D -> B == D
erpiInj refl = refl

arrInj : forall {n}{A B C D : Er n} -> arr A B == arr C D -> A == C * B == D
arrInj refl = refl , refl

lamInj  : forall {n}{s t : Er (su n)} -> Er.Er.lam s == lam t -> s == t
lamInj refl = refl

varInj : forall {n}{x y : Fin n} -> Er.var x == var y -> x == y
varInj refl = refl

appInj  : forall {n}{e s f t : Er n} -> Er._$_ e s == f $ t -> e == f * s == t
appInj refl = refl , refl

-- if thinEr th1 s == thinEr th2 t, then all the pieces of s and t
-- are equal under the appropriate thinning
data ViewThEr {n m}(th1 th2 : n <= m) : Er n -> Er n -> Set where
  star : ViewThEr th1 th2 star star
  pi : forall {A C} -> thinEr th1 A == thinEr th2 C
    -> forall {B D} -> thinEr (os th1) B == thinEr (os th2) D
    -> ViewThEr th1 th2 (pi A B) (pi C D)
  erpi : forall {B D} -> thinEr (os th1) B == thinEr (os th2) D
      -> ViewThEr th1 th2 (erpi B) (erpi D)
  arr : forall {A C} -> thinEr th1 A == thinEr th2 C
     -> forall {B D} -> thinEr th1 B == thinEr th2 D
     -> ViewThEr th1 th2 (arr A B) (arr C D)
  lam : forall {s t} -> thinEr (os th1) s == thinEr (os th2) t -> ViewThEr th1 th2 (lam s) (lam t)
  var : forall {x y} -> thin th1 x == thin th2 y -> ViewThEr th1 th2 (var x) (var y)
  _$_ : forall {e f} -> thinEr th1 e == thinEr th2 f
     -> forall {s t} -> thinEr th1 s == thinEr th2 t
     -> ViewThEr th1 th2 (e $ s) (f $ t)

viewThEr : forall {n m}{th1 th2 : n <= m}{t1 t2}
    -> thinEr th1 t1 == thinEr th2 t2
    -> ViewThEr th1 th2 t1 t2
viewThEr {t1 = star} {star} refl = star
viewThEr {t1 = star} {pi _ _} ()
viewThEr {t1 = star} {erpi _} ()
viewThEr {t1 = star} {arr _ _} ()
viewThEr {t1 = star} {lam _} ()
viewThEr {t1 = star} {var x} ()
viewThEr {t1 = star} {_ $ _} ()
viewThEr {t1 = pi _ _} {star} ()
viewThEr {t1 = pi A B} {pi C D} p with piInj p
... | thA=thC , thB=thD = pi thA=thC thB=thD
viewThEr {t1 = pi _ _} {erpi _} ()
viewThEr {t1 = pi _ _} {arr _ _} ()
viewThEr {t1 = pi _ _} {lam _} ()
viewThEr {t1 = pi _ _} {var x} ()
viewThEr {t1 = pi _ _} {_ $ _} ()
viewThEr {t1 = erpi _} {star} ()
viewThEr {t1 = erpi _} {pi _ _} ()
viewThEr {t1 = erpi B} {erpi D} p = erpi (erpiInj p)
viewThEr {t1 = erpi _} {arr _ _} ()
viewThEr {t1 = erpi _} {lam _} ()
viewThEr {t1 = erpi _} {var x} ()
viewThEr {t1 = erpi _} {_ $ _} ()
viewThEr {t1 = arr _ _} {star} ()
viewThEr {t1 = arr _ _} {pi _ _} ()
viewThEr {t1 = arr _ _} {erpi _} ()
viewThEr {t1 = arr A B} {arr C D} p with arrInj p
... | thA=thC , thB=thD = arr thA=thC thB=thD
viewThEr {t1 = arr _ _} {lam _} ()
viewThEr {t1 = arr _ _} {var x} ()
viewThEr {t1 = arr _ _} {_ $ _} ()
viewThEr {t1 = lam _} {star} ()
viewThEr {t1 = lam _} {pi _ _} ()
viewThEr {t1 = lam _} {erpi _} ()
viewThEr {t1 = lam _} {arr _ _} ()
viewThEr {t1 = lam s} {lam t} p = lam (lamInj p)
viewThEr {t1 = lam _} {var x} ()
viewThEr {t1 = lam _} {_ $ _} ()
viewThEr {t1 = var x} {star} ()
viewThEr {t1 = var x} {pi _ _} ()
viewThEr {t1 = var x} {erpi _} ()
viewThEr {t1 = var x} {arr _ _} ()
viewThEr {t1 = var x} {lam _} ()
viewThEr {t1 = var x} {var y} p = var (varInj p)
viewThEr {t1 = var x} {_ $ _} ()
viewThEr {t1 = _ $ _} {star} ()
viewThEr {t1 = _ $ _} {pi _ _} ()
viewThEr {t1 = _ $ _} {erpi _} ()
viewThEr {t1 = _ $ _} {arr _ _} ()
viewThEr {t1 = _ $ _} {lam _} ()
viewThEr {t1 = _ $ _} {var x} ()
viewThEr {t1 = e $ s} {f $ t} p with appInj p
... | the=thf , ths=tht = the=thf $ ths=tht


thinErFunct : forall {n m l}(th : m <= l)(ph : n <= m)
   -> forall t -> thinEr (th -<- ph) t == thinEr th (thinEr ph t)
thinErFunct th ph star = refl
thinErFunct th ph (pi S T)
  rewrite thinErFunct th ph S | thinErFunct (os th) (os ph) T = refl
thinErFunct th ph (erpi T)
  rewrite thinErFunct (os th) (os ph) T = refl
thinErFunct th ph (arr S T)
  rewrite thinErFunct th ph S | thinErFunct th ph T = refl
thinErFunct th ph (lam t)
  rewrite thinErFunct (os th) (os ph) t = refl
thinErFunct th ph (var x) = cong var (sym (thinCo th ph x))
thinErFunct th ph (f $ s)
  rewrite thinErFunct th ph f | thinErFunct th ph s = refl

thinErInj : forall {n m}{th : n <= m}
         -> forall {s t} -> thinEr th s == thinEr th t
         -> s == t
thinErInj {th = th} p with viewThEr p
... | star = refl
... | pi thA=thC thB=thD rewrite thinErInj thA=thC | thinErInj thB=thD = refl
... | erpi thB=thD rewrite thinErInj thB=thD = refl
... | arr thA=thC thB=thD rewrite thinErInj thA=thC | thinErInj thB=thD = refl
... | lam ths=tht rewrite thinErInj ths=tht = refl
... | var thx=thy rewrite thinInj th thx=thy = refl
... | the=thf $ ths=tht rewrite thinErInj the=thf | thinErInj ths=tht = refl

thino' : forall {n m}{th1 th2 : n <= m}{t1 t2}
      -> thinEr (o' th1) t1 == thinEr (o' th2) t2
      -> thinEr th1 t1 == thinEr th2 t2
thino' {th1 = th1}{th2}{t1}{t2} p
  rewrite cong o' (sym (oi-<-Q th1)) | thinErFunct (o' oi) th1 t1
        | cong o' (sym (oi-<-Q th2)) | thinErFunct (o' oi) th2 t2
  = thinErInj p

-- Unerased Ga m is unique (if it exists)
unerasedUniq : forall {n Ga m1 m2}
            -> (uner1 : Unerased {n} Ga m1)
            -> (uner2 : Unerased Ga m2)
            -> _==_ (m1 , uner1) (m2 , uner2)
unerasedUniq [] [] = refl
unerasedUniq (kee uner1 ke1) (kee uner2 ke2)
  with unerasedUniq uner1 uner2 | uip ke1 ke2
... | refl | refl = refl
unerasedUniq (kee uner1 ke1) (del uner2 de2) = naughty (erXorKp de2 ke1)
unerasedUniq (del uner1 de1) (kee uner2 ke2) = naughty (erXorKp de1 ke2)
unerasedUniq (del uner1 de1) (del uner2 de2)
  with unerasedUniq uner1 uner2 | uip de1 de2
... | refl | refl = refl


-- Erasures of terms are unique
eraseUniqCHK : forall {n Ga1 Ga2} -> Equiv! Ga1 Ga2
            -> forall {m} -> (unerGa1 : Unerased Ga1 m) -> (unerGa2 : Unerased Ga2 m)
            -> forall {S T} -> Equiv S T
            -> forall {w}{t : Tm n chk}
            -> forall {keepW1 t1} -> (St : CHKEr Ga1 unerGa1 w keepW1 S t t1)
            -> forall {keepW2 t2} -> (Tt : CHKEr Ga2 unerGa2 w keepW2 T t t2)
            -> thinEr (unerThin unerGa1) t1 == thinEr (unerThin unerGa2) t2
eraseUniqSYN : forall {n Ga1 Ga2} -> Equiv! Ga1 Ga2
            -> forall {m} -> (unerGa1 : Unerased Ga1 m) -> (unerGa2 : Unerased Ga2 m)
            -> forall {w}{e : Tm n syn}
            -> forall {keepW1 S e1} -> (eS : SYNEr Ga1 unerGa1 w keepW1 e S e1)
            -> forall {keepW2 T e2} -> (eT : SYNEr Ga2 unerGa2 w keepW2 e T e2)
            -> Equiv S T * thinEr (unerThin unerGa1) e1 == thinEr (unerThin unerGa2) e2
eraseUniqCHK Ga1eqvGa2 uner1 uner2 (SR ~>>*<<~ TR) (pre S'S St) Tt
  with confluence SR (S'S ,- [])
... | R' , RR' , S'R' = eraseUniqCHK Ga1eqvGa2 uner1 uner2 (S'R' ~>>*<<~ (TR ++ RR')) St Tt
eraseUniqCHK Ga1eqvGa2 uner1 uner2 (SR ~>>*<<~ TR) St (pre T'T Tt)
  with confluence TR (T'T ,- [])
... | R' , RR' , T'R' = eraseUniqCHK Ga1eqvGa2 uner1 uner2 (SR ++ RR' ~>>*<<~ T'R') St Tt
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT (star tyW1) (star tyW2)
  = refl
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (piEE tyW1 quw1 erQUW1 erSQUW1 *S1 *TT'1)
  (piEE tyW2 quw2 erQUW2 erSQUW2 *S2 *TT'2)
  = thino' (eraseUniqCHK (CxEqv Ga1eqvGa2 equivRefl)
             (del uner1 erQUW1) (del uner2 erQUW2)
             equivRefl *TT'1 *TT'2)
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (piEE _ quw1 _ erSQUW _ _) (piArr _ quw2 _ keepSQUW _ _)
  rewrite #functional quw1 quw2 = naughty (erXorKp erSQUW keepSQUW)
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (piEE _ quw1 erQUW _ _ _) (piE _ quw2 keepQUW _ _ _)
  rewrite #functional quw1 quw2 = naughty (erXorKp erQUW keepQUW)
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (piEE _ quw1 erQUW _ _ _) (pi _ quw2 keepQUW _ _ _)
  rewrite #functional quw1 quw2 = naughty (erXorKp erQUW keepQUW)
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (piArr _ quw1 _ keepSQUW _ _) (piEE _ quw2 _ erSQUW _ _)
  rewrite #functional quw1 quw2 = naughty (erXorKp erSQUW keepSQUW)
eraseUniqCHK Ga1eqvGa2 uner1 uner2 ABeqvCD
  (piArr _ quw1 erQUW1 keepSQUW1 *AA' *BB') (piArr _ quw2 erQUW2 keepSQUW2 *CC' *DD')
  rewrite #functional quw1 quw2
        | eraseUniqCHK Ga1eqvGa2 uner1 uner2 equivRefl *AA' *CC'
        | thino' (eraseUniqCHK (CxEqv Ga1eqvGa2 equivRefl)
                         (del uner1 erQUW1) (del uner2 erQUW2)
                         equivRefl *BB' *DD')
  = refl
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (piArr _ quw1 _ keepSQUW _ _) (piE _ quw2 _ erSQUW _ _)
  rewrite #functional quw1 quw2 = naughty (erXorKp erSQUW keepSQUW)
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (piArr _ quw1 erQUW _ _ _) (pi _ quw2 keepQUW _ _ _)
  rewrite #functional quw1 quw2 = naughty (erXorKp erQUW keepQUW)
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (piE _ quw1 keepQUW _ _ _) (piEE _ quw2 erQUW _ _ _)
  rewrite #functional quw1 quw2 = naughty (erXorKp erQUW keepQUW)
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (piE _ quw1 _ erSQUW _ _) (piArr _ quw2 _ keepSQUW _ _)
  rewrite #functional quw1 quw2 = naughty (erXorKp erSQUW keepSQUW)
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (piE _ quw1 keepQUW1 erSQUW1 *A *BB') (piE _ quw2 keepQUW2 erSQUW2 *C *DD')
  rewrite eraseUniqCHK (CxEqv Ga1eqvGa2 equivRefl)
                       (kee uner1 keepQUW1) (kee uner2 keepQUW2)
                       equivRefl *BB' *DD'
  = refl
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (piE _ quw1 _ erSQUW _ _) (pi _ quw2 _ keepSQUW _ _)
  rewrite #functional quw1 quw2 = naughty (erXorKp erSQUW keepSQUW)
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (pi _ quw1 keepQUW _ _ _) (piEE _ quw2 erQUW _ _ _)
  rewrite #functional quw1 quw2 = naughty (erXorKp erQUW keepQUW)
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (pi _ quw1 keepQUW _ _ _) (piArr _ quw2 erQUW _ _ _)
  rewrite #functional quw1 quw2 = naughty (erXorKp erQUW keepQUW)
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (pi _ quw1 _ keepSQUW _ _) (piE _ quw2 _ erSQUW _ _)
  rewrite #functional quw1 quw2 = naughty (erXorKp erSQUW keepSQUW)
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (pi _ quw1 keepQUW1 keepSQUW1 *AA' *BB') (pi _ quw2 keepQUW2 keepSQUW2 *CC' *DD')
  rewrite #functional quw1 quw2
        | eraseUniqCHK Ga1eqvGa2 uner1 uner2 equivRefl *AA' *CC'
        | eraseUniqCHK (CxEqv Ga1eqvGa2 equivRefl)
                       (kee uner1 keepQUW1) (kee uner2 keepQUW2)
                       equivRefl *BB' *DD'
  = refl
eraseUniqCHK Ga1eqvGa2 uner1 uner2 ASeqvBT
  (lamE qw1 erQW1 Stt') (lamE qw2 erQW2 Ttt')
  with piSplitEquiv ASeqvBT
... | A~>C ~>>*<<~ B~>C , SeqvT
  = thino' (eraseUniqCHK (CxEqv Ga1eqvGa2 (A~>C ~>>*<<~ B~>C))
                         (del uner1 erQW1) (del uner2 erQW2) SeqvT Stt' Ttt')
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (lamE qw1 erQW _) (lam qw2 keepQW _)
  rewrite piEquivSameW SeqvT qw1 qw2
  = naughty (erXorKp erQW keepQW)
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  (lam qw1 keepQW _) (lamE qw2 erQW _)
  rewrite piEquivSameW SeqvT qw1 qw2
  = naughty (erXorKp erQW keepQW)
eraseUniqCHK Ga1eqvGa2 uner1 uner2 ASeqvBT
  (lam qw1 keepQW1 Stt') (lam qw2 keepQW2 Ttt')
  with piSplitEquiv ASeqvBT
... | A~>C ~>>*<<~ B~>C , SeqvT
  = cong lam
    (eraseUniqCHK (CxEqv Ga1eqvGa2 (A~>C ~>>*<<~ B~>C))
      (kee uner1 keepQW1) (kee uner2 keepQW2) SeqvT Stt' Ttt')
eraseUniqCHK Ga1eqvGa2 uner1 uner2 SeqvT
  ([ eSe' ] _) ([ eTe' ] _)
    = snd (eraseUniqSYN Ga1eqvGa2 uner1 uner2 eSe' eTe')


eraseUniqSYN Ga1eqvGa2 uner1 uner2 (post eS SS') eT
  with eraseUniqSYN Ga1eqvGa2 uner1 uner2 eS eT
... | SR ~>>*<<~ TR , eUniq with confluence (SS' ,- []) SR
... | R' , SR' , RR' = (SR' ~>>*<<~ TR ++ RR') , eUniq
eraseUniqSYN Ga1eqvGa2 uner1 uner2 eS (post eT TT')
  with eraseUniqSYN Ga1eqvGa2 uner1 uner2 eS eT
... | SR ~>>*<<~ TR , eUniq with confluence (TT' ,- []) TR
... | R' , TR' , RR' = (SR ++ RR' ~>>*<<~ TR') , eUniq
eraseUniqSYN Ga1eqvGa2 uner1 uner2 {keepW1 = keepW1} (var i u<w1) {keepW2} (var .i u<w2)
  rewrite thinErase uner1 i (downsetKeep u<w1 keepW1)
        | thinErase uner2 i (downsetKeep u<w2 keepW2)
  = cxEquiv Ga1eqvGa2 i , refl
eraseUniqSYN Ga1eqvGa2 uner1 uner2 (appE fAB qw1 erQW1 As) (appE fCD qw2 erQW2 Cs)
  with eraseUniqSYN Ga1eqvGa2 uner1 uner2 fAB fCD
... | ABeqvCD , f1=f2
  with piSplitEquiv ABeqvCD
... | AeqvC , BeqvD = substEquiv AeqvC BeqvD _ , f1=f2
eraseUniqSYN Ga1eqvGa2 uner1 uner2 (appE fAB qw1 erQW1 As) (fCD $~ qw2 ^ keepQW2 ~$ Cs)
  with eraseUniqSYN Ga1eqvGa2 uner1 uner2 fAB fCD
... | ABeqvCD , f1=f2 rewrite piEquivSameW ABeqvCD qw1 qw2 = naughty (erXorKp erQW1 keepQW2)
eraseUniqSYN Ga1eqvGa2 uner1 uner2 (fAB $~ qw1 ^ keepQW1 ~$ As) (appE fCD qw2 erQW2 Cs)
  with eraseUniqSYN Ga1eqvGa2 uner1 uner2 fAB fCD
... | ABeqvCD , f1=f2 rewrite piEquivSameW ABeqvCD qw1 qw2 = naughty (erXorKp erQW2 keepQW1)
eraseUniqSYN Ga1eqvGa2 uner1 uner2 (fAB $~ qw1 ^ keepQW1 ~$ As) (fCD $~ qw2 ^ keepQW2 ~$ Cs)
  with eraseUniqSYN Ga1eqvGa2 uner1 uner2 fAB fCD
... | ABeqvCD , f'uniq rewrite piEquivSameW ABeqvCD qw1 qw2
  with piSplitEquiv ABeqvCD
... | AeqvC , BeqvD
  with eraseUniqCHK Ga1eqvGa2 uner1 uner2 AeqvC As Cs
... | s'uniq rewrite f'uniq | s'uniq
  = substEquiv AeqvC BeqvD _ , refl
eraseUniqSYN Ga1eqvGa2 uner1 uner2 (*T :~: Tss') (*T' :~: Ttt')
  = equivRefl , eraseUniqCHK Ga1eqvGa2 uner1 uner2 equivRefl Tss' Ttt'
