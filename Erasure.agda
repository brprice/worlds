open import WorldSystem
import ErasureSet

module Erasure {QW : WorldSystem}{E : ErasureSet.ErasureSet {QW}} where

open WorldSystem.WorldSystem QW
open ErasureSet {QW}
open ErasureSet.ErasureSet E

open import Basics
open import OPE
open import Dir
open import Tm {Q Real}
open import Env
open import Subst {Q Real}
open import Par {Q Real}
open import Typing {QW}
open import Er


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
