open import WorldSystem

module Progress {QW : WorldSystem} where

open WorldSystem.WorldSystem QW

open import Basics
open import Star
open import Dir
open import Tm {Q Real}
open import RedNorm {Q Real}
open import Par {Q Real}
open import Typing {QW}

data Progressive {n} : Tm n chk -> Set where
  nm : (t : Nm n chk) -> Progressive (fog t)
  go : {t t' : Tm n chk} -> t ~> t' -> Progressive t

data Operative {n} : Tm n syn -> Set where
  ne   : (e : Nm n syn) -> Operative (fog e)
  _::_ : (t T : Nm n chk) -> Operative (fog t :: fog T)
  go   : {e e' : Tm n syn} -> e ~> e' -> Operative e

findPi : forall {n}{V q S' T'}(U : Nm n chk) ->
         V ~>>* pi q S' T' -> V == fog U ->
         Sg (Nm n chk) \ S -> Sg (Nm (su n) chk) \ T ->
         (U == pi q S T) * (S' == fog S) * (T' == fog T)
findPi U VpiST q with starb parReds VpiST
findPi star VpiST () | []
findPi (pi q S T) VpiST refl | [] = S , T , refl , refl , refl
findPi (lam U) VpiST () | []
findPi [ U ] VpiST () | []
findPi U VpiST refl | r ,- rs = naughty (nmNoRed U r refl)

progCHK : forall {n Ga w}{T t : Tm n chk} ->
          CHK Ga w T t -> Progressive t
operSYN : forall {n Ga w}{e : Tm n syn}{S} ->
          SYN Ga w e S -> Operative e
progCHK (pre TT' T't) = progCHK T't
progCHK (star tyW) = nm star
progCHK (pi _ _ *S *T) with progCHK *S
progCHK (pi _ _ *S *T) | nm S with progCHK *T
progCHK (pi _ _ *S *T) | nm S | (nm T) = nm (pi _ S T)
progCHK (pi _ _ *S *T) | nm S | (go TT') = go (piR _ _ TT')
progCHK (pi _ _ *S *T) | go SS' = go (piL _ SS' _)
progCHK (lam _ Tt) with progCHK Tt
progCHK (lam _ Tt) | nm t = nm (lam t)
progCHK (lam _ Tt) | go tt' = go (lam tt')
progCHK ([ eS ] refl) with operSYN eS
progCHK ([ eS ] refl) | ne e   = nm [ e ]
progCHK ([ eS ] refl) | t :: T = go upsi
progCHK ([ eS ] refl) | go ee' = go [ ee' ]
operSYN (post eS SS') = operSYN eS
operSYN (var i u<w)   = ne (var i)
operSYN (fpiST $~ _ ~$ Ss) with operSYN fpiST
operSYN (fpiST $~ _ ~$ Ss) | ne e with progCHK Ss
operSYN (fpiST $~ _ ~$ Ss) | ne e | nm s = ne (e $ s)
operSYN (fpiST $~ _ ~$ Ss) | ne e | go s = go (_ $R s)
operSYN (fpiST $~ _ ~$ Ss) | t :: T with progCHK Ss
operSYN {n}{Ga} (fpiST $~ _ ~$ Ss) | t :: U | nm s with annInv fpiST
... | *F , Ff , FpiST with findPi U FpiST refl
operSYN (fpiST $~ _ ~$ Ss) | star :: .(pi _ S T) | (nm s) | (*F , Ff , FpiST)
  | (S , T , refl , refl , refl) = naughty (killPi* Ff)
operSYN (fpiST $~ _ ~$ Ss) | pi _ t t₁ :: .(pi _ S T) | (nm s) | (*F , Ff , FpiST)
  | (S , T , refl , refl , refl) = naughty (killPiPi Ff)
operSYN (fpiST $~ _ ~$ Ss) | lam t :: .(pi _ S T) | (nm s) | (*F , Ff , FpiST)
  | (S , T , refl , refl , refl)
  = go beta
operSYN (fpiST $~ _ ~$ Ss) | [ e ] :: .(pi _ S T) | (nm s) | (*F , Ff , FpiST)
  | (S , T , refl , refl , refl)
  = ne ([ e ]::Pi _ ! S > T :$ s)
operSYN (fpiST $~ _ ~$ Ss) | t :: T | go s = go (_ $R s)
operSYN (fpiST $~ _ ~$ Ss) | go ff' = go (ff' $L _)
operSYN (*T :~: Tt) with progCHK Tt
operSYN (*T :~: Tt) | nm t with progCHK *T
operSYN (*T :~: Tt) | nm t | nm T    = t :: T
operSYN (*T :~: Tt) | nm t | go TT'  = go (_ ::R TT')
operSYN (*T :~: Tt) | go tt'         = go (tt' ::L _)
