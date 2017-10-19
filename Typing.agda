open import WorldSystem

module Typing {QW : WorldSystem} where

open WorldSystem.WorldSystem QW

open import Basics
open import Star
open import OPE
open import Dir
open import Tm {Q Real}
open import Env
open import Subst {Q Real}
open import Par {Q Real}

data Cx : Nat -> Set where
  [] : Cx ze
  _-,_ : forall {n} -> Cx n -> W * Tm n chk -> Cx (su n)

cxWTy : forall {n} -> Cx n -> Fin n -> W * Tm n chk
cxWTy (Ga -, (w , S)) ze = w , Th.act (o' oi) S
cxWTy (Ga -, _) (su i) with cxWTy Ga i
... | w , S = w , Th.act (o' oi) S

cxW : forall {n} -> Cx n -> Fin n -> W
cxW Ga i = fst (cxWTy Ga i)

cxTy : forall {n} -> Cx n -> Fin n -> Tm n chk
cxTy Ga i = snd (cxWTy Ga i)

data CHK {n}(Ga : Cx n)(w : W) : Tm n chk -> Tm n chk -> Set
data SYN {n}(Ga : Cx n)(w : W) : Tm n syn -> Tm n chk -> Set

data CHK {n} Ga w where

  pre  : forall {T T' t} ->
         T ~>> T' -> CHK Ga w T' t ->
         CHK Ga w T t

  star : tyW w -> CHK Ga w star star

  pi   : forall {q quw S T} ->
         tyW w -> snd (q &unst& inl <>) # w ~ quw -> --q ## unst w ~ quw ->
         CHK Ga (st-act quw) star S -> CHK (Ga -, (quw , S)) w star T ->
         CHK Ga w star (pi q S T)

  lam  : forall {q qw S T t} ->
         q # w ~ qw ->
         CHK (Ga -, (qw , S)) w T t ->
         CHK Ga w (pi q S T) (lam t)

  [_]  : forall {e S T} ->
         SYN Ga w e S -> S == T ->
         CHK Ga w T [ e ]

data SYN {n} Ga w where

  post : forall {e S S'} ->
         SYN Ga w e S -> S ~>> S' ->
         SYN Ga w e S'

  var  : forall i ->
         cxW Ga i << w ->
         SYN Ga w (var i) (cxTy Ga i)

  _$~_~$_  : forall {q qw f s S T} ->
             SYN Ga w f (pi q S T) ->
             q # w ~ qw ->
             CHK Ga qw S s ->
             SYN Ga w (f $ s) (Sb.act (si -, (s :: S)) T)

  _:~:_ : forall {t T} ->
          CHK Ga (st-act w) star T ->
          CHK Ga w T t ->
          SYN Ga w (t :: T) T

data VALID : {n : Nat} -> Cx n -> Set where
  emp : VALID []
  ext : forall {n Ga w}{S : Tm n chk} -> VALID Ga -> CHK Ga (st-act w) star S -> VALID (Ga -, (w , S))

------------------------------------------------------------------------------
----- Thinnings preserve judgements ------------------------------------------
------------------------------------------------------------------------------
ThinC : forall {n m} -> n <= m -> Cx n -> Cx m -> Set
ThinC oz [] [] = One
ThinC (os th) (Ga -, (u , S)) (De -, (v , S')) = ThinC th Ga De * u == v * (Th.act th S == S')
ThinC (o' th) Ga (De -, _) = ThinC th Ga De

ThinWithTypes : forall {n m}(th : n <= m)
                (Ga : Cx n)(De : Cx m) -> ThinC th Ga De ->
                Set
ThinWithTypes oz [] [] <> = One
ThinWithTypes (os th) (Ga -, (_ , _)) (De -, (_ , _)) (thC , _ , _) = ThinWithTypes th Ga De thC
ThinWithTypes (o' th) Ga (De -, (w , S)) thC = ThinWithTypes th Ga De thC * CHK De (st-act w) star S

idThinC : forall {n}(Ga : Cx n) -> ThinC oi Ga Ga
idThinC [] = <>
idThinC (Ga -, (w , S)) = idThinC Ga , refl , ActId.actId THINID S

cxWThin : forall {n m}(th : n <= m)(Ga : Cx n)(De : Cx m) ->
           ThinC th Ga De -> (i : Fin n) ->
           cxW Ga i == cxW De (thin th i)
cxWThin oz Ga De p ()
cxWThin (os th) (Ga -, (u , _)) (De -, (v , _)) (thGaDe , u=v , _) ze = u=v
cxWThin (os th) (Ga -, _) (De -, _) (thGaDe , _ , _) (su i) = cxWThin th Ga De thGaDe i
cxWThin (o' th) Ga (De -, _) p i = cxWThin th Ga De p i

cxTyThin : forall {n m}(th : n <= m)(Ga : Cx n)(De : Cx m) ->
           ThinC th Ga De -> (i : Fin n) ->
           Th.act th (cxTy Ga i) == cxTy De (thin th i)
cxTyThin oz Ga De thGaDe ()
cxTyThin (os th) (Ga -, (_ , S)) (De -, (_ , S')) (thGaDe , _ , thSS') ze
  rewrite sym thSS'
        | ActCo.actCo THINTHINTHIN (o' oi) th S
        | ActCo.actCo THINTHINTHIN (os th) (o' oi) S
        | oi-<-Q th
        | th -<-oiQ
        = refl
cxTyThin (os th) (Ga -, _) (De -, _) (thGaDe , _ , _) (su i)
  with cxTyThin th Ga De thGaDe i
... | q rewrite sym q
        | ActCo.actCo THINTHINTHIN (o' oi) th (cxTy Ga i)
        | ActCo.actCo THINTHINTHIN (os th) (o' oi) (cxTy Ga i)
        | oi-<-Q th
        | th -<-oiQ
        = refl
cxTyThin (o' th) Ga (De -, _) thGaDe i with cxTyThin th Ga De thGaDe i
... | q rewrite sym q
              | ActCo.actCo THINTHINTHIN (o' oi) th (cxTy Ga i)
              | oi-<-Q th
              = refl

thinVALID : forall {n m}(th : n <= m)
            {Ga : Cx n}{De : Cx m} ->
            (thC : ThinC th Ga De) -> ThinWithTypes th Ga De thC ->
            VALID Ga -> VALID De
thinCHK : forall {n m}(th : n <= m)
          {Ga : Cx n}{De : Cx m} -> ThinC th Ga De ->
          forall {w T t} -> CHK Ga w T t ->
             CHK De w (Th.act th T) (Th.act th t)
thinSYN : forall {n m}(th : n <= m)
          {Ga : Cx n}{De : Cx m} -> ThinC th Ga De ->
          forall {w e S} -> SYN Ga w e S ->
             SYN De w (Th.act th e) (Th.act th S)
thinVALID oz {.[]} {[]} thC thT emp = emp
thinVALID (os th) {Ga -, (_ , _)} {De -, (_ , _)} (thC , refl , refl) thT (ext valid *S)
  = ext (thinVALID th thC thT valid) (thinCHK th thC *S)
thinVALID (o' th) {Ga} {De -, (w , S)} thC (thT , *S) valid = ext (thinVALID th thC thT valid) *S
thinCHK th thC (pre TT' Tt) = pre (parThin th TT') (thinCHK th thC Tt)
thinCHK th thC (star p) = star p
thinCHK th thC (pi tyW quw *S *T) = pi tyW quw
                                       (thinCHK th thC *S)
                                       (thinCHK (os th) (thC , refl , refl) *T)
thinCHK th thC (lam qw Tt) = lam qw (thinCHK (os th) (thC , refl , refl) Tt)
thinCHK th thC ([ eS ] refl) = [ thinSYN th thC eS ] refl
thinSYN th thC (post eS SS') = post (thinSYN th thC eS) (parThin th SS')
thinSYN th thC (var i p) rewrite cxTyThin th _ _ thC i
                               | cxWThin th _ _ thC i
                         = var (thin th i) p
thinSYN th thC (_$~_~$_ {s = s}{S}{T} fST qw Ss) with thinSYN th thC fST $~ qw ~$ thinCHK th thC Ss
... | h
    rewrite ActCo.actCo SUBSTTHINSUBST (si -, Th.act th (s :: S)) (os th) T
          | ActCo.actCo THINSUBSTSUBST th (si -, (s :: S)) T
          | thin/idQ th = h
thinSYN th thC (T :~: t) = thinCHK th thC T :~: thinCHK th thC t


------------------------------------------------------------------------------
----- Strengthenings preserve judgements -------------------------------------
------------------------------------------------------------------------------
-- first, synthesising a type for a thinned term in a thinned context
-- will always give a thinned types
SYNpresThin : {n m : Nat}(th : n <= m)(Ga : Cx n)(De : Cx m)
           -> ThinC th Ga De
           -> (e' : Tm n syn){e : Tm m syn} -> e == Th.act th e'
           -> {w : W}{S : Tm m chk}
           -> SYN De w e S
           -> Sg (Tm n chk) \S' -> S == Th.act th S'
SYNpresThin th Ga De thC e' the (post eT T~>S)
  with SYNpresThin th Ga De thC e' the eT
... | strT , prT
  with redPresThin th strT prT T~>S
... | strS , prS , strT~>strS = strS , prS
SYNpresThin th Ga De thC e' p (var i x)
  with thinUnderVar th e' p
... | j , refl , refl
  = cxTy Ga j , sym (cxTyThin th Ga De thC j)
SYNpresThin th Ga De thC e' p (fST $~ qw ~$ Ss)
  with thinUnderApp th e' p
... | strf , strs , refl , refl , refl
  with SYNpresThin th Ga De thC strf refl fST
... | strST , prST
  with thinUnderPi th strST prST
... | strS , strT , refl , refl , refl
  rewrite ActCo.actCo SUBSTTHINSUBST (si -, (Th.act th strs :: Th.act th strS)) (os th) strT
        | sym (thin/idQ th)
        | sym (ActCo.actCo THINSUBSTSUBST th (si -, (strs :: strS)) strT)
  = Sb.act (si -, (strs :: strS)) strT , refl
SYNpresThin th Ga De thC e' p (*T :~: Tt)
  with thinUnderAnn th e' p
... | strt , strT , refl , refl , refl
 = strT , refl

-- I need the extra T', t' arguments and equalities to be able
-- to pattern match on the derivation
strengthenCHK : {n m : Nat}(th : n <= m)(Ga : Cx n)(De : Cx m)
               -> ThinC th Ga De
               -> {w : W}{T : Tm m chk}{t : Tm m chk}
               -> CHK De w T t
               -> {T' : Tm n chk}{t' : Tm n chk}
               -> T == Th.act th T' -> t == Th.act th t'
               -> CHK Ga w T' t'
strengthenSYN : {n m : Nat}(th : n <= m)(Ga : Cx n)(De : Cx m)
               -> ThinC th Ga De
               -> {w : W}{e : Tm m syn}{S : Tm m chk}
               -> SYN De w e S
               -> {e' : Tm n syn}{S' : Tm n chk}
               -> e == Th.act th e' -> S == Th.act th S'
               -> SYN Ga w e' S'
strengthenCHK th Ga De thC (pre T~>S St) {T'}{t'} p q
  with redPresThin th T' p T~>S
... | strS , prS , T'~>strS with strengthenCHK th Ga De thC St {strS} {t'} prS q
...                | bb = pre T'~>strS bb
strengthenCHK th Ga De thC (star tyW) {T'} {t'} p q
  with thinUnderStar th T' p | thinUnderStar th t' q
... | refl | refl = star tyW
strengthenCHK th Ga De thC (pi tyW quw *S *T) {T'} {t'} p q
  with thinUnderStar th T' p | thinUnderPi th t' q
... | refl | strS , strT , refl , refl , refl
  = pi tyW quw (strengthenCHK th Ga De thC *S refl refl)
               (strengthenCHK _ (Ga -, (_ , strS)) _ (thC , refl , refl) *T refl refl)
strengthenCHK th Ga De thC (lam qw Tt) {T'} {t'} p q
  with thinUnderPi th T' p | thinUnderLam th t' q
... | strS , strT , refl , refl , refl | strt , refl , refl
 = lam qw (strengthenCHK (os th) (Ga -, (_ , _)) (De -, (_ , _)) (thC , refl , refl) Tt refl refl)
strengthenCHK th Ga De thC ([ eS ] r) {T'} {t'} p q
  with thinUnderEmb th t' q
... | stre , refl , refl
  = [ strengthenSYN th Ga De thC eS {stre}{T'} refl (trans r p) ] refl

strengthenSYN th Ga De thC (post eT TS) {e'}{S'} p refl
  with SYNpresThin th Ga De thC e' p eT
... | strT , refl
  with thinReflectRed th strT S' TS
... | strT~>S' = post (strengthenSYN th Ga De thC eT {S' = strT} p refl) strT~>S'
strengthenSYN th Ga De thC (var i r) {e'} {S'} p q
  with thinUnderVar th e' p
... | j , refl , refl
  rewrite sym (cxTyThin th Ga De thC j)
        | sym (thinActInj th (cxTy Ga j) S' q)
        | sym (cxWThin th Ga De thC j)
  = var j r
strengthenSYN th Ga De thC (fST $~ qw ~$ Ss) {e'} {S'} p q
  with thinUnderApp th e' p
... | strf , strs , refl , refl , refl
  with SYNpresThin th Ga De thC strf refl fST
... | strST , prST
  with thinUnderPi th strST prST
... | strS , strT , refl , refl , refl
  rewrite ActCo.actCo SUBSTTHINSUBST (si -, (Th.act th strs :: Th.act th strS)) (os th) strT
        | sym (thin/idQ th)
        | sym (ActCo.actCo THINSUBSTSUBST th (si -, (strs :: strS)) strT)
        | sym (thinActInj th (Sb.act (si -, (strs :: strS)) strT) S' q)
  = strengthenSYN th Ga De thC fST {strf}{pi _ strS strT} refl refl
                            $~ qw ~$
                            strengthenCHK th Ga De thC Ss {strS}{strs} refl refl
strengthenSYN th Ga De thC (*T :~: Tt) {e'} {S'} p q
  with thinUnderAnn th e' p
... | strt , strT , refl , refl , refl
  rewrite thinActInj th strT S' q
 =    strengthenCHK th Ga De thC *T {star} {S'} refl refl
  :~: strengthenCHK th Ga De thC Tt {S'}{strt} refl refl

strengthenVALID : forall {n m}(th : n <= m)
                  {Ga : Cx n}{De : Cx m} ->
                  ThinC th Ga De ->
                  VALID De -> VALID Ga
strengthenVALID oz {[]}{[]} thC valid = valid
strengthenVALID (os th) {Ga -, (u , S)}{De -, (v , T)} (thC , refl , refl) (ext valid *T)
  = ext (strengthenVALID th thC valid) (strengthenCHK th Ga De thC *T refl refl)
strengthenVALID (o' th) {De = De -, (v , T)} thC (ext valid *T) = strengthenVALID th thC valid


------------------------------------------------------------------------------
----- Lowering the context ---------------------------------------------------
------------------------------------------------------------------------------
-- Lift << to contexts
_!<<_ : forall {n} -> Cx n -> Cx n -> Set
[] !<< [] = One
(Ga -, (u , S)) !<< (De -, (v , T)) = (Ga !<< De) * u << v * S == T

!<<refl : forall {n}{Ga : Cx n} -> Ga !<< Ga
!<<refl {_} {[]} = <>
!<<refl {._} {Ga -, (w , T)} = !<<refl , <<refl , refl

lowerCxWTy : forall {n}{Ga De : Cx n} ->
            De !<< Ga ->
            forall i ->
            cxW De i << cxW Ga i * cxTy Ga i == cxTy De i
lowerCxWTy {_} {[]} {[]} <> i = <<refl , refl
lowerCxWTy {_} {Ga -, (u , S)} {De -, (v , T)} (De<Ga , u<v , refl) ze = u<v , refl
lowerCxWTy {_} {Ga -, (u , S)} {De -, (v , T)} (De<Ga , _) (su i) with lowerCxWTy De<Ga i
... | u<v , S=T rewrite S=T = u<v , refl

lowerCxW : forall {n}{Ga De : Cx n} ->
           De !<< Ga ->
           forall i ->
           cxW De i << cxW Ga i
lowerCxW De<Ga i = fst (lowerCxWTy De<Ga i)

lowerCxTy : forall {n}{Ga De : Cx n} ->
            De !<< Ga ->
            forall i ->
            cxTy Ga i == cxTy De i
lowerCxTy De<Ga i = snd (lowerCxWTy De<Ga i)

-- If something is true in a context with higher worlds (more restrictive use of variables)
-- then it is true in a lower context
lowerCxCHK : forall {n}{Ga De : Cx n} ->
             De !<< Ga ->
             forall {w T t} ->
             CHK Ga w T t ->
             CHK De w T t
lowerCxSYN : forall {n}{Ga De : Cx n} ->
             De !<< Ga ->
             forall {w e S} ->
             SYN Ga w e S ->
             SYN De w e S
lowerCxCHK De<Ga (pre TT' Tt) = pre TT' (lowerCxCHK De<Ga Tt)
lowerCxCHK De<Ga (star tyW) = star tyW
lowerCxCHK De<Ga (pi tyW quw *S *T) = pi tyW quw (lowerCxCHK De<Ga *S)
                                         (lowerCxCHK (De<Ga , <<refl , refl) *T)
lowerCxCHK De<Ga (lam qw Tt) = lam qw (lowerCxCHK (De<Ga , <<refl , refl) Tt)
lowerCxCHK De<Ga ([ eS ] S=T) = [ lowerCxSYN De<Ga eS ] S=T

lowerCxSYN De<Ga (post eS' S'S) = post (lowerCxSYN De<Ga eS') S'S
lowerCxSYN De<Ga (var i p) rewrite lowerCxTy De<Ga i = var i (<<trans (lowerCxW De<Ga i) p)
lowerCxSYN De<Ga (fST $~ qw ~$ Ss) = lowerCxSYN De<Ga fST $~ qw ~$ lowerCxCHK De<Ga Ss
lowerCxSYN De<Ga (*S :~: Ss) = lowerCxCHK De<Ga *S :~: lowerCxCHK De<Ga Ss

------------------------------------------------------------------------------
----- Subsumption ------------------------------------------------------------
------------------------------------------------------------------------------
-- CxHole must be backwards style --- i.e. keep "local" end accessible
-- since when we go under a binder, we extend the CxHole!

-- We will lift to the free monoid, since for subsumption we need both the case
-- where judgement world has quantifier applied and is just a plain world

Q' : Set
Q' = One + Q Real

-- We won't inline this definition, since this one enforces Sort = Real
-- and we rely on this to use forall q, rather than q : Q' in many places
_#'_ : Q' -> W -> Maybe W
_#'_ = _#?_
infixr 40 _#'_

-- NOTE: naming scheme
-- we will often use qw : q #' w ~ qw'

-- We won't add this to WorldSystem as it is not that general: could have q : Q' also
_&'_ : Q Real -> Q' -> Q Real
q &' (inl <>) = q
q &' (inr r) = q & r
infixr 50 _&'_

data CxHole (n : Nat) : Nat -> Set where
-- indices are "start" and "end" (not "length")
  [] : CxHole n n
  _-,_ : forall {m} -> CxHole n m -> Sg Sort Q * Tm m chk -> CxHole n (su m)

-- note that this is actually proposition
-- i.e. we won't get different outcomes from Ga < v >< De ^ p depending on p
CxHoleDef : forall {n m} -> CxHole n m -> W -> Set
CxHoleDef [] w = One
CxHoleDef (De -, ((_ , q) , S)) w = CxHoleDef De w * Sg W \qw -> q # w ~ qw

subsumeCxHoleDef : forall {n m}{De : CxHole n m}{u v} -> CxHoleDef De u -> u << v -> CxHoleDef De v
subsumeCxHoleDef {De = []} <> uv = <>
subsumeCxHoleDef {De = De -, (q , S)} (p , qu' , qu) uv = subsumeCxHoleDef p uv , defUpset qu uv

-- Not really fish, but I can't think of a better name...
-- Should only be used locally, so doesn't matter much!
_<_><_^_ : forall {n m} -> (Ga : Cx n) -> (w : W) -> (De : CxHole n m) -> CxHoleDef De w -> Cx m
Ga < w >< [] ^ <> = Ga
--Ga < w >< De -, q ~ S ^ (p , defqw) = (Ga < w >< De ^ p) -, defAct q w defqw ~ S
Ga < w >< De -, (q , S) ^ (p , qw' , qw) = (Ga < w >< De ^ p) -, (qw' , S)

-- We won't add this to WorldSystem as it is not that general: could have q : Q' also
isActionR' : forall q r w {rw qrw} -> r #' w ~ rw -> q # rw ~ qrw -> (q &' r) # w ~ qrw
isActionR' q (inl <>) w refl qw = qw
isActionR' q (inr r) w rw qrw = isActionR rw qrw

-- We won't add this to WorldSystem as it is not that general: could have q : Q' also
defUpsetCommAct' : forall q r v
                   {rv'}(rv : r #' v ~ rv')
                   {qrv'}(qrv : q # rv' ~ qrv')
                   {w}
                   (v<w : v << w)
                -> q # defUpset?Act r rv v<w ~ defUpsetAct (isActionR' q r v rv qrv) v<w
defUpsetCommAct' q (inl <>) v rv qrv v<w = defUpsetPf (isActionR' q (inl <>) v rv qrv) v<w
defUpsetCommAct' q (inr r) v rv qrv v<w = defUpsetCommAct rv qrv v<w


-- we won't put this in WorldSystem as it is not very general -- could have s rather than inl <>
&unst&-actionL : forall q r {rv' qurv'} -> snd (q &unst& inl <>) # rv' ~ qurv'
              -> forall {v} -> r #? v ~ rv'
              -> snd (q &unst& r) # v ~ qurv'
&unst&-actionL q r {rv'} q-rv {v} r-v rewrite &unst&-action q (inl <>) rv' | &unst&-action q r v | r-v
  = q-rv

defUpset-comm-unst-act : forall {r qv' ruqv'} -> (ru-qv : snd (r &unst& inl <>) # qv' ~ ruqv')
                      -> forall {q v} -> (qv : q #' v ~ qv')
                      -> forall {w} -> (vw : v << w)
                      -> snd (r &unst& inl <>) # defUpset?Act q qv vw
                         ~ defUpsetAct (&unst&-actionL r q ru-qv qv) vw
defUpset-comm-unst-act {r}{_}{ruqv} ru-qv {q}{v} qv {w} vw
  = let a : snd (r &unst& q) # w ~ defUpsetAct ru-qv (op? q qv vw)
        a = &unst&-actionL r q (defUpsetPf ru-qv (op? q qv vw)) (defUpset?Pf q qv vw)
        b : snd (r &unst& q) # w ~ defUpsetAct (&unst&-actionL r q ru-qv qv) vw
        b = defUpsetPf (&unst&-actionL r q ru-qv qv) vw
        c : defUpsetAct ru-qv (op? q qv vw) == defUpsetAct (&unst&-actionL r q ru-qv qv) vw
        c = #functional a b
        d : snd (r &unst& inl <>) # (defUpset?Act q qv vw) ~ defUpsetAct ru-qv (op? q qv vw)
        d = defUpsetPf ru-qv (op? q qv vw)
    in trans d (cong Just c)

subsumeTy : forall {n m v w}
            (Ga : Cx n)(De : CxHole n m)(def : CxHoleDef De v)
         -> (v<w : v << w)
         -> (i : Fin m)
         -> cxTy (Ga < v >< De ^ def) i == cxTy (Ga < w >< De ^ subsumeCxHoleDef def v<w) i
subsumeTy Ga [] def vw i = refl
subsumeTy Ga (De -, (_ , T)) def vw ze = refl
subsumeTy Ga (De -, _) (def , _) vw (su i) rewrite subsumeTy Ga De def vw i = refl

subsumeW : forall {n m v w}
           (Ga : Cx n)(De : CxHole n m)(def : CxHoleDef De v)
        -> (v<w : v << w)
        -> (i : Fin m)(q : Q'){qv' : W}
        -> (qv : q #' v ~ qv')
        -> cxW (Ga < v >< De ^ def) i << qv'
        -> cxW (Ga < w >< De ^ subsumeCxHoleDef def v<w) i << defUpset?Act q qv v<w
subsumeW Ga [] def v<w i q qv u<qv = <<trans u<qv (op? q qv v<w)
subsumeW Ga (De -, ((_ , r) , _)) (_ , rv' , rv) v<w ze q qv rv<qv = dominateUpset r q rv qv rv<qv v<w
subsumeW Ga (De -, _) (def , _) v<w (su i) q qv u<qv = subsumeW Ga De def v<w i q qv u<qv

subsumeVar' : forall {n m v w}
              (Ga : Cx n)(De : CxHole n m)(def : CxHoleDef De v)
              (q : Q'){qv' : W}
              (qv : q #' v ~ qv')
              (v<w : v << w)
           -> (i : Fin m)(p : cxW (Ga < v >< De ^ def) i << qv')
           -> SYN (Ga < w >< De ^ subsumeCxHoleDef def v<w)
                  (defUpset?Act q qv v<w)
                  (var i)
                  (cxTy (Ga < w >< De ^ subsumeCxHoleDef def v<w) i)
subsumeVar' Ga De p q qv vw i u<qv = var i (subsumeW Ga De p vw i q qv u<qv)

subsumeVALID' : forall {n m v w}
                (Ga : Cx n)(De : CxHole n m)(def : CxHoleDef De v)
                (v<w : v << w)
              -> VALID (Ga < v >< De ^ def)
              -> VALID (Ga < w >< De ^ subsumeCxHoleDef def v<w)
subsumeCHK' : forall {n m v w}
              (Ga : Cx n)(De : CxHole n m)(def : CxHoleDef De v)
              (q : Q')
              {qv'}(qv : q #' v ~ qv')
              (v<w : v << w)
              {T t : Tm m chk}
           -> CHK (Ga < v >< De ^ def) qv' T t
           -> CHK (Ga < w >< De ^ subsumeCxHoleDef def v<w) (defUpset?Act q qv v<w) T t
subsumeSYN' : forall {n m v w}
              (Ga : Cx n)(De : CxHole n m)(def : CxHoleDef De v)
              (q : Q')
              {qv'}(qv : q #' v ~ qv')
              (v<w : v << w)
              {e : Tm m syn}{S : Tm m chk}
           -> SYN (Ga < v >< De ^ def) qv' e S
           -> SYN (Ga < w >< De ^ subsumeCxHoleDef def v<w) (defUpset?Act q qv v<w) e S
subsumeVALID' Ga [] def vw valid = valid
subsumeVALID' Ga (De -, (q , S)) (def , qv' , qv) vw (ext valid *S)
  with subsumeCHK' Ga De def (inr (starSg& q)) (starSg&-pf qv) vw *S
... | subsume*S rewrite sym (defUpsetCommStarAct qv vw)
  = ext (subsumeVALID' Ga De def vw valid) subsume*S
subsumeCHK' Ga De def q qv vw (pre x p) = pre x (subsumeCHK' Ga De def q qv vw p)
subsumeCHK' Ga De def q qv vw (star p) = star (tyWUpset (op? q qv vw) p)
subsumeCHK' {v = v}{w} Ga De def q qv vw (pi {r}{S = S} p ru-qv *S *T)
  = let assoc-ruq-v : snd (r &unst& q) # v ~ _
        assoc-ruq-v = &unst&-actionL r q ru-qv qv
        *Sw : CHK (Ga < w >< De ^ _)
                  (defUpsetAct (starSg&-pf (&unst&-actionL r q ru-qv qv)) vw)
                  star S
        *Sw = subsumeCHK' Ga De def (inr (starSg& (r &unst& q))) (starSg&-pf assoc-ruq-v) vw *S
        worlds-same : defUpsetAct (starSg&-pf (&unst&-actionL r q ru-qv qv)) vw
                   == st-act (defUpsetAct (&unst&-actionL r q ru-qv qv) vw)
        worlds-same = #functional
                        (defUpsetPf (starSg&-pf (&unst&-actionL r q ru-qv qv)) vw)
                        (starSg&-pf (defUpsetPf assoc-ruq-v vw))
    in pi (tyWUpset (op? q qv vw) p)
          (defUpset-comm-unst-act ru-qv qv vw)
          (subst worlds-same *Sw)
          (subsumeCHK' Ga (De -, (r &unst& q , S)) (def , _ , assoc-ruq-v) q qv vw *T)
  where subst : forall {GD T t w w'} -> w == w' -> CHK GD w T t -> CHK GD w' T t
        subst refl x = x
subsumeCHK' Ga De def q qv vw (lam rqv Tt)
  = lam (defUpsetCommAct' _ q _ qv rqv vw)
        (subsumeCHK' Ga (De -, ((_ , _ &' q) , _)) (def , _ , isActionR' _ q _ qv rqv) q qv vw Tt)
subsumeCHK' Ga De def q qv vw ([ eS ] S=T) = [ subsumeSYN' Ga De def q qv vw eS ] S=T
subsumeSYN' Ga De def q qv vw (post p x) = post (subsumeSYN' Ga De def q qv vw p) x
subsumeSYN' {w = w} Ga De def q qv vw (var i p) rewrite subsumeTy Ga De def vw i = subsumeVar' Ga De def q qv vw i p
subsumeSYN' Ga De def q qv vw (_$~_~$_ {r} fST rqv Ss)
  = subsumeSYN' Ga De def q qv vw fST
    $~ defUpsetCommAct' r q _ qv rqv vw ~$
    subsumeCHK' Ga De def (inr (r &' q)) (isActionR' r q _ qv rqv) vw Ss
subsumeSYN' Ga De def q qv vw (*S :~: Ss)
  = let *Sw : CHK (Ga < _ >< De ^ subsumeCxHoleDef def vw)
                 (defUpsetAct (isActionR' st q _ qv (st-pr _)) vw)
                 star
                 _
        *Sw = subsumeCHK' Ga De def (inr (st &' q)) (isActionR' st q _ qv (st-pr _)) vw *S
        worlds-same : st-act (defUpset?Act q qv vw)
                   == defUpsetAct (isActionR' st q _ qv (st-pr _)) vw
        worlds-same = st-functional (defUpsetCommAct' st q _ qv (st-pr _) vw)
    in subst (sym worlds-same) *Sw
    :~:
    subsumeCHK' Ga De def q qv vw Ss
  where subst : forall {GD T t w w'} -> w == w' -> CHK GD w T t -> CHK GD w' T t
        subst refl x = x

subsumeCHK : forall {n v w}
             (Ga : Cx n)
             {T t : Tm n chk}
          -> v << w
          -> CHK Ga v T t
          -> CHK Ga w T t
subsumeCHK Ga vw Tt = subsumeCHK' Ga [] <> (inl <>) refl vw Tt

subsumeSYN : forall {n v w}
             (Ga : Cx n)
             {e : Tm n syn}{S : Tm n chk}
          -> v << w
          -> SYN Ga v e S
          -> SYN Ga w e S
subsumeSYN Ga vw eS = subsumeSYN' Ga [] <> (inl <>) refl vw eS


------------------------------------------------------------------------------
----- Substitution -----------------------------------------------------------
------------------------------------------------------------------------------
CxMor : {n m : Nat} -> Cx m -> Cx n -> Env (Tm m syn) n -> Set
CxMor De [] [] = One
CxMor De (Ga -, (w , S)) (ez -, e) = CxMor De Ga ez * SYN De w e (Sb.act ez S)

thinCxMor : {n m l : Nat}(th : m <= l) ->
            {De : Cx m}{Th : Cx l} -> ThinC th De Th ->
            {Ga : Cx n}(ez : Env (Tm m syn) n) ->
            CxMor De Ga ez ->
            CxMor Th Ga (env (Th.act th) ez)
thinCxMor th thC {[]} [] <> = <>
thinCxMor th thC {Ga -, (w , S)} (ez -, e) (ezok , eS)
  with thinSYN th thC eS
... | eS'
  rewrite ActCo.actCo THINSUBSTSUBST th ez S
  = (thinCxMor th thC {Ga} ez ezok) , eS'

-- weaken a CxMor
CxMorW : {n m : Nat}{De : Cx m}{Ga : Cx n}(ez : Env (Tm m syn) n) ->
          CxMor De Ga ez ->
          (w : W) ->
          (S : Tm n chk) ->
          CxMor (De -, (w , Sb.act ez S)) (Ga -, (w , S)) (Sb.actW ez)
CxMorW {De = De} ez ezok w S
  with the (SYN (De -, (w , Sb.act ez S)) w (var ze) (Th.act (o' oi) (Sb.act ez S)))
           (var ze <<refl)
... | h
  rewrite ActCo.actCo THINSUBSTSUBST (o' oi) ez S
  = thinCxMor (o' oi) (idThinC De) ez ezok , h

idCxMor : forall {n}(Ga : Cx n) -> CxMor Ga Ga si
idCxMor [] = <>
idCxMor (Ga -, (w , S)) with CxMorW si (idCxMor Ga) w S
... | h
    rewrite ActId.actId SUBSTID S
    = h

yelp : forall {n m}(ez : Env (Tm m syn) n) s S ->
       env (Sb.act (si -, Sb.act ez (s :: S))) (env (Th.act (o' oi)) ez)
       == ez
yelp {n}{m} ez s S
  rewrite envenvQ (Sb.act (si -, Sb.act ez (s :: S))) (Th.act (o' oi)) ez
  = envIdQ _ zelp ez
  where
    zelp : (x : Tm m syn) ->
            Sb.act (si -, Sb.act ez (s :: S)) (Th.act (o' oi) x) == x
    zelp x
      rewrite ActCo.actCo SUBSTTHINSUBST (si -, Sb.act ez (s :: S)) (o' oi) x
            | si{m} /oiQ
      = ActId.actId SUBSTID x

substVar : forall {n m}{Ga : Cx n}{De : Cx m}
           (ez : Env (Tm m syn) n) -> CxMor De Ga ez ->
           (i : Fin n) ->
           SYN De (cxW Ga i) (ez ! i) (Sb.act ez (cxTy Ga i))
substVar {Ga = Ga -, (w , S)} (ez -, e) (ezok , eS) ze
  rewrite ActCo.actCo SUBSTTHINSUBST (ez -, e) (o' oi) S
        | ez /oiQ
  = eS
substVar {Ga = Ga -, (_ , S)} (ez -, e) (ezok , _) (su i) with substVar ez ezok i
... | eS
  rewrite ActCo.actCo SUBSTTHINSUBST (ez -, e) (o' oi) (cxTy Ga i)
        | ez /oiQ
  = eS

substCHK : forall {n m}{Ga : Cx n}{De : Cx m}
           (ez : Env (Tm m syn) n) -> CxMor De Ga ez ->
           forall {w T t} ->
           CHK Ga w T t -> CHK De w (Sb.act ez T) (Sb.act ez t)
substSYN : forall {n m}{Ga : Cx n}{De : Cx m}
           (ez : Env (Tm m syn) n) -> CxMor De Ga ez ->
           forall {w e S} ->
           SYN Ga w e S -> SYN De w (Sb.act ez e) (Sb.act ez S)

substCHK ez ezok (pre TT' Tt) =
  pre (parStab (parzRefl ez) TT') (substCHK ez ezok Tt)
substCHK ez ezok (star p) = star p
substCHK ez ezok {w} (pi {q}{quw'}{S} p quw *S *T) =
  pi p quw (substCHK ez ezok *S) (substCHK (Sb.actW ez) (CxMorW ez ezok quw' S) *T)
substCHK ez ezok {w} (lam {_}{qw'}{S} qw Tt) =
  lam qw (substCHK (Sb.actW ez) (CxMorW ez ezok qw' S) Tt)
substCHK ez ezok ([ eS ] refl) =
  [ substSYN ez ezok eS ] refl
substSYN ez ezok (post eS SS') =
  post (substSYN ez ezok eS) (parStab (parzRefl ez) SS')
substSYN ez ezok (var i p) = subsumeSYN _ p (substVar ez ezok i)
substSYN ez ezok (_$~_~$_ {f = f}{s}{S}{T} fST qw Ss)
  with substSYN ez ezok fST $~ qw ~$ substCHK ez ezok Ss
... | h
  rewrite ActCo.actCo SUBSTSUBSTSUBST (si -, Sb.act ez (s :: S)) (Sb.actW ez) T
        | yelp ez s S
        | ActCo.actCo SUBSTSUBSTSUBST ez (si -, (s :: S)) T
        | subsiQ ez
  = h
substSYN ez ezok (*T :~: Tt) = substCHK ez ezok *T :~: substCHK ez ezok Tt

-- This is extra data needed over CxMor to be a substitution intstance
-- and then we will preserve validity
-- (note that a CxMor can introduce complete garbage, so won't preserve validity)
CxMorIsSub : {n m : Nat} -> Cx m -> Cx n -> Env (Tm m syn) n -> m <= n -> Set
CxMorIsSub De (Ga -, (w , S)) (ez -, x) (o' th) = CxMorIsSub De Ga ez th
CxMorIsSub {su n}{su m} (De -, (u , T)) (Ga -, (v , S)) (ez -, e) (os th)
  = e == var ze
  * u == v
  * Sg (Env (Tm m syn) n) (\ez' ->
    (ez == env (Th.act (o' oi)) ez')
  * T == Sb.act ez' S -- A CxMor (De -, u ~ T) (Ga -, v ~ S) (ez -, var ze)
                      -- will only say SYN De (var ze) (Sb.act ez S)
                      -- i.e. T ~>>* S, whereas we need equality
  * CxMorIsSub De Ga ez' th)
CxMorIsSub [] [] [] oz = One

strengthenCxMor : {m m' : Nat}(th : m <= m')(De : Cx m)(De' : Cx m')
               -> ThinC th De De'
               -> {n : Nat}(Ga : Cx n)
               -> (ez : Env (Tm m syn) n)
               -> CxMor De' Ga (env (Th.act th) ez)
               -> CxMor De Ga ez
strengthenCxMor th De De' thC [] [] isMor = isMor
strengthenCxMor th De De' thC (Ga -, (w , S)) (ez -, e) (isMor , eS)
  = strengthenCxMor th De De' thC Ga ez isMor
  , strengthenSYN th De De' thC eS {e}{Sb.act ez S} refl (sym (ActCo.actCo THINSUBSTSUBST th ez S))

substVALID : forall {n m}(th : m <= n){Ga : Cx n}{De : Cx m}
              (ez : Env (Tm m syn) n) -> CxMor De Ga ez -> CxMorIsSub De Ga ez th ->
              VALID Ga -> VALID De
substVALID oz {[]}{[]} ez isMor isSub valid = valid
substVALID (os th) {Ga -, (u , S)}{De -, (._ , ._)} (._ -, e) (isMor , eS') (p' , refl , ez' , refl , refl , isSub) (ext valid *S)
  = ext (substVALID th ez' isMor' isSub valid)
        (substCHK ez' isMor' *S)
  where isMor' = strengthenCxMor (o' oi) De (De -, (u , Sb.act ez' S)) (idThinC De) Ga ez' isMor
substVALID (o' th) {Ga -, (_ , S)}{De} (ez -, _) (isMor , _) isSub (ext valid *S)
  = substVALID th ez isMor isSub valid


------------------------------------------------------------------------------
----- A Pi will never accept a Pi or * ---------------------------------------
------------------------------------------------------------------------------
killPiPi : forall {n}{Ga : Cx n}{w q q' S S' T T'} ->
           CHK Ga w (pi q S T) (pi q' S' T') -> Zero
killPiPi (pre (pi _ _ _) bad) = killPiPi bad

killPi* : forall {n}{Ga : Cx n}{w q S T} ->
           CHK Ga w (pi q S T) star -> Zero
killPi* (pre (pi _ _ _) bad) = killPi* bad

------------------------------------------------------------------------------
----- Boost pre and post rules to allow multistep reduction ------------------
------------------------------------------------------------------------------
pre* : forall {n}{Ga : Cx n}{w T T' t} ->
         T ~>>* T' -> CHK Ga w T' t ->
         CHK Ga w T t
pre* [] Tt = Tt
pre* (rT ,- rTs) T't = pre rT (pre* rTs T't)

post* : forall {n}{Ga : Cx n}{w e S S'} ->
        SYN Ga w e S -> S ~>>* S' -> SYN Ga w e S'
post* eS [] = eS
post* eS (r ,- rs) = post* (post eS r) rs

------------------------------------------------------------------------------
----- Inversion principles which strip off pre and post ----------------------
------------------------------------------------------------------------------
annInv : forall {n}{Ga w}{t T T' : Tm n chk} ->
         SYN Ga w (t :: T) T' ->
         CHK Ga (st-act w) star T * CHK Ga w T t * (T ~>>* T')
annInv (post tT r) with annInv tT
... | T , t , rs = T , t , rs ++ (r ,- [])
annInv (T :~: t)   = T , t , []

lamInv : forall {n}{Ga w q}{S : Tm n chk}{T t} ->
         CHK Ga w (pi q S T) (lam t) ->
         Sg W \qw -> q # w ~ qw *
         Sg (Tm n chk) \ S' -> Sg (Tm (su n) chk) \ T' ->
         (S ~>>* S') * (T ~>>* T') *
         CHK (Ga -, (qw , S')) w T' t
lamInv (pre (pi _ rS rT) d) with lamInv d
... | qw' , qw , _ , _ , rsS , rsT , d' = qw' , qw , _ , _ , (rS ,- rsS) , (rT ,- rsT) , d'
lamInv (lam qw d) = _ , qw , _ , _ , [] , [] , d

-- Note that this is not the inversion principle you may want, which would be
-- CHK Ga (st # w) star (pi q S T) ->
-- CHK Ga (st # q # w) star S * CHK (Ga -, q # w ~ S) (st # w) star T
piInv : forall {n}{Ga w q}{S : Tm n chk}{T} ->
        CHK Ga w star (pi q S T) ->
        Sg W \quw -> snd (q &unst& inl <>) # w ~ quw *
        CHK Ga (st-act quw) star S * CHK (Ga -, (quw , S)) w star T
piInv (pre star *piST) = piInv *piST
piInv (pi _ quw *S *T) = _ , quw , *S , *T


helpPiInvSt1 : forall {n Ga}{q : Q Real}{S : Tm n chk}{T}{w}
               (u v : Sg W (\u -> st-act u == w * Sg W \qu -> q # u ~ qu)) ->
               ((fst u << fst v) + (fst (snd (snd v)) << fst (snd (snd u)))) ->
               CHK (Ga -, (fst (snd (snd u)) , S)) w star T ->
               CHK (Ga -, (fst (snd (snd v)) , S)) w star T
helpPiInvSt1 {_}{Ga}{q}{S} (u , refl , qu~qu') (v , stv=w , qv~qv') (inl u<v) *Tu
  with subsumeCHK' Ga ([] -, ((_ , q) , S)) (<> , qu~qu') (inr st) (st-pr u) u<v *Tu
... | *Tv rewrite #functionalSg (defUpset (snd qu~qu') u<v) qv~qv'
                | sym (st-functional (defUpsetPf (st-pr u) u<v))
                | stv=w
  = *Tv
helpPiInvSt1 u v (inr qu>qv) *Tu = lowerCxCHK (!<<refl , qu>qv , refl) *Tu

helpPiInvSt2 : forall {n Ga}{S : Tm n chk}{T u v w} ->
               st-act u == w -> st-act v == w ->
               forall {q qu' qv'} -> q # u ~ qu' -> q # v ~ qv' ->
               CHK (Ga -, (qu' , S)) w star T ->
               CHK (Ga -, (qv' , S)) w star T
helpPiInvSt2 stu=w stv=w qu qv = starLiftPres _ (\{u}{v} -> helpPiInvSt1 u v) (GwqConn _ _ stu=w qu stv=w qv)

-- This is the nice version of inverting a Pi
piInvSt : forall {n}{Ga w} ->
          forall {q qw'} -> q # w ~ qw' ->
          forall {S : Tm n chk}{T} ->
          CHK Ga (st-act w) star (pi q S T) ->
          CHK Ga (st-act qw') star S * CHK (Ga -, (qw' , S)) (st-act w) star T
piInvSt qw (pre star *piST) = piInvSt qw *piST
piInvSt {w = w}{q} qw (pi tyWsw qu-sw *S *T)
  rewrite &unst&-action q (inl <>) (st-act w)
  with split## (unst (st-act w)) qu-sw
... | w' , u-sw , q-w'
  rewrite stq (st-unst u-sw) refl q-w' qw
  = *S , helpPiInvSt2 (st-unst u-sw) refl q-w' qw *T

------------------------------------------------------------------------------
----- The forwards direction of "nice pi" is admissible ----------------------
------------------------------------------------------------------------------
-- This is the same reasoning as the inversion principle, but backwards
piSt : forall {n}{Ga w q}{S : Tm n chk}{T} ->
       forall {qw'} -> q # w ~ qw' -> -- needed to have a derivation at world "q # w"
       forall {qusw'} -> snd (q &unst& inl <>) # (st-act w) ~ qusw' -> -- premiss
       CHK Ga (st-act qw') star S -> CHK (Ga -, (qw' , S)) (st-act w) star T ->
       CHK Ga (st-act w) star (pi q S T)
piSt {w = w}{q} q-w qu-sw *S *T
  with split## (unst (st-act w))
               (trans (sym (&unst&-action q (inl <>) (st-act w))) qu-sw)
... | w' , u-sw , q-w'
  rewrite stq refl (st-unst u-sw) q-w q-w'
  = pi (stTyW w) qu-sw *S (helpPiInvSt2 refl (st-unst u-sw) q-w q-w' *T)

