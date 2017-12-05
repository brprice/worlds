module Par {Q : Set} where

open import Basics
open import Star
open import OPE
open import Dir
open import Tm {Q}
open import Env
open import Subst {Q}
open import RedNorm {Q}

data _~>>_ {n} : {d : Dir} -> Tm n d -> Tm n d -> Set where
  star : star ~>> star
  pi   : forall q {S S' T T'} -> S ~>> S' -> T ~>> T' -> pi q S T ~>> pi q S' T'
  lam  : forall {t t'} -> t ~>> t' -> lam t ~>> lam t'
  [_]  : forall {e e'} -> e ~>> e' -> [ e ] ~>> [ e' ]
  var  : (i : Fin n) -> var i ~>> var i
  _$_  : forall {f f' s s'} -> f ~>> f' -> s ~>> s' -> (f $ s) ~>> (f' $ s')
  _::_ : forall {t t' T T'} -> t ~>> t' -> T ~>> T' -> (t :: T) ~>> (t' :: T')
  beta : forall {q t t' S S' T T' s s'} ->
           t ~>> t' -> S ~>> S' -> T ~>> T' -> s ~>> s' ->
           ((lam t :: pi q S T) $ s) ~>> Sb.act (si -, (s' :: S')) (t' :: T')
  upsi : forall {t t' T} -> t ~>> t' -> [ t :: T ] ~>> t'

_~>>*_ : forall {d n} -> Tm n d -> Tm n d -> Set
s ~>>* t = Star _~>>_ s t

parRefl : forall {d n}(t : Tm n d) -> t ~>> t
parRefl star = star
parRefl (pi q S T) = pi q (parRefl S) (parRefl T)
parRefl (lam t) = lam (parRefl t)
parRefl [ e ] = [ parRefl e ]
parRefl (var i) = var i
parRefl (f $ s) = parRefl f $ parRefl s
parRefl (t :: T) = parRefl t :: parRefl T

redPar : forall {n d}{t t' : Tm n d} -> t ~> t' -> t ~>> t'
redPar (piL q SS' T) = pi q (redPar SS') (parRefl T)
redPar (piR q S TT') = pi q (parRefl S) (redPar TT')
redPar (lam tt') = lam (redPar tt')
redPar [ ee' ] = [ redPar ee' ]
redPar (ff' $L s) = redPar ff' $ parRefl s
redPar (f $R ss') = parRefl f $ redPar ss'
redPar (tt' ::L T) = redPar tt' :: parRefl T
redPar (t ::R TT') = parRefl t :: redPar TT'
redPar beta = beta (parRefl _) (parRefl _) (parRefl _) (parRefl _)
redPar upsi = upsi (parRefl _)

~>To~>>* : forall {n d}{s t : Tm n d} -> s ~> t -> s ~>>* t
~>To~>>* s~>t = redPar s~>t ,- []

pi* : forall {n}{S S' : Tm n chk}{T T'} -> S ~>>* S' -> T ~>>* T' -> forall {q} -> pi q S T ~>>* pi q S' T'
pi* S~>S' T~>T' = starm _ (pi _ (parRefl _)) T~>T' ++ starm _ (\r -> pi _ r (parRefl _)) S~>S'

lam* : forall {n}{t t' : Tm (su n) chk} -> t ~>>* t' -> lam t ~>>* lam t'
lam* t~>t' = starm _ lam t~>t'

[_]* : forall {n}{e e' : Tm n syn} -> e ~>>* e' -> [ e ] ~>>* [ e' ]
[ e~>e' ]* = starm _ [_] e~>e'

_$*_ : forall {n}{f f' : Tm n syn}{s s'} -> f ~>>* f' -> s ~>>* s' -> (f $ s) ~>>* (f' $ s')
f~>f' $* s~>s' = starm _ (parRefl _ $_) s~>s' ++ starm _ (_$ parRefl _) f~>f'

_::*_ : forall {n}{t t' T T' : Tm n chk} -> t ~>>* t' -> T ~>>* T' -> (t :: T) ~>>* (t' :: T')
t~>t' ::* T~>T' = starm _ (parRefl _ ::_) T~>T' ++ starm _ (_:: parRefl _) t~>t'


_~~>>_ : forall {n m} -> Env (Tm m syn) n -> Env (Tm m syn) n -> Set
[] ~~>> [] = One
(sz -, s) ~~>> (tz -, t) = (sz ~~>> tz) * (s ~>> t)

parzRefl : forall {n m}(sz : Env (Tm m syn) n) -> sz ~~>> sz
parzRefl [] = <>
parzRefl (sz -, s) = parzRefl sz , parRefl s

parThin : forall {d n m}{s t : Tm n d}(th : n <= m) ->
           s ~>> t -> Th.act th s ~>> Th.act th t
parThin th star = star
parThin th (pi q rS rT) = pi q (parThin th rS) (parThin (os th) rT)
parThin th (lam rt) = lam (parThin (os th) rt)
parThin th [ re ] = [ parThin th re ]
parThin th (var i) = var (thin th i)
parThin th (rf $ rs) = parThin th rf $ parThin th rs
parThin th (rt :: rT) = parThin th rt :: parThin th rT
parThin th (beta {q}{t}{t'}{S}{S'}{T}{T'}{s}{s'} rt rS rT rs)
  with the (_ ~>> _)
           (beta {q = q} (parThin (os th) rt) (parThin th rS)
             (parThin (os th) rT) (parThin th rs))
... | z
    rewrite ActCo.actCo THINSUBSTSUBST th (si -, (s' :: S')) t'
          | ActCo.actCo THINSUBSTSUBST th (si -, (s' :: S')) T'
          | ActCo.actCo SUBSTTHINSUBST (si -, Th.act th (s' :: S')) (os th) t'
          | ActCo.actCo SUBSTTHINSUBST (si -, Th.act th (s' :: S')) (os th) T'
          | thin/idQ th
          = z
parThin th (upsi rt) = upsi (parThin th rt)

parsThin : forall {d n m}{s t : Tm n d}(th : n <= m) ->
           s ~>>* t -> Th.act th s ~>>* Th.act th t
parsThin th [] = []
parsThin th (s~>>t ,- t~>>*r) = parThin th s~>>t ,- parsThin th t~>>*r

parThinz : forall {n m m'}(sz tz : Env (Tm m syn) n)(th : m <= m') ->
  sz ~~>> tz -> env (Th.act th) sz ~~>> env (Th.act th) tz
parThinz []        []        th <> = <>
parThinz (sz -, s) (tz -, t) th (rz , r) = parThinz sz tz th rz , parThin th r

parWeak : forall {n m}{sz tz : Env (Tm m syn) n} ->
          sz ~~>> tz -> Sb.actW sz ~~>> Sb.actW tz
parWeak rz = parThinz _ _ (o' oi) rz , var ze

parStab : forall {d n m}{sz tz : Env (Tm m syn) n}{s t : Tm n d} ->
          sz ~~>> tz -> s ~>> t -> Sb.act sz s ~>> Sb.act tz t
parStab rz star = star
parStab rz (pi q rS rT) = pi q (parStab rz rS) (parStab (parThinz _ _ (o' oi) rz , var _) rT)
parStab rz (lam rt) = lam (parStab (parThinz _ _ (o' oi) rz , var _) rt)
parStab rz [ re ] = [ parStab rz re ]
parStab rz (var i) = go _ _ rz i where
  go : forall {n m} (sz tz : Env (Tm m syn) n) ->
     sz ~~>> tz -> (i : Fin n) -> (sz ! i) ~>> (tz ! i)
  go (sz -, s) (tz -, t) (rz , r) ze = r
  go (sz -, s) (tz -, t) (rz , r) (su i) = go sz tz rz i
parStab rz (rf $ rs) = parStab rz rf $ parStab rz rs
parStab rz (rt :: rT) = parStab rz rt :: parStab rz rT
parStab {sz = sz}{tz = tz} rz (beta {q}{t}{t'}{S}{S'}{T}{T'}{s}{s'} rt rS rT rs)
    with the (_ ~>> _)
         (beta {q = q} (parStab (parThinz _ _ (o' oi) rz , var ze) rt)
               (parStab rz rS)
               (parStab (parThinz _ _ (o' oi) rz , var ze) rT)
               (parStab rz rs))
... | z
  rewrite ActCo.actCo SUBSTSUBSTSUBST tz (si -, (s' :: S')) t'
        | ActCo.actCo SUBSTSUBSTSUBST tz (si -, (s' :: S')) T'
        | ActCo.actCo SUBSTSUBSTSUBST (si -, Sb.act tz (s' :: S')) (Sb.actW tz) t'
        | ActCo.actCo SUBSTSUBSTSUBST (si -, Sb.act tz (s' :: S')) (Sb.actW tz) T'
        | envenvQ (Sb.act (si -, Sb.act tz (s' :: S'))) (Th.act (o' oi)) tz
        | envextQ (lemma2 si (Sb.act tz (s' :: S'))) tz
        | envIdQ (Sb.act si) (ActId.actId SUBSTID) tz
        | subsiQ tz
  = z
parStab rz (upsi rt) = upsi (parStab rz rt)

_~~>>*_ : forall {n m} -> Env (Tm m syn) n -> Env (Tm m syn) n -> Set
_~~>>*_ = Star _~~>>_

parsStab : forall {d n m}{sz tz : Env (Tm m syn) n}{s t : Tm n d} ->
           sz ~~>>* tz -> s ~>>* t -> Sb.act sz s ~>>* Sb.act tz t
parsStab {sz = sz} {.sz} [] [] = []
parsStab {sz = sz} {.sz} [] (r ,- rs)
  = parStab (parzRefl sz) r ,- parsStab [] rs
parsStab {sz = sz} {tz} {s = s} (rz ,- rzs) rs
  = parStab rz (parRefl s) ,- parsStab rzs rs

-- The case of parsStab where we are only substituting var ze
substStab : {n : Nat}{s s' S S' : Tm n chk}{d : Dir}{T T' : Tm (su n) d}
         -> s ~>>* s' -> S ~>>* S' -> T ~>>* T'
        -> Sb.act (si -, (s :: S)) T ~>>* Sb.act (si -, (s' :: S')) T'
substStab {_}{s}{s'}{S}{S'} s~>s' S~>S' T~>T'
  = parsStab (starm (si -,_) (parzRefl si ,_)
                    (starm (s ::_) (parRefl s ::_) S~>S'
                  ++ starm (_:: S') (_:: parRefl S') s~>s'))
             T~>T'

parReds : forall {n d}{t t' : Tm n d} -> t ~>> t' -> t ~>* t'
parReds star = []
parReds (pi q SS' TT') =
  starm _ (\ S -> piL q S _) (parReds SS') ++
  starm _ (\ T -> piR q _ T) (parReds TT')
parReds (lam tt') = starm _ lam (parReds tt')
parReds [ ee' ] = starm _ [_] (parReds ee')
parReds (var i) = []
parReds (ff' $ ss') =
  starm _ (_$L _) (parReds ff') ++
  starm _ (_ $R_) (parReds ss')
parReds (tt' :: TT') =
  starm _ (_::L _) (parReds tt') ++
  starm _ (_ ::R_) (parReds TT')
parReds (beta {q}{t}{t'}{S}{S'}{T}{T'}{s}{s'} tt' SS' TT' ss') = 
  (starm (_$ s) (_$L s)
     (starm (_:: pi q S T) (_::L _) (starm _ lam (parReds tt')) ++
      starm (lam t' ::_) (_ ::R_)
        (starm _ (\ S -> piL _ S _) (parReds SS') ++
         starm _ (\ T -> piR _ _ T) (parReds TT'))) ++
   starm _ (_ $R_) (parReds ss')) ++
  (beta {q = q}{t'}{S'}{T'}{s'} ,- [])
parReds (upsi tt') = upsi ,- parReds tt'

parsReds : forall {n d}{t t' : Tm n d} -> t ~>>* t' -> t ~>* t'
parsReds [] = []
parsReds (t~>t' ,- t'~>t'') = parReds t~>t' ++ parsReds t'~>t''

starInvRed : forall {n}{U : Tm n chk} -> star ~>>* U -> U == star
starInvRed [] = refl
starInvRed (star ,- rs) = starInvRed rs

piInvRed : forall {n}{q}{S U : Tm n chk}{T : Tm (su n) chk} ->
  pi q S T ~>>* U ->
  Sg (Tm n chk) \ S' -> Sg (Tm (su n) chk) \ T' ->
  (U == pi q S' T') * (S ~>>* S') * (T ~>>* T')
piInvRed [] = _ , _ , refl , [] , []
piInvRed (pi q S T ,- rs) with piInvRed rs
... | _ , _ , refl , SS' , TT' = _ , _ , refl , (S ,- SS') , (T ,- TT')

-- If a term does not mention some variables, then none of its reducts do
redPresThin : {n m : Nat}(th : n <= m){d : Dir}(s : Tm n d){s' t : Tm m d}
           -> s' == Th.act th s
           -> s' ~>> t
           -> Sg (Tm n d) \t' -> t == Th.act th t' * s ~>> t'
redPresThin th s p star = s , p , parRefl s
redPresThin th s p (pi q SS' TT') with thinUnderPi th s p
... | strS , strT , refl , refl , refl
  with redPresThin _ strS refl SS' | redPresThin _ strT refl TT'
... | strS' , refl , strS~>strS' | strT' , refl , strT~>strT'
  = pi q strS' strT' , refl , pi q strS~>strS' strT~>strT'
redPresThin th s p (lam tt') with thinUnderLam th s p
... | strt , refl , refl
  with redPresThin _ strt refl tt'
... | strt' , refl , strt~>strt'
 = lam strt' , refl , lam strt~>strt'
redPresThin th s p [ ee' ] with thinUnderEmb th s p
... | stre , refl , refl
  with redPresThin _ stre refl ee'
... | stre' , refl , stre~>stre'
 = [ stre' ] , refl , [ stre~>stre' ]
redPresThin th s p (var i) with thinUnderVar th s p
... | j , refl , refl = var j , refl , var j
redPresThin th s p (ff' $ ss') with thinUnderApp th s p
... | strf , strs ,  refl , refl , refl
  with redPresThin _ strf refl ff' | redPresThin _ strs refl ss'
... | strf' , refl , strf~>strf' | strs' , refl , strs~>strs'
  = strf' $ strs' , refl , strf~>strf' $ strs~>strs'
redPresThin th s p (tt' :: TT')  with thinUnderAnn th s p
... | strt , strT ,  refl , refl , refl
  with redPresThin _ strt refl tt' | redPresThin _ strT refl TT'
... | strt' , refl , strt~>strt' | strT' , refl , strT~>strT'
  = strt' :: strT' , refl , strt~>strt' :: strT~>strT'
redPresThin th s p (beta tt' SS' TT' ss') with thinUnderApp th s p
... | strltST , strs , refl , qltST , refl
 with thinUnderAnn th strltST qltST
... | strlt , strST , refl , qlt , qST
 with thinUnderLam th strlt qlt | thinUnderPi th strST qST
... | strt , refl , refl | strS , strT , refl , refl , refl
  with redPresThin _ strt refl tt' | redPresThin _ strS refl SS'
     | redPresThin _ strT refl TT' | redPresThin _ strs refl ss'
... | strt' , refl , strt~>strt' | strS' , refl , strS~>strS'
    | strT' , refl , strT~>strT' | strs' , refl , strs~>strs'
    rewrite ActCo.actCo SUBSTTHINSUBST (si -, Th.act th (strs' :: strS')) (os th) (strt' :: strT')
          | sym (thin/idQ th)
          | sym (ActCo.actCo THINSUBSTSUBST th (si -, strs' :: strS') (strt' :: strT'))
  = Sb.act (si -, (strs' :: strS')) (strt' :: strT')
  , refl
  , beta strt~>strt' strS~>strS' strT~>strT' strs~>strs'
redPresThin th s p (upsi tt') with thinUnderEmb th s p
... | strtT , refl , qtT with thinUnderAnn th strtT qtT
... | strt , strT , refl , refl , refl
  with redPresThin _ strt refl tt'
... | strt' , refl , strt~>strt'
 = strt' , refl , upsi strt~>strt'

-- A reduction between thinned terms gives rise to a reduction between the strengthened terms
thinReflectRed : {n m : Nat}(th : n <= m){d : Dir}
                 (s t : Tm n d)
              -> Th.act th s ~>> Th.act th t
              -> s ~>> t
thinReflectRed th s t s'~>t' with redPresThin th s refl s'~>t'
... | strt , prt , s~>strt rewrite thinActInj th t strt prt
  = s~>strt
