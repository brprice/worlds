module Dev {Q : Set} where

open import Basics
open import OPE
open import Dir
open import Tm {Q}
open import Env
open import Subst {Q}
open import Par {Q}
open import Star

NoRadFun : forall {n} -> Tm n syn -> Set
NoRadFun (lam _ :: pi _ _ _) = Zero
NoRadFun _ = One

NoRad : forall {n} -> Tm n syn -> Set
NoRad (_ :: _) = Zero
NoRad _ = One

data RedView {n} : forall {d} -> Tm n d -> Set where
  star : RedView star
  pi   : forall {q S T} -> RedView (pi q S T)
  lam  : forall {t} -> RedView (lam t)
  emb  : forall {e} -> NoRad e -> RedView [ e ]
  var  : forall {i} -> RedView (var i)
  app  : forall {f s} -> NoRadFun f -> RedView (f $ s)
  typ  : forall {t T} -> RedView (t :: T)
  beta : forall {t q S T s} -> RedView ((lam t :: pi q S T) $ s)
  upsi : forall {t T}     -> RedView [ t :: T ]

redView : forall {n d}(t : Tm n d) -> RedView t
redView star = star
redView (pi q S T) = pi
redView (lam t) = lam
redView [ var x ] = emb <>
redView [ e $ e₁ ] = emb <>
redView [ t :: T ] = upsi
redView (var i) = var
redView (var _ $ s) = app <>
redView ((_ $ _) $ s) = app <>
redView ((star :: T) $ s) = app <>
redView ((pi _ _ _ :: T) $ s) = app <>
redView ((lam _ :: star) $ s) = app <>
redView ((lam t :: pi q S T) $ s) = beta
redView ((lam _ :: lam _) $ s) = app <>
redView ((lam _ :: [ _ ]) $ s) = app <>
redView (([ _ ] :: T) $ s) = app <>
redView (t :: T) = typ

dev : forall {d n} -> Tm n d -> Tm n d
dev t = dev' (redView t)
  where dev' : forall {d n}{t : Tm n d} -> RedView t -> Tm n d
        dev' star = star
        dev' (pi {q}{S}{T}) = pi q (dev S) (dev T)
        dev' (lam {t}) = lam (dev t)
        dev' (emb {e} nr) = [ dev e ]
        dev' (var {i}) = var i
        dev' (app {f}{s} nr) = dev f $ dev s
        dev' (typ {t}{T}) = dev t :: dev T
        dev' (beta {t}{q}{S}{T}{s}) = Sb.act (si -, (dev s :: dev S)) (dev t :: dev T)
        dev' (upsi {t}{T}) = dev t

dev1 : forall {d n}(t : Tm n d) -> t ~>> dev t
dev1 t with redView t
dev1 ._ | star = star
dev1 ._ | pi = pi _ (dev1 _) (dev1 _)
dev1 ._ | lam = lam (dev1 _)
dev1 ._ | emb nr = [ dev1 _ ]
dev1 ._ | var = var _
dev1 ._ | app nr = dev1 _ $ dev1 _
dev1 ._ | typ = dev1 _ :: dev1 _
dev1 ._ | beta = beta (dev1 _) (dev1 _) (dev1 _) (dev1 _)
dev1 ._ | upsi = upsi (dev1 _)

dev2 : forall {d n}(t t' : Tm n d) -> t ~>> t' -> t' ~>> dev t
dev2 t t' r with redView t
dev2 .star .star star | star = star
dev2 .(pi _ _ _) .(pi _ _ _) (pi q r r') | pi = pi q (dev2 _ _ r) (dev2 _ _ r')
dev2 .(lam _) .(lam _) (lam r) | lam = lam (dev2 _ _ r)
dev2 .([ _ ]) .([ _ ]) [ r ] | emb x = [ dev2 _ _ r ]
dev2 .([ _ :: _ ]) t' (upsi r) | emb ()
dev2 .(var i) .(var i) (var i) | var = var i
dev2 .(_ $ _) .(_ $ _) (r $ r') | app x = dev2 _ _ r $ dev2 _ _ r'
dev2 .((lam _ :: pi _ _ _) $ _) ._ (beta _ _ _ _ ) | app ()
dev2 .(_ :: _) .(_ :: _) (r :: r') | typ = dev2 _ _ r :: dev2 _ _ r'
dev2 .((lam _ :: pi _ _ _) $ _) .((lam _ :: pi _ _ _) $ _) ((lam rt :: pi q rS rT) $ rs) | beta
  = beta (dev2 _ _ rt) (dev2 _ _ rS) (dev2 _ _ rT) (dev2 _ _ rs)
dev2 .((lam _ :: pi _ _ _) $ _) ._ (beta rt rS rT rs) | beta
  = parStab (parzRefl si , (dev2 _ _ rs :: dev2 _ _ rS)) (dev2 _ _ rt :: dev2 _ _ rT)
dev2 .([ _ :: _ ]) .([ _ :: _ ]) [ r :: r' ] | upsi = upsi (dev2 _ _ r)
dev2 .([ _ :: _ ]) t' (upsi r) | upsi = dev2 _ _ r

confluence : forall {d n} -> Diamond {Tm n d} _~>>*_
confluence = diamondLemma (\ {t} r s -> dev t , dev2 t _ r , dev2 t _ s)

consensus : forall {d n}(s : Tm n d)
            (ts : List (Tm n d)) -> All (s ~>>*_) ts ->
            Sg (Tm n d) \ u -> (s ~>>* u) * All (_~>>* u) ts
consensus s [] <> = s , [] , <>
consensus s (t ,- ts) (st , sts) with consensus s ts sts
... | v , sv , tvs with confluence st sv
... | w , tw , vw = w , (sv ++ vw) , tw , all (_++ vw) tvs
