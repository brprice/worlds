module WorldSystemExamples where

open import Basics hiding (the)
open import Star
open import WorldSystem

module OneWorld where
  oneWorld : WorldSystem
  oneWorld = record
               { W = One
               ; _<<_ = \_ _ -> One
               ; tyW = \_ -> One
               ; Q = \_ -> One
               ; st = <>
               ; _#_ = \_ w -> Just w --\_ _ -> Just <>
               ; _&_ = \_ _ -> <>
               ; star& = \_ -> <>
               ; unst = \w -> Just w
               ; _&unst&_ = \_ _ -> Real , <>
               ; <<refl = <>
               ; <<trans = \_ _ -> <>
               ; st-def = \w -> w , refl --\_ -> <> , refl
               ; st-unst = \{refl -> refl}
               ; defUpset = \{_}{_}{_}{_}{w} _ _ -> w , refl
               ; op = \_ _ -> <>
               ; dominateUpset = \_ _ _ _ _ _ -> <>
               ; stTyW = \_ -> <>
               ; tyWUpset = \_ _ -> <>
               ; st&-action = \_ _ -> refl
               ; &unst&-action = \{ _ (inl _) _ -> refl ; _ (inr _) _ -> refl}
               ; isActionL = \{_}{_}{w} p -> w , refl , p
               ; isActionR = \{refl refl -> refl}
               ; stq = \{ refl refl refl refl -> refl}
               ; GwqConn = \{ _ _ refl refl refl refl -> inl <> ,- []}
               }


module actByReplacement (W' : Set)(pt : W')
                        (_<_ : W' -> W' -> Set)
                        (<refl : forall {x} -> x < x)
                        (<trans : forall {x y z} -> x < y -> y < z -> x < z) where
  -- some poset of worlds, we add star at the top, Q=W+{unstar}+{q&unstar | q <- Q}
  -- unstar acts by picking some arbitrary (given) point from W
  data Top (A : Set) : Set where
    top : Top A
    the : A -> Top A
  W = Top W'

  data _<<_ : W -> W -> Set where
    <<top : forall u -> u << top
    th<<th : forall {u v} -> u < v -> the u << the v

  data Q : Sort -> Set where
    undef : Q Real
    const : W -> Q Real
    topTo : W -> Q Real

  -- undef or topTo _
  topTo? : Maybe W -> Q Real
  topTo? (Just w) = topTo w
  topTo? Nothing = undef

  -- undef or const _
  const? : Maybe W -> Q Real
  const? (Just w) = const w
  const? Nothing = undef

  _#_ : {s : Sort} -> Q s -> W -> Maybe W
  undef # _ = Nothing
  const x # w = Just x
  topTo x # top = Just x
  topTo x # the w = Nothing
  infix 40 _#_

  _&_ : Q Real -> Q Real -> Q Real
  q & undef = undef
  q & const x = const? (q # x)
  q & topTo x = topTo? (q # x)
  infix 50 _&_

  star& : Q Fake -> Q Real
  star& ()

  unst : W -> Maybe W
  unst top = Just (the pt)
  unst (the x) = Nothing

  _&unst&'_ : Q Real -> One + Q Real -> Q Real
  q &unst&' inr undef = undef
  q &unst&' inr (const top) = const? (q # the pt)
  q &unst&' inr (const (the x)) = undef
  q &unst&' inr (topTo top) = topTo? (q # the pt)
  q &unst&' inr (topTo (the x)) = undef
  q &unst&' inl <> = topTo? (q # the pt)

  _&unst&_ : Q Real -> One + Q Real -> Sg Sort Q
  q &unst& r = Real , q &unst&' r

  <<refl : {w : W} -> w << w
  <<refl {top} = <<top top
  <<refl {the x} = th<<th <refl

  <<trans : {u v w : W} -> u << v -> v << w -> u << w
  <<trans u<v (<<top v) = <<top _
  <<trans (th<<th u<v) (th<<th v<w) = th<<th (<trans u<v v<w)

  st-unst : forall {w usw} -> unst w ~ usw -> top == w
  st-unst {top} p = refl
  st-unst {the x} ()

  def-upset : forall {s}(q : Q s){v qv w} -> q # v ~ qv -> v << w -> Sg W (\qw -> q # w ~ qw)
  def-upset undef () v<w
  def-upset (const x) qv v<w = x , refl
  def-upset (topTo x) {top} refl (<<top .top) = x , refl
  def-upset (topTo x) {the y} () v<w

  op : forall {s}(q : Q s){v qv' w} -> (qv : q # v ~ qv') -> (v<w : v << w) -> qv' << fst (def-upset q qv v<w)
  op undef () v<w
  op (const x) refl v<w = <<refl
  op (topTo x) {top} refl (<<top .top) = <<refl
  op (topTo x) {the x₁} () v<w

  -- lift things to One + Q _
  -- TODO: is there a way to get these from the record we are in the process of defining?
  _#?_ : forall {s} -> One + Q s -> W -> Maybe W
  _#?_ {s} = either (\_ -> Just) _#_
  infix 40 _#?_

  def-upset? : forall {s}(q : One + Q s){v qv w} -> q #? v ~ qv -> v << w -> Sg W (q #? w ~_)
  def-upset? {s} = either {C = \q -> forall {v qv w} -> q #? v ~ qv -> v << w -> Sg W (q #? w ~_)}
                          (\_ {_}{_}{w} _ _ -> w , refl) (\q qv v<w -> def-upset q qv v<w)

  op? : forall {s}(q : One + Q s){v qv' w} -> (qv : q #? v ~ qv') -> (v<w : v << w)
     -> qv' << fst (def-upset? q qv v<w)
  op? = either {C = \q -> forall {v qv' w} -> (qv : q #? v ~ qv') -> (v<w : v << w)
                    -> qv' << fst (def-upset? q qv v<w)}
               (\{_ refl v<w -> v<w}) (\q qv v<w -> op q qv v<w)

  dominateUpset : forall {s}(q : Q s)(r : One + Q Real){v qv' rv' w}
               -> (qv : q # v ~ qv')(rv : r #? v ~ rv')
               -> qv' << rv' -> (v<w : v << w)
               -> fst (def-upset q qv v<w) << fst (def-upset? r rv v<w)
  dominateUpset undef r () rv qv<rv v<w
  dominateUpset (const x) r refl rv qv<rv v<w = <<trans qv<rv (op? r rv v<w)
  dominateUpset (topTo x) r {top} refl rv qv<rv (<<top .top) = <<trans qv<rv (op? r rv (<<top top))
  dominateUpset (topTo x) r {the _} () rv qv<rv v<w

  &unst&-action : forall q r w
               -> snd (q &unst& r) # w == ((q #_) =<< (unst =<< (r #? w)))
  &unst&-action q (inr undef) w = refl
  &unst&-action undef (inr (const top)) w = refl
  &unst&-action (const x) (inr (const top)) w = refl
  &unst&-action (topTo x) (inr (const top)) top = refl
  &unst&-action (topTo x) (inr (const top)) (the w) = refl
  &unst&-action q (inr (const (the x))) w = refl
  &unst&-action undef (inr (topTo top)) top = refl
  &unst&-action (const x) (inr (topTo top)) top = refl
  &unst&-action (topTo x) (inr (topTo top)) top = refl
  &unst&-action q (inr (topTo (the x))) top = refl
  &unst&-action undef (inr (topTo top)) (the w) = refl
  &unst&-action (const x) (inr (topTo top)) (the w) = refl
  &unst&-action (topTo x) (inr (topTo top)) (the w) = refl
  &unst&-action q (inr (topTo (the x))) (the w) = refl
  &unst&-action undef (inl <>) top = refl
  &unst&-action undef (inl <>) (the w) = refl
  &unst&-action (const x) (inl <>) top = refl
  &unst&-action (const x) (inl <>) (the w) = refl
  &unst&-action (topTo x) (inl <>) top = refl
  &unst&-action (topTo x) (inl <>) (the w) = refl


  isActionL : forall q r {w qrw'} -> q & r # w ~ qrw'
           -> Sg W (\rw' -> (r # w ~ rw') * (q # rw') ~ qrw')
  isActionL q undef ()
  isActionL undef (const y) ()
  isActionL (const x) (const y) qrw = y , refl , qrw
  isActionL (topTo x) (const top) qrw = top , refl , qrw
  isActionL (topTo x) (const (the y)) ()
  isActionL undef (topTo y) ()
  isActionL (const x) (topTo y) {top} refl = y , refl , refl
  isActionL (const x) (topTo y) {the _} ()
  isActionL (topTo x) (topTo top) {top} refl = top , refl , refl
  isActionL (topTo x) (topTo top) {the _} ()
  isActionL (topTo x) (topTo (the y)) ()

  isActionR : forall q r {w rw' qrw'}
           -> r # w ~ rw'
           -> q # rw' ~ qrw'
           -> q & r # w ~ qrw'
  isActionR q undef () qrw
  isActionR undef (const y) rw ()
  isActionR (const x) (const y) rw qrw = qrw
  isActionR (topTo x) (const top) refl qrw = qrw
  isActionR (topTo x) (const (the y)) refl ()
  isActionR undef (topTo y) rw ()
  isActionR (const x) (topTo y) {top} refl qrw = qrw
  isActionR (const x) (topTo y) {the x₁} () qrw
  isActionR (topTo x) (topTo y) {the x₁} () qrw
  isActionR (topTo x) (topTo top) {top} refl qrw = qrw
  isActionR (topTo x) (topTo (the y)) {top} refl ()

  GwqConn : forall (q : Q Real) (w : W) {u qu'} su=w qu {v qv'} sv=w qv
         -> Star {Sg W (\u -> top == w * Sg W \qu -> q # u ~ qu)}
                 (\{(u , _ , qu' , _) (v , _ , qv' , _) -> (u << v) + (qv' << qu')})
                 (u , su=w , qu' , qu) (v , sv=w , qv' , qv)
  GwqConn undef .top refl () refl ()
  GwqConn (const x) .top refl refl refl refl = inr <<refl ,- []
  GwqConn (topTo x) .top {top} refl refl {top} refl refl = []
  GwqConn (topTo x) .top {top} refl refl {the _} refl ()
  GwqConn (topTo x) .top {the _} refl () refl qv

  replacement : WorldSystem
  replacement = record
                  { W = W
                  ; _<<_ = _<<_
                  ; tyW = top ==_
                  ; Q = Q
                  ; st = const top
                  ; _#_ = _#_
                  ; _&_ = _&_
                  ; star& = star&
                  ; unst = unst
                  ; _&unst&_ = _&unst&_
                  ; <<refl = <<refl
                  ; <<trans = <<trans
                  ; st-def = \w -> top , refl
                  ; st-unst = st-unst
                  ; defUpset = \{_}{q} -> def-upset q
                  ; op = \{_}{q} -> op q
                  ; dominateUpset = dominateUpset
                  ; stTyW = \ _ -> refl
                  ; tyWUpset = \{ (<<top u) q → refl ; (th<<th x) ()}
                  ; st&-action = \()
                  ; &unst&-action = &unst&-action
                  ; isActionL = \{q}{r} -> isActionL q r
                  ; isActionR = \{q}{r} -> isActionR q r
                  ; stq = \_ _ _ _ -> refl
                  ; GwqConn = GwqConn
                  }


module twoWorlds where
  -- Heaven above earth
  data W : Set where H E : W

  data _<<_ : W -> W -> Set where
    E<E : E << E
    H<H : H << H
    E<H : E << H

  data Q : Sort -> Set where
  -- C stands for "current"
  -- H: constantly returns H
  -- HH: H->H, undefined on E
    C H HH undef : Q Real
  -- HE: H->E, undefined on E
  -- E: constantly returns E
    HE E : Q Fake

  _#_ : forall {s} -> Q s -> W -> Maybe W
  C # w = Just w
  H # w = Just H
  E # w = Just E
  HE # H = Just E
  HE # E = Nothing
  HH # H = Just H
  HH # E = Nothing
  undef # w = Nothing
  infix 40 _#_

  _&_ : Q Real -> Q Real -> Q Real
  q & C = q
  q & undef = undef
  C & q = q
  undef & q = undef
  H & H = H
  HH & H = H
  H & HH = HH
  HH & HH = HH
  infix 50 _&_

  star& : Q Fake -> Q Real
  star& HE = HH
  star& E = H

  unst : W -> Maybe W
  unst H = Just E
  unst E = Nothing

  _&unst&'_ : Q Real -> Q Real -> Sg Sort Q
  q &unst&' undef = Real , undef
  HH &unst&' r = Real , undef
  undef &unst&' r = Real , undef
  C &unst&' C = Fake , HE
  C &unst&' H = Fake , E
  C &unst&' HH = Fake , HE
  H &unst&' C = Real , HH
  H &unst&' H = Real , H
  H &unst&' HH = Real , HH

  _&unst&_ : Q Real -> One + Q Real -> Sg Sort Q
  q &unst& inl <> = q &unst&' C
  q &unst& inr r = q &unst&' r

  <<refl : {w : W} -> w << w
  <<refl {H} = H<H
  <<refl {E} = E<E

  <<trans : {u v w : W} → u << v → v << w → u << w
  <<trans {_} {H} u<v H<H = u<v
  <<trans {_} {E} E<E v<w = v<w

  st-unst : forall {w usw} -> unst w ~ usw -> H == w
  st-unst {H} _ = refl
  st-unst {E} ()

  def-upset : forall {s}(q : Q s){v qv' w} -> q # v == Just qv' -> v << w -> Sg W (\qw -> q # w == Just qw)
  def-upset q qv E<E = _ , qv
  def-upset q qv H<H = _ , qv
  def-upset C qv E<H = H , refl
  def-upset H qv E<H = H , refl
  def-upset E qv E<H = E , refl
  def-upset HE qv E<H = E , refl
  def-upset HH qv E<H = H , refl
  def-upset undef () E<H

  op : forall {s}(q : Q s){v qv' w} -> (qv : q # v == Just qv') -> (v<w : v << w) -> qv' << fst (def-upset q qv v<w)
  op q qv E<E = <<refl
  op q qv H<H = <<refl
  op C refl E<H = E<H
  op H refl E<H = H<H
  op HH () E<H
  op undef () E<H
  op HE () E<H
  op E refl E<H = E<E

  _#?_ : forall {s} -> One + Q s -> W -> Maybe W
  _#?_ {s} = either (\_ -> Just) _#_
  infix 40 _#?_

  def-upset? : forall {s}(q : One + Q s){v qv w} -> q #? v ~ qv -> v << w -> Sg W (q #? w ~_)
  def-upset? {s} = either {C = \q -> forall {v qv w} -> q #? v ~ qv -> v << w -> Sg W (q #? w ~_)}
                          (\_ {_}{_}{w} _ _ -> w , refl) (\q qv v<w -> def-upset q qv v<w)

  op? : forall {s}(q : One + Q s){v qv' w} -> (qv : q #? v ~ qv') -> (v<w : v << w)
     -> qv' << fst (def-upset? q qv v<w)
  op? = either {C = \q -> forall {v qv' w} -> (qv : q #? v ~ qv') -> (v<w : v << w)
                    -> qv' << fst (def-upset? q qv v<w)}
               (\{_ refl v<w -> v<w}) (\q qv v<w -> op q qv v<w)


  dominateUpset : forall {s}(q : Q s)(r : One + Q Real){v qv' rv' w}
               -> (qv : q # v ~ qv')(rv : r #? v ~ rv')
               -> qv' << rv' -> (v<w : v << w)
               -> fst (def-upset q qv v<w) << fst (def-upset? r rv v<w)
  dominateUpset q (inl <>) qv refl qv<rv E<E = qv<rv
  dominateUpset q (inl <>) qv refl qv<rv H<H = qv<rv
  dominateUpset C (inl <>) refl refl qv<rv E<H = H<H
  dominateUpset H (inl <>) refl refl qv<rv E<H = H<H
  dominateUpset HH (inl <>) () refl qv<rv E<H
  dominateUpset undef (inl <>) () refl qv<rv E<H
  dominateUpset HE (inl <>) () refl qv<rv E<H
  dominateUpset E (inl <>) refl refl qv<rv E<H = E<H
  dominateUpset q (inr r) qv rv qv<rv E<E = qv<rv
  dominateUpset q (inr r) qv rv qv<rv H<H = qv<rv
  dominateUpset C (inr C) refl refl qv<rv E<H = H<H
  dominateUpset C (inr H) refl refl qv<rv E<H = H<H
  dominateUpset C (inr HH) refl () qv<rv E<H
  dominateUpset C (inr undef) refl () qv<rv E<H
  dominateUpset H (inr C) refl refl qv<rv E<H = H<H
  dominateUpset H (inr H) refl refl qv<rv E<H = qv<rv
  dominateUpset H (inr HH) refl () qv<rv E<H
  dominateUpset H (inr undef) refl () qv<rv E<H
  dominateUpset HH (inr r) () rv qv<rv E<H
  dominateUpset undef (inr r) () rv qv<rv E<H
  dominateUpset HE (inr r) () rv qv<rv E<H
  dominateUpset E (inr C) refl refl qv<rv E<H = E<H
  dominateUpset E (inr H) refl refl qv<rv E<H = qv<rv
  dominateUpset E (inr HH) refl () qv<rv E<H
  dominateUpset E (inr undef) refl () qv<rv E<H

  st&-action : forall q w
            -> star& q # w == ((H #_) =<< q # w)
  st&-action HE H = refl
  st&-action HE E = refl
  st&-action E w = refl

  &unst&-action : forall q r w
               -> snd (q &unst& r) # w == ((q #_) =<< (unst =<< (r #? w)))
  &unst&-action C (inl <>) H = refl
  &unst&-action C (inl <>) E = refl
  &unst&-action H (inl <>) H = refl
  &unst&-action H (inl <>) E = refl
  &unst&-action HH (inl <>) H = refl
  &unst&-action HH (inl <>) E = refl
  &unst&-action undef (inl <>) H = refl
  &unst&-action undef (inl <>) E = refl
  &unst&-action C (inr C) H = refl
  &unst&-action C (inr C) E = refl
  &unst&-action H (inr C) H = refl
  &unst&-action H (inr C) E = refl
  &unst&-action HH (inr C) H = refl
  &unst&-action HH (inr C) E = refl
  &unst&-action undef (inr C) H = refl
  &unst&-action undef (inr C) E = refl
  &unst&-action C (inr H) w = refl
  &unst&-action H (inr H) w = refl
  &unst&-action HH (inr H) w = refl
  &unst&-action undef (inr H) w = refl
  &unst&-action C (inr HH) H = refl
  &unst&-action C (inr HH) E = refl
  &unst&-action H (inr HH) H = refl
  &unst&-action H (inr HH) E = refl
  &unst&-action HH (inr HH) H = refl
  &unst&-action HH (inr HH) E = refl
  &unst&-action undef (inr HH) H = refl
  &unst&-action undef (inr HH) E = refl
  &unst&-action q (inr undef) w = refl

  isActionL : forall q r {w qrw'} -> q & r # w ~ qrw'
           -> Sg W (\rw' -> (r # w ~ rw') * (q # rw') ~ qrw')
  isActionL q C qrw = _ , refl , qrw
  isActionL C H qrw = _ , qrw , refl
  isActionL H H qrw = H , refl , qrw
  isActionL HH H qrw = H , refl , qrw
  isActionL undef H ()
  isActionL C HH qrw = _ , qrw , refl
  isActionL H HH {H} refl = H , refl , refl
  isActionL H HH {E} ()
  isActionL HH HH {H} qrw = H , refl , qrw
  isActionL HH HH {E} ()
  isActionL undef HH ()
  isActionL q undef ()

  isActionR : forall q r {w rw' qrw'}
           -> r # w ~ rw'
           -> q # rw' ~ qrw'
           -> q & r # w ~ qrw'
  isActionR q C refl qrw = qrw
  isActionR C H refl qrw = qrw
  isActionR H H refl qrw = qrw
  isActionR HH H refl qrw = qrw
  isActionR undef H refl ()
  isActionR C HH rw refl = rw
  isActionR H HH {H} refl refl = refl
  isActionR H HH {E} () refl
  isActionR HH HH {H} refl qrw = qrw
  isActionR HH HH {E} () qrw
  isActionR undef HH rw ()
  isActionR q undef () qrw

  owoto : forall {u v} -> (u << v) + (v << u)
  owoto {H} {H} = inl H<H
  owoto {H} {E} = inr E<H
  owoto {E} {H} = inl E<H
  owoto {E} {E} = inl E<E

  GwqConn : forall {s}(q : Q s)(w : W) {u qu'} su=w qu {v qv'} sv=w qv
         -> Star {Sg W (\u -> H == w * Sg W \qu -> q # u ~ qu)}
                 (\{(u , _ , qu' , _) (v , _ , qv' , _) -> (u << v) + (qv' << qu')})
                 (u , su=w , qu' , qu) (v , sv=w , qv' , qv)
  GwqConn C .H refl refl refl refl = owoto ,- []
  GwqConn H .H refl refl refl refl = inr H<H ,- []
  GwqConn HH .H {H} refl refl {H} refl refl = inl H<H ,- []
  GwqConn HH .H {H} refl refl {E} refl ()
  GwqConn HH .H {E} refl () refl qv
  GwqConn undef .H refl () refl ()
  GwqConn HE .H {H} refl refl {H} refl refl = inl H<H ,- []
  GwqConn HE .H {H} refl refl {E} refl ()
  GwqConn HE .H {E} refl () refl qv
  GwqConn E .H refl refl refl refl = inr E<E ,- []

  twoWorlds : WorldSystem
  twoWorlds = record
                { W = W
                ; _<<_ = _<<_
                ; tyW = H ==_
                ; Q = Q
                ; st = H
                ; _#_ = _#_
                ; _&_ = _&_
                ; star& = star&
                ; unst = unst
                ; _&unst&_ = _&unst&_
                ; <<refl = <<refl
                ; <<trans = <<trans
                ; st-def = \w -> H , refl
                ; st-unst = st-unst
                ; defUpset = \{_}{q} -> def-upset q
                ; op = \{_}{q} -> op q
                ; dominateUpset = dominateUpset
                ; stTyW = \_ -> refl
                ; tyWUpset = \{ H<H refl -> refl}
                ; st&-action = st&-action
                ; &unst&-action = &unst&-action
                ; isActionL = \{q}{r} -> isActionL q r
                ; isActionR = \{q}{r} -> isActionR q r
                ; stq = \_ _ _ _ -> refl
                ; GwqConn = GwqConn
                }


-- TODO: Compare this to actual system F
-- My first attempt was wrong: had type operators!
module SystemF where
  data W : Set where
    tm ty box : W

  _<<_ : W -> W -> Set
  _<<_ = _==_

  tyW : W -> Set
  tyW tm = Zero
  tyW ty = One
  tyW box = One

-- Question: do we want to have a quant . which
-- a) takes tm -> tm, undefined else (currently have this - forces having tmTo : W -> Q Real,
--  and then tyTo ty , tyTo box : Q Real)
-- b) acts as the identity (can probably remove tmTo ty and tmTo box)
--
-- Turns out still need tmTo st and tmTo box in case (b)
-- because id &unst& st = tmTo tm : Q Fake
-- and st& tmTo tm = tmTo ty : Q Real
-- thus st & tmTo ty = tmTo box
--
-- So we wouldn't actually gain much in plan (b)
  data Q : Sort -> Set where
    tmTo : W -> Q Real
    tyTo : W -> Q Real
    st box : Q Real
    undef : Q Real


  _#_ : forall {s} -> Q s -> W -> Maybe W
  tmTo w # tm = Just w
  tmTo w # _ = Nothing
  st # tm = Just ty
  st # ty = Just box
  st # box = Just box
  box # w = Just box
  undef # w = Nothing
  tyTo w # ty = Just w
  tyTo w # _ = Nothing
  infix 40 _#_

  st-def : forall w -> Sg W (st # w ~_)
  st-def tm = ty , refl
  st-def ty = box , refl
  st-def box = box , refl

  st-act : W -> W
  st-act w = fst (st-def w)

  _&_ : Q Real -> Q Real -> Q Real
  tmTo v & tmTo tm = tmTo v
  tmTo v & tyTo tm = tyTo v
  tmTo v & _ = undef
  tyTo v & tmTo ty = tmTo v
  tyTo v & tyTo ty = tyTo v
  tyTo v & st = tmTo v
  tyTo v & _ = undef
  st & tmTo w = tmTo (st-act w)
  st & tyTo w = tyTo (st-act w)
  st & st = box
  st & box = box
  box & tmTo w = tmTo box
  box & tyTo w = tyTo box
  box & st = box
  box & box = box
  _ & undef = undef
  undef & _ = undef
  infix 50 _&_

  unst : W -> Maybe W
  unst ty = Just tm
  unst _ = Nothing

  _&unst&_ : Q Real -> One + Q Real -> Sg Sort Q
  q &unst& inl <> with q # tm
  ... | Just w = _ , tyTo w
  ... | Nothing = _ , undef
  q &unst& inr (tmTo ty) = _ , q & tmTo tm
  q &unst& inr (tmTo _) = _ , undef
  q &unst& inr (tyTo ty) = _ , q & tyTo tm
  q &unst& inr (tyTo _) = _ , undef
  q &unst& inr st = _ , q & tmTo tm
  q &unst& inr box = _ , undef
  q &unst& inr undef = _ , undef

  <<trans : forall {u v w} -> u << v -> v << w -> u << w
  <<trans refl refl = refl

  st-unst : forall {w usw} -> unst w ~ usw -> st-act usw == w
  st-unst {tm} ()
  st-unst {ty} refl = refl
  st-unst {box} ()

  def-upset : forall {s}(q : Q s){v qv w} -> q # v ~ qv -> v << w -> Sg W (\qw -> q # w ~ qw)
  def-upset q qv refl = _ , qv

  op : forall {s}(q : Q s){v qv' w} -> (qv : q # v ~ qv') -> (v<w : v << w) -> qv' << fst (def-upset q qv v<w)
  op q qv refl = refl

  _#?_ : forall {s} -> One + Q s -> W -> Maybe W
  _#?_ {s} = either (\_ -> Just) _#_
  infix 40 _#?_

  def-upset? : forall {s}(q : One + Q s){v qv w} -> q #? v ~ qv -> v << w -> Sg W (q #? w ~_)
  def-upset? {s} = either {C = \q -> forall {v qv w} -> q #? v ~ qv -> v << w -> Sg W (q #? w ~_)}
                          (\_ {_}{_}{w} _ _ -> w , refl) def-upset

  dominateUpset : forall {s}(q : Q s)(r : One + Q Real){v qv' rv' w}
               -> (qv : q # v ~ qv')(rv : r #? v ~ rv')
               -> qv' << rv' -> (v<w : v << w)
               -> fst (def-upset q qv v<w) << fst (def-upset? r rv v<w)
  dominateUpset _ (inl <>) qv refl refl refl = refl
  dominateUpset q (inr r) qv rv refl refl = refl

  stTyW : forall w -> tyW (st-act w)
  stTyW tm = <>
  stTyW ty = <>
  stTyW box = <>

  &unst&-action : forall q r w
               -> snd (q &unst& r) # w == ((q #_) =<< (unst =<< (r #? w)))
  &unst&-action q (inl <>) tm with q # tm
  &unst&-action q (inl <>) tm | Just x = refl
  &unst&-action q (inl <>) tm | Nothing = refl
  &unst&-action q (inl <>) ty with q # tm
  &unst&-action q (inl <>) ty | Just x = refl
  &unst&-action q (inl <>) ty | Nothing = refl
  &unst&-action q (inl <>) box with q # tm
  &unst&-action q (inl <>) box | Just x = refl
  &unst&-action q (inl <>) box | Nothing = refl
  &unst&-action q (inr (tmTo tm)) tm = refl
  &unst&-action q (inr (tmTo tm)) ty = refl
  &unst&-action q (inr (tmTo tm)) box = refl
  &unst&-action (tmTo x) (inr (tmTo ty)) tm = refl
  &unst&-action (tmTo x) (inr (tmTo ty)) ty = refl
  &unst&-action (tmTo x) (inr (tmTo ty)) box = refl
  &unst&-action (tyTo x) (inr (tmTo ty)) tm = refl
  &unst&-action (tyTo x) (inr (tmTo ty)) ty = refl
  &unst&-action (tyTo x) (inr (tmTo ty)) box = refl
  &unst&-action st (inr (tmTo ty)) tm = refl
  &unst&-action st (inr (tmTo ty)) ty = refl
  &unst&-action st (inr (tmTo ty)) box = refl
  &unst&-action box (inr (tmTo ty)) tm = refl
  &unst&-action box (inr (tmTo ty)) ty = refl
  &unst&-action box (inr (tmTo ty)) box = refl
  &unst&-action undef (inr (tmTo ty)) tm = refl
  &unst&-action undef (inr (tmTo ty)) ty = refl
  &unst&-action undef (inr (tmTo ty)) box = refl
  &unst&-action q (inr (tmTo box)) tm = refl
  &unst&-action q (inr (tmTo box)) ty = refl
  &unst&-action q (inr (tmTo box)) box = refl
  &unst&-action q (inr (tyTo tm)) tm = refl
  &unst&-action q (inr (tyTo tm)) ty = refl
  &unst&-action q (inr (tyTo tm)) box = refl
  &unst&-action (tmTo x) (inr (tyTo ty)) tm = refl
  &unst&-action (tmTo x) (inr (tyTo ty)) ty = refl
  &unst&-action (tmTo x) (inr (tyTo ty)) box = refl
  &unst&-action (tyTo x) (inr (tyTo ty)) tm = refl
  &unst&-action (tyTo x) (inr (tyTo ty)) ty = refl
  &unst&-action (tyTo x) (inr (tyTo ty)) box = refl
  &unst&-action st (inr (tyTo ty)) tm = refl
  &unst&-action st (inr (tyTo ty)) ty = refl
  &unst&-action st (inr (tyTo ty)) box = refl
  &unst&-action box (inr (tyTo ty)) tm = refl
  &unst&-action box (inr (tyTo ty)) ty = refl
  &unst&-action box (inr (tyTo ty)) box = refl
  &unst&-action undef (inr (tyTo ty)) tm = refl
  &unst&-action undef (inr (tyTo ty)) ty = refl
  &unst&-action undef (inr (tyTo ty)) box = refl
  &unst&-action q (inr (tyTo box)) tm = refl
  &unst&-action q (inr (tyTo box)) ty = refl
  &unst&-action q (inr (tyTo box)) box = refl
  &unst&-action (tmTo x) (inr st) tm = refl
  &unst&-action (tmTo x) (inr st) ty = refl
  &unst&-action (tmTo x) (inr st) box = refl
  &unst&-action (tyTo x) (inr st) tm = refl
  &unst&-action (tyTo x) (inr st) ty = refl
  &unst&-action (tyTo x) (inr st) box = refl
  &unst&-action st (inr st) tm = refl
  &unst&-action st (inr st) ty = refl
  &unst&-action st (inr st) box = refl
  &unst&-action box (inr st) tm = refl
  &unst&-action box (inr st) ty = refl
  &unst&-action box (inr st) box = refl
  &unst&-action undef (inr st) tm = refl
  &unst&-action undef (inr st) ty = refl
  &unst&-action undef (inr st) box = refl
  &unst&-action q (inr box) w = refl
  &unst&-action q (inr undef) w = refl

  isActionL : forall q r {w qrw'} -> q & r # w ~ qrw'
           -> Sg W (\rw' -> (r # w ~ rw') * (q # rw') ~ qrw')
  isActionL (tmTo x) (tmTo tm) {tm} refl = tm , refl , refl
  isActionL (tmTo x) (tmTo tm) {ty} ()
  isActionL (tmTo x) (tmTo tm) {box} ()
  isActionL (tmTo x) (tmTo ty) ()
  isActionL (tmTo x) (tmTo box) ()
  isActionL (tyTo x) (tmTo tm) ()
  isActionL (tyTo x) (tmTo ty) {tm} refl = ty , refl , refl
  isActionL (tyTo x) (tmTo ty) {ty} ()
  isActionL (tyTo x) (tmTo ty) {box} ()
  isActionL (tyTo x) (tmTo box) ()
  isActionL st (tmTo y) {tm} refl = y , refl , snd (st-def y)
  isActionL st (tmTo y) {ty} ()
  isActionL st (tmTo y) {box} ()
  isActionL box (tmTo y) {tm} refl = y , refl , refl
  isActionL box (tmTo y) {ty} ()
  isActionL box (tmTo y) {box} ()
  isActionL undef (tmTo y) ()
  isActionL (tmTo x) (tyTo tm) {tm} ()
  isActionL (tmTo x) (tyTo tm) {ty} refl = tm , refl , refl
  isActionL (tmTo x) (tyTo tm) {box} ()
  isActionL (tmTo x) (tyTo ty) ()
  isActionL (tmTo x) (tyTo box) ()
  isActionL (tyTo x) (tyTo tm) ()
  isActionL (tyTo x) (tyTo ty) {tm} ()
  isActionL (tyTo x) (tyTo ty) {ty} refl = ty , refl , refl
  isActionL (tyTo x) (tyTo ty) {box} ()
  isActionL (tyTo x) (tyTo box) ()
  isActionL st (tyTo y) {tm} ()
  isActionL st (tyTo y) {ty} refl = y , refl , snd (st-def y)
  isActionL st (tyTo y) {box} ()
  isActionL box (tyTo y) {tm} ()
  isActionL box (tyTo y) {ty} refl = y , refl , refl
  isActionL box (tyTo y) {box} ()
  isActionL undef (tyTo y) ()
  isActionL (tmTo x) st ()
  isActionL (tyTo x) st {tm} refl = ty , refl , refl
  isActionL (tyTo x) st {ty} ()
  isActionL (tyTo x) st {box} ()
  isActionL st st {tm} refl = ty , refl , refl
  isActionL st st {ty} refl = box , refl , refl
  isActionL st st {box} refl = box , refl , refl
  isActionL box st {w} refl = st-act w , snd (st-def w) , refl
  isActionL undef st ()
  isActionL (tmTo x) box ()
  isActionL (tyTo x) box ()
  isActionL st box refl = box , refl , refl
  isActionL box box refl = box , refl , refl
  isActionL undef box ()
  isActionL (tmTo x) undef ()
  isActionL (tyTo x) undef ()
  isActionL st undef ()
  isActionL box undef ()
  isActionL undef undef ()

  isActionR : forall q r {w rw' qrw'}
           -> r # w ~ rw'
           -> q # rw' ~ qrw'
           -> q & r # w ~ qrw'
  isActionR (tmTo x) (tmTo tm) {tm} refl refl = refl
  isActionR (tmTo x) (tmTo ty) {tm} refl ()
  isActionR (tmTo x) (tmTo box) {tm} refl ()
  isActionR (tyTo x) (tmTo tm) {tm} refl ()
  isActionR (tyTo x) (tmTo ty) {tm} refl refl = refl
  isActionR (tyTo x) (tmTo box) {tm} refl ()
  isActionR st (tmTo tm) {tm} refl refl = refl
  isActionR st (tmTo ty) {tm} refl refl = refl
  isActionR st (tmTo box) {tm} refl refl = refl
  isActionR box (tmTo tm) {tm} refl refl = refl
  isActionR box (tmTo ty) {tm} refl refl = refl
  isActionR box (tmTo box) {tm} refl refl = refl
  isActionR undef (tmTo tm) {tm} refl ()
  isActionR undef (tmTo ty) {tm} refl ()
  isActionR undef (tmTo box) {tm} refl ()
  isActionR q (tmTo x) {ty} () q-rw
  isActionR q (tmTo x) {box} () q-rw
  isActionR q (tyTo x) {tm} () q-rw
  isActionR (tmTo x) (tyTo tm) {ty} refl refl = refl
  isActionR (tmTo x) (tyTo ty) {ty} refl ()
  isActionR (tmTo x) (tyTo box) {ty} refl ()
  isActionR (tyTo x) (tyTo tm) {ty} refl ()
  isActionR (tyTo x) (tyTo ty) {ty} refl refl = refl
  isActionR (tyTo x) (tyTo box) {ty} refl ()
  isActionR st (tyTo tm) {ty} refl refl = refl
  isActionR st (tyTo ty) {ty} refl refl = refl
  isActionR st (tyTo box) {ty} refl refl = refl
  isActionR box (tyTo tm) {ty} refl refl = refl
  isActionR box (tyTo ty) {ty} refl refl = refl
  isActionR box (tyTo box) {ty} refl refl = refl
  isActionR undef (tyTo tm) {ty} refl ()
  isActionR undef (tyTo ty) {ty} refl ()
  isActionR undef (tyTo box) {ty} refl ()
  isActionR q (tyTo x) {box} () q-rw
  isActionR (tmTo x) st {tm} refl ()
  isActionR (tyTo x) st {tm} refl refl = refl
  isActionR st st {tm} refl refl = refl
  isActionR box st {tm} refl refl = refl
  isActionR undef st {tm} refl ()
  isActionR (tmTo x) st {ty} refl ()
  isActionR (tyTo x) st {ty} refl ()
  isActionR st st {ty} refl refl = refl
  isActionR box st {ty} refl refl = refl
  isActionR undef st {ty} refl ()
  isActionR (tmTo x) st {box} refl ()
  isActionR (tyTo x) st {box} refl ()
  isActionR st st {box} refl refl = refl
  isActionR box st {box} refl refl = refl
  isActionR undef st {box} refl ()
  isActionR (tmTo x) box {tm} refl ()
  isActionR (tyTo x) box {tm} refl ()
  isActionR st box {tm} refl refl = refl
  isActionR box box {tm} refl refl = refl
  isActionR undef box {tm} refl ()
  isActionR (tmTo x) box {ty} refl ()
  isActionR (tyTo x) box {ty} refl ()
  isActionR st box {ty} refl refl = refl
  isActionR box box {ty} refl refl = refl
  isActionR undef box {ty} refl ()
  isActionR (tmTo x) box {box} refl ()
  isActionR (tyTo x) box {box} refl ()
  isActionR st box {box} refl refl = refl
  isActionR box box {box} refl refl = refl
  isActionR undef box {box} refl ()
  isActionR q undef {tm} () q-rw
  isActionR q undef {ty} () q-rw
  isActionR q undef {box} () q-rw

  #functional : forall {s}(q : Q s){w qw1 qw2} -> q # w ~ qw1 -> q # w ~ qw2 -> qw1 == qw2
  #functional q {w} qw1 rewrite qw1 = \{refl -> refl}

  stq : forall {u su} -> st-act u == su
     -> forall {v} -> st-act v == su
     -> forall {q : Q Real}{qu} -> q # u ~ qu
     -> forall {qv} -> q # v ~ qv
     -> st-act qu == st-act qv
  stq {tm} refl {tm} refl {q} q-u q-v rewrite #functional q q-u q-v = refl
  stq {tm} refl {ty} () q-u q-v
  stq {tm} refl {box} () q-u q-v
  stq {ty} refl {tm} () q-u q-v
  stq {ty} refl {ty} refl {q} q-u q-v rewrite #functional q q-u q-v = refl
  stq {ty} refl {box} refl {tmTo x} () ()
  stq {ty} refl {box} refl {tyTo x} q-u ()
  stq {ty} refl {box} refl {st} refl refl = refl
  stq {ty} refl {box} refl {box} refl refl = refl
  stq {ty} refl {box} refl {undef} () ()
  stq {box} refl {tm} () q-u q-v
  stq {box} refl {ty} refl {tmTo x} () ()
  stq {box} refl {ty} refl {tyTo x} () q-v
  stq {box} refl {ty} refl {st} refl refl = refl
  stq {box} refl {ty} refl {box} refl refl = refl
  stq {box} refl {ty} refl {undef} () ()
  stq {box} refl {box} refl {q} q-u q-v rewrite #functional q q-u q-v = refl

  GwqConn : forall {s}(q : Q s)(w : W) {u qu'} su=w qu {v qv'} sv=w qv
         -> Star {Sg W (\u -> st-act u == w * Sg W \qu -> q # u ~ qu)}
                 (\{(u , _ , qu' , _) (v , _ , qv' , _) -> (u << v) + (qv' << qu')})
                 (u , su=w , qu' , qu) (v , sv=w , qv' , qv)
  GwqConn q tm {tm} () q-u {v} s-v q-v
  GwqConn q tm {ty} () q-u {v} s-v q-v
  GwqConn q tm {box} () q-u {v} s-v q-v
  GwqConn q ty {tm} refl q-u {tm} refl q-v = inl refl ,- []
  GwqConn q ty {tm} refl q-u {ty} () q-v
  GwqConn q ty {tm} refl q-u {box} () q-v
  GwqConn q ty {ty} () q-u {v} s-v q-v
  GwqConn q ty {box} () q-u {v} s-v q-v
  GwqConn q box {tm} () q-u {v} s-v q-v
  GwqConn q box {ty} refl q-u {tm} () q-v
  GwqConn q box {ty} refl q-u {ty} refl q-v = inl refl ,- []
  GwqConn (tmTo x) box {ty} refl () {box} refl q-v
  GwqConn (tyTo x) box {ty} refl refl {box} refl ()
  GwqConn st box {ty} refl refl {box} refl refl = inr refl ,- []
  GwqConn box box {ty} refl refl {box} refl refl = inr refl ,- []
  GwqConn undef box {ty} refl () {box} refl q-v
  GwqConn q box {box} refl q-u {tm} () q-v
  GwqConn (tmTo x) box {box} refl () {ty} refl q-v
  GwqConn (tyTo x) box {box} refl () {ty} refl q-v
  GwqConn st box {box} refl refl {ty} refl refl = inr refl ,- []
  GwqConn box box {box} refl refl {ty} refl refl = inr refl ,- []
  GwqConn undef box {box} refl () {ty} refl q-v
  GwqConn q box {box} refl q-u {box} refl q-v = inl refl ,- []

  systemF : WorldSystem
  systemF = record
              { W = W
              ; _<<_ = _<<_
              ; tyW = tyW
              ; Q = Q
              ; st = st
              ; _#_ = _#_
              ; _&_ = _&_
              ; star& = \()
              ; unst = unst
              ; _&unst&_ = _&unst&_
              ; <<refl = refl
              ; <<trans = <<trans
              ; st-def = st-def
              ; st-unst = st-unst
              ; defUpset = \{_}{q} -> def-upset q
              ; op = \{_}{q} -> op q
              ; dominateUpset = dominateUpset
              ; stTyW = stTyW
              ; tyWUpset = \{refl tyV -> tyV}
              ; st&-action = \()
              ; &unst&-action = &unst&-action
              ; isActionL = \{q}{r} -> isActionL q r
              ; isActionR = \{q}{r} -> isActionR q r
              ; stq = stq
              ; GwqConn = GwqConn
              }


module SystemFw where
  data W : Set where
    tm ty : W

  _<<_ : W -> W -> Set
  _<<_ = _==_

  tyW : W -> Set
  tyW tm = Zero
  tyW ty = One

  data Q : Sort -> Set where
    tmTo : W -> Q Real
    st tyToTy undef : Q Real
    unstar constTm : Q Fake

  _#_ : forall {s} -> Q s -> W -> Maybe W
  tmTo w # tm = Just w
  tmTo w # ty = Nothing
  st # w = Just ty
  undef # w = Nothing
  unstar # tm = Nothing
  unstar # ty = Just tm
  tyToTy # tm = Nothing
  tyToTy # ty = Just ty
  constTm # w = Just tm
  infix 40 _#_

  st-def : forall w -> Sg W (st # w ~_)
  st-def tm = ty , refl
  st-def ty = ty , refl

  st-act : W -> W
  st-act w = fst (st-def w)

  _&_ : Q Real -> Q Real -> Q Real
  tmTo w & tmTo tm = tmTo w
  tmTo w & _ = undef
  st & tmTo w = tmTo ty
  st & st = st
  st & tyToTy = tyToTy
  st & undef = undef
  tyToTy & tmTo tm = undef
  tyToTy & tmTo ty = tmTo ty
  tyToTy & st = st
  tyToTy & tyToTy = tyToTy
  tyToTy & undef = undef
  undef & r = undef
  infix 50 _&_

  star& : Q Fake → Q Real
  star& unstar = tyToTy
  star& constTm = st

  unst : W -> Maybe W
  unst ty = Just tm
  unst _ = Nothing

  _&unst&_ : Q Real -> One + Q Real -> Sg Sort Q
  q &unst& inl <> with q # tm
  ... | Just tm = _ , unstar
  ... | Just ty = _ , tyToTy
  ... | Nothing = _ , undef
  q &unst& inr (tmTo tm) = _ , undef
  q &unst& inr (tmTo ty) with q # tm
  ... | Just w = _ , tmTo w
  ... | Nothing = _ , undef
  q &unst& inr st with q # tm
  ... | Just tm = _ , constTm
  ... | Just ty = _ , st
  ... | Nothing = _ , undef
  q &unst& inr tyToTy with q # tm
  ... | Just tm = _ , unstar
  ... | Just ty = _ , tyToTy
  ... | Nothing = _ , undef
  q &unst& inr undef = _ , undef

  <<trans : forall {u v w} -> u << v -> v << w -> u << w
  <<trans refl refl = refl

  st-unst : forall {w usw} -> unst w ~ usw -> st-act usw == w
  st-unst {tm} ()
  st-unst {ty} refl = refl

  def-upset : forall {s}(q : Q s){v qv w} -> q # v ~ qv -> v << w -> Sg W (\qw -> q # w ~ qw)
  def-upset q qv refl = _ , qv

  op : forall {s}(q : Q s){v qv' w} -> (qv : q # v ~ qv') -> (v<w : v << w) -> qv' << fst (def-upset q qv v<w)
  op q qv refl = refl

  _#?_ : forall {s} -> One + Q s -> W -> Maybe W
  _#?_ {s} = either (\_ -> Just) _#_
  infix 40 _#?_

  def-upset? : forall {s}(q : One + Q s){v qv w} -> q #? v ~ qv -> v << w -> Sg W (q #? w ~_)
  def-upset? {s} = either {C = \q -> forall {v qv w} -> q #? v ~ qv -> v << w -> Sg W (q #? w ~_)}
                          (\_ {_}{_}{w} _ _ -> w , refl) def-upset

  dominateUpset : forall {s}(q : Q s)(r : One + Q Real){v qv' rv' w}
               -> (qv : q # v ~ qv')(rv : r #? v ~ rv')
               -> qv' << rv' -> (v<w : v << w)
               -> fst (def-upset q qv v<w) << fst (def-upset? r rv v<w)
  dominateUpset _ (inl <>) qv refl refl refl = refl
  dominateUpset q (inr r) qv rv refl refl = refl

  stTyW : forall w -> tyW (st-act w)
  stTyW tm = <>
  stTyW ty = <>

  st&-action : forall q w
            -> star& q # w == ((\_ -> Just ty) =<< q # w)
  st&-action unstar tm = refl
  st&-action unstar ty = refl
  st&-action constTm tm = refl
  st&-action constTm ty = refl

  &unst&-action : forall q r w
               -> snd (q &unst& r) # w == ((q #_) =<< (unst =<< (r #? w)))
  &unst&-action q (inl <>) tm with q # tm
  &unst&-action q (inl <>) tm | Just tm = refl
  &unst&-action q (inl <>) tm | Just ty = refl
  &unst&-action q (inl <>) tm | Nothing = refl
  &unst&-action q (inl <>) ty with q # tm
  &unst&-action q (inl <>) ty | Just tm = refl
  &unst&-action q (inl <>) ty | Just ty = refl
  &unst&-action q (inl <>) ty | Nothing = refl
  &unst&-action q (inr (tmTo tm)) tm = refl
  &unst&-action q (inr (tmTo tm)) ty = refl
  &unst&-action (tmTo x) (inr (tmTo ty)) tm = refl
  &unst&-action (tmTo x) (inr (tmTo ty)) ty = refl
  &unst&-action st (inr (tmTo ty)) tm = refl
  &unst&-action st (inr (tmTo ty)) ty = refl
  &unst&-action tyToTy (inr (tmTo ty)) tm = refl
  &unst&-action tyToTy (inr (tmTo ty)) ty = refl
  &unst&-action undef (inr (tmTo ty)) tm = refl
  &unst&-action undef (inr (tmTo ty)) ty = refl
  &unst&-action (tmTo x) (inr st) tm with tmTo x # tm
  ... | Just tm = refl
  ... | Just ty = refl
  ... | Nothing = refl
  &unst&-action (tmTo x) (inr st) ty with tmTo x # tm
  ... | Just tm = refl
  ... | Just ty = refl
  ... | Nothing = refl
  &unst&-action st (inr st) tm = refl
  &unst&-action st (inr st) ty = refl
  &unst&-action tyToTy (inr st) tm = refl
  &unst&-action tyToTy (inr st) ty = refl
  &unst&-action undef (inr st) tm = refl
  &unst&-action undef (inr st) ty = refl
  &unst&-action q (inr tyToTy) tm with q # tm
  &unst&-action q (inr tyToTy) tm | Just tm = refl
  &unst&-action q (inr tyToTy) tm | Just ty = refl
  &unst&-action q (inr tyToTy) tm | Nothing = refl
  &unst&-action q (inr tyToTy) ty with q # tm
  &unst&-action q (inr tyToTy) ty | Just tm = refl
  &unst&-action q (inr tyToTy) ty | Just ty = refl
  &unst&-action q (inr tyToTy) ty | Nothing = refl
  &unst&-action q (inr undef) w = refl

  isActionL : forall q r {w qrw'} -> q & r # w ~ qrw'
           -> Sg W (\rw' -> (r # w ~ rw') * (q # rw') ~ qrw')
  isActionL (tmTo x) (tmTo tm) {tm} refl = tm , refl , refl
  isActionL (tmTo x) (tmTo tm) {ty} ()
  isActionL (tmTo x) (tmTo ty) {w} ()
  isActionL (tmTo x) st {w} ()
  isActionL (tmTo x) tyToTy {w} ()
  isActionL (tmTo x) undef {w} ()
  isActionL st (tmTo x) {tm} p = x , refl , p
  isActionL st (tmTo x) {ty} ()
  isActionL st st {w} refl = ty , refl , refl
  isActionL st tyToTy {tm} ()
  isActionL st tyToTy {ty} refl = ty , refl , refl
  isActionL st undef {w} ()
  isActionL tyToTy (tmTo tm) {w} ()
  isActionL tyToTy (tmTo ty) {tm} refl = ty , refl , refl
  isActionL tyToTy (tmTo ty) {ty} ()
  isActionL tyToTy st {w} refl = ty , refl , refl
  isActionL tyToTy tyToTy {tm} ()
  isActionL tyToTy tyToTy {ty} refl = ty , refl , refl
  isActionL tyToTy undef {w} ()
  isActionL undef (tmTo x) {w} ()
  isActionL undef st {w} ()
  isActionL undef tyToTy {w} ()
  isActionL undef undef {w} ()

  isActionR : forall q r {w rw' qrw'}
           -> r # w ~ rw'
           -> q # rw' ~ qrw'
           -> q & r # w ~ qrw'
  isActionR (tmTo x) (tmTo tm) {tm} refl refl = refl
  isActionR st (tmTo tm) {tm} refl refl = refl
  isActionR tyToTy (tmTo tm) {tm} refl ()
  isActionR undef (tmTo tm) {tm} refl ()
  isActionR q (tmTo tm) {ty} () qrw
  isActionR (tmTo x) (tmTo ty) {tm} refl ()
  isActionR st (tmTo ty) {tm} refl refl = refl
  isActionR tyToTy (tmTo ty) {tm} refl refl = refl
  isActionR undef (tmTo ty) {tm} refl ()
  isActionR q (tmTo ty) {ty} () qrw
  isActionR (tmTo x) st {w} refl ()
  isActionR st st {w} refl refl = refl
  isActionR tyToTy st {w} refl refl = refl
  isActionR undef st {w} refl ()
  isActionR q tyToTy {tm} () qrw
  isActionR (tmTo x) tyToTy {ty} refl ()
  isActionR st tyToTy {ty} refl refl = refl
  isActionR tyToTy tyToTy {ty} refl refl = refl
  isActionR undef tyToTy {ty} refl ()
  isActionR q undef {w} () qrw

  #functional : forall {s}(q : Q s){w qw1 qw2} -> q # w ~ qw1 -> q # w ~ qw2 -> qw1 == qw2
  #functional q {w} qw1 rewrite qw1 = \{refl -> refl}

  stq : forall {u su} -> st-act u == su
     -> forall {v} -> st-act v == su
     -> forall {q : Q Real}{qu} -> q # u ~ qu
     -> forall {qv} -> q # v ~ qv
     -> st-act qu == st-act qv
  stq s-u s-v {qu = tm} qu {tm} qv = refl
  stq s-u s-v {qu = tm} qu {ty} qv = refl
  stq s-u s-v {qu = ty} qu {tm} qv = refl
  stq s-u s-v {qu = ty} qu {ty} qv = refl

  GwqConn : forall {s}(q : Q s)(w : W) {u qu'} su=w qu {v qv'} sv=w qv
         -> Star {Sg W (\u -> st-act u == w * Sg W \qu -> q # u ~ qu)}
                 (\{(u , _ , qu' , _) (v , _ , qv' , _) -> (u << v) + (qv' << qu')})
                 (u , su=w , qu' , qu) (v , sv=w , qv' , qv)
  GwqConn q .ty {tm} refl q-u {tm} refl q-v = inl refl ,- []
  GwqConn (tmTo x) .ty {tm} refl refl {ty} refl ()
  GwqConn st .ty {tm} refl refl {ty} refl refl = inr refl ,- []
  GwqConn tyToTy .ty {tm} refl () {ty} refl q-v
  GwqConn undef .ty {tm} refl () {ty} refl q-v
  GwqConn unstar .ty {tm} refl () {ty} refl q-v
  GwqConn constTm .ty {tm} refl refl {ty} refl refl = inr refl ,- []
  GwqConn (tmTo x) .ty {ty} refl () {tm} refl q-v
  GwqConn st .ty {ty} refl refl {tm} refl refl = inr refl ,- []
  GwqConn tyToTy .ty {ty} refl refl {tm} refl ()
  GwqConn undef .ty {ty} refl () {tm} refl q-v
  GwqConn unstar .ty {ty} refl refl {tm} refl ()
  GwqConn constTm .ty {ty} refl refl {tm} refl refl = inr refl ,- []
  GwqConn q .ty {ty} refl q-u {ty} refl q-v = inl refl ,- []

  systemFw : WorldSystem
  systemFw = record
              { W = W
              ; _<<_ = _<<_
              ; tyW = tyW
              ; Q = Q
              ; st = st
              ; _#_ = _#_
              ; _&_ = _&_
              ; star& = star&
              ; unst = unst
              ; _&unst&_ = _&unst&_
              ; <<refl = refl
              ; <<trans = <<trans
              ; st-def = st-def
              ; st-unst = st-unst
              ; defUpset = \{_}{q} -> def-upset q
              ; op = \{_}{q} -> op q
              ; dominateUpset = dominateUpset
              ; stTyW = stTyW
              ; tyWUpset = \{refl tyV -> tyV}
              ; st&-action = st&-action
              ; &unst&-action = &unst&-action
              ; isActionL = \{q}{r} -> isActionL q r
              ; isActionR = \{q}{r} -> isActionR q r
              ; stq = stq
              ; GwqConn = GwqConn
              }

module corec where
  data W : Set where
    w : Nat -> W
    ty : W

  open import OPE

  _<<_ : W -> W -> Set
  w x << w y = x <= y
  ty << w y = Zero
  u << ty = One

  tyW : W -> Set
  tyW (w x) = Zero
  tyW ty = One

  data Q : Sort -> Set where
    st tyToTy : Q Real
    plus : Nat -> Q Real
    undef : Q Real

    tyTow : Nat -> Q Fake
    constw : Nat -> Q Fake

  _#_ : {s : Sort} -> Q s -> W -> Maybe W
  st # u = Just ty
  tyToTy # w x = Nothing
  tyToTy # ty = Just ty
  plus x # w y = Just (w (x +N y))
  plus x # ty = Just ty
  tyTow x # w _ = Nothing
  tyTow x # ty = Just (w x)
  constw x # _ = Just (w x)
  undef # _ = Nothing
  infixr 40 _#_

  _&_ : Q Real -> Q Real -> Q Real
  undef & _ = undef
  _ & undef = undef
  q & st = st
  q & tyToTy = tyToTy
  st & plus x = st
  tyToTy & plus x = tyToTy
  plus x & plus y = plus (x +N y)

  star& : Q Fake → Q Real
  star& (tyTow x) = tyToTy
  star& (constw x) = st

  unst : W -> Maybe W
  unst (w x) = Nothing
  unst ty = Just (w ze)

  _&unst&_ : Q Real -> One + Q Real -> Sg Sort Q
  st &unst& inl <> = _ , tyToTy
  tyToTy &unst& inl <> = _ , undef
  plus x &unst& inl <> = _ , tyTow x
  undef &unst& _ = _ , undef
  st &unst& inr st = _ , st
  tyToTy &unst& inr st = _ , undef
  plus x &unst& inr st = _ , constw x
  st &unst& inr tyToTy = _ , tyToTy
  tyToTy &unst& inr tyToTy = _ , undef
  plus x &unst& inr tyToTy = _ , tyTow x
  st &unst& inr (plus y) = _ , tyToTy
  tyToTy &unst& inr (plus y) = _ , undef
  plus x &unst& inr (plus y) = _ , tyTow x
  _ &unst& inr undef = _ , undef

  <<refl : forall {u} -> u << u
  <<refl {w x} = oi
  <<refl {ty} = <>

  <<trans : forall {u v w} -> u << v -> v << w -> u << w
  <<trans {w x} {w y} {w z} p q = q -<- p
  <<trans {ty} {w y} {w z} () q
  <<trans {w x} {w y} {ty} p q = <>
  <<trans {ty} {w y} {ty} p q = <>
  <<trans {u} {ty} {w z} p ()
  <<trans {w x} {ty} {ty} p q = <>
  <<trans {ty} {ty} {ty} p q = <>

  st-def : forall w -> Sg W (st # w ~_)
  st-def u = ty , refl

  st-act : W -> W
  st-act u = fst (st-def u)

  st-unst : forall {w usw} -> unst w ~ usw -> st-act usw == w
  st-unst {w x} ()
  st-unst {ty} refl = refl

  def-upset : forall {s}(q : Q s){v qv w} -> q # v ~ qv -> v << w -> Sg W (\qw -> q # w ~ qw)
  def-upset st qu u<v = ty , refl
  def-upset tyToTy {w x} () u<v
  def-upset tyToTy {ty} {w = w x} refl ()
  def-upset tyToTy {ty} {w = ty} refl <> = ty , refl
  def-upset (plus x) {w y} {w = w z} refl u<v = w (x +N z) , refl
  def-upset (plus x) {w y} {w = ty} refl u<v = ty , refl
  def-upset (plus x) {ty} {w = w z} refl ()
  def-upset (plus x) {ty} {w = ty} refl <> = ty , refl
  def-upset undef () u<v
  def-upset (tyTow x) {w y} () u<v
  def-upset (tyTow x) {ty} {w = w z} qu ()
  def-upset (tyTow x) {ty} {w = ty} qu u<v = w x , refl
  def-upset (constw x) qu u<v = w x , refl

  n+N-op : forall {x y z} -> y <= z -> x +N y <= x +N z
  n+N-op {x} {.ze} {.ze} oz = oi
  n+N-op {x} {.(su _)} {.(su _)} (os y<z) = os (n+N-op y<z)
  n+N-op {x} {y} {.(su _)} (o' y<z) = o' (n+N-op y<z)

  op : forall {s}(q : Q s){v qv' w} -> (qv : q # v ~ qv') -> (v<w : v << w) -> qv' << fst (def-upset q qv v<w)
  op st refl u<v = <>
  op tyToTy {w x} () u<v
  op tyToTy {ty} {w = w x} qu ()
  op tyToTy {ty} {w = ty} refl u<v = <>
  op (plus x) {w y} {w = w z} refl u<v = n+N-op u<v
  op (plus x) {w y} {w = ty} refl u<v = <>
  op (plus x) {ty} {w = w z} refl ()
  op (plus x) {ty} {w = ty} refl u<v = <>
  op undef () u<v
  op (tyTow x) {w y} () u<v
  op (tyTow x) {ty} {w = w z} qu ()
  op (tyTow x) {ty} {w = ty} refl u<v = oi
  op (constw x) refl u<v = oi

  _#?_ : forall {s} -> One + Q s -> W -> Maybe W
  _#?_ {s} = either (\_ -> Just) _#_
  infix 40 _#?_

  def-upset? : forall {s}(q : One + Q s){v qv w} -> q #? v ~ qv -> v << w -> Sg W (q #? w ~_)
  def-upset? {s} = either {C = \q -> forall {v qv w} -> q #? v ~ qv -> v << w -> Sg W (q #? w ~_)}
                          (\_ {_}{_}{w} _ _ -> w , refl) def-upset

  lem+ : forall {x y z} -> y <= z -> x +N y <= y -> x +N z <= z
  lem+ oz oz = oz
  lem+ (o' y<z) x+y<y = os (lem+ y<z x+y<y)
  lem+ (os y<z) (os x+y<y) = os (lem+ y<z x+y<y)
  lem+ (os y<z) (o' x+y<y) = os (lem+ y<z (x+y<y -<- o' oi))

  lem+2 : forall a b c d -> a +N c <= b +N c -> a +N d <= b +N d
  lem+2 a b ze ze ac<bc = ac<bc
  lem+2 a b ze (su d) ac<bc = os (lem+2 a b ze d ac<bc)
  lem+2 a b (su c) d (os ac<bc) = lem+2 a b c d ac<bc
  lem+2 a b (su c) d (o' ac<bc) = lem+2 a b c d (ac<bc -<- o' oi)

  lem+3 : forall {b c} -> b <= c -> forall a -> a +N b <= a +N c
  lem+3 oz a = oi
  lem+3 (os b<c) a = os (lem+3 b<c a)
  lem+3 (o' b<c) a = o' (lem+3 b<c a)

  dominateUpset : forall {s}(q : Q s)(r : One + Q Real){u qu' ru' v}
               -> (qu : q # u ~ qu')(ru : r #? u ~ ru')
               -> qu' << ru' -> (u<v : u << v)
               -> fst (def-upset q qu u<v) << fst (def-upset? r ru u<v)
  dominateUpset st (inl <>) {u} {v = v} refl refl qu<ru u<v = <<trans {ty}{u}{v} qu<ru u<v
  dominateUpset tyToTy (inl <>) {w x} () refl qu<ru u<v
  dominateUpset tyToTy (inl <>) {ty} {v = w x} refl refl qu<ru ()
  dominateUpset tyToTy (inl <>) {ty} {v = ty} refl refl qu<ru u<v = <>
  dominateUpset (plus x) (inl <>) {w y} {v = w z} refl refl qu<ru u<v = lem+ u<v qu<ru
  dominateUpset (plus x) (inl <>) {w y} {v = ty} refl refl qu<ru u<v = <>
  dominateUpset (plus x) (inl <>) {ty} {v = w z} qu refl qu<ru ()
  dominateUpset (plus x) (inl <>) {ty} {v = ty} refl refl qu<ru u<v = <>
  dominateUpset undef (inl <>) () refl qu<ru u<v
  dominateUpset (tyTow x) (inl <>) {w y} () refl qu<ru u<v
  dominateUpset (tyTow x) (inl <>) {ty} {v = w z} refl refl qu<ru ()
  dominateUpset (tyTow x) (inl <>) {ty} {v = ty} refl refl qu<ru u<v = <>
  dominateUpset (constw x) (inl <>) {u} {v = v} refl refl qu<ru u<v = <<trans {w x}{u}{v} qu<ru u<v
  dominateUpset st (inr st) {u}{v = v} qu ru qu<ru u<v = <>
  dominateUpset st (inr tyToTy) {w x} {v = v} qu () qu<ru u<v
  dominateUpset st (inr tyToTy) {ty} {v = w x} qu ru qu<ru ()
  dominateUpset st (inr tyToTy) {ty} {v = ty} refl refl qu<ru u<v = <>
  dominateUpset st (inr (plus x)) {w x₁} {v = v} refl refl () u<v
  dominateUpset st (inr (plus x)) {ty} {v = w x₁} refl refl qu<ru ()
  dominateUpset st (inr (plus x)) {ty} {v = ty} refl refl qu<ru u<v = <>
  dominateUpset st (inr undef) qu () qu<ru u<v
  dominateUpset tyToTy (inr st) {w x} {v = v} () ru qu<ru u<v
  dominateUpset tyToTy (inr st) {ty} {v = w x} refl ru qu<ru ()
  dominateUpset tyToTy (inr st) {ty} {v = ty} refl ru qu<ru <> = <>
  dominateUpset tyToTy (inr tyToTy) {w x} {v = v} () ru qu<ru u<v
  dominateUpset tyToTy (inr tyToTy) {ty} {v = w x} refl ru qu<ru ()
  dominateUpset tyToTy (inr tyToTy) {ty} {v = ty} refl refl qu<ru <> = <>
  dominateUpset tyToTy (inr (plus x)) {w x₁} {v = v} () ru qu<ru u<v
  dominateUpset tyToTy (inr (plus x)) {ty} {v = w x₁} refl refl qu<ru ()
  dominateUpset tyToTy (inr (plus x)) {ty} {v = ty} refl refl qu<ru <> = <>
  dominateUpset tyToTy (inr undef) {u} {v = v} qu () qu<ru u<v
  dominateUpset (plus x) (inr st) {w x₁} {v = w x₂} refl ru qu<ru u<v = <>
  dominateUpset (plus x) (inr st) {w x₁} {v = ty} refl ru qu<ru u<v = <>
  dominateUpset (plus x) (inr st) {ty} {v = w x₁} refl ru qu<ru ()
  dominateUpset (plus x) (inr st) {ty} {v = ty} refl ru qu<ru u<v = <>
  dominateUpset (plus x) (inr tyToTy) {w x₁} {v = v} qu () qu<ru u<v
  dominateUpset (plus x) (inr tyToTy) {ty} {v = w x₁} qu refl qu<ru ()
  dominateUpset (plus x) (inr tyToTy) {ty} {v = ty} refl refl qu<ru <> = <>
  dominateUpset (plus x) (inr (plus x₁)) {w x₂} {v = w x₃} refl refl qu<ru u<v = lem+2 x x₁ x₂ x₃ qu<ru
  dominateUpset (plus x) (inr (plus x₁)) {w x₂} {v = ty} refl refl qu<ru u<v = <>
  dominateUpset (plus x) (inr (plus x₁)) {ty} {v = w x₂} refl refl qu<ru ()
  dominateUpset (plus x) (inr (plus x₁)) {ty} {v = ty} refl refl qu<ru u<v = <>
  dominateUpset (plus x) (inr undef) {u} {v = v} qu () qu<ru u<v
  dominateUpset undef (inr st) {u}{v = v} () ru qu<ru u<v
  dominateUpset undef (inr tyToTy) {u}{v = v} () ru qu<ru u<v
  dominateUpset undef (inr (plus x)) {u}{v = v} () ru qu<ru u<v
  dominateUpset undef (inr undef) {u}{v = v} () ru qu<ru u<v
  dominateUpset (tyTow x) (inr st) {w x₁} () ru qu<ru u<v
  dominateUpset (tyTow x) (inr st) {ty} {_} {_} {w x₁} refl ru qu<ru ()
  dominateUpset (tyTow x) (inr st) {ty} {v = ty} refl ru qu<ru u<v = <>
  dominateUpset (tyTow x) (inr tyToTy) {w x₁} {v = v} () ru qu<ru u<v
  dominateUpset (tyTow x) (inr tyToTy) {ty} {_} {_} {w x₁} refl refl qu<ru ()
  dominateUpset (tyTow x) (inr tyToTy) {ty} {v = ty} refl refl qu<ru u<v = <>
  dominateUpset (tyTow x) (inr (plus x₁)) {w x₂} {v = v} () ru qu<ru u<v
  dominateUpset (tyTow x) (inr (plus x₁)) {ty} {v = w x₂} refl refl qu<ru ()
  dominateUpset (tyTow x) (inr (plus x₁)) {ty} {v = ty} refl refl qu<ru <> = <>
  dominateUpset (tyTow x) (inr undef) qu () qu<ru u<v
  dominateUpset (constw x) (inr st) {u}{v = v} qu ru qu<ru u<v = <>
  dominateUpset (constw x) (inr tyToTy) {w x₁} {v = v} qu () qu<ru u<v
  dominateUpset (constw x) (inr tyToTy) {ty} {v = w x₁} qu refl qu<ru ()
  dominateUpset (constw x) (inr tyToTy) {ty} {v = ty} qu refl qu<ru <> = <>
  dominateUpset (constw x) (inr (plus x₁)) {w x₂} {v = w x₃} refl refl qu<ru u<v = lem+3 u<v x₁ -<- qu<ru
  dominateUpset (constw x) (inr (plus x₁)) {w x₂} {v = ty} refl refl qu<ru u<v = <>
  dominateUpset (constw x) (inr (plus x₁)) {ty} {v = w x₂} refl refl qu<ru ()
  dominateUpset (constw x) (inr (plus x₁)) {ty} {v = ty} refl refl qu<ru <> = <>
  dominateUpset (constw x) (inr undef) qu () qu<ru u<v

  tyWUpset : {u v : W} -> u << v -> tyW u -> tyW v
  tyWUpset {w x} u<v ()
  tyWUpset {ty} {w x} () <>
  tyWUpset {ty} {ty} <> <> = <>

  st&-action : forall q v
            -> (star& q # v) == ((\_ -> Just ty) =<< (q # v))
  st&-action (tyTow x) (w x₁) = refl
  st&-action (tyTow x) ty = refl
  st&-action (constw x) v = refl

  &unst&-action : forall q r v
               -> snd (q &unst& r) # v == ((q #_) =<< (unst =<< (r #? v)))
  &unst&-action st (inl <>) (w x) = refl
  &unst&-action st (inl <>) ty = refl
  &unst&-action st (inr st) v = refl
  &unst&-action st (inr tyToTy) (w x) = refl
  &unst&-action st (inr tyToTy) ty = refl
  &unst&-action st (inr (plus x)) (w x₁) = refl
  &unst&-action st (inr (plus x)) ty = refl
  &unst&-action st (inr undef) v = refl
  &unst&-action tyToTy (inl <>) (w x) = refl
  &unst&-action tyToTy (inl <>) ty = refl
  &unst&-action tyToTy (inr st) v = refl
  &unst&-action tyToTy (inr tyToTy) (w x) = refl
  &unst&-action tyToTy (inr tyToTy) ty = refl
  &unst&-action tyToTy (inr (plus x)) (w x₁) = refl
  &unst&-action tyToTy (inr (plus x)) ty = refl
  &unst&-action tyToTy (inr undef) v = refl
  &unst&-action (plus x) (inl <>) (w x₁) = refl
  &unst&-action (plus x) (inl <>) ty = refl
  &unst&-action (plus x) (inr st) v = refl
  &unst&-action (plus x) (inr tyToTy) (w x₁) = refl
  &unst&-action (plus x) (inr tyToTy) ty = refl
  &unst&-action (plus x) (inr (plus x₁)) (w x₂) = refl
  &unst&-action (plus x) (inr (plus x₁)) ty = refl
  &unst&-action (plus x) (inr undef) v = refl
  &unst&-action undef (inl <>) (w x) = refl
  &unst&-action undef (inl <>) ty = refl
  &unst&-action undef (inr st) v = refl
  &unst&-action undef (inr tyToTy) (w x) = refl
  &unst&-action undef (inr tyToTy) ty = refl
  &unst&-action undef (inr (plus x)) (w x₁) = refl
  &unst&-action undef (inr (plus x)) ty = refl
  &unst&-action undef (inr undef) v = refl

  isActionL : forall {q r v qrv'}
          -> ((q & r) # v) == Just qrv'
          -> Sg W (λ rv' -> Sg ((r # v) == Just rv') (λ _ -> (q # rv') == Just qrv'))
  isActionL {st} {st} {v} refl = ty , refl , refl
  isActionL {st} {tyToTy} {w x} ()
  isActionL {st} {tyToTy} {ty} refl = ty , refl , refl
  isActionL {st} {plus x} {w x₁} refl = w (x +N x₁) , refl , refl
  isActionL {st} {plus x} {ty} refl = ty , refl , refl
  isActionL {st} {undef} {v} ()
  isActionL {tyToTy} {st} {v} refl = ty , refl , refl
  isActionL {tyToTy} {tyToTy} {w x} ()
  isActionL {tyToTy} {tyToTy} {ty} refl = ty , refl , refl
  isActionL {tyToTy} {plus x} {w x₁} ()
  isActionL {tyToTy} {plus x} {ty} refl = ty , refl , refl
  isActionL {tyToTy} {undef} ()
  isActionL {plus x} {st} qrv = ty , refl , qrv
  isActionL {plus x} {tyToTy} {w x₁} ()
  isActionL {plus x} {tyToTy} {ty} refl = ty , refl , refl
  isActionL {plus x} {plus x₁} {w x₂} refl = _ , refl , cong (Just - w) (+Nassoc x x₁ x₂)
  isActionL {plus x} {plus x₁} {ty} refl = ty , refl , refl
  isActionL {plus x} {undef} ()
  isActionL {undef} {r} {v} ()

  isActionR : forall {q r v rv' qrv'}
          -> (r # v) == Just rv'
          -> (q # rv') == Just qrv'
          -> ((q & r) # v) == Just qrv'
  isActionR {st} {st} {v} refl qrv = qrv
  isActionR {tyToTy} {st} {v} refl qrv = qrv
  isActionR {plus x} {st} {v} refl qrv = qrv
  isActionR {undef} {st} {v} refl qrv = qrv
  isActionR {q} {tyToTy} {w x} () qrv
  isActionR {st} {tyToTy} {ty} refl qrv = qrv
  isActionR {tyToTy} {tyToTy} {ty} refl qrv = qrv
  isActionR {plus x} {tyToTy} {ty} refl qrv = qrv
  isActionR {undef} {tyToTy} {ty} refl qrv = qrv
  isActionR {st} {plus x} {w x₁} refl qrv = qrv
  isActionR {tyToTy} {plus x} {w x₁} refl qrv = qrv
  isActionR {plus x₂} {plus x} {w x₁} refl refl = cong (Just - w) (sym (+Nassoc x₂ x x₁))
  isActionR {undef} {plus x} {w x₁} refl qrv = qrv
  isActionR {st} {plus x} {ty} refl qrv = qrv
  isActionR {tyToTy} {plus x} {ty} refl qrv = qrv
  isActionR {plus x} {plus x₁} {ty} refl qrv = qrv
  isActionR {undef} {plus x} {ty} refl qrv = qrv
  isActionR {q} {undef} {v} () qrv

  stq : forall {u su'} -> st-act u == su'
     -> forall {v} -> st-act v == su'
     -> forall {q : Q Real}{qu'} -> q # u ~ qu'
     -> forall {qv'} -> q # v ~ qv'
     -> st-act qu' == st-act qv'
  stq s-u s-v qu qv = refl

  ze<= : forall n -> ze <= n
  ze<= ze = oz
  ze<= (su x) = o' (ze<= x)

  owoto : forall x y -> (x <= y) + (y <= x)
  owoto ze y = inl (ze<= y)
  owoto (su x) ze = inr (o' (ze<= x))
  owoto (su x) (su y) with owoto x y
  ... | inl p = inl (os p)
  ... | inr p = inr (os p)

  GwqConn : forall {s}(q : Q s)(x : W) {u qu'} su=x qu {v qv'} sv=x qv
         -> Star {Sg W (\u -> st-act u == x * Sg W \qu -> q # u ~ qu)}
                 (\{(u , _ , qu' , _) (v , _ , qv' , _) -> (u << v) + (qv' << qu')})
                 (u , su=x , qu' , qu) (v , sv=x , qv' , qv)
  GwqConn st x s-u refl s-v refl = inr <> ,- []
  GwqConn tyToTy x {w x₁} s-u () s-v qv
  GwqConn tyToTy x {ty} s-u refl {w x₁} s-v ()
  GwqConn tyToTy x {ty} s-u refl {ty} s-v refl = inl <> ,- []
  GwqConn (plus x) x₃ {w x₂} s-u refl {w x₁} s-v refl with owoto x₂ x₁
  ... | inl p = inl p ,- []
  ... | inr p = inr (lem+3 p x) ,- []
  GwqConn (plus x) x₂ {w x₁} s-u refl {ty} s-v refl = inl <> ,- []
  GwqConn (plus x) x₂ {ty} s-u refl {w x₁} s-v refl = inr <> ,- []
  GwqConn (plus x) x₁ {ty} s-u refl {ty} s-v refl = inl <> ,- []
  GwqConn undef x s-u () s-v qv
  GwqConn (tyTow x) x₁ {w x₂} s-u () s-v qv
  GwqConn (tyTow x) x₁ {ty} s-u refl {w x₂} s-v ()
  GwqConn (tyTow x) x₁ {ty} s-u refl {ty} s-v refl = inl <> ,- []
  GwqConn (constw x) x₁ s-u refl s-v refl = inr oi ,- []

  corec : WorldSystem
  corec = record
            { W = W
            ; _<<_ = _<<_
            ; tyW = tyW
            ; Q = Q
            ; st = st
            ; _#_ = _#_
            ; _&_ = _&_
            ; star& = star&
            ; unst = unst
            ; _&unst&_ = _&unst&_
            ; <<refl = \{u} -> <<refl {u}
            ; <<trans = \{u}{v}{w} -> <<trans {u}{v}{w}
            ; st-def = st-def
            ; st-unst = st-unst
            ; defUpset = \{_}{q} -> def-upset q
            ; op = \{_}{q} -> op q
            ; dominateUpset = dominateUpset
            ; stTyW = \w₁ -> <>
            ; tyWUpset = tyWUpset
            ; st&-action = st&-action
            ; &unst&-action = &unst&-action
            ; isActionL = \{q} -> isActionL {q}
            ; isActionR = \{q} -> isActionR {q}
            ; stq = stq
            ; GwqConn = GwqConn
            }
