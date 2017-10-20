module WorldSystem where

open import Basics
open import Star

data Maybe (A : Set) : Set where
  Just : A -> Maybe A
  Nothing : Maybe A

_=<<_ : {A B : Set} -> (A -> Maybe B) -> Maybe A -> Maybe B
f =<< Just x = f x
f =<< Nothing = Nothing
infix 30 _=<<_

either : {A B : Set}{C : A + B -> Set} -> ((a : A) -> C (inl a)) -> ((b : B) -> C (inr b)) -> (x : A + B) -> C x
either f g (inl x) = f x
either f g (inr x) = g x

_~_ : {A : Set} -> Maybe A -> A -> Set
a ~ b = a == Just b
--Just a ~ b = a == b
--Nothing ~ b = Zero
infix 10 _~_

data Sort : Set where Real Fake : Sort
-- For historical reasons we formulate quantifiers differently to the paper.
-- our Q Real is the paper's Q_J, and the paper's Q_C is Sg Sort Q, noting that
-- Q_J is a subset of Q_C.
--
-- This does mean we cannot restrict the quantifiers in terms as much as one can
-- in the paper, but this is irrelevant for the meta-theory.
--
-- Fake is things of the form q & unstar & r
-- Real is things where any unstar is "guarded" on the left by a star: star & q & unstar & r
-- Only Real ones are allowed to appear in terms, the Fake ones are to prove subsumption
-- (Could conflate the two, but then two worlds system fails dominateUpset. We are being a bit more fine-grained)

-- TODO: This is not the complete specification...
record WorldSystem : Set₁ where
  field
    W : Set
    _<<_ : W -> W -> Set
    tyW : W -> Set

    Q : Sort -> Set
    st : Q Real
{-
 We don't want this style -- it opens the possibility that the action is not a (partial) _function_
    actDef : Q -> W -> Set
    action : (q : Q) -> (w : W) -> actDef q w -> W
-}
    _#_ : forall {s} -> Q s -> W -> Maybe W
    _&_ : Q Real -> Q Real -> Q Real

    star& : Q Fake -> Q Real -- we like things which are "guarded"

    unst : W -> Maybe W
    _&unst&_ : Q Real -> One + Q Real -> Sg Sort Q -- q & unstar & r, "inl <>" means "identity"
       -- I'm using 1 rather than Maybe on purpose. inl <> is NOT failure



--  _#_~_ : forall {s} (q : Q s)(u v : W) -> Set
--  _#_~_ q u v = (q # u) == Just v

  infix 30 _<<_
  infixr 40 _#_
  infixr 50 _&_
  infix 50 _&unst&_
--  infix 20 _#_~_

{-
  -- We could equivalently use these instead of _#_~_
  -- but I've found it more convenient to have both the evidence of defined-ness
  -- and the result packaged together.
  -- For instance, for quantifiers are defined on upsets: it is nice that if we know
  -- q # v ~ qv and v << w, then with one application we get a qw and knowledge q # w ~ qw.
  isDef : Q -> W -> Set
  isDef q w with q # w
  ... | Nothing = Zero
  ... | Just _ = One

  defAct : forall q w -> isDef q w -> W
  defAct q w d with q # w
  defAct q w () | Nothing
  defAct q w <> | Just qw = qw
-}

  field
    -- W is a preorder
    <<refl : forall {w} -> w << w
    <<trans : forall {u v w} -> u << v -> v << w -> u << w

    -- star has a total action
    st-def : forall w -> Sg W (st # w ~_)
  st-act : W -> W
  st-act w = fst (st-def w)
  st-pr : (w : W) -> st # w ~ st-act w
  st-pr w = snd (st-def w)

  _##_ : forall {s} -> Q s -> Maybe W -> Maybe W
  _##_ q w = (q #_) =<< w
  infix 40 _##_

  _#?_ : forall {s} -> One + Q s -> W -> Maybe W
  _#?_ {s} = either (\_ -> Just) _#_
  infix 40 _#?_


  field
    -- unst is a partial section of the action of st
    st-unst : forall {w usw} -> unst w ~ usw -> st-act usw == w

    -- quantifiers are defined on upsets
    defUpset : forall {s}{q : Q s}{v qv w} -> q # v ~ qv -> v << w -> Sg W (q # w ~_)
  defUpsetAct : forall {s}{q : Q s}{v qv w} -> q # v ~ qv -> v << w -> W
  defUpsetAct qv v<w = fst (defUpset qv v<w)
  defUpsetPf : forall {s}{q : Q s}{v qv' w} -> (qv : q # v ~ qv') -> (v<w : v << w) -> q # w ~ defUpsetAct qv v<w
  defUpsetPf qv v<w = snd (defUpset qv v<w)

  -- Lift to One + Q
  defUpset? : forall {s}(q : One + Q s){v qv w} -> q #? v ~ qv -> v << w -> Sg W (q #? w ~_)
  defUpset? {s} = either {C = \q -> forall {v qv w} -> q #? v ~ qv -> v << w -> Sg W (q #? w ~_)}
                         (\_ {_}{_}{w} _ _ -> w , refl) (\q qv v<w -> defUpset qv v<w)
  defUpset?Act : forall {s}(q : One + Q s){v qv w} -> q #? v ~ qv -> v << w -> W
  defUpset?Act q qv v<w = fst (defUpset? q qv v<w)
  defUpset?Pf : forall {s}(q : One + Q s){v qv' w} -> (qv : q #? v ~ qv') -> (v<w : v << w) -> q #? w ~ defUpset?Act q qv v<w
  defUpset?Pf q qv v<w = snd (defUpset? q qv v<w)

  field
    -- Actions are order preserving
    op : forall {s}{q : Q s}{v qv' w} -> (qv : q # v ~ qv') -> (v<w : v << w) -> qv' << defUpsetAct qv v<w

    -- guarded quantifiers (or identity) dominate any quantifiers on upsets
    dominateUpset : forall {s}(q : Q s)(r : One + Q Real){v qv rv w}
                    (qvDef : q # v ~ qv)(rvDef : r #? v ~ rv)
                 -> qv << rv
                 -> (v<w : v << w)
                 -> defUpsetAct qvDef v<w  << defUpset?Act r rvDef v<w

    -- This is now subsumed into dominateUpset
    --deflateUpset : forall {q v qv' w} -> (qv : q # v ~ qv') -> qv' << v -> (v<w : v << w)
    --            -> defUpsetAct qv v<w << w

    -- st always emits tyW worlds
    stTyW : forall w -> tyW (st-act w)

    -- tyW is an upset
    tyWUpset : forall {v w} -> v << w -> tyW v -> tyW w

  -- star& q has same action as star's action composed with q's
    st&-action : (q : Q Fake)(w : W) -> star& q # w == (st ## (q # w)) -- WHY do I need to bracket this??

    -- q &unst& r has same action as q's action composed with unstar composed with r's action
    &unst&-action : (q : Q Real)(r : One + Q Real)(w : W)
                 -> snd (q &unst& r) # w == (q ## unst =<< (r #? w))

    -- Action respects magma structure
    isActionL : forall {q r w qrw} -> q & r # w ~ qrw -> Sg W (\rw' -> r # w ~ rw' * q # rw' ~ qrw)
    isActionR : forall {q r w rw qrw} -> r # w ~ rw -> q # rw ~ qrw -> (q & r) # w ~ qrw

    -- if u and v have the same world for their types, then so do qu and qv (if defined)
    -- only actually need for actual quantifiers (i.e. those which appear in terms)
    stq : forall {u su} -> st-act u == su
       -> forall {v} -> st-act v == su
       -> forall {q : Q Real}{qu} -> q # u ~ qu
       -> forall {qv} -> q # v ~ qv
       -> st-act qu == st-act qv

    -- The graph G(w,q) is connected. Only need q a Real quantifier
    GwqConn : forall (q : Q Real) w {u qu'} su=w qu {v qv'} sv=w qv
           -> Star {Sg W (\u -> st-act u == w * Sg W \qu -> q # u ~ qu)}
                   (\{(u , _ , qu' , _) (v , _ , qv' , _) -> (u << v) + qv' << qu'})
                   (u , su=w , qu' , qu) (v , sv=w , qv' , qv)

  split## : forall w {s}{q : Q s}{qw'} -> q ## w ~ qw' -> Sg W (\w' -> w ~ w' * q # w' ~ qw')
  split## (Just w') qw = w' , refl , qw
  split## Nothing ()

  #functional : forall {s}{q : Q s}{w qw1 qw2} -> q # w ~ qw1 -> q # w ~ qw2 -> qw1 == qw2
  #functional {q}{w} qw1 rewrite qw1 = \{refl -> refl}

  #functionalSg : forall {s}{q : Q s}{w}(qw1 qw2 : Sg W (q # w ~_)) -> fst qw1 == fst qw2
  #functionalSg {q}{w} (_ , qw1) (_ , qw2) = #functional qw1 qw2

  st-functional : forall {w sw} -> st # w ~ sw -> st-act w == sw
  st-functional sw = #functional (st-pr _) sw

  st-op : forall {v w} -> v << w -> st-act v << st-act w
  st-op v<w with op (st-pr _) v<w
  ... | sv<sw' rewrite st-functional (defUpsetPf (st-pr _) v<w)
    = sv<sw'

  st& : forall {q v qv'} -> q # v ~ qv' -> st & q # v ~ st-act qv'
  st& {qv' = qv'} qv with st-pr qv'
  ... | s-qv = isActionR qv s-qv

  defUpsetCommAct : forall {q r v rv'}(rv : r # v ~ rv'){qrv'}(qrv : q # rv' ~ qrv'){w}(v<w : v << w)
                 -> q # defUpsetAct rv v<w ~ defUpsetAct (isActionR rv qrv) v<w
  defUpsetCommAct rv qrv v<w with defUpset rv v<w | defUpset (isActionR rv qrv) v<w
  ... | (rw' , rw) | (qrw' , qrw) with isActionL qrw
  ...    | (rw'1 , rw1 , qrw1) rewrite rw with rw1
  ...      | refl = qrw1

  starSg& : Sg Sort Q -> Q Real
  starSg& (Real , q) = st & q
  starSg& (Fake , q) = star& q

  starSg&-pf : forall {q w qw'} -> snd q # w ~ qw' -> starSg& q # w ~ st-act qw'
  starSg&-pf {Real , q} qw = st& qw
  starSg&-pf {Fake , q}{w}{qw'} qw rewrite st&-action q w | qw = snd (st-def qw')


  defUpsetCommStarAct : forall {s}{q : Q s}{v qv'}(qv : q # v ~ qv'){w}(v<w : v << w)
                       -> st-act (defUpsetAct qv v<w) == defUpsetAct (starSg&-pf qv) v<w
  defUpsetCommStarAct {Real} {q} qv {w} v<w = st-functional (defUpsetCommAct qv (st-pr _) v<w)
  defUpsetCommStarAct {Fake} {q}{v} qv {w} v<w
    with defUpset qv v<w | defUpset (starSg&-pf qv) v<w
  ... | qw' , qw | sqw' , sqw
    rewrite st&-action q w | qw
    = st-functional sqw

  -- Lift op to One + Q s
  op? : forall {s}(q : One + Q s){v qv' w} -> (qv : q #? v ~ qv') -> (v<w : v << w) -> qv' << defUpset?Act q qv v<w
  op? (inl <>) refl v<w = v<w
  op? (inr q) qv v<w = op qv v<w

{-
----- Let's leave this until we know if we want Q Real only, or any Q s + unstar etc...
  -- We get the action is "associative", even if Q not a semigroup
  data Tree : Set where
    L : Q -> Tree
    N : Tree -> Tree -> Tree

  runTree : Tree -> Q
  runTree (L q) = q
  runTree (N l r) = runTree l & runTree r

  flattenTree' : Tree -> NEL Q
  flattenTree' (L q) = [ q ]
  flattenTree' (N l r) = flattenTree' l +NL+ flattenTree' r

  &[_] : NEL Q -> Q
  &[_] = foldr1 _&_

  flattenTree : Tree -> Q
  flattenTree t = &[ flattenTree' t ]

  actionAssocL' : (l : NEL Q)(r : NEL Q){v lrv : W}
               -> &[ l +NL+ r ] # v ~ lrv
               -> Sg W \rv -> &[ r ] # v ~ rv * &[ l ] # rv ~ lrv
  actionAssocL' [ l ] rs lrs-v = isActionL lrs-v
  actionAssocL' (l :: ls) rs llsrs-v with isActionL llsrs-v
  ... | lsrsv' , lsrs-v , l-lsrsv with actionAssocL' ls rs lsrs-v
  ...    | rsv' , rs-v , ls-rsv = rsv' , rs-v , isActionR ls-rsv l-lsrsv

  actionAssocR' : (l : NEL Q){rv lrv : W} -> &[ l ] # rv ~ lrv
               -> (r : NEL Q){v : W} -> &[ r ] # v ~ rv
               -> &[ l +NL+ r ] # v ~ lrv
  actionAssocR' [ l ] l-rv rs rs-v = isActionR rs-v l-rv
  actionAssocR' (l :: ls) lls-rv rs rs-v with isActionL lls-rv
  ... | lsrv' , ls-rv , l-lsrv = isActionR (actionAssocR' ls ls-rv rs rs-v) l-lsrv

  actionAssocL : (t : Tree){v w : W} -> runTree t # v ~ w -> flattenTree t # v ~ w
  actionAssocL (L x) tvw = tvw
  actionAssocL (N l r) tvw with isActionL tvw
  ... | rv' , rv , lrv with actionAssocL r rv | actionAssocL l lrv
  ...   | flatrv | flatlrv = actionAssocR' (flattenTree' l) flatlrv (flattenTree' r) flatrv

-- could get away with just saying runTree t # v is defined...
  actionUnAssocL : (t : Tree){v w : W} -> flattenTree t # v ~ w -> runTree t # v ~ w
  actionUnAssocL (L x) flattv = flattv
  actionUnAssocL (N l r) flattv with actionAssocL' (flattenTree' l) (flattenTree' r) flattv
  ... | flatrv' , flatr-v , flatl-rv = isActionR (actionUnAssocL r flatr-v) (actionUnAssocL l flatl-rv)

  actionAssoc : (t1 : Tree){v w : W} -> runTree t1 # v ~ w
             -> (t2 : Tree) -> flattenTree t1 == flattenTree t2
             -> runTree t2 # v ~ w
  actionAssoc t1 t1v t2 p with actionAssocL t1 t1v
  ... | flatt1v rewrite p = actionUnAssocL t2 flatt1v
-}
