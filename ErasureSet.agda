open import WorldSystem

module ErasureSet {QW : WorldSystem} where

open WorldSystem.WorldSystem QW

open import Basics


------------------------------------------------------------------------------
----- Describing an up-set to erase ------------------------------------------
------------------------------------------------------------------------------
data Erase? : Set where
  keep delete : Erase?

uip : {a b : Erase?} -> (p q : a == b) -> p == q
uip {keep} refl refl = refl
uip {delete} refl refl = refl

record ErasureSet : Set where
  field
    er? : W -> Erase?
    upsetEr : forall {u v} -> u << v -> er? u == delete -> er? v == delete
    -- We need that if an arrow lies in the downset to keep, then it's image lies either
    -- within or without said set (rather than starting inside and ending outside)
    noStraddle : forall {u v} -> (u<v : u << v) -> er? v == keep
              -> forall {s}(q : Q s){qu'} -> (qu : q # u ~ qu')
              -> er? qu' == keep -> er? (defUpsetAct qu u<v) == keep

  erXorKp : forall {w} -> er? w == delete -> er? w == keep -> Zero
  erXorKp {w} e k = help (trans (sym e) k)
    where help : delete == keep -> Zero
          help ()

  downsetKeep : forall {u v} -> u << v -> er? v == keep -> er? u == keep
  downsetKeep {u} u<v keepV with er? u | upsetEr u<v
  ... | keep | _ = refl
  ... | delete | p = naughty (erXorKp (p refl) keepV)

  caseEr' : {e : Erase?}{w : W} -> er? w == e -> (er? w == keep -> Set) -> (er? w == delete -> Set) -> Set
  caseEr' {keep} ke A B = A ke
  caseEr' {delete} de A B = B de

  caseEr : (w : W){A : er? w == keep -> Set}{B : er? w == delete -> Set}
        -> ((ke : er? w == keep) -> A ke)
        -> ((de : er? w == delete) -> B de)
     -> Sg _ \e -> Sg (er? w == e) \p -> caseEr' p A B
  caseEr w {A}{B} ke de = foo (er? w) refl
    where foo : (e : Erase?) -> (er? w == e) -> Sg _ \e -> Sg (er? w == e) \p -> caseEr' p A B
          foo keep p = keep , p , ke p
          foo delete p = delete , p , de p


  -- lift noStraddle to One + Q s
  noStraddle? : forall {u v} -> (u<v : u << v) -> er? v == keep
             -> forall {s}(q : One + Q s){qu'} -> (qu : q #? u ~ qu')
             -> er? qu' == keep -> er? (defUpset?Act q qu u<v) == keep
  noStraddle? u<v keV (inl <>) qu keQU = keV
  noStraddle? u<v keV (inr q) qu keQU = noStraddle u<v keV q qu keQU
