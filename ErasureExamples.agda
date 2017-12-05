module ErasureExamples where

open import Basics
open import Dir
open import WorldSystem
open import WorldSystemExamples

module polyId where
  open twoWorlds
  open WorldSystem.WorldSystem twoWorlds using (defUpsetAct)

  open import Tm {Q Real}
  open import Typing {twoWorlds}
  open import Er
  open import ErasureSet {twoWorlds}

  erTy : ErasureSet
  erTy = record { er? = er?
                ; upsetEr = upsetEr
                ; noStraddle = noStraddle}
    where er? : W -> Erase?
          er? H = delete
          er? E = keep
          upsetEr : forall {u v} -> u << v -> er? u == delete -> er? v == delete
          upsetEr {u} {H} u<v eru = refl
          upsetEr {E} {E} E<E ()
          noStraddle : forall {u v} -> (u<v : u << v) -> er? v == keep
                    -> forall {s}(q : Q s){qu'} -> (qu : q # u ~ qu')
                    -> er? qu' == keep -> er? (defUpsetAct qu u<v) == keep
          noStraddle E<E kev q qu kequ = kequ
          noStraddle H<H kev q qu kequ = kequ
          noStraddle E<H () q qu kequ

  open import Erasure {twoWorlds}{erTy}

  id : Tm ze chk
  id = lam (lam [ var ze ])

  idTy : Tm ze chk
  idTy = pi H star (pi C [ var ze ] [ var (su ze) ])

  idCHK : CHK [] E idTy id
  idCHK = lam refl (lam refl ([ var ze E<E ] refl))

  erId : Sg (Er ze) (CHKEr [] [] E refl idTy id)
  erId = eraseCHK [] {E} refl idCHK

  expect : fst (erId) == lam (var ze)
  expect = refl
