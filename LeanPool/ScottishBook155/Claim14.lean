/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.Paper1

/-!
# Formal target for canonical claim 14

This file fixes the exact existential statement before the transfinite
construction is assembled.  The witness packages two real Banach spaces and a
bijection satisfying the paper's closed-ball conclusion while failing to be a
global isometry.
-/

namespace ScottishBook155

universe u

/-- A bundled real Banach space, used so that the source and target types of
the final existential statement may themselves be chosen by the construction. -/
structure RealBanachSpace where
  carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [normedSpace : NormedSpace ℝ carrier]
  [completeSpace : CompleteSpace carrier]

attribute [instance] RealBanachSpace.normedAddCommGroup
  RealBanachSpace.normedSpace RealBanachSpace.completeSpace

instance : CoeSort (RealBanachSpace.{u}) (Type u) :=
  ⟨RealBanachSpace.carrier⟩

/-- Bundle an already-instanced real Banach space. -/
def RealBanachSpace.ofType (X : Type u) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] : RealBanachSpace.{u} where
  carrier := X

/-- Exact witness asserted by canonical claim 14. -/
structure Claim14Witness where
  source : RealBanachSpace.{u}
  target : RealBanachSpace.{u}
  map : source → target
  isCounterexample : IsCounterexampleAt ((1 : ℝ) / 4) map

/-- The exact formal proposition corresponding to canonical claim 14. -/
def Claim14 : Prop := Nonempty (Claim14Witness.{u})

/-- The stronger construction invariant used in the paper is sufficient for
the exact claim-14 witness. -/
def claim14Witness_of_halfScale
    (X : RealBanachSpace.{u}) (Y : RealBanachSpace.{u}) (U : X → Y)
    (hbij : Function.Bijective U)
    (hshort : PreservesUpTo ((1 : ℝ) / 2) U)
    {p q : X} (hcontracts : dist (U p) (U q) ≠ dist p q) :
    Claim14Witness.{u} where
  source := X
  target := Y
  map := U
  isCounterexample :=
    isCounterexampleAt_one_quarter_of_short_scale hbij hshort hcontracts

end ScottishBook155
