/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import LeanPool.ScottishBook155.Paper1


/-!
# Formal target for canonical claim 14

This file fixes the exact existential statement before the transfinite
construction is assembled.  The witness packages two real Banach spaces and a
bijection satisfying the paper's closed-ball conclusion while failing to be a
global isometry.
-/

@[expose] public section

namespace ScottishBook155

universe u

/-- A bundled real Banach space, used so that the source and target types of
the final existential statement may themselves be chosen by the construction. -/
structure RealBanachSpace where
  /-- The underlying type of the bundled real Banach space. -/
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
  /-- The real Banach space on which the counterexample map is defined. -/
  source : RealBanachSpace.{u}
  /-- The real Banach space into which the counterexample map takes values. -/
  target : RealBanachSpace.{u}
  /-- The map witnessing the failure of global distance preservation at protected scale
  one quarter. -/
  map : source → target
  isCounterexample : IsCounterexampleAt ((1 : ℝ) / 4) map

/-- The exact formal proposition corresponding to canonical claim 14. -/
def Claim14 : Prop := Nonempty (Claim14Witness.{u})

/-- The stronger construction invariant used in the paper is sufficient for
the exact claim-14 witness. -/
def claim14WitnessOfHalfScale
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
