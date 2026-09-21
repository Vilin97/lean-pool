/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.StepA
import LeanPool.RegtsSevenster.RS.Classical.Deligne.TwistState
import LeanPool.RegtsSevenster.RS.Classical.Deligne.TwistSymPow

/-!
# The line step of the dévissage

When every alternating power of the remainder survives, twisting
by the odd line turns them into surviving symmetric powers, so
the unit step applies to the twisted state and splits a unit
factor off it.  Twisting back turns that unit factor into a line
factor of the original state.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v}

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

/-- **The line step of the dévissage**: when every alternating
power of the remainder survives, a further line factor splits
off it. -/
theorem devissageStepB
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalLinear ℂ (Ind C)]
    (L : OddLine (Ind C)) (X : Ind C) :
    DevissageStepB (Ind C) L X := by
  intro st hAlt
  letI := st.monObj
  letI := st.comm
  obtain ⟨st', hu, hl⟩ :=
    devissageStepA L (L.obj ⊗ X) (twistState L st)
      (not_isZero_symPow_twist st.base L st.rest hAlt)
  exact ⟨(twistState L st').transportObj (untwistIso L X),
    hl, hu⟩

end RS
