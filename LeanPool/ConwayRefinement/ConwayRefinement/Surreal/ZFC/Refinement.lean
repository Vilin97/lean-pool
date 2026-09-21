/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.OmnificInteger
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.RefinementConjecture
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.Refinement

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.PrimalPreimage

/-!
# Conway's refinement conjecture for class-coded omnific integers

The cut-preserving ring equivalence identifies the four-factor formula on class-coded omnific
values with the formula on the surreal omnific-integer ring. All four inputs and all four factors
are unrestricted, including zero. This states the class presentation of LM24,
Conjecture 1.1.1(2); it does not assert the conjecture.
-/

universe u

public noncomputable section

namespace ZFSet.Surreal.OmnificInteger

/-- Conway's four-factor conjecture in the class presentation; no nonzero hypotheses are imposed. -/
def RefinementConjecture : Prop := HasFourFactorRefinement OmnificInteger.{u}

/-- The class formulation is equivalent to the existing refinement conjecture, not a weakening. -/
theorem refinementConjecture_iff : RefinementConjecture.{u} ↔ ConwayRefinementConjecture.{u} := by
  rw [RefinementConjecture, hasFourFactorRefinement_iff_forall_isPrimal]
  have htarget : ConwayRefinementConjecture.{u} ↔
      ∀ b : _root_.Surreal.OmnificInteger.{u}, IsPrimal b := by
    rw [conwayRefinementConjecture_def, ← hasFourFactorRefinement_def,
      hasFourFactorRefinement_iff_forall_isPrimal]
  rw [htarget, ringEquiv.surjective.forall]
  exact forall_congr' fun x ↦ (RingEquiv.isPrimal_iff ringEquiv x).symm

end ZFSet.Surreal.OmnificInteger
