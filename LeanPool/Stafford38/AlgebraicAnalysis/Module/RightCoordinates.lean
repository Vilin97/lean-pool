/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Finsupp.SMul
import Mathlib.Tactic

/-!
# The concrete right-coordinate model for a stage

The iterated Ore tower currently supplies nested additive normal forms, but it
does not yet identify a localized stage with a free right module over its
coefficient stage.  This file formalizes the part that is unconditional and
used once that identification is available: the canonical coordinatewise
right action on the free coordinate object `ι →₀ S`, together with its finite
single-coordinate decomposition.  No freeness of an Ore localization is
assumed or encoded by an equivalent hypothesis here.
-/

namespace AlgebraicAnalysis.RightCoordinates

noncomputable section

variable {S ι α : Type*} [Ring S]

/-- The coordinatewise right action on finitely supported `S`-coordinates. -/
def rightCoordinateAction (v : ι →₀ S) (a : S) : ι →₀ S :=
  (MulOpposite.op a : Sᵐᵒᵖ) • v

@[simp] theorem rightCoordinateAction_apply (v : ι →₀ S) (a : S) (i : ι) :
    rightCoordinateAction v a i = v i * a := rfl

@[simp] theorem rightCoordinateAction_eq_op_smul (v : ι →₀ S) (a : S) :
    rightCoordinateAction v a =
      (MulOpposite.op a : Sᵐᵒᵖ) • v := rfl

/-- Coordinatewise right multiplication is additive in the vector. -/
theorem rightCoordinateAction_add (v w : ι →₀ S) (a : S) :
    rightCoordinateAction (v + w) a =
      rightCoordinateAction v a + rightCoordinateAction w a := by
  ext i
  simp [rightCoordinateAction, add_mul]

/-- Coordinatewise right multiplication is additive in the scalar. -/
theorem rightCoordinateAction_add_scalar (v : ι →₀ S) (a b : S) :
    rightCoordinateAction v (a + b) =
      rightCoordinateAction v a + rightCoordinateAction v b := by
  ext i
  simp [rightCoordinateAction, mul_add]

@[simp] theorem rightCoordinateAction_one (v : ι →₀ S) :
    rightCoordinateAction v 1 = v := by
  simpa only [rightCoordinateAction_eq_op_smul, MulOpposite.op_one, one_smul]

/-- Written in right-sided order, successive coordinate actions multiply the
scalars in the same order. -/
theorem rightCoordinateAction_mul (v : ι →₀ S) (a b : S) :
    rightCoordinateAction (rightCoordinateAction v a) b =
      rightCoordinateAction v (a * b) := by
  ext i
  simp [rightCoordinateAction, mul_assoc]

/-- Coordinatewise right multiplication commutes with finite additive sums. -/
theorem rightCoordinateAction_sum (t : Finset α) (f : α → ι →₀ S) (a : S) :
    rightCoordinateAction (∑ j ∈ t, f j) a =
      ∑ j ∈ t, rightCoordinateAction (f j) a := by
  ext i
  simp [rightCoordinateAction, Finset.sum_mul]

/-- A single coordinate remains a single coordinate under the right action. -/
theorem rightCoordinateAction_single (i : ι) (s a : S) :
    rightCoordinateAction (Finsupp.single i s) a =
      Finsupp.single i (s * a) := by
  ext j
  by_cases h : i = j
  · subst j
    simp [rightCoordinateAction]
  · simp [rightCoordinateAction, h, Ne.symm h]

/-- Every finitely supported coordinate vector is the finite sum of its pure
coordinate vectors. -/
theorem rightCoordinate_decomposition (v : ι →₀ S) :
    v = ∑ i ∈ v.support, Finsupp.single i (v i) := by
  symm
  exact Finsupp.sum_single v

/-- After a right action, the finite coordinate decomposition is acted on
coordinatewise. -/
theorem rightCoordinate_decomposition_action (v : ι →₀ S) (a : S) :
    rightCoordinateAction v a =
      ∑ i ∈ v.support, Finsupp.single i (v i * a) := by
  calc
    rightCoordinateAction v a =
        rightCoordinateAction
          (∑ i ∈ v.support, Finsupp.single i (v i)) a := by
      exact congrArg (fun w => rightCoordinateAction w a)
        (rightCoordinate_decomposition v)
    _ = ∑ i ∈ v.support,
          rightCoordinateAction (Finsupp.single i (v i)) a := by
      rw [rightCoordinateAction_sum]
    _ = ∑ i ∈ v.support, Finsupp.single i (v i * a) := by
      simp_rw [rightCoordinateAction_single]

/-- The canonical pure coordinates generate the free right-coordinate model. -/
theorem rightCoordinate_eq_top_of_single_mem
    (H : Submodule Sᵐᵒᵖ (ι →₀ S))
    (hH : ∀ i : ι, ∀ s : S, Finsupp.single i s ∈ H) :
    H = ⊤ := by
  apply top_unique
  intro v hv
  rw [rightCoordinate_decomposition v]
  apply Submodule.sum_mem
  intro i hi
  exact hH i (v i)


end
end AlgebraicAnalysis.RightCoordinates
