/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.NumericalRange.Adjoint
import LeanPool.OperatorTheory.Operator.NumericalRange.Radius

/-!
# Adjoint and unitary invariance of the numerical radius

The numerical range of the adjoint is obtained by complex conjugation, so its
radius is unchanged.  Likewise, unitary changes of orthonormal coordinates
preserve the entire numerical range and hence the numerical radius.
-/

open Complex
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Taking the adjoint cannot increase the numerical radius. -/
theorem numericalRadius_adjoint_le (A : E →L[ℂ] E) :
    numericalRadius (A†) ≤ numericalRadius A := by
  unfold numericalRadius
  refine Real.iSup_le (fun z => ?_) (numericalRadius_nonneg A)
  refine Real.iSup_le (fun hz => ?_) (numericalRadius_nonneg A)
  rw [numericalRange_adjoint A] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [starRingEnd_apply, norm_star]
  exact norm_le_numericalRadius A hw

/-- Numerical radius is invariant under adjoint. -/
@[simp] theorem numericalRadius_adjoint (A : E →L[ℂ] E) :
    numericalRadius (A†) = numericalRadius A := by
  apply le_antisymm (numericalRadius_adjoint_le A)
  simpa only [adjoint_adjoint] using numericalRadius_adjoint_le (A†)

/-- Conjugating an operator by a unitary preserves its numerical range. -/
theorem numericalRange_unitary_conjugate (A U : E →L[ℂ] E)
    (hU : U ∈ unitary (E →L[ℂ] E)) :
    numericalRange (U† * A * U) = numericalRange A := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨U x, (norm_map_of_mem_unitary hU x).trans hx, ?_⟩
    simp only [mul_apply_eq_comp]
    rw [adjoint_inner_right]
  · rintro ⟨x, hx, rfl⟩
    have hUadj : U† ∈ unitary (E →L[ℂ] E) := Unitary.star_mem hU
    refine ⟨(U†) x, (norm_map_of_mem_unitary hUadj x).trans hx, ?_⟩
    have hcancel (v : E) : U ((U†) v) = v := by
      change U ((star U) v) = v
      have h := congrArg (fun T : E →L[ℂ] E => T v)
        (Unitary.mul_star_self_of_mem hU)
      simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
    simp only [mul_apply_eq_comp, hcancel]
    exact inner_map_map_of_mem_unitary hUadj x (A x)

/-- The alternate orientation of unitary conjugation also preserves the
numerical range. -/
theorem numericalRange_unitary_conjugate' (A U : E →L[ℂ] E)
    (hU : U ∈ unitary (E →L[ℂ] E)) :
    numericalRange (U * A * U†) = numericalRange A := by
  simpa only [adjoint_adjoint] using
    numericalRange_unitary_conjugate A (U†) (Unitary.star_mem hU)

/-- Numerical radius is invariant under unitary conjugation. -/
theorem numericalRadius_unitary_conjugate (A U : E →L[ℂ] E)
    (hU : U ∈ unitary (E →L[ℂ] E)) :
    numericalRadius (U† * A * U) = numericalRadius A := by
  unfold numericalRadius
  rw [numericalRange_unitary_conjugate A U hU]

/-- Numerical radius is invariant under the alternate orientation of unitary
conjugation. -/
theorem numericalRadius_unitary_conjugate' (A U : E →L[ℂ] E)
    (hU : U ∈ unitary (E →L[ℂ] E)) :
    numericalRadius (U * A * U†) = numericalRadius A := by
  unfold numericalRadius
  rw [numericalRange_unitary_conjugate' A U hU]

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
