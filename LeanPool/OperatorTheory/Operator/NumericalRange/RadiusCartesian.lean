/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.NumericalRange.RadiusAdjoint
public import LeanPool.OperatorTheory.Operator.NumericalRange.RadiusNormal

/-!
# Cartesian-part bounds from numerical radius

The selfadjoint and skew-adjoint numerators of an operator are each bounded
in norm by twice its numerical radius.
-/

@[expose] public section

open Complex ContinuousLinearMap
open scoped InnerProductSpace InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The selfadjoint numerator `A + A†` has norm at most `2w(A)`. -/
theorem norm_add_adjoint_le_two_mul_numericalRadius (A : E →L[ℂ] E) :
    ‖A + A†‖ ≤ 2 * numericalRadius A := by
  have hself : IsSelfAdjoint (A + A†) := IsSelfAdjoint.add_star_self A
  rw [← numericalRadius_eq_norm_of_isSelfAdjoint (A + A†) hself]
  calc
    numericalRadius (A + A†) ≤ numericalRadius A + numericalRadius (A†) :=
      numericalRadius_add_le A (A†)
    _ = 2 * numericalRadius A := by rw [numericalRadius_adjoint]; ring

/-- The skew-adjoint numerator `A - A†` has norm at most `2w(A)`. -/
theorem norm_sub_adjoint_le_two_mul_numericalRadius (A : E →L[ℂ] E) :
    ‖A - A†‖ ≤ 2 * numericalRadius A := by
  have hskew' : A - star A ∈ skewAdjoint (E →L[ℂ] E) := by
    rw [skewAdjoint.mem_iff]
    rw [star_sub, star_star]
    module
  have hskew : A - A† ∈ skewAdjoint (E →L[ℂ] E) := by
    simpa only [star_eq_adjoint] using hskew'
  let _ : IsStarNormal (A - A†) :=
    skewAdjoint.isStarNormal_of_mem hskew
  calc
    ‖A - A†‖ = numericalRadius (A - A†) :=
      (numericalRadius_eq_norm_of_isStarNormal (A - A†)).symm
    _ ≤ numericalRadius A + numericalRadius (A†) :=
      numericalRadius_sub_le A (A†)
    _ = 2 * numericalRadius A := by rw [numericalRadius_adjoint]; ring

/-- The selfadjoint Cartesian part has norm at most the numerical radius. -/
theorem norm_inv_two_smul_add_adjoint_le_numericalRadius
    (A : E →L[ℂ] E) :
    ‖(2 : ℂ)⁻¹ • (A + A†)‖ ≤ numericalRadius A := by
  have hc : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  calc
    ‖(2 : ℂ)⁻¹ • (A + A†)‖ = (2 : ℝ)⁻¹ * ‖A + A†‖ := by
      rw [norm_smul, hc]
    _ ≤ (2 : ℝ)⁻¹ * (2 * numericalRadius A) :=
      mul_le_mul_of_nonneg_left
        (norm_add_adjoint_le_two_mul_numericalRadius A) (by positivity)
    _ = numericalRadius A := by ring

/-- The skew-adjoint Cartesian part has norm at most the numerical radius. -/
theorem norm_inv_two_smul_sub_adjoint_le_numericalRadius
    (A : E →L[ℂ] E) :
    ‖(2 : ℂ)⁻¹ • (A - A†)‖ ≤ numericalRadius A := by
  have hc : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  calc
    ‖(2 : ℂ)⁻¹ • (A - A†)‖ = (2 : ℝ)⁻¹ * ‖A - A†‖ := by
      rw [norm_smul, hc]
    _ ≤ (2 : ℝ)⁻¹ * (2 * numericalRadius A) :=
      mul_le_mul_of_nonneg_left
        (norm_sub_adjoint_le_two_mul_numericalRadius A) (by positivity)
    _ = numericalRadius A := by ring

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
