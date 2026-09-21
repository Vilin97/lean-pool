/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Mul
import LeanPool.OperatorTheory.Operator.NumericalRange.Radius

/-!
# Numerical ranges of isometric compressions

If `V : F → E` is an isometry, the compression `V† A V` has numerical range
contained in that of `A`.  Numerical radius is therefore monotone under
isometric compression.
-/

open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The numerical range of an isometric compression is contained in the
original numerical range. -/
theorem numericalRange_compression_subset
    (A : E →L[ℂ] E) (V : F →L[ℂ] E) (hV : Isometry V) :
    numericalRange ((V† ∘L A) ∘L V) ⊆ numericalRange A := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ :=
    (mem_numericalRange ((V† ∘L A) ∘L V) z).mp hz
  have hVnorm : ‖V x‖ = ‖x‖ := by
    calc
      ‖V x‖ = dist (V x) (V 0) := by rw [map_zero, dist_zero_right]
      _ = dist x 0 := hV.dist_eq x 0
      _ = ‖x‖ := by rw [dist_zero_right]
  refine (mem_numericalRange A _).2 ⟨V x, hVnorm.trans hx, ?_⟩
  simp only [ContinuousLinearMap.comp_apply]
  rw [adjoint_inner_right]

/-- General congruence estimate for numerical radius. -/
theorem numericalRadius_adjoint_comp_comp_le
    (A : E →L[ℂ] E) (V : F →L[ℂ] E) :
    numericalRadius ((V† ∘L A) ∘L V) ≤ ‖V‖ ^ 2 * numericalRadius A := by
  unfold numericalRadius
  refine Real.iSup_le (fun z => ?_)
    (mul_nonneg (sq_nonneg ‖V‖) (numericalRadius_nonneg A))
  refine Real.iSup_le (fun hz => ?_)
    (mul_nonneg (sq_nonneg ‖V‖) (numericalRadius_nonneg A))
  obtain ⟨x, hx, rfl⟩ :=
    (mem_numericalRange ((V† ∘L A) ∘L V) z).mp hz
  simp only [ContinuousLinearMap.comp_apply]
  rw [adjoint_inner_right]
  calc
    ‖⟪V x, A (V x)⟫_ℂ‖ ≤ numericalRadius A * ‖V x‖ ^ 2 :=
      norm_inner_apply_self_le_numericalRadius_mul_norm_sq A (V x)
    _ ≤ numericalRadius A * (‖V‖ * ‖x‖) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg (V x)) (V.le_opNorm x) 2)
        (numericalRadius_nonneg A)
    _ = ‖V‖ ^ 2 * numericalRadius A := by rw [hx]; ring

/-- Numerical radius cannot increase under isometric compression. -/
theorem numericalRadius_compression_le
    (A : E →L[ℂ] E) (V : F →L[ℂ] E) (hV : Isometry V) :
    numericalRadius ((V† ∘L A) ∘L V) ≤ numericalRadius A := by
  unfold numericalRadius
  refine Real.iSup_le (fun z => ?_) (numericalRadius_nonneg A)
  refine Real.iSup_le (fun hz => ?_) (numericalRadius_nonneg A)
  exact norm_le_numericalRadius A (numericalRange_compression_subset A V hV hz)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
