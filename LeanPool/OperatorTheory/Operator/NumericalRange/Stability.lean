/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Operator-norm stability of the numerical range

Using the same unit-vector witness for two operators shows that their
numerical ranges mutually approximate one another to within the
operator-norm distance.
-/
import LeanPool.OperatorTheory.Operator.NumericalRange.Bounded

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Every point of `W(A)` is within `‖A-B‖` of a point of `W(B)`. -/
theorem exists_mem_numericalRange_norm_sub_le_norm_sub
    (A B : E →L[ℂ] E) {z : ℂ} (hz : z ∈ numericalRange A) :
    ∃ w ∈ numericalRange B, ‖z - w‖ ≤ ‖A - B‖ := by
  obtain ⟨x, hx, rfl⟩ := (mem_numericalRange A z).mp hz
  refine ⟨⟪x, B x⟫_ℂ, (mem_numericalRange B _).2 ⟨x, hx, rfl⟩, ?_⟩
  calc
    ‖⟪x, A x⟫_ℂ - ⟪x, B x⟫_ℂ‖ = ‖⟪x, (A - B) x⟫_ℂ‖ := by
      simp only [sub_apply, inner_sub_right]
    _ ≤ ‖x‖ * ‖(A - B) x‖ := norm_inner_le_norm x _
    _ = ‖(A - B) x‖ := by rw [hx, one_mul]
    _ ≤ ‖A - B‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖A - B‖ := by rw [hx, mul_one]

/-- Symmetric form: the numerical ranges of `A` and `B` mutually
approximate one another within their operator-norm distance. -/
theorem numericalRange_mutually_approximates
    (A B : E →L[ℂ] E) :
    (∀ z ∈ numericalRange A,
        ∃ w ∈ numericalRange B, ‖z - w‖ ≤ ‖A - B‖) ∧
      (∀ w ∈ numericalRange B,
        ∃ z ∈ numericalRange A, ‖w - z‖ ≤ ‖A - B‖) := by
  constructor
  · exact fun _ hz => exists_mem_numericalRange_norm_sub_le_norm_sub A B hz
  · intro w hw
    obtain ⟨z, hz, hdist⟩ :=
      exists_mem_numericalRange_norm_sub_le_norm_sub B A hw
    refine ⟨z, hz, ?_⟩
    exact hdist.trans_eq (norm_sub_rev B A)

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
