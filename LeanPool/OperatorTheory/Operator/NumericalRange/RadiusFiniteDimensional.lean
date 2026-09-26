/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.NumericalRange.Compact
public import LeanPool.OperatorTheory.Operator.NumericalRange.Radius

/-!
# Attainment of numerical radius in finite dimension

In a nontrivial finite-dimensional Hilbert space the numerical range is a
nonempty compact set, so its norm achieves the numerical radius.
-/

@[expose] public section

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Nontrivial E]

/-- In finite dimension, some point of the numerical range has modulus equal
to the numerical radius. -/
theorem exists_mem_numericalRange_norm_eq_numericalRadius
    (A : E →L[ℂ] E) :
    ∃ z ∈ numericalRange A, ‖z‖ = numericalRadius A := by
  obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hW : (numericalRange A).Nonempty := by
    refine ⟨⟪x, A x⟫_ℂ, ?_⟩
    rw [numericalRange_eq_image]
    exact ⟨x, hx, rfl⟩
  obtain ⟨z, hz, hmax⟩ :=
    (isCompact_numericalRange A).exists_isMaxOn hW continuous_norm.continuousOn
  refine ⟨z, hz, le_antisymm (norm_le_numericalRadius A hz) ?_⟩
  unfold numericalRadius
  exact Real.iSup_le (fun w => Real.iSup_le (fun hw => hmax hw) (norm_nonneg z))
    (norm_nonneg z)

/-- In finite dimension, a unit vector attains the numerical radius. -/
theorem exists_norm_eq_one_norm_inner_apply_eq_numericalRadius
    (A : E →L[ℂ] E) :
    ∃ x : E, ‖x‖ = 1 ∧ ‖⟪x, A x⟫_ℂ‖ = numericalRadius A := by
  obtain ⟨z, hz, hnorm⟩ :=
    exists_mem_numericalRange_norm_eq_numericalRadius A
  obtain ⟨x, hx, rfl⟩ := (mem_numericalRange A z).mp hz
  exact ⟨x, hx, hnorm⟩

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
