/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Analysis.Normed.Affine.MazurUlam

/-! # From punctured derivative bounds to a linear isometry -/

@[expose] public noncomputable section
open Set
namespace LichnerowiczObata

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- For a norm-preserving map, the origin need not be differentiable in the
mean-value argument: segments through zero are controlled by the triangle
inequality and the equality of the two radial lengths. -/
theorem norm_sub_le_of_norm_preserving_derivative_off_zero
    {F : P → V} (hnorm : ∀ x, ‖F x‖ = ‖x‖)
    (hd : ∀ x ≠ 0, DifferentiableAt ℝ F x)
    (hbound : ∀ x ≠ 0, ‖fderiv ℝ F x‖ ≤ 1) (x y : P) :
    ‖F y - F x‖ ≤ ‖y - x‖ := by
  by_cases hzero : (0 : P) ∈ segment ℝ x y
  · have hlen := dist_add_dist_of_mem_segment hzero
    have hsum : ‖y‖ + ‖x‖ = ‖y - x‖ := by
      simpa only [dist_zero_right, dist_zero_left, dist_eq_norm, sub_zero, norm_sub_rev, add_comm]
        using hlen
    calc
      ‖F y - F x‖ ≤ ‖F y‖ + ‖F x‖ := norm_sub_le _ _
      _ = ‖y‖ + ‖x‖ := by rw [hnorm, hnorm]
      _ = ‖y - x‖ := hsum
  · have hne : ∀ z ∈ segment ℝ x y, z ≠ 0 := by
      intro z hz h
      exact hzero (h ▸ hz)
    simpa only [one_mul] using
      (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
        (fun z hz => hd z (hne z hz)) (fun z hz => hbound z (hne z hz))
        (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)

/-- A norm-preserving equivalence with derivative norm at most one away
from zero in both directions is the underlying map of a real linear isometry. -/
theorem exists_linearIsometryEquiv_of_norm_preserving_derivative_off_zero
    (F : P ≃ V) (hnorm : ∀ x, ‖F x‖ = ‖x‖)
    (hd : ∀ x ≠ 0, DifferentiableAt ℝ F x)
    (hbound : ∀ x ≠ 0, ‖fderiv ℝ F x‖ ≤ 1)
    (hdi : ∀ y ≠ 0, DifferentiableAt ℝ F.symm y)
    (hboundi : ∀ y ≠ 0, ‖fderiv ℝ F.symm y‖ ≤ 1) :
    ∃ L : P ≃ₗᵢ[ℝ] V, ∀ x, L x = F x := by
  have hnormi : ∀ y, ‖F.symm y‖ = ‖y‖ := by
    intro y
    simpa only [F.apply_symm_apply] using (hnorm (F.symm y)).symm
  have hiso : Isometry F := by
    apply isometry_iff_dist_eq.mpr
    intro x y
    simp only [dist_eq_norm]
    apply le_antisymm
    · exact norm_sub_le_of_norm_preserving_derivative_off_zero hnorm hd hbound y x
    · simpa only [F.symm_apply_apply] using
        norm_sub_le_of_norm_preserving_derivative_off_zero hnormi hdi hboundi (F y) (F x)
  let e : P ≃ᵢ V := ⟨F, hiso⟩
  have h0 : e 0 = 0 := by
    change F 0 = 0
    exact norm_eq_zero.mp (by simpa only [norm_zero] using hnorm 0)
  exact ⟨e.toRealLinearIsometryEquivOfMapZero h0, fun _ => rfl⟩

end LichnerowiczObata
