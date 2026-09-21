/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Limits along positive real parameters

This module provides elementary filter limits for positive real resolvent
parameters and a filter-generic criterion that turns a vanishing square bound
into convergence to zero.
-/

namespace MarkovProcess.Semigroup

open Filter Set Topology

/-- Positive real parameters, ordered by their underlying real values. -/
abbrev PositiveShift := Set.Ioi (0 : ℝ)

/-- Positive parameters tend to infinity in the ambient real line. -/
theorem tendsto_positiveShift_coe_atTop :
    Tendsto (fun α : PositiveShift ↦ (α : ℝ)) atTop atTop := by
  exact (tendsto_comp_val_Ioi_atTop (a := (0 : ℝ))).2 tendsto_id

/-- The inverse of a positive parameter tends to zero as the parameter tends to infinity. -/
theorem tendsto_positiveShift_inv_atTop_zero :
    Tendsto (fun α : PositiveShift ↦ (α : ℝ)⁻¹) atTop (nhds 0) := by
  exact (tendsto_comp_val_Ioi_atTop (a := (0 : ℝ))).2 tendsto_inv_atTop_zero

/-- A fixed real constant times the inverse parameter tends to zero. -/
theorem tendsto_const_mul_positiveShift_inv_atTop_zero (C : ℝ) :
    Tendsto (fun α : PositiveShift ↦ C * (α : ℝ)⁻¹) atTop (nhds 0) := by
  simpa only [mul_zero] using
    (tendsto_const_nhds (x := C)).mul tendsto_positiveShift_inv_atTop_zero

/-- A nonnegative quantity tends to zero if its square is bounded by a quantity
that tends to zero. This avoids introducing square roots in limit estimates. -/
theorem tendsto_zero_of_nonneg_sq_le {ι : Type*} {l : Filter ι}
    {e r : ι → ℝ}
    (he : ∀ i, 0 ≤ e i)
    (her : ∀ i, (e i) ^ 2 ≤ r i)
    (hr : Tendsto r l (nhds 0)) :
    Tendsto e l (nhds 0) := by
  rw [Metric.tendsto_nhds] at hr ⊢
  intro ε hε
  filter_upwards [hr (ε ^ 2) (sq_pos_of_pos hε)] with i hi
  have he_sq_lt : (e i) ^ 2 < ε ^ 2 := by
    calc
      (e i) ^ 2 ≤ r i := her i
      _ ≤ |r i| := le_abs_self (r i)
      _ = dist (r i) 0 := by rw [Real.dist_eq, sub_zero]
      _ < ε ^ 2 := hi
  have he_lt : e i < ε :=
    (sq_lt_sq₀ (he i) hε.le).1 he_sq_lt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (he i)]
  exact he_lt

end MarkovProcess.Semigroup
