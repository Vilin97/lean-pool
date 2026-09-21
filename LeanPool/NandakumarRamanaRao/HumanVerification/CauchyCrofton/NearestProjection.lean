/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.HumanVerification.CauchyCrofton.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-! # Nearest Projection -/

open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace HumanVerification.CauchyCrofton

/-- A nearest point of `x` in the compact convex body `K`. -/
noncomputable def nearestPoint (K : Body) (x : Point2) : Point2 :=
  Classical.choose
    (exists_norm_eq_iInf_of_complete_convex
      K.nonempty K.isCompact.isComplete K.convex x)

theorem nearestPoint_spec (K : Body) (x : Point2) :
    nearestPoint K x ∈ (K : Set Point2) ∧
      ‖x - nearestPoint K x‖ =
        ⨅ y : (K : Set Point2), ‖x - (y : Point2)‖ :=
  Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex
      K.nonempty K.isCompact.isComplete K.convex x)

@[simp] theorem nearestPoint_mem (K : Body) (x : Point2) :
    nearestPoint K x ∈ (K : Set Point2) :=
  (nearestPoint_spec K x).1

/-- Variational characterization of the nearest point. -/
theorem nearestPoint_inner_le_zero (K : Body) (x : Point2)
    {y : Point2} (hy : y ∈ (K : Set Point2)) :
    inner ℝ (x - nearestPoint K x) (y - nearestPoint K x) ≤ 0 := by
  exact
    (norm_eq_iInf_iff_real_inner_le_zero K.convex
      (nearestPoint_mem K x)).mp (nearestPoint_spec K x).2 y hy

/-- Nearest-point projection fixes every point of the body. -/
@[simp] theorem nearestPoint_eq_self (K : Body) {x : Point2}
    (hx : x ∈ (K : Set Point2)) : nearestPoint K x = x := by
  have h := nearestPoint_inner_le_zero K x hx
  have hnorm : ‖x - nearestPoint K x‖ ^ 2 ≤ 0 := by
    simpa [real_inner_self_eq_norm_sq] using h
  have hzero : ‖x - nearestPoint K x‖ = 0 := by nlinarith [norm_nonneg (x - nearestPoint K x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

/-- The metric projection onto a closed convex set is nonexpansive. -/
theorem dist_nearestPoint_le (K : Body) (x y : Point2) :
    dist (nearestPoint K x) (nearestPoint K y) ≤ dist x y := by
  let px := nearestPoint K x
  let py := nearestPoint K y
  have hx := nearestPoint_inner_le_zero K x (nearestPoint_mem K y)
  have hy := nearestPoint_inner_le_zero K y (nearestPoint_mem K x)
  have hquad : ‖px - py‖ ^ 2 ≤ inner ℝ (x - y) (px - py) := by
    have h1 : inner ℝ (x - px) (py - px) ≤ 0 := by simpa [px, py] using hx
    have h2 : inner ℝ (y - py) (px - py) ≤ 0 := by simpa [px, py] using hy
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢
    have hcomm : (inner ℝ px py : ℝ) = inner ℝ py px := real_inner_comm _ _
    linarith
  have hcs : inner ℝ (x - y) (px - py) ≤ ‖x - y‖ * ‖px - py‖ :=
    real_inner_le_norm _ _
  have hnonneg : 0 ≤ ‖px - py‖ := norm_nonneg _
  have : ‖px - py‖ ≤ ‖x - y‖ := by
    by_cases hz : ‖px - py‖ = 0
    · simp [hz]
    · have hp : 0 < ‖px - py‖ := lt_of_le_of_ne hnonneg (Ne.symm hz)
      nlinarith
  simpa [dist_eq_norm, px, py] using this

/-- The nearest-point projection is globally one-Lipschitz. -/
theorem lipschitz_nearestPoint (K : Body) :
    LipschitzWith 1 (nearestPoint K) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa using dist_nearestPoint_le K x y

end HumanVerification.CauchyCrofton
