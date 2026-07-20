/-
Copyright (c) 2026 Ben Cassie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Cassie
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import LeanPool.Kuramoto.GradientFlow

/-!
# Pairwise contraction

The relative velocity of two oscillators and the resulting pairwise contraction: when the
phase gap lies in `(0, π)` and the coupling is positive, the gap is contracting.
-/

open Real Finset

lemma kuramoto_relative_velocity
    (K : ℝ) (θ : Fin 2 → ℝ) :
    kuramotoF K 2 0 θ - kuramotoF K 2 1 θ = -K * Real.sin (θ 0 - θ 1) := by
  unfold kuramotoF
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [sub_self, Real.sin_zero, zero_add, add_zero]
  have hsin : Real.sin (θ 1 - θ 0) = -Real.sin (θ 0 - θ 1) := by
    have harg : θ 1 - θ 0 = -(θ 0 - θ 1) := by ring
    rw [harg, Real.sin_neg]
  rw [hsin]
  ring

theorem kuramoto_pairwise_contraction
    (K : ℝ) (hK : 0 < K) (θ : Fin 2 → ℝ)
    (hgap : 0 < θ 0 - θ 1) (hpi : θ 0 - θ 1 < Real.pi) :
    kuramotoF K 2 0 θ < kuramotoF K 2 1 θ := by
  have hrel := kuramoto_relative_velocity K θ
  have hsin : 0 < Real.sin (θ 0 - θ 1) :=
    Real.sin_pos_of_pos_of_lt_pi hgap hpi
  have hneg : -K * Real.sin (θ 0 - θ 1) < 0 := by
    nlinarith [mul_pos hK hsin]
  have hsub : kuramotoF K 2 0 θ - kuramotoF K 2 1 θ < 0 := by
    rw [hrel]
    exact hneg
  linarith

-- For any pair (i, j), the contribution of their direct coupling
-- to the relative velocity (F i - F j) is strictly negative
-- when the phase gap is in (0, π) and coupling is positive.
theorem kuramoto_coupling_contraction
    (K : ℝ) (hK : 0 < K)
    (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) (i j : Fin N)
    (hWpos : 0 < W i j)
    (hgap : 0 < θ i - θ j) (hpi : θ i - θ j < Real.pi) :
    K * W i j * Real.sin (θ j - θ i) - K * W j i * Real.sin (θ i - θ j) < 0 := by
  have hsinpos : 0 < Real.sin (θ i - θ j) :=
    Real.sin_pos_of_pos_of_lt_pi hgap hpi
  have hsinneg : Real.sin (θ j - θ i) = -Real.sin (θ i - θ j) := by
    have harg : θ j - θ i = -(θ i - θ j) := by ring
    rw [harg, Real.sin_neg]
  rw [hW j i, hsinneg]
  nlinarith [mul_pos hK hWpos, hsinpos]
