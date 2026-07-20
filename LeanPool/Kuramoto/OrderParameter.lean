/-
Copyright (c) 2026 Ben Cassie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Cassie
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Kuramoto order parameter

The Kuramoto order parameter for `N` oscillators with phases `θ : Fin N → ℝ`.
Each oscillator contributes a unit phasor `exp (i θ_k)`, and the main result is the
bound `‖R‖ ≤ 1` where `R = (∑_k exp (i θ_k)) / N`.
-/

open Complex Finset

/-- The Kuramoto order parameter `R = (∑_k exp (i θ_k)) / N`. -/
noncomputable def kuramotoR (N : ℕ) (θ : Fin N → ℝ) : ℂ :=
  (∑ k, Complex.exp (θ k * Complex.I)) / N

theorem kuramotoR_norm_le_one (N : ℕ) (hN : 0 < N) (θ : Fin N → ℝ) :
    ‖kuramotoR N θ‖ ≤ 1 := by
  have hnorm (k : Fin N) : ‖Complex.exp (θ k * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I (θ k)
  have hsum :
      ‖∑ k : Fin N, Complex.exp (θ k * Complex.I)‖ ≤ (N : ℝ) := by
    calc
      ‖∑ k : Fin N, Complex.exp (θ k * Complex.I)‖
          ≤ ∑ k : Fin N, ‖Complex.exp (θ k * Complex.I)‖ := by
            simpa using norm_sum_le (Finset.univ : Finset (Fin N))
              (fun k : Fin N => Complex.exp (θ k * Complex.I))
      _ = (N : ℝ) := by
            simp [hnorm]
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    ‖kuramotoR N θ‖
        = ‖∑ k : Fin N, Complex.exp (θ k * Complex.I)‖ / (N : ℝ) := by
          simp [kuramotoR]
    _ ≤ (N : ℝ) / (N : ℝ) := by
          exact div_le_div_of_nonneg_right hsum hNreal.le
    _ = 1 := div_self hNreal.ne'
