/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Core.NesterovScheme

/-!
# Bootstrap Step 1: Geometric Decay by Induction

If Lₙ₊₁ ≤ c · Lₙ whenever a predicate P(n) holds, and P is preserved,
then Lₙ ≤ cⁿ · L₀.

## Geometric Series Sum
S_a = Σ_{k=0}^∞ (1-a/2)^{k/2} = 1/(1-√(1-a/2)) is finite for a > 0.

## Total Displacement Control
Σ_{k=1}^n ‖h_k‖ ≤ C_h √η Σ_{k=1}^n √L_k ≤ C_h √η · R · S_a
-/

noncomputable section

namespace PLAcceleratedNesterovLean

/-- Geometric decay: if f(n+1) ≤ c * f(n) for all n, then f(n) ≤ c^n * f(0). -/
theorem geometric_decay (f : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hstep : ∀ n, f (n + 1) ≤ c * f n) :
    ∀ n, f n ≤ c ^ n * f 0 := by
  intro n
  induction n with
  | zero => simp only [pow_zero, one_mul, le_refl]
  | succ n ih =>
    calc f (n + 1) ≤ c * f n := hstep n
      _ ≤ c * (c ^ n * f 0) := by gcongr
      _ = c ^ (n + 1) * f 0 := by ring

/-- Geometric decay with invariant: if contraction holds whenever P(n) is true,
    and P is preserved, then both the invariant and the decay hold for all n. -/
theorem geometric_decay_with_invariant (f : ℕ → ℝ) (P : ℕ → Prop)
    (c : ℝ) (hc : 0 ≤ c) (_hc1 : c ≤ 1) (_hf0 : 0 ≤ f 0)
    (hP0 : P 0)
    (hstep : ∀ n, P n → f (n + 1) ≤ c * f n ∧ P (n + 1)) :
    ∀ n, P n ∧ f n ≤ c ^ n * f 0 := by
  intro n
  induction n with
  | zero => exact ⟨hP0, by simp only [pow_zero, one_mul, le_refl]⟩
  | succ n ih =>
    obtain ⟨hPn, hfn⟩ := ih
    obtain ⟨hfn1, hPn1⟩ := hstep n hPn
    refine ⟨hPn1, ?_⟩
    calc f (n + 1) ≤ c * f n := hfn1
      _ ≤ c * (c ^ n * f 0) := by nlinarith [pow_nonneg hc n]
      _ = c ^ (n + 1) * f 0 := by ring

/-- Partial geometric series: Σ_{k=0}^{n-1} r^k ≤ 1/(1-r) for 0 ≤ r < 1. -/
theorem partial_geom_series_bound (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (Finset.range n).sum (fun k => r ^ k) ≤ 1 / (1 - r) := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hr_ne : r ≠ 1 := ne_of_lt hr1
  rw [geom_sum_eq hr_ne]
  -- Goal: (r ^ n - 1) / (r - 1) ≤ 1 / (1 - r)
  have h3 : r - 1 ≠ 0 := by linarith
  have h4 : (1 : ℝ) - r ≠ 0 := ne_of_gt h1r
  have key : (r ^ n - 1) / (r - 1) = (1 - r ^ n) / (1 - r) := by
    rw [div_eq_div_iff h3 h4]; ring
  rw [key]
  -- Goal: (1 - r ^ n) / (1 - r) ≤ 1 / (1 - r)
  apply div_le_div_of_nonneg_right _ (le_of_lt h1r)
  linarith [pow_nonneg hr0 n]

/-- Telescoping sum: ‖x_{n+1} - x_1‖ ≤ Σ_{k=0}^{n-1} ‖x_{k+1} - x_k‖. -/
theorem telescoping_norm_bound {d : ℕ} (x : ℕ → E d) (n : ℕ) :
    ‖x n - x 0‖ ≤ (Finset.range n).sum (fun k => ‖x (k + 1) - x k‖) := by
  induction n with
  | zero => simp only [sub_self, norm_zero, Finset.range_zero, Finset.sum_empty, le_refl]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc ‖x (n + 1) - x 0‖
        = ‖(x (n + 1) - x n) + (x n - x 0)‖ := by congr 1; abel
      _ ≤ ‖x (n + 1) - x n‖ + ‖x n - x 0‖ := norm_add_le _ _
      _ ≤ ‖x (n + 1) - x n‖ + (Finset.range n).sum (fun k => ‖x (k + 1) - x k‖) := by
          gcongr
      _ = _ := by abel

end PLAcceleratedNesterovLean
