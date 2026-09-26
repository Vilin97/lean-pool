/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Constants for the fractional Sobolev versus Besov comparison

Every numeric fact used by the `W^{s,p}` versus `B^s_{p,p}` equivalence is
proved here, once, with explicit hypotheses.  The proof files consume these
lemmas with `exact`; no `positivity`/`nlinarith` grinding happens outside this
file.

Uniformity ledger (each bound is uniform in `s ∈ (0,1)` and `p ∈ [1,∞)`, so
the final equivalence constant depends on the dimension only):

* geometric tails have ratio at most `3⁻¹`, hence sum at most `3/2 ≤ 2`;
* the kernel-insertion prefactor `3^{d/p+s}` is at most `3^{d+1}`;
* the triangle-splitting factor `(2^{p-1})^{1/p}` is at most `2`.
-/

@[expose] public section

namespace Homogenization
namespace Gagliardo

open scoped ENNReal

/-- Geometric series with ratio at most `3⁻¹` sums to at most `2` in `ℝ≥0∞`. -/
theorem tsum_pow_le_two_of_le_third {c : ℝ≥0∞} (hc : c ≤ 3⁻¹) :
    (∑' n : ℕ, c ^ n) ≤ 2 := by
  have hc2 : c ≤ 2⁻¹ :=
    hc.trans (ENNReal.inv_le_inv.2 (by norm_num))
  have hsum : (∑' n : ℕ, c ^ n) ≤ ∑' n : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ n :=
    ENNReal.tsum_le_tsum fun n => pow_le_pow_left' hc2 n
  refine hsum.trans ?_
  rw [ENNReal.tsum_geometric]
  have hhalf : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ :=
    ENNReal.sub_eq_of_eq_add (by simp) ENNReal.inv_two_add_inv_two.symm
  rw [hhalf, inv_inv]

/-- Finite geometric sums with ratio at most `3⁻¹` are at most `2` in `ℝ≥0∞`. -/
theorem sum_range_pow_le_two_of_le_third {c : ℝ≥0∞} (hc : c ≤ 3⁻¹) (N : ℕ) :
    (∑ n ∈ Finset.range N, c ^ n) ≤ 2 :=
  (ENNReal.sum_le_tsum (Finset.range N)).trans (tsum_pow_le_two_of_le_third hc)

/-- The kernel-insertion prefactor collapses to a dimensional constant:
`3^{d/p + s} ≤ 3^{d+1}` for `s < 1 ≤ p`, in `ℝ≥0∞`. -/
theorem rpow_three_kernel_exponent_le {d : ℕ} {s pr : ℝ}
    (hs : s < 1) (hp : 1 ≤ pr) :
    (3 : ℝ≥0∞) ^ ((d : ℝ) / pr + s) ≤ (3 : ℝ≥0∞) ^ ((d : ℝ) + 1) := by
  refine ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hd : (d : ℝ) / pr ≤ (d : ℝ) := by
    apply div_le_self (Nat.cast_nonneg d) hp
  linarith

/-- Triangle-splitting cost after the `p`-th root: `(2^{p-1})^{1/p} ≤ 2`
for `p ≥ 1`, phrased in `ℝ≥0∞`. -/
theorem rpow_two_sub_one_div_le_two {pr : ℝ} (hp : 1 ≤ pr) :
    (2 : ℝ≥0∞) ^ ((pr - 1) * (1 / pr)) ≤ 2 := by
  have hexp : (pr - 1) * (1 / pr) ≤ 1 := by
    have hpr : 0 < pr := lt_of_lt_of_le one_pos hp
    rw [mul_one_div, div_le_one hpr]
    linarith
  calc (2 : ℝ≥0∞) ^ ((pr - 1) * (1 / pr)) ≤ (2 : ℝ≥0∞) ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = 2 := by simp

/-- Monotone collapse for powers of three with bounded exponent, `ℝ≥0∞` form. -/
theorem rpow_three_le_rpow_three {a b : ℝ} (h : a ≤ b) :
    (3 : ℝ≥0∞) ^ a ≤ (3 : ℝ≥0∞) ^ b :=
  ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) h

/-- `3^x` is positive (nonzero) in `ℝ≥0∞`. -/
theorem rpow_three_ne_zero (x : ℝ) : (3 : ℝ≥0∞) ^ x ≠ 0 := by
  simp [ENNReal.rpow_eq_zero_iff]

/-- `3^x` is finite in `ℝ≥0∞`. -/
theorem rpow_three_ne_top (x : ℝ) : (3 : ℝ≥0∞) ^ x ≠ ∞ := by
  simp [ENNReal.rpow_eq_top_iff]

end Gagliardo
end Homogenization
