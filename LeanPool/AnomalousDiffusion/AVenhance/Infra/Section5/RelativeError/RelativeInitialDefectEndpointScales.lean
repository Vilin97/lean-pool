/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectEndpoint

/-! Scalar absorption of the actual endpoint source coefficients. The same
estimate includes the terminal one-letter level; there is no extra derivative
or time-zero regularity assumption. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5.RelativeError

/-- Each endpoint coefficient is bounded uniformly in both finite indices. -/
theorem relative_initial_endpoint_coefficient_le {a e κ ν τ τP Cq Cg K L S : ℝ}
    (he : 0 < e) (hκ : 0 < κ) (hν : 0 < ν) (hτ : 0 < τ) (hτP : 0 < τP)
    (hCq : 0 ≤ Cq) (hCg : 0 ≤ Cg) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hRatio : e ^ 2 / (κ * τ) ≤ 1) (hTime : 8 * τ / τP ≤ 1)
    (hX : a ^ 2 * e ^ 4 / κ ≤ K * ν) (n r : ℕ) :
    8 * (Cq * (a ^ 2 * e ^ 2) * (e ^ 2 / (κ * τ)) ^ n * (8 * τ) ^ r) *
        (Cg * S * (e ^ 2 / κ) / Real.sqrt ν * L * (τP⁻¹) ^ r) ≤
      8 * Cq * Cg * K * Real.sqrt ν * L * S := by
  have hroot : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hn : (e ^ 2 / (κ * τ)) ^ n ≤ 1 :=
    pow_le_one₀ (by positivity) hRatio
  have hr : (8 * τ / τP) ^ r ≤ 1 := pow_le_one₀ (by positivity) hTime
  have hnr : (e ^ 2 / (κ * τ)) ^ n * (8 * τ / τP) ^ r ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hn hr (by positivity) (by norm_num)
      _ = 1 := one_mul 1
  have hXroot : (a ^ 2 * e ^ 4 / κ) / Real.sqrt ν ≤ K * Real.sqrt ν := by
    apply (div_le_iff₀ hroot).2
    calc
      _ ≤ K * ν := hX
      _ = (K * Real.sqrt ν) * Real.sqrt ν := by
        rw [mul_assoc, ← pow_two, Real.sq_sqrt hν.le]
  have htimeEq : (8 * τ) ^ r * (τP⁻¹) ^ r = (8 * τ / τP) ^ r := by
    rw [← mul_pow, div_eq_mul_inv]
  have hf : 0 ≤ 8 * Cq * Cg * L * S := by positivity
  have hbase : 0 ≤ (a ^ 2 * e ^ 4 / κ) / Real.sqrt ν := by positivity
  calc
    _ = (8 * Cq * Cg * L * S) * ((a ^ 2 * e ^ 4 / κ) / Real.sqrt ν) *
        ((e ^ 2 / (κ * τ)) ^ n * (8 * τ / τP) ^ r) := by
      rw [show (8 * τ / τP) ^ r = (8 * τ) ^ r * (τP⁻¹) ^ r from htimeEq.symm]
      ring
    _ ≤ (8 * Cq * Cg * L * S) * ((a ^ 2 * e ^ 4 / κ) / Real.sqrt ν) * 1 :=
      mul_le_mul_of_nonneg_left hnr (mul_nonneg hf hbase)
    _ ≤ (8 * Cq * Cg * L * S) * (K * Real.sqrt ν) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left hXroot hf
    _ = _ := by ring

/-- The finite endpoint source coefficient sum has a constant independent of r. -/
theorem relative_initial_endpoint_coefficient_sum_le {a e κ ν τ τP Cq Cg K L S : ℝ}
    (he : 0 < e) (hκ : 0 < κ) (hν : 0 < ν) (hτ : 0 < τ) (hτP : 0 < τP)
    (hCq : 0 ≤ Cq) (hCg : 0 ≤ Cg) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hRatio : e ^ 2 / (κ * τ) ≤ 1) (hTime : 8 * τ / τP ≤ 1)
    (hX : a ^ 2 * e ^ 4 / κ ≤ K * ν) (N r : ℕ) :
    (∑ n ∈ Finset.range N,
      ENNReal.ofReal (8 * (Cq * (a ^ 2 * e ^ 2) * (e ^ 2 / (κ * τ)) ^ n * (8 * τ) ^ r) *
        (Cg * S * (e ^ 2 / κ) / Real.sqrt ν * L * (τP⁻¹) ^ r))) ≤
      ENNReal.ofReal ((N : ℝ) * (8 * Cq * Cg * K * Real.sqrt ν * L * S)) := by
  calc
    _ ≤ ∑ _n ∈ Finset.range N,
        ENNReal.ofReal (8 * Cq * Cg * K * Real.sqrt ν * L * S) := by
      apply Finset.sum_le_sum
      intro n _
      exact ENNReal.ofReal_le_ofReal (relative_initial_endpoint_coefficient_le
        he hκ hν hτ hτP hCq hCg hL hS hRatio hTime hX n r)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]

end AVenhance.Infra.Section5.RelativeError
