/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Comparing exponential bases with polynomial factors

A fixed polynomial factor cannot compensate for a larger exponential
base. This form applies directly to tensor-dimension estimates.
-/

@[expose] public section

namespace RS

/-- An exponential bounded by another exponential times a fixed
polynomial has no larger base. -/
theorem le_of_pow_le_pow_mul_polynomial (a b d : ℕ)
    (h : ∀ n : ℕ, a ^ n ≤ b ^ n * (n + 1) ^ d) : a ≤ b := by
  by_contra hab
  have hba : b < a := by omega
  have ha : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  by_cases hb : b = 0
  · have h1 := h 1
    simp [hb] at h1
    omega
  have hbpos : (0 : ℝ) < b := by
    exact_mod_cast Nat.pos_of_ne_zero hb
  let r : ℝ := b / a
  have hrpos : 0 < r := div_pos hbpos ha
  have hrlt : r < 1 := by
    rw [div_lt_one ha]
    exact_mod_cast hba
  have hlim : Filter.Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ d * r ^ n)
      Filter.atTop (nhds 0) := by
    have ht := ((tendsto_pow_const_mul_const_pow_of_lt_one d
      hrpos.le hrlt).comp (Filter.tendsto_add_atTop_nat 1)).div_const r
    simpa [Function.comp_def, pow_succ, ← mul_assoc, hrpos.ne'] using ht
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds
    (show (0 : ℝ) < 1 by norm_num))).exists
  have hreal : (a : ℝ) ^ n ≤ (b : ℝ) ^ n * (n + 1 : ℝ) ^ d := by
    exact_mod_cast h n
  have hquot : 1 ≤ (n + 1 : ℝ) ^ d * r ^ n := by
    dsimp only [r]
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos ha n)).mpr
    simpa [mul_comm] using hreal
  exact (not_lt_of_ge hquot) (by exact_mod_cast hn)

/-- Taking even roots removes a fixed polynomial loss from an
exponential sandwich, including when the exponential base is zero. -/
theorem tendsto_even_root_of_polynomial_bounds
    (a : ℕ → ℕ) (d c : ℕ)
    (hlower : ∀ n, d ^ (2 * n) ≤ a n * (n + 1) ^ c)
    (hupper : ∀ n, a n ≤ d ^ (2 * n)) :
    Filter.Tendsto (fun n => (a n : ℝ) ^ ((2 * n : ℕ) : ℝ)⁻¹)
      Filter.atTop (nhds (d : ℝ)) := by
  let p : ℕ → ℝ := fun n =>
    (n + 1 : ℝ) ^ ((c : ℝ) / (2 * n))
  have hpoly : Filter.Tendsto p Filter.atTop (nhds 1) := by
    have h := (tendsto_rpow_div_mul_add (c : ℝ) 2 (-2)
      (by norm_num)).comp
      (tendsto_natCast_atTop_atTop.comp
        (Filter.tendsto_add_atTop_nat 1))
    convert h using 1
    funext n
    simp only [p, Function.comp_apply, Nat.cast_add, Nat.cast_one]
    congr 2
    ring
  have hlowerLimit : Filter.Tendsto (fun n => (d : ℝ) / p n)
      Filter.atTop (nhds (d : ℝ)) := by
    have hlim := (tendsto_const_nhds (x := (d : ℝ))).div hpoly (by norm_num)
    change Filter.Tendsto (fun n ↦ (d : ℝ) / p n) Filter.atTop
      (nhds ((d : ℝ) / 1)) at hlim
    simpa only [div_one] using hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerLimit tendsto_const_nhds
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnzero : 2 * n ≠ 0 := by omega
    have hp : 0 < p n := Real.rpow_pos_of_pos (by positivity) _
    apply (div_le_iff₀ hp).mpr
    have hreal : (d : ℝ) ^ (2 * n) ≤
        (a n : ℝ) * (n + 1 : ℝ) ^ c := by
      exact_mod_cast hlower n
    have h := Real.rpow_le_rpow (by positivity) hreal
      (show (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ)⁻¹ by positivity)
    rw [Real.pow_rpow_inv_natCast (by positivity) hnzero,
      Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast (n + 1 : ℝ) c,
      ← Real.rpow_mul (by positivity)] at h
    simpa [p, div_eq_mul_inv, Nat.cast_mul] using h
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnzero : 2 * n ≠ 0 := by omega
    have hreal : (a n : ℝ) ≤ (d : ℝ) ^ (2 * n) := by
      exact_mod_cast hupper n
    have h := Real.rpow_le_rpow (by positivity) hreal
      (show (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ)⁻¹ by positivity)
    simpa only [Real.pow_rpow_inv_natCast
      (show (0 : ℝ) ≤ d by positivity) hnzero] using h

end RS
