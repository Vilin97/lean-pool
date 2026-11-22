/-
Copyright (c) 2026 Weighted Horn Cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weighted Horn Cores contributors
-/
module

public import LeanPool.WeightedHornCores.Budget
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A real exponential bound for the capacity

The tangent inequality for the exponential controls the linear interpolation within each
period, at the cost of a factor `1 / Real.log 2`.
-/

@[expose] public section

namespace WeightedHornCores

/-- Real exponential upper bound for the discrete capacity at any positive period. -/
theorem capacity_le_rpow {p : ℕ} (hp : 0 < p) (t : ℕ) :
    (capacity p t : ℝ) ≤ ((p : ℝ) / Real.log 2) * (2 : ℝ) ^ ((t : ℝ) / p) := by
  let d := t / p
  let s := ((t % p : ℕ) : ℝ) / p
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hs : s * p = (t % p : ℕ) := div_mul_cancel₀ _ hp'.ne'
  have ht : (t : ℝ) / p = (d : ℝ) + s := by
    apply (div_eq_iff hp'.ne').2
    rw [add_mul, hs, mul_comm (d : ℝ), add_comm]
    exact_mod_cast (Nat.mod_add_div t p).symm
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_le : Real.log 2 ≤ 1 := by
    calc
      Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
  have hfrac : 1 + s ≤ (2 : ℝ) ^ s / Real.log 2 := by
    apply (le_div_iff₀ hlog).2
    calc
      (1 + s) * Real.log 2 = Real.log 2 + s * Real.log 2 := by rw [add_mul, one_mul]
      _ ≤ 1 + s * Real.log 2 := add_le_add hlog_le le_rfl
      _ = Real.log 2 * s + 1 := by ring
      _ ≤ Real.exp (Real.log 2 * s) := Real.add_one_le_exp _
      _ = (2 : ℝ) ^ s := (Real.rpow_def_of_pos (by norm_num) s).symm
  have hbase : (p : ℝ) + (t % p : ℕ) = (1 + s) * p := by rw [add_mul, one_mul, hs]
  rw [ht, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  simp only [capacity, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, hbase]
  calc
    (1 + s) * p * (2 : ℝ) ^ d ≤ ((2 : ℝ) ^ s / Real.log 2) * p * (2 : ℝ) ^ d :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfrac hp'.le) (by positivity)
    _ = _ := by ring

end WeightedHornCores
