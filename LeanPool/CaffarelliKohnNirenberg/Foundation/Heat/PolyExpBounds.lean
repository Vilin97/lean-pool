/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Tactic.Positivity

/-!
# Poly Exp Bounds

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

noncomputable section

namespace CKN.Foundation.Heat

/-- For nonnegative `a` and `k : ℕ`, `a ^ k * exp(-a) ≤ k!`. -/
theorem exp_poly_bound {k : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    a ^ k * Real.exp (-a) ≤ (k.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp a ha k
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  have hmul : a ^ k ≤ Real.exp a * (k.factorial : ℝ) := (div_le_iff₀ hfac).mp h
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos a)).2
  calc
    a ^ k ≤ Real.exp a * (k.factorial : ℝ) := hmul
    _ = (k.factorial : ℝ) * Real.exp a := by ring

/-- For nonnegative `a` and `n : ℕ`, `(1 + a)^n * exp(-a) ≤ 2^(n-1) * (1 + n!)`. -/
theorem one_add_pow_exp_neg_le {n : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    (1 + a) ^ n * Real.exp (-a) ≤ (2 : ℝ) ^ (n - 1) * (1 + (n.factorial : ℝ)) := by
  have hp := add_pow_le (zero_le_one : (0 : ℝ) ≤ 1) ha n
  have h0 : Real.exp (-a) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr ha
  have hn' := exp_poly_bound (k := n) ha
  have hsum : (1 + a ^ n) * Real.exp (-a) ≤ 1 + (n.factorial : ℝ) := by
    calc
      (1 + a ^ n) * Real.exp (-a) = Real.exp (-a) + a ^ n * Real.exp (-a) := by ring
      _ ≤ 1 + (n.factorial : ℝ) := add_le_add h0 hn'
  have hp' : (1 + a) ^ n ≤ 2 ^ (n - 1) * (1 + a ^ n) := by
    simpa only [one_pow] using hp
  calc
    (1 + a) ^ n * Real.exp (-a) ≤
        2 ^ (n - 1) * (1 + a ^ n) * Real.exp (-a) :=
      mul_le_mul_of_nonneg_right hp' (Real.exp_nonneg _)
    _ = 2 ^ (n - 1) * ((1 + a ^ n) * Real.exp (-a)) := by ring
    _ ≤ 2 ^ (n - 1) * (1 + (n.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)

/-- For positive time `t`, the heat prefactor `(4πt)^(-3/2)` is bounded by `(√t)^(-3)`. -/
theorem heat_prefactor_le {t : ℝ} (ht : 0 < t) :
    (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) ≤ (Real.sqrt t) ^ (-(3 : ℝ)) := by
  have hbase : t ≤ 4 * Real.pi * t := by
    have hpi : (1 : ℝ) ≤ 4 * Real.pi := by
      nlinarith only [Real.two_le_pi]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hpi ht.le
  have hpow : t ^ ((3 : ℝ) / 2) ≤ (4 * Real.pi * t) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow ht.le hbase (by positivity)
  have hsqrt : (Real.sqrt t) ^ (3 : ℕ) = t ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  calc
    (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) = ((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹ := by
      rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring, Real.rpow_neg (by positivity)]
    _ ≤ (t ^ ((3 : ℝ) / 2))⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
    _ = (Real.sqrt t) ^ (-(3 : ℝ)) := by
      rw [← hsqrt, Real.rpow_neg (by positivity)]
      exact congrArg Inv.inv (Real.rpow_natCast (Real.sqrt t) 3).symm

/-- For positive `z`, `z^(-3)` equals `(z^3)⁻¹`. -/
theorem heat_rpow_neg_three (z : ℝ) (hz : 0 < z) :
    z ^ (-(3 : ℝ)) = (z ^ (3 : ℕ))⁻¹ := by
  rw [Real.rpow_neg hz.le]
  exact congrArg Inv.inv (Real.rpow_natCast z 3)

end CKN.Foundation.Heat
