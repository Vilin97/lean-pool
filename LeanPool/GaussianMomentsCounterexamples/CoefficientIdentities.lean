/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Finite coefficient identities underlying the Gaussian counterexamples. -/

public section

namespace GaussianMomentsCounterexamples
open Finset

private theorem choose_recurrence (r : ℂ) (n : ℕ) :
    (n + 1 : ℂ) * Ring.choose r (n + 1) = (r - n) * Ring.choose r n := by
  apply mul_left_cancel₀ (show (n.factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero n)
  have h := Ring.descPochhammer_eq_factorial_smul_choose r (n + 1)
  rw [descPochhammer_succ_right, Polynomial.smeval_mul,
    Ring.descPochhammer_eq_factorial_smul_choose] at h
  simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast,
    pow_zero, nsmul_eq_mul, mul_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one] at h
  linear_combination h.symm

/-- The central binomial coefficients are the coefficients of the formal exponent -1/2. -/
theorem choose_neg_half (n : ℕ) :
    Ring.choose (-1 / 2 : ℂ) n = (-1 : ℂ)^n / 4^n * ((2*n).choose n : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply mul_left_cancel₀ (show (n + 1 : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n)
    rw [choose_recurrence, ih]
    have h : ((n : ℂ) + 1) * ((2 * (n + 1)).choose (n + 1) : ℂ) =
        2 * (2 * n + 1) * ((2 * n).choose n : ℂ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    simp only [pow_succ]
    field_simp
    linear_combination 2 * h

/-- The formal branch of the inverse square root becomes the geometric inverse
under the substitution X(2+X). -/
theorem binomial_neg_half_subst_mul :
    PowerSeries.subst (PowerSeries.X * (2 + PowerSeries.X : PowerSeries ℂ))
      (PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ)) * (1 + PowerSeries.X) = 1 := by
  let u : PowerSeries ℂ := PowerSeries.X * (2 + PowerSeries.X)
  have hu : PowerSeries.HasSubst u := PowerSeries.HasSubst.X'.mul_left
  let F := PowerSeries.substAlgHom (R := ℂ) hu
  let B := PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ)
  have hB : B * B * (1 + PowerSeries.X) = 1 := by
    have h1 : (1 + PowerSeries.X : PowerSeries ℂ) = PowerSeries.binomialSeries ℂ (1 : ℂ) := by
      simpa using (PowerSeries.binomialSeries_nat (A := ℂ) (R := ℂ) 1).symm
    rw [h1]
    dsimp [B]
    rw [← PowerSeries.binomialSeries_add, ← PowerSeries.binomialSeries_add]
    norm_num
  have hsq : (F B * (1 + PowerSeries.X)) ^ 2 = 1 := by
    have hh := congrArg F hB
    dsimp [F] at hh
    simp only [map_mul, map_add, map_one, PowerSeries.substAlgHom_X] at hh
    dsimp [u] at hh
    linear_combination hh
  have hor := eq_or_eq_neg_of_sq_eq_sq _ _
    (show (F B * (1 + PowerSeries.X)) ^ 2 = (1 : PowerSeries ℂ)^2 by
    simpa using hsq)
  rcases hor with hp | hn
  · simpa only [F, PowerSeries.coe_substAlgHom, B, u] using hp
  · have hh := congrArg PowerSeries.constantCoeff hn
    have hb : PowerSeries.constantCoeff (F B) = 1 := by
      dsimp only [F]
      rw [PowerSeries.coe_substAlgHom]
      change MvPowerSeries.constantCoeff (PowerSeries.subst u B) = 1
      rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero]
      · simp [B]
      · change PowerSeries.constantCoeff u = 0
        simp [u]
    simp only [map_mul, map_add, map_one, PowerSeries.constantCoeff_X, add_zero, mul_one,
      map_neg, hb] at hh
    norm_num at hh

/-- Extracting a coefficient after substitution needs only finitely many input terms. -/
theorem coeff_mul_subst_X_mul (f g h : PowerSeries ℂ) (m : ℕ) :
    PowerSeries.coeff m (g * PowerSeries.subst (PowerSeries.X * h) f) =
      ∑ k ∈ range (m + 1), PowerSeries.coeff k f *
        PowerSeries.coeff (m - k) (g * h ^ k) := by
  let u := PowerSeries.X * h
  have hu : PowerSeries.HasSubst u := PowerSeries.HasSubst.X'.mul_left
  let F := PowerSeries.substAlgHom (R := ℂ) hu
  have hf := PowerSeries.eq_shift_mul_X_pow_add_trunc (m + 1) f
  have he := congrArg F hf
  simp only [map_add, map_mul, map_pow, F, PowerSeries.substAlgHom_X,
    PowerSeries.substAlgHom_coe] at he
  rw [PowerSeries.coe_substAlgHom] at he
  change PowerSeries.subst u f = _ at he
  change PowerSeries.coeff m (g * PowerSeries.subst u f) = _
  rw [he, mul_add, map_add]
  have hz : PowerSeries.coeff m
      (g * (PowerSeries.subst u (PowerSeries.mk fun i => PowerSeries.coeff (i + (m + 1)) f) *
        u ^ (m + 1))) = 0 := by
    dsimp [u]
    rw [mul_pow]
    have hh : g * (PowerSeries.subst u (PowerSeries.mk fun i => PowerSeries.coeff (i + (m +
      1)) f) *
        (PowerSeries.X ^ (m + 1) * h ^ (m + 1))) =
        (g * PowerSeries.subst u
          (PowerSeries.mk fun i => PowerSeries.coeff (i + (m + 1)) f) * h ^ (m + 1)) *
          PowerSeries.X ^ (m + 1) := by
          ring
    rw [hh, PowerSeries.coeff_mul_X_pow']
    simp
  rw [hz, zero_add]
  change PowerSeries.coeff m (g * (Polynomial.eval₂ (algebraMap ℂ (PowerSeries ℂ)) u (f.trunc
    (m + 1)))) = _
  rw [PowerSeries.eval₂_trunc_eq_sum_range, mul_sum, map_sum]
  apply sum_congr rfl
  intro k hk
  have hkm : k ≤ m := Nat.le_of_lt_succ (mem_range.mp hk)
  change PowerSeries.coeff m (g * (PowerSeries.C (PowerSeries.coeff k f) * u ^ k)) = _
  have hh : g * (PowerSeries.C (PowerSeries.coeff k f) * u ^ k) =
      PowerSeries.C (PowerSeries.coeff k f) * ((g * h ^ k) * PowerSeries.X ^ k) := by
        dsimp [u]
        rw [mul_pow]
        ring
  rw [hh, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', ite_eq_left hkm]

/-- The finite coefficient identity in the three-variable master formula. -/
theorem coefficient_identity_three (A : Polynomial ℂ) (m : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ range (m + 1), ((-1 : ℂ)^k / 4^k * ((2*k).choose k : ℂ)) *
      (A * (1 + Polynomial.X)^m * (2 + Polynomial.X)^k).coeff (m-k)) =
      (A * (1 + Polynomial.X)^(m-1)).coeff m := by
  let S := PowerSeries.subst (PowerSeries.X * (2 + PowerSeries.X : PowerSeries ℂ))
    (PowerSeries.binomialSeries ℂ (-1/2 : ℂ))
  have hid : ((A : PowerSeries ℂ) * (1 + PowerSeries.X)^m) * S =
      (A : PowerSeries ℂ) * (1 + PowerSeries.X)^(m-1) := by
    have hp : m = (m - 1) + 1 := by omega
    conv_lhs => rw [hp, pow_succ]
    have hh := binomial_neg_half_subst_mul
    change S * (1 + PowerSeries.X) = 1 at hh
    calc
      _ = ((A : PowerSeries ℂ) * (1 + PowerSeries.X)^(m-1)) * (S * (1 + PowerSeries.X)) := by
        ring
      _ = _ := by rw [hh, mul_one]
  have he := coeff_mul_subst_X_mul (PowerSeries.binomialSeries ℂ (-1/2 : ℂ))
    ((A : PowerSeries ℂ) * (1 + PowerSeries.X)^m) (2 + PowerSeries.X) m
  simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one, choose_neg_half] at he
  rw [show PowerSeries.coeff m (((A : PowerSeries ℂ) * (1 + PowerSeries.X)^m) * S) =
    (A * (1 + Polynomial.X)^(m-1)).coeff m by
      rw [hid]
      simp only [← Polynomial.coeff_coe, Polynomial.coe_mul, Polynomial.coe_pow,
        Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]] at he
  have htwo : ((2 : Polynomial ℂ) : PowerSeries ℂ) = 2 := by
    rw [show (2 : Polynomial ℂ) = 1 + 1 by ring, Polynomial.coe_add, Polynomial.coe_one]; ring
  simpa only [← Polynomial.coeff_coe, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_add, Polynomial.coe_one,
    Polynomial.coe_X, htwo] using he.symm

/-- The geometric inverse series has alternating coefficients. -/
theorem choose_neg_one (n : ℕ) : Ring.choose (-1 : ℂ) n = (-1 : ℂ)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply mul_left_cancel₀ (show (n + 1 : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n)
    rw [choose_recurrence, ih, pow_succ]
    ring

/-- The finite coefficient identity in the four-variable master formula. -/
theorem coefficient_identity_four (A : Polynomial ℂ) (m : ℕ) (hm : 1 ≤ m) :
    (∑ a ∈ range (m+1), (-1 : ℂ)^a * (A * (1 + Polynomial.X)^m).coeff (m-a)) =
      (A * (1 + Polynomial.X)^(m-1)).coeff m := by
  let B := PowerSeries.binomialSeries ℂ (-1 : ℂ)
  have hb : B * (1 + PowerSeries.X) = 1 := by
    have h1 : (1 + PowerSeries.X : PowerSeries ℂ) = PowerSeries.binomialSeries ℂ (1 : ℂ) := by
      simpa using (PowerSeries.binomialSeries_nat (A := ℂ) (R := ℂ) 1).symm
    rw [h1]
    dsimp [B]
    rw [← PowerSeries.binomialSeries_add]
    norm_num
  have hid : ((A : PowerSeries ℂ) * (1 + PowerSeries.X)^m) * B =
      (A : PowerSeries ℂ) * (1 + PowerSeries.X)^(m-1) := by
    have hp : m = (m - 1) + 1 := by omega
    conv_lhs => rw [hp, pow_succ]
    calc
      _ = ((A : PowerSeries ℂ) * (1 + PowerSeries.X)^(m-1)) * (B * (1 + PowerSeries.X)) := by
        ring
      _ = _ := by rw [hb, mul_one]
  have he := coeff_mul_subst_X_mul B ((A : PowerSeries ℂ) * (1 + PowerSeries.X)^m) 1 m
  simp only [mul_one, one_pow, PowerSeries.X_subst] at he
  simp only [B, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one, choose_neg_one] at he
  rw [show PowerSeries.coeff m (((A : PowerSeries ℂ) * (1 + PowerSeries.X)^m) * B) =
    (A * (1 + Polynomial.X)^(m-1)).coeff m by
      rw [hid]
      simp only [← Polynomial.coeff_coe, Polynomial.coe_mul, Polynomial.coe_pow,
        Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]] at he
  simpa only [← Polynomial.coeff_coe, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_add, Polynomial.coe_one,
    Polynomial.coe_X] using he.symm

/-- The master coefficient vanishes for the constant test polynomial. -/
theorem master_coefficient_one (m : ℕ) (hm : 1 ≤ m) :
    ((1 : Polynomial ℂ) * (1 + Polynomial.X)^(m-1)).coeff m = 0 := by
  rw [one_mul, Polynomial.coeff_one_add_X_pow, Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-- The master coefficient is one for the linear test polynomial. -/
theorem master_coefficient_X (m : ℕ) (hm : 1 ≤ m) :
    ((Polynomial.X : Polynomial ℂ) * (1 + Polynomial.X)^(m-1)).coeff m = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simp only [Nat.succ_sub_one, Polynomial.coeff_X_mul, Polynomial.coeff_one_add_X_pow,
    Nat.choose_self, Nat.cast_one]

/-- Exact factorial cancellation in the three-variable Gaussian expansion. -/
theorem three_moment_scalar (m k : ℕ) (hk : k ≤ m) :
    (m.choose k : ℂ) * ((m-k).factorial : ℂ) * (-1/2 : ℂ)^k *
        ((2*k).factorial : ℂ) / (2^k * (k.factorial : ℂ)) =
      (m.factorial : ℂ) * ((-1 : ℂ)^k / 4^k * ((2*k).choose k : ℂ)) := by
  have h1 : (m.choose k : ℂ) * (k.factorial : ℂ) * ((m-k).factorial : ℂ) =
      (m.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have h2 : ((2*k).choose k : ℂ) * (k.factorial : ℂ) * (k.factorial : ℂ) =
      ((2*k).factorial : ℂ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2*k by omega)
    rw [show 2*k-k=k by omega] at h
    exact_mod_cast h
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [div_pow, show (4 : ℂ) = 2*2 by norm_num, mul_pow]
  field_simp
  rw [← h2]
  linear_combination (((2*k).choose k : ℂ) * (k.factorial : ℂ)) * h1

end GaussianMomentsCounterexamples
