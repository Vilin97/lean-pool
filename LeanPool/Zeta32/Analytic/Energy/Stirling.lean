/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Family
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! Factorial bounds for `S_n = (5n)!/(n!)⁴` and `F_n = ∏_{i<3n} (i!)²`
(the proof notes (5′), (6′)).
-- adapted from Li2Unified/Modular/Base/FactorialLogBounds.lean, Base/SumNatMulLog.lean,
-- Base/OriginalFnLogBounds.lean (factorial_log_sum_bounds), Base/OriginalSnLogBounds.lean
-- (pattern). -/

public section

open MeasureTheory Set
open scoped BigOperators

namespace Zeta32.Analytic.EnergyI
noncomputable section

theorem factorial_log_error_bounds (n : ℕ) (hn : 1 ≤ n) :
    (1 / 2 : ℝ) * Real.log (n : ℝ) + 11 / 12 ≤
        Real.log (n.factorial : ℝ) - (n : ℝ) * Real.log (n : ℝ) + (n : ℝ) ∧
      Real.log (n.factorial : ℝ) - (n : ℝ) * Real.log (n : ℝ) + (n : ℝ) ≤
        (1 / 2 : ℝ) * Real.log (n : ℝ) + 1 := by
  cases n with
  | zero => norm_num at hn
  | succ k =>
      have hn0 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hlo := Stirling.log_stirlingSeq_bounded_by_constant k
      have hhi :
          Real.log (Stirling.stirlingSeq (k + 1)) ≤
            Real.log (Stirling.stirlingSeq 1) :=
        Stirling.log_stirlingSeq'_antitone (Nat.zero_le k)
      rw [Stirling.stirlingSeq_one,
        Real.log_div (by positivity) (by positivity), Real.log_exp,
        Real.log_sqrt (by norm_num)] at hhi
      have hformula := Stirling.log_stirlingSeq_formula (k + 1)
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0,
        Real.log_div hn0 (Real.exp_ne_zero 1), Real.log_exp] at hformula
      norm_num only at hlo
      constructor <;> nlinarith only [hlo, hhi, hformula]

lemma integral_mul_log_one {b : ℝ} (hb : 1 ≤ b) :
    (∫ x in (1 : ℝ)..b, x * Real.log x) =
      b ^ 2 / 2 * Real.log b - b ^ 2 / 4 + 1 / 4 := by
  have hd (x : ℝ) (hx : 1 ≤ x) :
      HasDerivAt
        (fun t : ℝ => t ^ 2 / 2 * Real.log t - t ^ 2 / 4)
        (x * Real.log x) x := by
    have hx0 : x ≠ 0 := by linarith
    convert! ((((hasDerivAt_id x).fun_pow 2).div_const 2).mul
      (Real.hasDerivAt_log hx0)).sub
        (((hasDerivAt_id x).fun_pow 2).div_const 4) using 1
    dsimp only [id_eq]
    field_simp [hx0]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (1 : ℝ)) (b := b)
    (f := fun t : ℝ => t ^ 2 / 2 * Real.log t - t ^ 2 / 4)
    (f' := fun t : ℝ => t * Real.log t)
    (fun x hx => hd x (by
      have hx' : x ∈ Icc (1 : ℝ) b := by
        simpa only [uIcc_of_le hb] using hx
      exact hx'.1))
    (Real.continuous_mul_log.intervalIntegrable 1 b)
  simpa only [one_pow, Real.log_one, mul_zero, zero_sub,
    sub_neg_eq_add] using hi

theorem sum_nat_mul_log_bounds (h : ℕ) (hh : 1 ≤ h) :
    (h : ℝ) ^ 2 / 2 * Real.log (h : ℝ) -
        (h : ℝ) ^ 2 / 4 + 1 / 4 - (h : ℝ) * Real.log (h : ℝ) ≤
      (∑ i ∈ Finset.range h, (i : ℝ) * Real.log (i : ℝ)) ∧
    (∑ i ∈ Finset.range h, (i : ℝ) * Real.log (i : ℝ)) ≤
      (h : ℝ) ^ 2 / 2 * Real.log (h : ℝ) -
        (h : ℝ) ^ 2 / 4 + 1 / 4 := by
  let f : ℝ → ℝ := fun x => x * Real.log x
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 0 := by simp [f]
  have hhpos : 0 < h := lt_of_lt_of_le Nat.zero_lt_one hh
  have hhR : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hm : MonotoneOn f (Icc (1 : ℝ) (h : ℝ)) := by
    intro x hx z hz hxz
    have hx0 : 0 < x := by linarith [hx.1]
    have hz0 : 0 ≤ z := by linarith [hz.1]
    calc
      f x = x * Real.log x := rfl
      _ ≤ z * Real.log x :=
        mul_le_mul_of_nonneg_right hxz (Real.log_nonneg hx.1)
      _ ≤ z * Real.log z :=
        mul_le_mul_of_nonneg_left (Real.log_le_log hx0 hxz) hz0
      _ = f z := rfl
  have hleft : (∑ i ∈ Finset.Ico 1 h, f (i : ℝ)) =
        ∑ i ∈ Finset.range h, f (i : ℝ) := by
    simpa only [Nat.cast_zero, hf0, zero_add] using
      (Finset.sum_range_eq_add_Ico (fun i : ℕ => f (i : ℝ)) hhpos).symm
  have hremove : (∑ i ∈ Finset.range h, f ((i + 1 : ℕ) : ℝ)) =
        ∑ i ∈ Finset.Ico 1 h, f ((i + 1 : ℕ) : ℝ) := by
    simpa only [Nat.zero_add, Nat.cast_one, hf1, zero_add] using
      (Finset.sum_range_eq_add_Ico
        (fun i : ℕ => f ((i + 1 : ℕ) : ℝ)) hhpos)
  have hright : (∑ i ∈ Finset.Ico 1 h, f ((i + 1 : ℕ) : ℝ)) =
        (∑ i ∈ Finset.range h, f (i : ℝ)) + f (h : ℝ) := by
    have hs := Finset.sum_range_succ' (fun i : ℕ => f (i : ℝ)) h
    rw [Finset.sum_range_succ] at hs
    simp only [Nat.cast_zero, hf0, add_zero, hremove] at hs
    exact hs.symm
  have hmNat : MonotoneOn f (Icc ((1 : ℕ) : ℝ) (h : ℝ)) := by
    simpa only [Nat.cast_one] using hm
  have hup := MonotoneOn.sum_le_integral_Ico (f := f) hh hmNat
  have hlo := MonotoneOn.integral_le_sum_Ico (f := f) hh hmNat
  simp only [Nat.cast_one] at hup hlo
  rw [hleft] at hup
  rw [hright] at hlo
  have hi : (∫ x in (1 : ℝ)..(h : ℝ), f x) =
      (h : ℝ) ^ 2 / 2 * Real.log (h : ℝ) -
        (h : ℝ) ^ 2 / 4 + 1 / 4 := integral_mul_log_one hhR
  rw [hi] at hup hlo
  dsimp only [f] at hup hlo
  constructor <;> linarith only [hup, hlo]

lemma factorial_log_sum_bounds (h : ℕ) (hh : 1 ≤ h) :
    (h : ℝ) ^ 2 * Real.log (h : ℝ) - (3 / 2 : ℝ) * (h : ℝ) ^ 2 -
        2 * (h : ℝ) * Real.log (h : ℝ) ≤
      2 * (∑ i ∈ Finset.range h, Real.log (i.factorial : ℝ)) ∧
    2 * (∑ i ∈ Finset.range h, Real.log (i.factorial : ℝ)) ≤
      (h : ℝ) ^ 2 * Real.log (h : ℝ) - (3 / 2 : ℝ) * (h : ℝ) ^ 2 +
        (h : ℝ) * Real.log (h : ℝ) + 4 * (h : ℝ) := by
  have hhR : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hlogh : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg hhR
  obtain ⟨htlo, hthi⟩ := sum_nat_mul_log_bounds h hh
  have hslo : (∑ i ∈ Finset.range h,
        ((i : ℝ) * Real.log (i : ℝ) - (i : ℝ))) ≤
      (∑ i ∈ Finset.range h, Real.log (i.factorial : ℝ)) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi0 : i = 0
    · simp [hi0]
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
      have hlogi : 0 ≤ Real.log (i : ℝ) := Real.log_nonneg hiR
      have hb := (factorial_log_error_bounds i hi1).1
      linarith only [hb, hlogi]
  have hsup : (∑ i ∈ Finset.range h, Real.log (i.factorial : ℝ)) ≤
      (∑ i ∈ Finset.range h,
        ((i : ℝ) * Real.log (i : ℝ) - (i : ℝ) +
          ((1 / 2 : ℝ) * Real.log (h : ℝ) + 1))) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hi0 : i = 0
    · simpa [hi0] using
        (show (0 : ℝ) ≤ (1 / 2 : ℝ) * Real.log (h : ℝ) + 1 by
          linarith only [hlogh])
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
      have hih : (i : ℝ) ≤ (h : ℝ) := by
        exact_mod_cast (Finset.mem_range.mp hi).le
      have hlogi : Real.log (i : ℝ) ≤ Real.log (h : ℝ) :=
        Real.log_le_log (by linarith only [hiR]) hih
      have hb := (factorial_log_error_bounds i hi1).2
      linarith only [hb, hlogi]
  simp only [Finset.sum_sub_distrib] at hslo
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsup
  have hid0 : (∑ i ∈ Finset.range h, (i : ℝ)) * 2 =
        (h : ℝ) * ((h - 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] using
      congrArg (fun k : ℕ => (k : ℝ)) (Finset.sum_range_id_mul_two h)
  have hid : (∑ i ∈ Finset.range h, (i : ℝ)) * 2 =
        (h : ℝ) * ((h : ℝ) - 1) := by
    simpa only [Nat.cast_sub hh, Nat.cast_one] using hid0
  constructor
  · nlinarith only [hslo, htlo, hid, hhR]
  · nlinarith only [hsup, hthi, hid, hhR]

/-- `log S_n ≤ n log n + (5 log 5 − 1) n + 1`. -/
theorem Sn_log_upper (n : ℕ) (hn : 1 ≤ n) :
    Real.log (Sn n : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) + (5 * Real.log 5 - 1) * (n : ℝ) + 1 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hcast : (Sn n : ℝ) = ((5 * n).factorial : ℝ) / (n.factorial : ℝ) ^ 4 := by
    simp only [Sn, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  have hnum : 0 < ((5 * n).factorial : ℝ) := by positivity
  have hden : 0 < (n.factorial : ℝ) := by positivity
  have hlog : Real.log (Sn n : ℝ) =
      Real.log ((5 * n).factorial : ℝ) - 4 * Real.log (n.factorial : ℝ) := by
    rw [hcast, Real.log_div hnum.ne' (pow_ne_zero 4 hden.ne'), Real.log_pow]
    norm_num
  have hlog5n : Real.log ((5 * n : ℕ) : ℝ) = Real.log 5 + Real.log (n : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hnpos.ne')
  obtain ⟨hnlo, _⟩ := factorial_log_error_bounds n hn
  obtain ⟨_, h5hi⟩ := factorial_log_error_bounds (5 * n) (by omega)
  rw [hlog5n] at h5hi
  push_cast at h5hi
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlog5 : Real.log 5 < 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 5 / 4 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      at this
    have h2 := Real.log_two_lt_d9
    push_cast at this
    linarith
  rw [hlog]
  nlinarith

/-- `log F_n ≥ h² log h − (3/2)h² − 2h log h`, `h = 3n`. -/
theorem Fn_log_lower (n : ℕ) (hn : 1 ≤ n) :
    ((3 * n : ℕ) : ℝ) ^ 2 * Real.log ((3 * n : ℕ) : ℝ) - (3 / 2 : ℝ) * ((3 * n : ℕ) : ℝ) ^ 2 -
        2 * ((3 * n : ℕ) : ℝ) * Real.log ((3 * n : ℕ) : ℝ) ≤ Real.log (Fn n : ℝ) := by
  have hcast : (Fn n : ℝ) = ∏ i ∈ Finset.range (3 * n), (i.factorial : ℝ) ^ 2 := by
    simp only [Fn, Rat.cast_prod, Rat.cast_pow, Rat.cast_natCast]
  have hnonzero : ∀ i ∈ Finset.range (3 * n), (i.factorial : ℝ) ^ 2 ≠ 0 := by
    intro i _; positivity
  have hlog : Real.log (Fn n : ℝ) = 2 * (∑ i ∈ Finset.range (3 * n), Real.log (i.factorial : ℝ))
    := by
    rw [hcast, Real.log_prod hnonzero]
    simp only [Real.log_pow, Nat.cast_ofNat, Finset.mul_sum]
  rw [hlog]
  exact (factorial_log_sum_bounds (3 * n) (by omega)).1

end
end Zeta32.Analytic.EnergyI

end
