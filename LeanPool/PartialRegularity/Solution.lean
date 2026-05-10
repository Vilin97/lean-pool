/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang
-/
import Mathlib

/-! # Almost all primes are partially regular

This file proves that the count of primes `p ≤ X` that are not `M_α(p)`-regular is
`O(X / (log X) ^ (2α))` for fixed `α > 1/2`, where `M_α(p) = ⌊√p / (log p)^α⌋`.
-/

namespace LeanPool.PartialRegularity

/-- A prime `p` is `m`-regular if it is odd and does not divide the numerator of the
    Bernoulli number `B_{2k}` for each `k` with `1 ≤ 2k ≤ min(m, p - 3)`. -/
def IsRegularPrime (m : ℕ) (p : ℕ) : Prop :=
  Nat.Prime p ∧ Odd p ∧
    ∀ k : ℕ, 1 ≤ 2 * k → 2 * k ≤ min m (p - 3) →
      ¬((p : ℤ) ∣ (bernoulli (2 * k)).num)

noncomputable instance decidable_IsRegularPrime (m : ℕ) (p : ℕ) : Decidable (IsRegularPrime m p) :=
  Classical.propDecidable (IsRegularPrime m p)

/-- For `α > 1/2` and prime `p`, `M_α(p) = ⌊√p / (log p)^α⌋`. -/
noncomputable def M_alpha (α : ℝ) (p : ℕ) : ℕ :=
  ⌊Real.sqrt p / (Real.log p) ^ α⌋₊

/-- Count of primes `p ≤ X` that are not `M_α(p)`-regular. -/
noncomputable def countNonRegularPrimes (α : ℝ) (X : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊X⌋₊).filter (fun p =>
    Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p)).card

/-- `K_max(X) = ⌊√X / (2 * (log X)^α)⌋` bounds the range of k in the double counting argument. -/
noncomputable def K_max (α : ℝ) (X : ℝ) : ℕ :=
  ⌊Real.sqrt X / (2 * (Real.log X) ^ α)⌋₊
lemma sqrt_div_log_pow_nonneg (α : ℝ) (X : ℝ) (hX : 1 < X) (hα : 0 < α) :
    0 ≤ Real.sqrt X / (2 * (Real.log X) ^ α) := by
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos_of_pos (by linarith)
  have hdenom : 0 < 2 * (Real.log X) ^ α := by positivity
  exact div_nonneg hsqrt.le hdenom.le

lemma rhs_simplify (α : ℝ) (X : ℝ) (hX : 1 < X) (hα : 0 < α) :
    (Real.sqrt X / (2 * (Real.log X) ^ α)) ^ 2 = X / (4 * (Real.log X) ^ (2 * α)) := by
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hsqrt : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt (by linarith)
  have hpow : ((Real.log X) ^ α) ^ 2 = (Real.log X) ^ (2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog.le]
    ring_nf
  rw [div_pow, mul_pow, hsqrt, hpow]
  ring

lemma K_max_sq_le (α : ℝ) (X : ℝ) (hX : 1 < X) (hα : 0 < α) :
    ((K_max α X : ℕ) : ℝ) ^ 2 ≤ X / (4 * (Real.log X) ^ (2 * α)) := by
  have h_nonneg := sqrt_div_log_pow_nonneg α X hX hα
  have h_floor_le : (K_max α X : ℝ) ≤ Real.sqrt X / (2 * (Real.log X) ^ α) :=
    Nat.floor_le h_nonneg
  have h_sq_le : ((K_max α X : ℕ) : ℝ) ^ 2 ≤ (Real.sqrt X / (2 * (Real.log X) ^ α)) ^ 2 := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _) h_floor_le
  calc ((K_max α X : ℕ) : ℝ) ^ 2
      ≤ (Real.sqrt X / (2 * (Real.log X) ^ α)) ^ 2 := h_sq_le
    _ = X / (4 * (Real.log X) ^ (2 * α)) := rhs_simplify α X hX hα

lemma K_max_sq_isBigO (α : ℝ) (hα : 1/2 < α) :
    (fun X : ℝ => ((K_max α X : ℕ) : ℝ) ^ 2) =O[Filter.atTop]
    (fun X : ℝ => X / (Real.log X) ^ (2 * α)) := by
  apply Asymptotics.IsBigO.of_bound (1/4)
  filter_upwards [Filter.eventually_gt_atTop 1] with X hX
  simp only [Real.norm_eq_abs]
  have hα' : 0 < α := by linarith
  have h1 : ((K_max α X : ℕ) : ℝ) ^ 2 ≤ X / (4 * (Real.log X) ^ (2 * α)) := K_max_sq_le α X hX hα'
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hlog_pow : 0 < (Real.log X) ^ (2 * α) := by positivity
  have h2 : X / (4 * (Real.log X) ^ (2 * α)) = (1/4) * (X / (Real.log X) ^ (2 * α)) := by ring
  calc |((K_max α X : ℕ) : ℝ) ^ 2|
      = ((K_max α X : ℕ) : ℝ) ^ 2 := abs_of_nonneg (sq_nonneg _)
    _ ≤ X / (4 * (Real.log X) ^ (2 * α)) := h1
    _ = (1/4) * (X / (Real.log X) ^ (2 * α)) := h2
    _ ≤ (1/4) * |X / (Real.log X) ^ (2 * α)| := by {
        have hX' : 0 < X := by linarith
        have : 0 < X / (Real.log X) ^ (2 * α) := by positivity
        rw [abs_of_pos this]
      }


/-- The set of primes p with p ∣ (bernoulli (2*k)).num, p ≤ X, M_α(p) ≥ 2k -/
noncomputable def primeCountSet (α : ℝ) (k : ℕ) (X : ℝ) : Finset ℕ :=
  Finset.filter
    (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num ∧
              p ≤ ⌊X⌋₊ ∧ M_alpha α p ≥ 2 * k)
    (Finset.Icc 1 ⌊X⌋₊)

lemma two_k_add_one_le (k : ℕ) (hk : 1 ≤ k) : (2 * k + 1 : ℝ) ≤ 3 * k := by
  have : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
  linarith

lemma two_pi_gt_one : (1 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three]

lemma one_lt_re_two_mul_nat (k : ℕ) (hk : 1 ≤ k) : 1 < (2 * k : ℂ).re := by
  have h : (2 * k : ℂ).re = (2 * k : ℝ) := by simp
  rw [h]
  have : (k : ℝ) ≥ 1 := by exact_mod_cast hk
  linarith

lemma zeta_term_re_nonneg (n : ℕ) (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ (Real.cos (2 * Real.pi * 0 * n) / (n : ℂ) ^ (2 * k : ℂ)).re := by
  simp only [mul_zero, zero_mul, Real.cos_zero]
  rcases n with _ | n
  · have h2k_ne : (2 * (k : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (by omega))
    simp [Complex.zero_cpow h2k_ne]
  · rw [show (2 * k : ℂ) = ((2 * k : ℕ) : ℂ) by simp, Complex.cpow_natCast]
    norm_cast
    positivity

lemma zeta_term_at_one_re_pos (k : ℕ) (_hk : 1 ≤ k) :
    0 < (Real.cos (2 * Real.pi * 0 * ((1 : ℕ) : ℝ)) / ((1 : ℕ) : ℂ) ^ (2 * k : ℂ)).re := by
  simp [Real.cos_zero, Complex.one_cpow]

lemma riemannZeta_two_mul_nat_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < (riemannZeta (2 * k : ℂ)).re := by
  have hre : 1 < (2 * k : ℂ).re := one_lt_re_two_mul_nat k hk
  have hsum := HurwitzZeta.hasSum_nat_cosZeta 0 hre
  rw [AddCircle.coe_zero, HurwitzZeta.cosZeta_zero] at hsum
  have hsum_re := Complex.reCLM.hasSum hsum
  simp only [Complex.reCLM_apply] at hsum_re
  rw [hsum_re.tsum_eq.symm]
  exact hsum_re.summable.tsum_pos (zeta_term_re_nonneg · k hk) 1 (zeta_term_at_one_re_pos k hk)

theorem complex_zeta_series_summable (m : ℕ) (hm : 1 < m) :
    Summable (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ m) := by
  have h : 1 < (m : ℂ).re := by simp; exact_mod_cast hm
  simpa using Complex.summable_one_div_nat_cpow.mpr h

lemma riemannZeta_nat_re_eq_tsum (m : ℕ) (hm : 1 < m) :
    (riemannZeta (m : ℂ)).re = ∑' n : ℕ, ((1 : ℂ) / (n : ℂ) ^ m).re := by
  rw [zeta_nat_eq_tsum_of_gt_one hm]
  exact Complex.re_tsum (complex_zeta_series_summable m hm)

lemma one_div_nat_pow_complex_re (n m : ℕ) :
    ((1 : ℂ) / (n : ℂ) ^ m).re = 1 / (n : ℝ) ^ m := by
  simp [Complex.ext_iff, pow_ne_zero, Complex.div_re, Complex.div_im, Complex.normSq, pow_two,
    pow_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_one]
  <;> norm_cast
  <;> field_simp [Complex.ext_iff, pow_ne_zero, Complex.div_re, Complex.div_im, Complex.normSq,
    pow_two, pow_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_one]
  <;> ring_nf
  <;> simp_all [Complex.ext_iff, pow_ne_zero, Complex.div_re, Complex.div_im, Complex.normSq,
    pow_two, pow_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_one]
  <;> norm_cast
  <;> simp_all [Complex.ext_iff, pow_ne_zero, Complex.div_re, Complex.div_im, Complex.normSq,
    pow_two, pow_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_one]
  <;> field_simp [Complex.ext_iff, pow_ne_zero, Complex.div_re, Complex.div_im, Complex.normSq,
    pow_two, pow_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_one]

lemma one_div_pow_strict_antimono (n k : ℕ) (hn : 2 ≤ n) (hk : 1 < k) :
    (1 : ℝ) / (n : ℝ) ^ (2 * k) < 1 / (n : ℝ) ^ 2 := by
  have hn_real : (n : ℝ) ≥ 2 := by simp_all
  have hn_gt_one : (1 : ℝ) < (n : ℝ) := by nlinarith
  have h_exp : (2 : ℕ) < 2 * k := by simp_all
  exact one_div_pow_lt_one_div_pow_of_lt hn_gt_one h_exp

lemma one_div_pow_antimono (n k : ℕ) (hk : 1 ≤ k) :
    (1 : ℝ) / (n : ℝ) ^ (2 * k) ≤ 1 / (n : ℝ) ^ 2 := by
  rcases n with _ | n
  · simp [zero_pow (by omega : 2 * k ≠ 0)]
  · exact one_div_pow_le_one_div_pow_of_le (by simp : (1 : ℝ) ≤ n.succ) (by omega : 2 ≤ 2 * k)

lemma riemannZeta_two_mul_nat_lt_of_one_lt (k : ℕ) (hk : 1 < k) :
    (riemannZeta (2 * k : ℂ)).re < (riemannZeta 2).re := by
  have h2k : 1 < 2 * k := by omega
  rw [show (2 * k : ℂ) = ((2 * k : ℕ) : ℂ) by simp, show (2 : ℂ) = ((2 : ℕ) : ℂ) by simp,
    riemannZeta_nat_re_eq_tsum (2 * k) h2k, riemannZeta_nat_re_eq_tsum 2 (by norm_num)]
  simp only [one_div_nat_pow_complex_re]
  exact Summable.tsum_lt_tsum_of_nonneg (i := 2) (fun _ => by positivity)
    (fun n => one_div_pow_antimono n k (le_of_lt hk))
    (one_div_pow_strict_antimono 2 k (le_refl 2) hk) (Real.summable_one_div_nat_pow.mpr (by norm_num))

lemma riemannZeta_two_mul_nat_le_two (k : ℕ) (hk : 1 ≤ k) :
    (riemannZeta (2 * k : ℂ)).re ≤ (riemannZeta 2).re := by
  rcases eq_or_lt_of_le hk with rfl | hk'
  · simp
  · exact le_of_lt (riemannZeta_two_mul_nat_lt_of_one_lt _ hk')

lemma riemannZeta_two_re_lt_two : (riemannZeta 2).re < 2 := by
  have h1 : (riemannZeta 2).re = (Real.pi : ℝ) ^ 2 / 6 := by
    have h2 : riemannZeta 2 = (Real.pi : ℝ) ^ 2 / 6 := by
      rw [riemannZeta_two]
    simp [h2, Complex.ext_iff]
    <;>
    simp_all [Complex.ext_iff, pow_two]

  have h2 : (Real.pi : ℝ) ^ 2 / 6 < 2 := by
    have := Real.pi_lt_d2
    norm_num at this ⊢ <;>
    (try nlinarith [Real.pi_pos, Real.pi_gt_three])

  rw [h1]
  exact h2

lemma riemannZeta_two_mul_nat_im_eq_zero (k : ℕ) (hk : 1 ≤ k) :
    (riemannZeta (2 * k : ℂ)).im = 0 := by
  have h₁ : (2 * k : ℕ) ≠ 0 := by
    omega

  have h₂ : (riemannZeta (2 * (k : ℕ) : ℂ)).im = 0 := by
    have h₃ : (riemannZeta (2 * (k : ℕ) : ℂ)) = (-1 : ℂ) ^ ((k : ℕ) + 1) * (2 : ℂ) ^ (2 * (k : ℕ) - 1) * (Real.pi : ℂ) ^ (2 * (k : ℕ)) * (bernoulli (2 * (k : ℕ)) : ℂ) / ((2 * (k : ℕ)).factorial : ℂ) := by
      have h₄ := riemannZeta_two_mul_nat (by
        simpa using h₁)
      simp_all [Complex.ext_iff, pow_mul]

    rw [h₃]
    simp [Complex.ext_iff, pow_mul, pow_add, pow_one, Complex.ext_iff, pow_mul, pow_add, pow_one]
    <;>
    (try
      norm_cast) <;>
    (try
      ring_nf) <;>
    (try
      simp_all [Complex.ext_iff, pow_mul, pow_add, pow_one, Complex.ext_iff, pow_mul, pow_add, pow_one])

  simpa [h₁] using h₂

lemma two_pow_mul_pi_pow_eq (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) = (2 * Real.pi) ^ (2 * k) / 2 := by
  have h₂ : (2 * Real.pi : ℝ) ^ (2 * k) / 2 = (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) := by
    have h₆ : (2 : ℕ) * k - 1 + 1 = (2 : ℕ) * k := by
      have h₈ : (2 : ℕ) * k - 1 + 1 = (2 : ℕ) * k := by
        omega
      exact h₈
    calc
      (2 * Real.pi : ℝ) ^ (2 * k) / 2 = ((2 : ℝ) * Real.pi) ^ (2 * k) / 2 := by norm_num
      _ = ((2 : ℝ) ^ (2 * k) * Real.pi ^ (2 * k)) / 2 := by
        rw [mul_pow]
      _ = (2 : ℝ) ^ (2 * k) * Real.pi ^ (2 * k) / 2 := by ring
      _ = (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) := by
        have h₉ : (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ (2 * k - 1) * 2 := by
          have h₁₂ : (2 : ℝ) ^ (2 * k : ℕ) = (2 : ℝ) ^ ((2 * k - 1 : ℕ) + 1 : ℕ) := by
            rw [h₆]
          calc
            (2 : ℝ) ^ (2 * k : ℕ) = (2 : ℝ) ^ ((2 * k - 1 : ℕ) + 1 : ℕ) := by rw [h₁₂]
            _ = (2 : ℝ) ^ (2 * k - 1 : ℕ) * (2 : ℝ) ^ (1 : ℕ) := by
              rw [pow_add]
            _ = (2 : ℝ) ^ (2 * k - 1 : ℕ) * 2 := by norm_num
            _ = (2 : ℝ) ^ (2 * k - 1) * 2 := by norm_cast
        rw [h₉]
        <;> ring_nf
  linarith

lemma bernoulli_eq_zeta_formula_aux (k : ℕ) (hk : 1 ≤ k) :
    (riemannZeta (2 * k : ℂ)).re = (-1 : ℝ)^(k + 1) * 2^(2 * k - 1) * Real.pi ^ (2 * k) * (bernoulli (2 * k) : ℝ) / (2 * k).factorial := by
  have h₁ : (k : ℕ) ≠ 0 := by
    omega

  have h₂ : riemannZeta (2 * (k : ℕ)) = (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1 : ℕ) * (Real.pi : ℂ) ^ (2 * k) * (bernoulli (2 * k) : ℂ) / (2 * k : ℕ).factorial := by
    have h₃ : (k : ℕ) ≠ 0 := h₁
    have h₄ : riemannZeta (2 * (k : ℕ)) = (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1 : ℕ) * (Real.pi : ℂ) ^ (2 * k) * (bernoulli (2 * k) : ℂ) / (2 * k : ℕ).factorial := by
      -- Use the given lemma to get the formula for riemannZeta at 2k
      have h₅ : riemannZeta (2 * (k : ℕ)) = (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1 : ℕ) * (Real.pi : ℂ) ^ (2 * k) * (bernoulli (2 * k) : ℂ) / (2 * k : ℕ).factorial := by
        simpa [Complex.ext_iff, pow_mul, mul_assoc] using riemannZeta_two_mul_nat h₃
      exact h₅
    exact h₄

  have h₃ : (riemannZeta (2 * k : ℂ)).re = (riemannZeta (2 * (k : ℕ))).re := by
    norm_cast

  have h₄ : ((-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1 : ℕ) * (Real.pi : ℂ) ^ (2 * k) * (bernoulli (2 * k) : ℂ) / (2 * k : ℕ).factorial : ℂ).re = (-1 : ℝ)^(k + 1) * 2^(2 * k - 1) * Real.pi ^ (2 * k) * (bernoulli (2 * k) : ℝ) / (2 * k).factorial := by
    simp [Complex.ext_iff, pow_mul, Complex.ext_iff, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div]
    <;>
    simp_all [Complex.ext_iff, pow_mul, Complex.ext_iff, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div]
    <;>
    norm_cast
    <;>
    ring_nf
    <;>
    field_simp [Complex.ext_iff, pow_mul, Complex.ext_iff, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div]
    <;>
    simp_all [Complex.ext_iff, pow_mul, Complex.ext_iff, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div]
    <;>
    ring_nf

  have h₅ : (riemannZeta (2 * k : ℂ)).re = (-1 : ℝ)^(k + 1) * 2^(2 * k - 1) * Real.pi ^ (2 * k) * (bernoulli (2 * k) : ℝ) / (2 * k).factorial := by
    calc
      (riemannZeta (2 * k : ℂ)).re = (riemannZeta (2 * (k : ℕ))).re := by rw [h₃]
      _ = ((-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1 : ℕ) * (Real.pi : ℂ) ^ (2 * k) * (bernoulli (2 * k) : ℂ) / (2 * k : ℕ).factorial : ℂ).re := by
        rw [h₂]
      _ = (-1 : ℝ)^(k + 1) * 2^(2 * k - 1) * Real.pi ^ (2 * k) * (bernoulli (2 * k) : ℝ) / (2 * k).factorial := by
        rw [h₄]

  exact h₅

lemma neg_one_pow_mul_self (n : ℕ) : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by
  have h₁ : (-1 : ℝ)^n * (-1 : ℝ)^n = ((-1 : ℝ)^2)^n := by
    calc
      (-1 : ℝ)^n * (-1 : ℝ)^n = ((-1 : ℝ)^n * (-1 : ℝ)^n) := by rfl
      _ = ((-1 : ℝ)^(n + n)) := by
        rw [← pow_add]
      _ = ((-1 : ℝ)^(2 * n)) := by
        ring_nf
      _ = ((-1 : ℝ)^2)^n := by
        rw [← pow_mul]
  rw [h₁]
  have h₂ : ((-1 : ℝ)^2 : ℝ) = 1 := by norm_num
  rw [h₂]
  have h₃ : (1 : ℝ)^n = 1 := by norm_num
  rw [h₃]

lemma bernoulli_eq_zeta_formula (k : ℕ) (hk : 1 ≤ k) :
    (bernoulli (2 * k) : ℝ) = (-1 : ℝ)^(k + 1) * (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / (2 ^ (2 * k - 1) * Real.pi ^ (2 * k)) := by
  have h_aux := bernoulli_eq_zeta_formula_aux k hk
  have h_pos_2 : (2 : ℝ)^(2 * k - 1) > 0 := by positivity
  have h_pos_pi : Real.pi ^ (2 * k) > 0 := by positivity
  have h_pos_fact : ((2 * k).factorial : ℝ) > 0 := by positivity
  have h_denom_ne : (2 : ℝ)^(2 * k - 1) * Real.pi ^ (2 * k) ≠ 0 := by positivity
  have h_neg_one_pow_ne : (-1 : ℝ)^(k + 1) ≠ 0 := by
    cases' Nat.even_or_odd (k + 1) with he ho
    · simp [he.neg_one_pow]
    · simp [ho.neg_one_pow]
  have h_neg_one_sq : (-1 : ℝ)^(k + 1) * (-1 : ℝ)^(k + 1) = 1 := neg_one_pow_mul_self (k + 1)
  -- From h_aux: ζ.re = (-1)^(k+1) * 2^(2k-1) * π^(2k) * B / (2k)!
  -- Rearranging: B = (-1)^(k+1) * ζ.re * (2k)! / (2^(2k-1) * π^(2k))
  have h1 : (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial =
            (-1 : ℝ)^(k + 1) * 2^(2 * k - 1) * Real.pi ^ (2 * k) * (bernoulli (2 * k) : ℝ) := by
    field_simp at h_aux; linarith
  have h2 : (-1 : ℝ)^(k + 1) * (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial =
            2^(2 * k - 1) * Real.pi ^ (2 * k) * (bernoulli (2 * k) : ℝ) := by
    have step : (-1 : ℝ)^(k + 1) * ((riemannZeta (2 * k : ℂ)).re * (2 * k).factorial)
              = (-1 : ℝ)^(k + 1) * ((-1 : ℝ)^(k + 1) * 2^(2 * k - 1) * Real.pi ^ (2 * k) * (bernoulli (2 * k) : ℝ)) := by
      rw [h1]
    have step2 : (-1 : ℝ)^(k + 1) * (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial
              = (-1 : ℝ)^(k + 1) * ((riemannZeta (2 * k : ℂ)).re * (2 * k).factorial) := by ring
    rw [step2, step]
    calc (-1 : ℝ)^(k + 1) * ((-1 : ℝ)^(k + 1) * 2^(2 * k - 1) * Real.pi ^ (2 * k) * (bernoulli (2 * k) : ℝ))
        = ((-1 : ℝ)^(k + 1) * (-1 : ℝ)^(k + 1)) * 2^(2 * k - 1) * Real.pi ^ (2 * k) * (bernoulli (2 * k) : ℝ) := by ring
      _ = 2^(2 * k - 1) * Real.pi ^ (2 * k) * (bernoulli (2 * k) : ℝ) := by rw [h_neg_one_sq]; ring
  field_simp
  linarith

lemma bernoulli_abs_eq_zeta_aux (k : ℕ) (hk : 1 ≤ k)
    (hform : (bernoulli (2 * k) : ℝ) = (-1 : ℝ)^(k + 1) * (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / (2 ^ (2 * k - 1) * Real.pi ^ (2 * k)))
    (hpos : 0 < (riemannZeta (2 * k : ℂ)).re)
    (halg : (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) = (2 * Real.pi) ^ (2 * k) / 2) :
    |(bernoulli (2 * k) : ℝ)| = 2 * (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / (2 * Real.pi) ^ (2 * k) := by
  have h4 : |(bernoulli (2 * k) : ℝ)| = 2 * (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / (2 * Real.pi) ^ (2 * k) := by
    have h5 : (bernoulli (2 * k) : ℝ) = (-1 : ℝ)^(k + 1) * (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / (2 ^ (2 * k - 1) * Real.pi ^ (2 * k)) := by
      exact hform
    rw [h5]
    have h8 : 0 < (2 * Real.pi : ℝ) ^ (2 * k) := by positivity
    have h10 : ((-1 : ℝ)^(k + 1) * (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / (2 ^ (2 * k - 1) * Real.pi ^ (2 * k)) : ℝ) = ((-1 : ℝ)^(k + 1)) * ((riemannZeta (2 * k : ℂ)).re * (2 * k).factorial) / ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)) := by
      ring_nf
    rw [h10]
    have h11 : |((-1 : ℝ)^(k + 1)) * ((riemannZeta (2 * k : ℂ)).re * (2 * k).factorial) / ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k))| = (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)) := by
      have h16 : |((-1 : ℝ)^(k + 1)) * ((riemannZeta (2 * k : ℂ)).re * (2 * k).factorial) / ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k))| = (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)) := by
        have h17 : |((-1 : ℝ)^(k + 1)) * ((riemannZeta (2 * k : ℂ)).re * (2 * k).factorial) / ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k))| = |((-1 : ℝ)^(k + 1))| * |((riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)))| := by
          simp [abs_mul]
          <;> ring_nf
          <;> simp_all [abs_mul]
        rw [h17]
        have h18 : |((-1 : ℝ)^(k + 1))| = 1 := by
          have h19 : ((-1 : ℝ)^(k + 1)) = 1 ∨ ((-1 : ℝ)^(k + 1)) = -1 := by
            have h20 : ((-1 : ℝ)^(k + 1)) = 1 ∨ ((-1 : ℝ)^(k + 1)) = -1 := by
              have h21 : (k + 1) % 2 = 0 ∨ (k + 1) % 2 = 1 := by omega
              cases h21 with
              | inl h21 =>
                have h22 : (k + 1) % 2 = 0 := h21
                have h23 : ((-1 : ℝ)^(k + 1)) = 1 := by
                  have h24 : (k + 1) % 2 = 0 := h22
                  have h25 : ((-1 : ℝ)^(k + 1)) = 1 := by
                    rw [← Nat.mod_add_div (k + 1) 2]
                    simp [h24, pow_add, pow_mul, pow_two, mul_neg, mul_one]
                  exact h25
                exact Or.inl h23
              | inr h21 =>
                have h22 : (k + 1) % 2 = 1 := h21
                have h23 : ((-1 : ℝ)^(k + 1)) = -1 := by
                  have h24 : (k + 1) % 2 = 1 := h22
                  have h25 : ((-1 : ℝ)^(k + 1)) = -1 := by
                    rw [← Nat.mod_add_div (k + 1) 2]
                    simp [h24, pow_add, pow_mul, pow_two, mul_neg, mul_one]
                  exact h25
                exact Or.inr h23
            exact h20
          cases h19 with
          | inl h19 =>
            rw [h19]
            <;> simp [abs_of_pos]
          | inr h19 =>
            rw [h19]
            <;> simp [abs_of_neg]
        have h20 : |((riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)))| = (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)) := by
          have h21 : (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)) > 0 := by
            positivity
          have h22 : |((riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)))| = (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)) := by
            rw [abs_of_nonneg (le_of_lt h21)]
          rw [h22]
        rw [h18, h20]
        <;> ring_nf
      rw [h16]
    rw [h11]
    have h21 : (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)) = 2 * (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / (2 * Real.pi) ^ (2 * k) := by
      have h22 : (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) = (2 * Real.pi) ^ (2 * k) / 2 := by
        exact halg
      rw [h22]
      have h24 : (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / ((2 * Real.pi) ^ (2 * k) / 2) = 2 * (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / (2 * Real.pi) ^ (2 * k) := by
        field_simp [h8.ne']
      calc
        (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / ((2 * Real.pi) ^ (2 * k) / 2) = 2 * (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / (2 * Real.pi) ^ (2 * k) := by
          rw [h24]
        _ = 2 * (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / (2 * Real.pi) ^ (2 * k) := by rfl
    rw [h21]
  exact h4

lemma bernoulli_abs_eq_zeta (k : ℕ) (hk : 1 ≤ k) :
    |(bernoulli (2 * k) : ℝ)| = 2 * (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / (2 * Real.pi) ^ (2 * k) := by
  have hpos : 0 < (riemannZeta (2 * k : ℂ)).re := riemannZeta_two_mul_nat_pos k hk
  have halg : (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) = (2 * Real.pi) ^ (2 * k) / 2 := two_pow_mul_pi_pow_eq k hk
  have hform : (bernoulli (2 * k) : ℝ) = (-1 : ℝ)^(k + 1) * (riemannZeta (2 * k : ℂ)).re * (2 * k).factorial / (2 ^ (2 * k - 1) * Real.pi ^ (2 * k)) := bernoulli_eq_zeta_formula k hk
  exact bernoulli_abs_eq_zeta_aux k hk hform hpos halg

lemma bernoulli_abs_bound (k : ℕ) (hk : 1 ≤ k) :
    |(bernoulli (2 * k) : ℝ)| ≤ 4 * (2 * k).factorial / (2 * Real.pi) ^ (2 * k) := by
  rw [bernoulli_abs_eq_zeta k hk]
  have h1 : (riemannZeta (2 * k : ℂ)).re ≤ (riemannZeta 2).re := riemannZeta_two_mul_nat_le_two k hk
  have h2 : (riemannZeta 2).re < 2 := riemannZeta_two_re_lt_two
  have h3 : (riemannZeta (2 * k : ℂ)).re < 2 := lt_of_le_of_lt h1 h2
  have h4 : 0 < (riemannZeta (2 * k : ℂ)).re := riemannZeta_two_mul_nat_pos k hk
  have h5 : 0 < (2 : ℝ) * Real.pi := by positivity
  have h6 : 0 < (2 * Real.pi) ^ (2 * k) := pow_pos h5 _
  gcongr
  linarith

def vonStaudtPrimes (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 2)).filter (fun p => Nat.Prime p ∧ (p - 1) ∣ n)

lemma vonStaudtPrimes_prod_pos (n : ℕ) : 0 < ∏ p ∈ vonStaudtPrimes n, p := by
  apply Finset.prod_pos
  intro p hp
  have h₁ : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
  exact Nat.Prime.pos h₁

lemma bernoulli_two_den : (bernoulli 2).den = 6 := by
  have h₀ : bernoulli 2 = 1 / 6 := by
    norm_num [bernoulli_two]

  rw [h₀]
  <;> simp [div_eq_mul_inv]

lemma prime_dvd_six_iff (p : ℕ) (hp : Nat.Prime p) : p ∣ 6 ↔ p = 2 ∨ p = 3 := by
  have h_imp : p ∣ 6 → p = 2 ∨ p = 3 := by
    intro h
    have h₁ : p ∣ 2 * 3 := by
      simpa [mul_comm] using h
    have h₂ : p ∣ 2 ∨ p ∣ 3 := by
      apply (Nat.Prime.dvd_mul hp).mp h₁
    cases h₂ with
    | inl h₂ =>
      have h₃ : p ∣ 2 := h₂
      have h₄ : p ≤ 2 := Nat.le_of_dvd (by decide) h₃
      have h₅ : p ≥ 2 := Nat.Prime.two_le hp
      have h₆ : p = 2 := by
        omega
      exact Or.inl h₆
    | inr h₂ =>
      have h₃ : p ∣ 3 := h₂
      have h₄ : p ≤ 3 := Nat.le_of_dvd (by decide) h₃
      have h₅ : p ≥ 2 := Nat.Prime.two_le hp
      have h₆ : p = 3 := by
        interval_cases p <;> norm_num at hp ⊢ <;> try contradiction
      exact Or.inr h₆

  have h_converse : (p = 2 ∨ p = 3) → p ∣ 6 := by
    intro h
    rcases h with (rfl | rfl)
    · -- Case p = 2
      norm_num
    · -- Case p = 3
      norm_num

  exact ⟨h_imp, h_converse⟩

lemma prime_sub_one_dvd_two_iff (p : ℕ) (hp : Nat.Prime p) : (p - 1) ∣ 2 ↔ p = 2 ∨ p = 3 := by
  have h₁ : p ≥ 2 := Nat.Prime.two_le hp
  constructor
  · -- Prove the forward direction: (p - 1) ∣ 2 → p = 2 ∨ p = 3
    intro h
    have h₂ : p - 1 ∣ 2 := h
    have h₃ : p - 1 = 1 ∨ p - 1 = 2 := by
      -- Since p is a prime, p - 1 must be 1 or 2 to divide 2
      have h₄ : p - 1 ∣ 2 := h₂
      have h₅ : p - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) h₄
      have h₆ : p - 1 ≥ 1 := by
        -- Since p ≥ 2, p - 1 ≥ 1
        have h₈ : p - 1 ≥ 1 := by
          omega
        exact h₈
      interval_cases p - 1 <;> norm_num at h₄ ⊢
    -- Now consider the two cases for p - 1
    cases h₃ with
    | inl h₃ =>
      -- Case p - 1 = 1
      have h₄ : p = 2 := by
        have h₆ : p = 2 := by
          omega
        exact h₆
      exact Or.inl h₄
    | inr h₃ =>
      -- Case p - 1 = 2
      have h₄ : p = 3 := by
        have h₆ : p = 3 := by
          omega
        exact h₆
      exact Or.inr h₄
  · -- Prove the reverse direction: p = 2 ∨ p = 3 → (p - 1) ∣ 2
    intro h
    cases h with
    | inl h =>
      -- Case p = 2
      have h₁ : p = 2 := h
      have h₂ : p - 1 ∣ 2 := by
        rw [h₁]
        norm_num
      exact h₂
    | inr h =>
      -- Case p = 3
      have h₁ : p = 3 := h
      have h₂ : p - 1 ∣ 2 := by
        rw [h₁]
      exact h₂

lemma prime_dvd_bernoulli_two_den_iff (p : ℕ) (hp : Nat.Prime p) :
    p ∣ (bernoulli 2).den ↔ (p - 1) ∣ 2 := by
  rw [bernoulli_two_den, prime_dvd_six_iff p hp, prime_sub_one_dvd_two_iff p hp]

lemma padicValNat_six_le_one (p : ℕ) (hp : Nat.Prime p) : padicValNat p 6 ≤ 1 := by
  have h6 : (6 : ℕ) = 2 * 3 := rfl
  have hcop : Nat.Coprime 2 3 := by
    apply Nat.coprime_of_dvd
    intro k hpk hdiv2 hdiv3
    have h2 : k ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv2
    have h3 : k ≤ 3 := Nat.le_of_dvd (by norm_num) hdiv3
    interval_cases k <;> simp_all [Nat.Prime]
  have hsq : Squarefree (6 : ℕ) := by
    rw [h6, Nat.squarefree_mul_iff]
    exact ⟨hcop, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  rw [← Nat.factorization_def 6 hp]
  exact Squarefree.natFactorization_le_one p hsq

lemma padic_val_bernoulli_two_ge_neg_one (p : ℕ) (hp : Nat.Prime p) :
    padicValRat p (bernoulli 2) ≥ -1 := by
  rw [bernoulli_two]
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [show (6 : ℚ)⁻¹ = 1 / 6 by ring]
  rw [padicValRat.div (by norm_num : (1 : ℚ) ≠ 0) (by norm_num : (6 : ℚ) ≠ 0)]
  simp only [padicValRat.one]
  rw [show (6 : ℚ) = ↑(6 : ℕ) by norm_cast, padicValRat.of_nat]
  have h := padicValNat_six_le_one p hp
  omega

lemma card_units_nsmul_one_eq_neg_one (p : ℕ) [Fact (Nat.Prime p)] :
    (p - 1) • (1 : ZMod p) = -1 := by
  have h_p_pos : 0 < p := Nat.pos_of_neZero p
  simp_all

lemma generator_pow_eq_one_iff (p : ℕ) [Fact (Nat.Prime p)] (g : (ZMod p)ˣ)
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (n : ℕ) :
    g ^ n = 1 ↔ (p - 1) ∣ n := by
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  rw [← hord]
  exact orderOf_dvd_iff_pow_eq_one.symm

lemma g_pow_esymm_eq (p : ℕ) [Fact (Nat.Prime p)] (g : (ZMod p)ˣ) (hfin : IsOfFinOrder g)
    (heq : Subgroup.zpowers g = ⊤) (x : (ZMod p)ˣ) :
    let e := (finEquivZPowers hfin).trans ((MulEquiv.subgroupCongr heq).trans Subgroup.topEquiv).toEquiv
    (g : ZMod p) ^ (↑(e.symm x) : ℕ) = (x : ZMod p) := by
  intro e
  have h1 : e.symm x = (finEquivZPowers hfin).symm
      ((MulEquiv.subgroupCongr heq).symm (Subgroup.topEquiv.symm x)) := rfl
  rw [h1]
  have h2 := pow_finEquivZPowers_symm_apply hfin
      ((MulEquiv.subgroupCongr heq).symm (Subgroup.topEquiv.symm x))
  have h3 : (g : ZMod p) ^ (↑((finEquivZPowers hfin).symm
      ((MulEquiv.subgroupCongr heq).symm (Subgroup.topEquiv.symm x))) : ℕ) =
      ↑((MulEquiv.subgroupCongr heq).symm (Subgroup.topEquiv.symm x) : (ZMod p)ˣ) := by
    rw [← Units.val_pow_eq_pow_val]
    simp only [h2]
  rw [h3, MulEquiv.subgroupCongr_symm_apply, Subgroup.topEquiv_symm_apply_coe]

lemma reindex_term_eq (p : ℕ) [Fact (Nat.Prime p)] (g : (ZMod p)ˣ) (hfin : IsOfFinOrder g)
    (heq : Subgroup.zpowers g = ⊤) (n : ℕ) (x : (ZMod p)ˣ) :
    let e := (finEquivZPowers hfin).trans ((MulEquiv.subgroupCongr heq).trans Subgroup.topEquiv).toEquiv
    (x : ZMod p) ^ n = (g : ZMod p) ^ (↑(e.symm x) * n) := by
  intro e
  rw [← g_pow_esymm_eq p g hfin heq x]
  ring

lemma sum_units_pow_eq_sum_range_pow (p : ℕ) [Fact (Nat.Prime p)] (g : (ZMod p)ˣ)
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (n : ℕ) :
    ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ n = ∑ i ∈ Finset.range (p - 1), (g : ZMod p) ^ (i * n) := by
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  rw [← hord, ← Fin.sum_univ_eq_sum_range]
  have heq : Subgroup.zpowers g = ⊤ := by
    ext x; simp only [Subgroup.mem_top, iff_true]; exact hg x
  let e : Fin (orderOf g) ≃ (ZMod p)ˣ :=
    (finEquivZPowers hfin).trans ((MulEquiv.subgroupCongr heq).trans Subgroup.topEquiv).toEquiv
  rw [Fintype.sum_equiv e.symm]
  exact fun x => reindex_term_eq p g hfin heq n x

lemma sum_range_pow_dvd_case (p : ℕ) [Fact (Nat.Prime p)] (g : (ZMod p)ˣ)
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (n : ℕ) (hdvd : (p - 1) ∣ n) :
    ∑ i ∈ Finset.range (p - 1), (g : ZMod p) ^ (i * n) = -1 := by
  have hgn : g ^ n = 1 := (generator_pow_eq_one_iff p g hg n).mpr hdvd
  have hterm : ∀ i ∈ Finset.range (p - 1), (g : ZMod p) ^ (i * n) = 1 := by
    intro i _hi
    calc (g : ZMod p) ^ (i * n) = ((g : ZMod p) ^ n) ^ i := by rw [pow_mul']
      _ = ((g ^ n : (ZMod p)ˣ) : ZMod p) ^ i := rfl
      _ = ((1 : (ZMod p)ˣ) : ZMod p) ^ i := by rw [hgn]
      _ = (1 : ZMod p) ^ i := rfl
      _ = 1 := one_pow i
  calc ∑ i ∈ Finset.range (p - 1), (g : ZMod p) ^ (i * n)
      = ∑ i ∈ Finset.range (p - 1), (1 : ZMod p) := Finset.sum_congr rfl hterm
    _ = (Finset.range (p - 1)).card • (1 : ZMod p) := Finset.sum_const 1
    _ = (p - 1) • (1 : ZMod p) := by rw [Finset.card_range]
    _ = -1 := card_units_nsmul_one_eq_neg_one p

lemma sum_range_pow_not_dvd_case (p : ℕ) [Fact (Nat.Prime p)] (g : (ZMod p)ˣ)
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (n : ℕ) (hndvd : ¬(p - 1) ∣ n) :
    ∑ i ∈ Finset.range (p - 1), (g : ZMod p) ^ (i * n) = 0 := by
  set r : ZMod p := (g : ZMod p) ^ n with hr_def
  have hrw : ∀ i, (g : ZMod p) ^ (i * n) = r ^ i := fun i => by rw [mul_comm, pow_mul, hr_def]
  simp_rw [hrw]
  have hgeom : (∑ i ∈ Finset.range (p - 1), r ^ i) * (r - 1) = r ^ (p - 1) - 1 := geom_sum_mul r (p - 1)
  have hr_pow : r ^ (p - 1) = 1 := by
    rw [hr_def, ← pow_mul]
    have hdvd : (p - 1) ∣ (n * (p - 1)) := dvd_mul_left (p - 1) n
    have hgen := (generator_pow_eq_one_iff p g hg (n * (p - 1))).mpr hdvd
    have : (g : ZMod p) ^ (n * (p - 1)) = ((g ^ (n * (p - 1))) : (ZMod p)ˣ) := by
      simp [Units.val_pow_eq_pow_val]
    rw [this, hgen]; simp
  rw [hr_pow, sub_self] at hgeom
  have hr_ne_one : r ≠ 1 := by
    rw [hr_def]; intro h
    have : g ^ n = 1 := by ext; simp only [Units.val_pow_eq_pow_val, h, Units.val_one]
    rw [generator_pow_eq_one_iff p g hg n] at this
    exact hndvd this
  exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hr_ne_one)

lemma sum_pow_units_eq (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    ∑ u : (ZMod p)ˣ, (u : ZMod p)^n = if (p - 1) ∣ n then -1 else 0 := by
  haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime (Fact.out : Nat.Prime p)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  rw [sum_units_pow_eq_sum_range_pow p g hg n]
  split_ifs with hdvd
  · exact sum_range_pow_dvd_case p g hg n hdvd
  · exact sum_range_pow_not_dvd_case p g hg n hdvd

lemma fin_coe_eq_finEquiv (p : ℕ) [hp : Fact (Nat.Prime p)] (x : Fin p) :
    (x : ZMod p) = (ZMod.finEquiv p) x := by
  -- For p > 0, ZMod p = Fin p definitionally
  -- finEquiv p is RingEquiv.refl for p = n+1
  -- The goal is (x.val : ZMod p) = x
  -- Since ZMod p = Fin p, this is ((x.val : ℕ) : Fin p) = x
  -- which follows from Fin.val_cast_of_lt
  cases p with
  | zero => exact (hp.out.ne_zero rfl).elim
  | succ n =>
    -- ZMod (n+1) = Fin (n+1), finEquiv = refl
    simp only [ZMod.finEquiv]
    -- Goal: ↑↑x = (RingEquiv.refl (Fin (n+1))) x
    -- Use Fin.ext to compare values
    refine Fin.ext ?_
    -- Now we compare natural number values
    -- Goal: ↑↑↑x = ↑((RingEquiv.refl (Fin (n + 1))) x)
    -- LHS: val of (x.val cast to Fin (n+1))
    -- RHS: val of (RingEquiv.refl x) = x.val
    have h3 : ((RingEquiv.refl (Fin (n + 1))) x).val = x.val := rfl
    -- For Fin.val_natCast: ↑↑a = a % n where first ↑ is Fin.val
    -- Fin.val_natCast : ∀ (a n : ℕ) [inst : NeZero n], ↑↑a = a % n
    haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
    -- So (x.val : Fin (n+1)).val = x.val % (n+1)
    rw [Fin.val_natCast x.val (n + 1), Nat.mod_eq_of_lt x.isLt]
    -- Goal now: ↑x = ↑((RingEquiv.refl (Fin (n + 1))) x)
    exact h3.symm

lemma sum_Fin_eq_sum_ZMod (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    ∑ a : Fin p, (a : ZMod p)^n = ∑ a : ZMod p, a^n := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  refine Fintype.sum_equiv (ZMod.finEquiv p) _ _ (fun x => ?_)
  simp only [fin_coe_eq_finEquiv, RingEquiv.coe_toEquiv]

lemma powerSum_mod_eq (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (hn : 0 < n) :
    (∑ a : Fin p, (a : ZMod p)^n) = if (p - 1) ∣ n then -1 else 0 := by
  have hp : Nat.Prime p := Fact.out
  rw [sum_Fin_eq_sum_ZMod, ← Fintype.sum_subtype_add_sum_subtype (fun x : ZMod p => x ≠ 0)]
  have h2 : ∑ x : {x : ZMod p // x ≠ 0}, (x : ZMod p)^n = ∑ u : (ZMod p)ˣ, (u : ZMod p)^n := by
    rw [← Fintype.sum_equiv unitsEquivNeZero.symm]; intro x; simp
  rw [h2, sum_pow_units_eq]
  have h3 : ∑ x : {x : ZMod p // ¬x ≠ 0}, (x : ZMod p)^n = 0 := by
    have : ∀ x : {x : ZMod p // ¬x ≠ 0}, (x : ZMod p)^n = 0 := by
      intro ⟨x, hx⟩; simp only [not_not] at hx; simp [hx, zero_pow hn.ne']
    simp [Fintype.sum_eq_zero _ this]
  rw [h3, add_zero]

lemma prime_dvd_den_imp_padic_neg (q : ℚ) (p : ℕ) (hp : Nat.Prime p) (hdvd : p ∣ q.den) :
    padicValRat p q < 0 := by
  haveI := Fact.mk hp
  have h₁ : padicValRat p q = padicValInt p q.num - padicValNat p q.den := by
    rw [padicValRat.eq_1]

  rw [h₁]
  have h₂ : padicValNat p q.den ≥ 1 := by
    have h₃ : q.den ≠ 0 := by
      exact mod_cast q.den_nz
    have h₄ : p ∣ q.den := hdvd
    have h₅ : 1 ≤ padicValNat p q.den := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro h₆
      have h₈ : ¬p ∣ q.den := by
        intro h₉
        have h₁₀ : 1 ≤ padicValNat p q.den := by
          apply one_le_padicValNat_of_dvd
          <;> (try norm_num at h₃ ⊢)
          <;> (try assumption)
        linarith
      exact h₈ h₄
    exact h₅
  have h₃ : padicValInt p q.num = 0 := by
    have h₄ : ¬(p : ℤ) ∣ q.num := by
      intro h₅
      have h₆ : (p : ℕ) ∣ q.num.natAbs := by
        (try
          {
            have h₇ : (p : ℤ) ∣ q.num := h₅
            have h₈ : (p : ℕ) ∣ q.num.natAbs := by
              exact Int.natCast_dvd_natCast.mp (by simpa [Int.natAbs_of_nonneg (by
                have h₉ : 0 ≤ (p : ℤ) := by positivity
                linarith [h₉]
              )] using h₇)
            exact_mod_cast h₈
          })
      have h₇ : (p : ℕ) ∣ q.num.natAbs := h₆
      have h₈ : (p : ℕ) ∣ q.den := hdvd
      have h₉ : Nat.Coprime q.num.natAbs q.den := q.reduced
      have h₁₀ : (p : ℕ) ∣ q.num.natAbs := h₇
      have h₁₁ : (p : ℕ) ∣ q.den := h₈
      have h₁₂ : (p : ℕ) ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h₁₀ h₁₁
      have h₁₃ : Nat.gcd q.num.natAbs q.den = 1 := h₉
      have h₁₄ : (p : ℕ) ∣ 1 := by simpa [h₁₃] using h₁₂
      have h₁₅ : p ≤ 1 := Nat.le_of_dvd (by norm_num) h₁₄
      have h₁₆ : p ≥ 2 := Nat.Prime.two_le hp
      linarith
    have h₅ : padicValInt p q.num = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      exact_mod_cast h₄
    exact h₅

  have h₄ : (padicValInt p q.num : ℤ) - (padicValNat p q.den : ℤ) < 0 := by
    have h₅ : (padicValInt p q.num : ℤ) = 0 := by
      norm_cast
    rw [h₅]
    have h₆ : (padicValNat p q.den : ℤ) ≥ 1 := by
      norm_cast
    linarith

  have h₅ : (padicValInt p q.num : ℤ) - (padicValNat p q.den : ℤ) < 0 := h₄
  exact by
    simpa [h₁] using h₅

lemma padic_neg_imp_prime_dvd_den (q : ℚ) (p : ℕ) (hp : Nat.Prime p) (hneg : padicValRat p q < 0) :
    p ∣ q.den := by
  have hq_num_ne_zero : q.num ≠ 0 := by grind only [Rat.num_eq_zero, padicValRat.zero]
  have h_padicValInt_nonneg : 0 ≤ padicValInt p q.num := by simp
  have h_main_ineq : (padicValInt p q.num : ℤ) < (padicValNat p q.den : ℤ) := by grind only [padicValRat_def]
  have h_padicValNat_pos : 1 ≤ padicValNat p q.den := by grind
  have h_final : p ∣ q.den := by grind only [dvd_of_one_le_padicValNat]
  assumption

lemma prime_dvd_den_iff_padic_neg (q : ℚ) (p : ℕ) (hp : Nat.Prime p) :
    p ∣ q.den ↔ padicValRat p q < 0 :=
  ⟨prime_dvd_den_imp_padic_neg q p hp, padic_neg_imp_prime_dvd_den q p hp⟩

lemma two_pow_ge_succ (n : ℕ) (hn : 4 ≤ n) : 2 ^ n ≥ n + 1 := by
  have h_base : 2 ^ 4 ≥ 4 + 1 := by simp
  have h_inductive_step : ∀ (k : ℕ), 4 ≤ k → 2 ^ k ≥ k + 1 → 2 ^ (k + 1) ≥ (k + 1) + 1 := by grind
  have h_main : 2 ^ n ≥ n + 1 := by
    grind only [Int.two_pow_pred_sub_two_pow', Nat.lt_pow_self]
  assumption

lemma log_n_plus_one_le_n (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p) :
    Nat.log p (2 * k + 1) ≤ 2 * k := by
  have hk4 : 4 ≤ 2 * k := by omega
  have h2pow : 2 ^ (2 * k) ≥ 2 * k + 1 := two_pow_ge_succ (2 * k) hk4
  have hp2 : 2 ≤ p := hp.two_le
  have hpow : p ^ (2 * k) ≥ 2 ^ (2 * k) := Nat.pow_le_pow_left hp2 (2 * k)
  have hppow : p ^ (2 * k) ≥ 2 * k + 1 := le_trans h2pow hpow
  have hp1 : 1 < p := hp.one_lt
  calc Nat.log p (2 * k + 1) ≤ Nat.log p (p ^ (2 * k)) := Nat.log_mono_right hppow
    _ = 2 * k := Nat.log_pow hp1 (2 * k)

lemma padic_val_n_plus_one_le_n (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p) :
    (padicValNat p (2 * k + 1) : ℤ) ≤ 2 * k := by
  have h1 : padicValNat p (2 * k + 1) ≤ Nat.log p (2 * k + 1) := padicValNat_le_nat_log (2 * k + 1)
  have h2 : Nat.log p (2 * k + 1) ≤ 2 * k := log_n_plus_one_le_n k hk p hp
  calc (padicValNat p (2 * k + 1) : ℤ)
      ≤ (Nat.log p (2 * k + 1) : ℤ) := by exact_mod_cast h1
    _ ≤ (2 * k : ℤ) := by exact_mod_cast h2

lemma term_j0_padic_val_nonneg (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p) :
    let n := 2 * k
    let T0 := (p : ℚ)^n / (n + 1)
    0 ≤ padicValRat p T0 := by
  intro n T0
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hn_pos : 0 < n := by omega
  have hn1_pos : 0 < n + 1 := by omega
  have hp_pos : 0 < p := hp.pos
  have hp_gt_one : 1 < p := hp.one_lt
  have hpn_ne : ((p : ℚ)^n : ℚ) ≠ 0 := by positivity
  have hp_ne : (p : ℚ) ≠ 0 := by positivity
  have hn1_ne' : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  show 0 ≤ padicValRat p ((p : ℚ)^n / ((n : ℚ) + 1))
  rw [show ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) by simp]
  rw [padicValRat.div hpn_ne hn1_ne']
  simp only [padicValRat.of_nat]
  rw [padicValRat.pow hp_ne, padicValRat.self hp_gt_one]
  simp only [mul_one]
  have h := padic_val_n_plus_one_le_n k hk p hp
  have heq : n + 1 = 2 * k + 1 := rfl
  simp only [heq]
  omega

lemma term_j1_padic_val_nonneg (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p) :
    let n := 2 * k
    let T1 := (-(p : ℚ)^(n-1)) / 2
    0 ≤ padicValRat p T1 := by
  intro n T1
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hn1_pos : 0 < n - 1 := by omega
  have hp_ne_zero : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpow_ne : (p : ℚ)^(n-1) ≠ 0 := pow_ne_zero _ hp_ne_zero
  have hneg_ne : -(p : ℚ)^(n-1) ≠ 0 := neg_ne_zero.mpr hpow_ne
  have htwo_ne : (2 : ℚ) ≠ 0 := two_ne_zero
  -- Rewrite T1 = -p^(n-1) / 2 and use v_p(a/b) = v_p(a) - v_p(b)
  rw [padicValRat.div hneg_ne htwo_ne]
  -- Now need: 0 ≤ v_p(-p^(n-1)) - v_p(2)
  rw [padicValRat.neg]
  -- v_p(p^(n-1)) = n-1 as a rational p-adic valuation
  have hval_pow : padicValRat p ((p : ℚ) ^ (n - 1)) = (n - 1 : ℕ) := by
    have : ((p : ℚ) ^ (n - 1)) = ((p ^ (n-1) : ℕ) : ℚ) := by norm_cast
    rw [this, padicValRat.of_nat, padicValNat.prime_pow]
  rw [hval_pow]
  -- Now we need: 0 ≤ (n-1) - v_p(2)
  -- Since n = 2k with k ≥ 2, we have n - 1 = 2k - 1 ≥ 3.
  -- If p = 2: v_2(2) = 1, so we need 0 ≤ (n-1) - 1 = n - 2 = 2k - 2 ≥ 2.
  -- If p ≠ 2: v_p(2) = 0, so we need 0 ≤ n - 1 ≥ 3.
  rcases eq_or_ne p 2 with rfl | hp2
  · have h2 : (2 : ℚ) = ((2 : ℕ) : ℚ) := by norm_num
    rw [h2, padicValRat.of_nat, padicValNat_self]; omega
  · have h2 : (2 : ℚ) = ((2 : ℕ) : ℚ) := by norm_num
    have hval_two : padicValRat p 2 = 0 := by
      rw [h2, padicValRat.of_nat, Nat.cast_eq_zero]
      refine padicValNat.eq_zero_of_not_dvd ?_
      intro hdiv; exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdiv)
    rw [hval_two]; simp only [sub_zero]; omega

lemma padicValNat_succ_le_sub_one (p : ℕ) (hp : Nat.Prime p) (r : ℕ) (hr : 2 ≤ r) :
    padicValNat p (r + 1) ≤ r - 1 := by
  calc padicValNat p (r + 1) ≤ Nat.log p (r + 1) := padicValNat_le_nat_log (r + 1)
    _ ≤ r - 1 := by
      rcases hr.lt_or_eq with hr3 | rfl
      · have hr1 : r + 1 ≠ 0 := by omega
        have key : r + 1 < 2 ^ r := by
          have hr3' : 3 ≤ r := by omega
          have key' : ∀ n, 3 ≤ n → n + 1 < 2 ^ n := by
            intro n hn
            induction n using Nat.strong_induction_on with
            | _ n ih =>
              match n with
              | 0 => omega | 1 => omega | 2 => omega | 3 => norm_num | 4 => norm_num
              | n' + 5 =>
                have hlt : n' + 4 + 1 < 2 ^ (n' + 4) := ih (n' + 4) (by omega) (by omega)
                calc n' + 5 + 1 ≤ 2 * (n' + 4 + 1) := by omega
                  _ < 2 * 2 ^ (n' + 4) := by nlinarith
                  _ = 2 ^ (n' + 5) := by ring
          exact key' r hr3'
        have h2p : 2 ^ r ≤ p ^ r := Nat.pow_le_pow_left hp.two_le r
        have hlt : r + 1 < p ^ r := Nat.lt_of_lt_of_le key h2p
        have hlog : Nat.log p (r + 1) < r := Nat.log_lt_of_lt_pow hr1 hlt
        omega
      · have h3 : (3 : ℕ) ≠ 0 := by omega
        simp only [show (2 : ℕ) + 1 = 3 by omega, show (2 : ℕ) - 1 = 1 by omega]
        have hlt : 3 < p ^ 2 := calc
          3 < 4 := by omega
          _ = 2 ^ 2 := by norm_num
          _ ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2
        rw [← Nat.lt_succ_iff]
        exact Nat.log_lt_of_lt_pow h3 hlt

lemma even_j_ih_apply (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p)
    (ih : ∀ k' < k, 1 ≤ k' → padicValRat p (bernoulli (2 * k')) ≥ -1)
    (j : ℕ) (hj_even : Even j) (hj_ge : 2 ≤ j) (hj_lt : j < 2 * k) :
    padicValRat p (bernoulli j) ≥ -1 := by
  have h₁ : ∃ k', j = 2 * k' := by
    cases' hj_even with m hm
    exact ⟨m, by linarith⟩
  obtain ⟨k', hk'⟩ := h₁
  have h₂ : k' < k := by
    omega
  have h₃ : 1 ≤ k' := by
    omega
  have h₄ : padicValRat p (bernoulli (2 * k')) ≥ -1 := ih k' h₂ h₃
  have h₅ : bernoulli j = bernoulli (2 * k') := by
    rw [hk']
  rw [h₅]
  exact h₄

lemma r_ge_two (k : ℕ) (hk : 2 ≤ k) (j : ℕ) (hj_even : Even j) (hj_lt : j < 2 * k) :
    2 * k - j ≥ 2 := by
  have h₁ : j ≤ 2 * k := by
    omega
  have h₂ : j < 2 * k := hj_lt
  have h₃ : 2 * k - j > 0 := by
    omega
  have h₄ : Even j := hj_even
  -- Since j is even and j < 2k, we can write j = 2m for some m.
  -- We need to show that 2k - j ≥ 2, which is equivalent to j ≤ 2k - 2.
  -- Given that j is even and less than 2k, the largest possible value of j is 2k - 2.
  -- So we can directly check that 2k - j ≥ 2.
  have h₅ : 2 * k - j ≥ 2 := by
    by_contra h
    -- If 2k - j < 2, then 2k - j ≤ 1.
    have h₆ : 2 * k - j ≤ 1 := by
      omega
    -- But since j < 2k, we have 2k - j ≥ 1.
    have h₇ : 2 * k - j ≥ 1 := by
      omega
    -- So 2k - j = 1 or 2k - j = 0, but 2k - j cannot be 0 because j < 2k.
    have h₈ : 2 * k - j = 1 := by
      omega
    -- If 2k - j = 1, then j = 2k - 1. But j is even, so 2k - 1 is even.
    -- This implies that 2k is odd, which is a contradiction because 2k is always even.
    have h₉ : j = 2 * k - 1 := by
      omega
    have h₁₀ : Even j := hj_even
    rw [h₉] at h₁₀
    have h₁₁ : ¬Even (2 * k - 1) := by
      have h₁₂ : 2 * k - 1 = 2 * k - 1 := rfl
      rw [even_iff_two_dvd] at *
      have h₁₃ : 2 * k - 1 = 2 * (k - 1) + 1 := by
        cases k with
        | zero => omega
        | succ k' =>
          simp [Nat.mul_succ, Nat.add_assoc]
      rw [h₁₃]
      simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
    exact h₁₁ h₁₀
  exact h₅

lemma padic_val_Tj_eq (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p) (j : ℕ) (hj_ge : 2 ≤ j) (hj_lt : j < 2 * k) :
    let n := 2 * k
    let r := n - j
    let Tj := (Nat.choose n j : ℚ) / (r + 1) * bernoulli j * (p : ℚ)^r
    bernoulli j ≠ 0 →
    padicValRat p Tj = padicValRat p (Nat.choose n j : ℚ) - padicValRat p (r + 1 : ℚ) +
                        padicValRat p (bernoulli j) + r := by
  intro n r Tj hBj
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hC_ne : (Nat.choose n j : ℚ) ≠ 0 := by simp; exact (Nat.choose_pos (le_of_lt hj_lt)).ne'
  have hr1_ne : (r + 1 : ℚ) ≠ 0 := by positivity
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpr_ne : (p : ℚ)^r ≠ 0 := pow_ne_zero r hp_ne
  have hA_ne : (Nat.choose n j : ℚ) / (r + 1) ≠ 0 := div_ne_zero hC_ne hr1_ne
  have hB_ne : (Nat.choose n j : ℚ) / (r + 1) * bernoulli j ≠ 0 := mul_ne_zero hA_ne hBj
  show padicValRat p ((Nat.choose n j : ℚ) / (r + 1) * bernoulli j * (p : ℚ)^r) = _
  rw [padicValRat.mul hB_ne hpr_ne, padicValRat.mul hA_ne hBj,
      padicValRat.div hC_ne hr1_ne, padicValRat.pow hp_ne, padicValRat.self hp.one_lt]
  ring

lemma valuation_bound_nonneg (vC vD vB : ℤ) (r : ℕ) (hr : 2 ≤ r)
    (hvC : 0 ≤ vC) (hvD : vD ≤ r - 1) (hvB : -1 ≤ vB) :
    0 ≤ vC - vD + vB + r := by
  have h₅ : 0 ≤ vC - vD + vB + r := by nlinarith
  assumption

lemma term_zero_when_bernoulli_zero (k : ℕ) (p : ℕ) (j : ℕ) (hBj : bernoulli j = 0) :
    let n := 2 * k
    let r := n - j
    let Tj := (Nat.choose n j : ℚ) / (r + 1) * bernoulli j * (p : ℚ)^r
    0 ≤ padicValRat p Tj := by
  intro n r Tj
  have h₁ : Tj = 0 := by grind
  have h₂ : 0 ≤ padicValRat p Tj := by simp_all
  assumption

lemma padicValRat_nat_add_one_eq (p r : ℕ) :
    padicValRat p ((r : ℚ) + 1) = padicValNat p (r + 1) := by
  have h₁ : (r : ℚ) + 1 = (r + 1 : ℕ) := by norm_cast
  rw [h₁]; simp [padicValRat_of_nat]

lemma term_even_j_padic_val_nonneg (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p)
    (ih : ∀ k' < k, 1 ≤ k' → padicValRat p (bernoulli (2 * k')) ≥ -1)
    (j : ℕ) (hj_even : Even j) (hj_ge : 2 ≤ j) (hj_lt : j < 2 * k) :
    let n := 2 * k
    let r := n - j
    let Tj := (Nat.choose n j : ℚ) / (r + 1) * bernoulli j * (p : ℚ)^r
    0 ≤ padicValRat p Tj := by
  intro n r Tj
  -- Case split: if bernoulli j = 0, then Tj = 0 and padic val is 0 ≥ 0
  by_cases hBj : bernoulli j = 0
  · exact term_zero_when_bernoulli_zero k p j hBj
  -- Otherwise, use the valuation decomposition
  · have hr : 2 ≤ r := r_ge_two k hk j hj_even hj_lt
    have hvB : padicValRat p (bernoulli j) ≥ -1 := even_j_ih_apply k hk p hp ih j hj_even hj_ge hj_lt
    have hvC : 0 ≤ padicValRat p (Nat.choose n j : ℚ) := zero_le_padicValRat_of_nat _
    have hvD : (padicValNat p (r + 1) : ℤ) ≤ r - 1 := by
      have := padicValNat_succ_le_sub_one p hp r hr
      omega
    have hvD' : padicValRat p ((r : ℚ) + 1) ≤ r - 1 := by
      rw [padicValRat_nat_add_one_eq]
      exact_mod_cast hvD
    have hval := padic_val_Tj_eq k hk p hp j hj_ge hj_lt hBj
    rw [hval]
    exact valuation_bound_nonneg _ _ _ r hr hvC hvD' hvB

lemma n_plus_one_ne_zero (k : Nat) (hk : 2 <= k) : ((2 * k + 1 : Nat) : Rat) != 0 := by
  have h₁ : (2 * k + 1 : ℕ) ≠ 0 := by
    omega
  -- We need to show that the rational number corresponding to (2 * k + 1 : ℕ) is not zero.
  -- This is equivalent to showing that (2 * k + 1 : ℕ) is not zero, which we have already established.
  norm_cast at h₁ ⊢

lemma prime_cast_ne_zero (p : Nat) (hp : Nat.Prime p) : (p : Rat) != 0 := by
  have h₁ : p ≠ 0 := by
    intro h
    have h₂ := Nat.Prime.ne_zero hp
    contradiction
  -- Now use the fact that the cast is zero iff the natural number is zero
  norm_cast at h₁ ⊢
  <;> simp_all

lemma pow_factor_p (p n j : Nat) (hj : j < n) :
    (p : Rat)^(n + 1 - j) = p * (p : Rat)^(n - j) := by
  have h1 : n + 1 - j = (n - j) + 1 := by grind
  have h3 : (p : Rat)^((n - j) + 1) = p * (p : Rat)^(n - j) := by ring
  have h4 : (p : Rat)^(n + 1 - j) = p * (p : Rat)^(n - j) := by simp_all
  assumption

lemma faulhaber_term_at_n (n p : Nat) (hn : 0 < n) :
    bernoulli n * ((n + 1).choose n : Rat) * (p : Rat)^(n + 1 - n) / (n + 1) = p * bernoulli n := by
  have h_choose : (Nat.choose (n + 1) n : Rat) = (n + 1 : Rat) := by
    have h₁ : Nat.choose (n + 1) n = n + 1 := by
      simp [Nat.choose_succ_succ, Nat.choose_zero_right, Nat.choose_one_right]
    norm_cast

  have h_pow : (p : Rat) ^ (n + 1 - n : ℕ) = (p : Rat) := by
    have h₁ : (n + 1 - n : ℕ) = 1 := by
      have h₂ : n + 1 - n = 1 := by
        have h₄ : n + 1 - n = 1 := by
          omega
        exact h₄
      exact h₂
    rw [h₁]
    <;> simp [pow_one]

  calc
    bernoulli n * ((n + 1).choose n : Rat) * (p : Rat) ^ (n + 1 - n) / (n + 1) = bernoulli n * ((n + 1 : Rat)) * (p : Rat) / (n + 1 : Rat) := by
      rw [h_choose, h_pow]
    _ = (bernoulli n : Rat) * (p : Rat) := by
      have h₁ : (n + 1 : Rat) ≠ 0 := by positivity
      field_simp [h₁]
    _ = (p : Rat) * (bernoulli n : Rat) := by
      ring_nf
    _ = p * bernoulli n := by
      norm_cast

lemma S_eq_faulhaber_sum (n p : Nat) :
    (Finset.sum (Finset.range p) (fun a => (a : Rat)^n)) =
      Finset.sum (Finset.range (n + 1)) (fun i => bernoulli i * ((n + 1).choose i : Rat) * (p : Rat)^(n + 1 - i) / (n + 1)) := by
  exact sum_range_pow p n

lemma faulhaber_sum_split (n p : Nat) :
    Finset.sum (Finset.range (n + 1)) (fun i => bernoulli i * ((n + 1).choose i : Rat) * (p : Rat)^(n + 1 - i) / (n + 1)) =
    (Finset.sum (Finset.range n) (fun j => bernoulli j * ((n + 1).choose j : Rat) * (p : Rat)^(n + 1 - j) / (n + 1))) +
    bernoulli n * ((n + 1).choose n : Rat) * (p : Rat)^(n + 1 - n) / (n + 1) := by
  have h₁ : Finset.sum (Finset.range (n + 1)) (fun i => bernoulli i * ((n + 1).choose i : Rat) * (p : Rat)^(n + 1 - i) / (n + 1)) =
    (Finset.sum (Finset.range n) (fun j => bernoulli j * ((n + 1).choose j : Rat) * (p : Rat)^(n + 1 - j) / (n + 1))) +
    bernoulli n * ((n + 1).choose n : Rat) * (p : Rat)^(n + 1 - n) / (n + 1) := by
    rw [Finset.sum_range_succ]
  exact h₁

lemma remaining_sum_factor_p (n p : Nat) (hn : 0 < n) :
    (Finset.sum (Finset.range n) (fun j => bernoulli j * ((n + 1).choose j : Rat) * (p : Rat)^(n + 1 - j) / (n + 1))) =
    p * (Finset.sum (Finset.range n) (fun j => bernoulli j * ((n + 1).choose j : Rat) * (p : Rat)^(n - j) / (n + 1))) := by
  have h₁ : (Finset.sum (Finset.range n) (fun j => bernoulli j * ((n + 1).choose j : Rat) * (p : Rat)^(n + 1 - j) / (n + 1))) = (Finset.sum (Finset.range n) (fun j => p * (bernoulli j * ((n + 1).choose j : Rat) * (p : Rat)^(n - j) / (n + 1)))) := by
    apply Finset.sum_congr rfl
    intro j hj
    have h₂ : j ∈ Finset.range n := hj
    have h₃ : j < n := Finset.mem_range.mp h₂
    have h₄ : (n + 1 - j : ℕ) = (n - j : ℕ) + 1 := by
      have h₆ : n + 1 - j = (n - j) + 1 := by
        have h₈ : n + 1 - j = (n - j) + 1 := by
          omega
        exact h₈
      exact h₆
    have h₅ : ((p : Rat) : Rat) ^ (n + 1 - j : ℕ) = (p : Rat) ^ ((n - j : ℕ) + 1) := by
      rw [h₄]
    rw [h₅]
    have h₆ : (p : Rat) ^ ((n - j : ℕ) + 1) = (p : Rat) ^ (n - j : ℕ) * (p : Rat) := by
      rw [pow_succ]
    rw [h₆]
    have h₇ : (bernoulli j * ((n + 1).choose j : Rat) * ((p : Rat) ^ (n - j : ℕ) * (p : Rat)) / (n + 1 : Rat)) = p * (bernoulli j * ((n + 1).choose j : Rat) * (p : Rat) ^ (n - j : ℕ) / (n + 1 : Rat)) := by
      have h₈ : (bernoulli j * ((n + 1).choose j : Rat) * ((p : Rat) ^ (n - j : ℕ) * (p : Rat)) / (n + 1 : Rat)) = (bernoulli j * ((n + 1).choose j : Rat) * (p : Rat) ^ (n - j : ℕ) * (p : Rat) / (n + 1 : Rat)) := by ring
      rw [h₈]
      <;> ring_nf
    rw [h₇]
  rw [h₁]
  have h₂ : (Finset.sum (Finset.range n) (fun j => p * (bernoulli j * ((n + 1).choose j : Rat) * (p : Rat)^(n - j) / (n + 1)))) = p * (Finset.sum (Finset.range n) (fun j => bernoulli j * ((n + 1).choose j : Rat) * (p : Rat)^(n - j) / (n + 1))) := by
    rw [Finset.mul_sum]
  rw [h₂]

lemma S_eq_p_times_sum (k : Nat) (hk : 2 <= k) (p : Nat) :
    let n := 2 * k
    let S := (Finset.sum (Finset.range p) (fun a => (a : Rat)^n))
    let R := Finset.sum (Finset.range n) (fun j => bernoulli j * ((n + 1).choose j : Rat) * (p : Rat)^(n - j) / (n + 1))
    S = p * bernoulli n + p * R := by
  intro n S R
  have hn : 0 < n := by omega
  calc S = Finset.sum (Finset.range (n + 1)) (fun i => bernoulli i * ((n + 1).choose i : Rat) * (p : Rat)^(n + 1 - i) / (n + 1)) := S_eq_faulhaber_sum n p
    _ = (Finset.sum (Finset.range n) (fun j => bernoulli j * ((n + 1).choose j : Rat) * (p : Rat)^(n + 1 - j) / (n + 1))) +
        bernoulli n * ((n + 1).choose n : Rat) * (p : Rat)^(n + 1 - n) / (n + 1) := faulhaber_sum_split n p
    _ = (Finset.sum (Finset.range n) (fun j => bernoulli j * ((n + 1).choose j : Rat) * (p : Rat)^(n + 1 - j) / (n + 1))) +
        p * bernoulli n := by rw [faulhaber_term_at_n n p hn]
    _ = p * R + p * bernoulli n := by rw [remaining_sum_factor_p n p hn]
    _ = p * bernoulli n + p * R := by ring

lemma div_sub_eq_of_eq_mul (S B R : Rat) (p : Rat) (hp : p != 0) (hS : S = p * B + p * R) :
    S / p - B = R := by
  have h_div : S / p = B + R := by grind
  have h_final : S / p - B = R := by simp_all
  exact h_final

lemma faulhaber_remainder_eq_sum_terms (k : Nat) (hk : 2 <= k) (p : Nat) (hp : Nat.Prime p) :
    let n := 2 * k
    let S := (Finset.sum (Finset.range p) (fun a => (a : Rat)^n))
    S / p - bernoulli n =
      Finset.sum (Finset.range n) (fun j => (bernoulli j * (Nat.choose (n+1) j) * (p : Rat)^(n-j) / (n+1))) := by
  intro n S
  have hp_ne : (p : Rat) != 0 := prime_cast_ne_zero p hp
  have hS : S = p * bernoulli n + p * (Finset.sum (Finset.range n) (fun j => bernoulli j * ((n + 1).choose j : Rat) * (p : Rat)^(n - j) / (n + 1))) := S_eq_p_times_sum k hk p
  exact div_sub_eq_of_eq_mul S (bernoulli n) _ p hp_ne hS

lemma padic_val_neg_one_div_p (p : ℕ) (hp : Nat.Prime p) :
    padicValRat p ((-1 : ℚ) / p) = -1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have h₁ : padicValRat p ((-1 : ℚ) / p) = padicValRat p ((1 : ℚ) / p) := by
    have h₂ : padicValRat p ((-1 : ℚ) / p) = padicValRat p (-((1 : ℚ) / p)) := by
      norm_num [div_eq_mul_inv]
    rw [h₂]
    have h₃ : padicValRat p (-((1 : ℚ) / p)) = padicValRat p ((1 : ℚ) / p) := by
      -- Use the property that the p-adic valuation is the same for a number and its negative
      rw [padicValRat.neg]
    rw [h₃]
  rw [h₁]
  have h₂ : padicValRat p ((1 : ℚ) / p) = padicValRat p (1 : ℚ) - padicValRat p (p : ℚ) := by
    -- Use the property of the p-adic valuation for division
    have h₄ : (p : ℚ) ≠ 0 := by
      norm_cast
      <;> exact Nat.Prime.ne_zero hp
    have h₅ : padicValRat p ((1 : ℚ) / p) = padicValRat p (1 : ℚ) - padicValRat p (p : ℚ) := by
      rw [padicValRat.div] <;> simp_all
    exact h₅
  rw [h₂]
  have h₃ : padicValRat p (1 : ℚ) = 0 := by
    -- The p-adic valuation of 1 is 0
    simp [padicValRat.one]
  have h₄ : padicValRat p (p : ℚ) = 1 := by
    -- The p-adic valuation of p is 1
    have h₅ : 1 < p := Nat.Prime.one_lt hp
    have h₆ : padicValRat p (p : ℚ) = 1 := by
      -- Use the property of the p-adic valuation for p
      norm_cast
      <;> simp_all [padicValRat, Nat.cast_one, Nat.cast_zero, Nat.cast_add, padicValInt]
    exact h₆
  rw [h₃, h₄]
  <;> norm_num

lemma padic_val_int_cast_nonneg (p : ℕ) (t : ℤ) : 0 ≤ padicValRat p (t : ℚ) := by
  have h_final : 0 ≤ padicValRat p (t : ℚ) := by simp
  exact h_final

lemma term_form_eq (n p j : ℕ) (hj : j ≤ n) :
    let r := n - j
    (Nat.choose n j : ℚ) / (r + 1) * bernoulli j * (p : ℚ)^r =
    bernoulli j * (Nat.choose (n+1) j) * (p : ℚ)^(n-j) / (n+1) := by
  intro r
  have h₁ : r = n - j := rfl
  have h₂ : n - j + 1 = n + 1 - j := by
    have h₄ : n - j + j = n := by omega
    have h₆ : n - j + 1 = n + 1 - j := by
      omega
    exact h₆
  have h₃ : (n + 1 - j : ℕ) = (r + 1 : ℕ) := by
    simp [h₁, h₂] at *
  have h₄ : (Nat.choose (n + 1) j : ℚ) = ((n + 1 : ℚ) : ℚ) / (r + 1 : ℚ) * (Nat.choose n j : ℚ) := by
    have h₅ : Nat.choose (n + 1) j * (r + 1 : ℕ) = (n + 1 : ℕ) * Nat.choose n j := by
      have h₆ : r = n - j := rfl
      have h₉ : (n + 1).choose j * (n + 1 - j) = (n + 1 : ℕ) * n.choose j := by
        have h₁₀ : n.choose j * (n + 1) = (n + 1).choose j * (n + 1 - j) := by
          have h₁₁ : n.choose j * (n + 1) = (n + 1).choose j * (n + 1 - j) := by
            rw [Nat.choose_mul_succ_eq]
          exact h₁₁
        linarith
      calc
        Nat.choose (n + 1) j * (r + 1 : ℕ) = (n + 1).choose j * (n + 1 - j) := by
          simp [h₆]
          <;>
          (try omega)
        _ = (n + 1 : ℕ) * n.choose j := by
          rw [h₉]
        _ = (n + 1 : ℕ) * Nat.choose n j := by
          simp [Nat.choose_symm_add]
    have h₆ : (Nat.choose (n + 1) j : ℚ) = ((n + 1 : ℚ) : ℚ) / (r + 1 : ℚ) * (Nat.choose n j : ℚ) := by
      have h₇ : (r + 1 : ℕ) ≠ 0 := by
        omega
      have h₈ : (Nat.choose (n + 1) j : ℚ) * (r + 1 : ℚ) = ((n + 1 : ℚ) : ℚ) * (Nat.choose n j : ℚ) := by
        norm_cast at h₅ ⊢
      have h₉ : (r + 1 : ℚ) ≠ 0 := by positivity
      field_simp at h₈ ⊢ <;>
      (try ring_nf at * <;> nlinarith)
    exact h₆
  calc
    (Nat.choose n j : ℚ) / (r + 1) * bernoulli j * (p : ℚ) ^ r = (Nat.choose n j : ℚ) / (r + 1) * (p : ℚ) ^ r * bernoulli j := by ring
    _ = (Nat.choose n j : ℚ) / (r + 1) * (p : ℚ) ^ (n - j) * bernoulli j := by
      simp [h₁] at *
    _ = ((Nat.choose n j : ℚ) / (r + 1)) * (p : ℚ) ^ (n - j) * bernoulli j := by ring
    _ = ((n + 1 : ℚ) / (r + 1 : ℚ) * (Nat.choose n j : ℚ)) / (n + 1 : ℚ) * (p : ℚ) ^ (n - j) * bernoulli j := by
      field_simp
    _ = (Nat.choose (n + 1) j : ℚ) / (n + 1 : ℚ) * (p : ℚ) ^ (n - j) * bernoulli j := by
      rw [h₄]
    _ = bernoulli j * (Nat.choose (n + 1) j : ℚ) * (p : ℚ) ^ (n - j) / (n + 1 : ℚ) := by
      ring_nf
    _ = bernoulli j * (Nat.choose (n + 1) j) * (p : ℚ) ^ (n - j) / (n + 1) := by norm_cast

lemma term_j1_alternate_form (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p) :
    let n := 2 * k
    0 ≤ padicValRat p ((Nat.choose n 1 : ℚ) / (↑(n - 1) + 1) * bernoulli 1 * (p : ℚ)^(n - 1)) := by
  intro n
  -- n = 2*k with k ≥ 2, so n ≥ 4
  have hn : n = 2 * k := rfl
  have hn_ge : n ≥ 4 := by omega
  have hn_pos : 0 < n := by omega
  have hn_sub_one_pos : 0 < n - 1 := by omega
  -- (n - 1) + 1 = n in ℕ (since n ≥ 1)
  have h_nsum : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  -- choose n 1 = n
  have h_choose : n.choose 1 = n := Nat.choose_one_right n
  -- The quotient is 1
  have h_quot : (n.choose 1 : ℚ) / (↑(n - 1) + 1) = 1 := by
    rw [h_choose]
    have h_cast : (↑(n - 1) + 1 : ℚ) = (n : ℚ) := by
      simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      ring
    rw [h_cast]
    field_simp
  -- bernoulli 1 = -1/2
  have h_B1 : bernoulli 1 = -1/2 := bernoulli_one
  -- Now show the expression equals -p^(n-1)/2
  have h_expr : (n.choose 1 : ℚ) / (↑(n - 1) + 1) * bernoulli 1 * (p : ℚ)^(n - 1) =
                -(p : ℚ)^(n - 1) / 2 := by
    rw [h_quot, h_B1]
    ring
  rw [h_expr]
  exact term_j1_padic_val_nonneg k hk p hp

lemma all_terms_padic_val_nonneg (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p)
    (ih : ∀ k' < k, 1 ≤ k' → padicValRat p (bernoulli (2 * k')) ≥ -1)
    (j : ℕ) (hj : j < 2 * k) :
    let n := 2 * k
    let Tj := bernoulli j * (Nat.choose (n+1) j) * (p : ℚ)^(n-j) / (n+1)
    0 ≤ padicValRat p Tj := by
  simp only
  have hj_le : j ≤ 2 * k := Nat.le_of_lt hj
  rw [← term_form_eq (2 * k) p j hj_le]
  rcases j with _ | j
  · -- j = 0
    simp only [bernoulli_zero, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
    have heq : (1 : ℚ) / (↑(2 * k) + 1) * 1 * ↑p ^ (2 * k) = ↑p ^ (2 * k) / (↑(2 * k) + 1) := by ring
    rw [heq]
    exact term_j0_padic_val_nonneg k hk p hp
  · rcases j with _ | j
    · -- j = 1
      exact term_j1_alternate_form k hk p hp
    · -- j ≥ 2
      have hj_ge2 : 2 ≤ j + 2 := by omega
      rcases Nat.even_or_odd (j + 2) with heven | hodd
      · -- even case
        exact term_even_j_padic_val_nonneg k hk p hp ih (j + 2) heven hj_ge2 hj
      · -- odd case, j + 2 > 1
        have hgt1 : 1 < j + 2 := by omega
        have hbern : bernoulli (j + 2) = 0 := bernoulli_eq_zero_of_odd hodd hgt1
        exact term_zero_when_bernoulli_zero k p (j + 2) hbern

lemma sum_padic_val_nonneg_of_all_nonneg (p : ℕ) (hp : Nat.Prime p)
    (S : Finset ℕ) (f : ℕ → ℚ)
    (h : ∀ j ∈ S, 0 ≤ padicValRat p (f j)) :
    0 ≤ padicValRat p (∑ j ∈ S, f j) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  induction S using Finset.induction_on with
  | empty => simp [padicValRat.zero]
  | insert a S' hnotin ih =>
    rw [Finset.sum_insert hnotin]
    by_cases hsum : f a + ∑ j ∈ S', f j = 0
    · simp [hsum, padicValRat.zero]
    · have h1 : 0 ≤ padicValRat p (f a) := h a (Finset.mem_insert_self a S')
      have h2 : 0 ≤ padicValRat p (∑ j ∈ S', f j) := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      calc 0 ≤ min (padicValRat p (f a)) (padicValRat p (∑ j ∈ S', f j)) := le_min h1 h2
        _ ≤ padicValRat p (f a + ∑ j ∈ S', f j) := padicValRat.min_le_padicValRat_add hsum

lemma faulhaber_remainder_padic_val_nonneg (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p)
    (ih : ∀ k' < k, 1 ≤ k' → padicValRat p (bernoulli (2 * k')) ≥ -1) :
    let n := 2 * k
    let S := (∑ a ∈ Finset.range p, (a : ℚ)^n)
    0 ≤ padicValRat p (S / p - bernoulli n) := by
  intro n S
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [faulhaber_remainder_eq_sum_terms k hk p hp]
  apply sum_padic_val_nonneg_of_all_nonneg p hp (Finset.range n)
  intro j hj
  exact all_terms_padic_val_nonneg k hk p hp ih j (Finset.mem_range.mp hj)

lemma sum_int_cast_eq_sum_zmod (p n : ℕ) [hp : Fact (Nat.Prime p)] :
    (↑(∑ a ∈ Finset.range p, (a : ℤ)^n) : ZMod p) = ∑ a : Fin p, (a : ZMod p)^n := by
  rw [Int.cast_sum]
  simp only [Int.cast_pow, Int.cast_natCast]
  rw [Finset.sum_range]

lemma rat_sum_range_eq_int_sum_cast (p n : ℕ) :
    (∑ a ∈ Finset.range p, (a : ℚ)^n) = ((∑ a ∈ Finset.range p, (a : ℤ)^n) : ℚ) := by
  have h₁ : (∑ a ∈ Finset.range p, (a : ℚ)^n) = ∑ a ∈ Finset.range p, ((a : ℤ)^n : ℚ) := by
    apply Finset.sum_congr rfl
    intro a _
    have h₂ : (a : ℚ) ^ n = ((a : ℤ) ^ n : ℚ) := by
      norm_cast
    rw [h₂]
  rw [h₁]

lemma powerSum_dvd_of_not_dvd (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p)
    (hndvd : ¬(p - 1) ∣ (2 * k)) :
    ∃ t : ℤ, (∑ a ∈ Finset.range p, (a : ℚ)^(2 * k)) = p * t := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  -- Step 1: The ZMod p sum is 0 by powerSum_mod_eq
  have hn_pos : 0 < 2 * k := Nat.mul_pos (by norm_num) (Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hk)
  have hsum_zero : (∑ a : Fin p, (a : ZMod p)^(2 * k)) = 0 := by
    rw [powerSum_mod_eq p (2 * k) hn_pos]
    simp only [hndvd, ↓reduceIte]
  -- Step 2: By sum_int_cast_eq_sum_zmod, the integer sum cast to ZMod p is 0
  have hcast_zero : (↑(∑ a ∈ Finset.range p, (a : ℤ)^(2 * k)) : ZMod p) = 0 := by
    rw [sum_int_cast_eq_sum_zmod]
    exact hsum_zero
  -- Step 3: By ZMod.intCast_zmod_eq_zero_iff_dvd, p divides the integer sum
  have hdvd : (p : ℤ) ∣ (∑ a ∈ Finset.range p, (a : ℤ)^(2 * k)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hcast_zero
  -- Step 4: Get the witness t
  obtain ⟨t, ht⟩ := hdvd
  use t
  -- Step 5: Rewrite the ℚ sum as the integer sum cast to ℚ
  rw [rat_sum_range_eq_int_sum_cast]
  exact_mod_cast ht

lemma bernoulli_two_mul_ne_zero (k : ℕ) (hk : 1 ≤ k) : bernoulli (2 * k) ≠ 0 := by
  have h1 : (2 * k : ℕ) ≠ 0 := by
    omega

  have h2 : riemannZeta (2 * (k : ℕ)) = (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1) *
      (Real.pi : ℂ) ^ (2 * k) * (bernoulli (2 * k) : ℂ) / ((2 * k).factorial : ℂ) := by
    have h4 : riemannZeta (2 * (k : ℕ)) = (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1) * (Real.pi : ℂ) ^ (2 * k) * (bernoulli (2 * k) : ℂ) / ((2 * k).factorial : ℂ) := by
      have h5 : riemannZeta (2 * (k : ℕ)) = (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1) * (Real.pi : ℂ) ^ (2 * k) * (bernoulli (2 * k) : ℂ) / ((2 * k).factorial : ℂ) := by
        -- Use the known formula for ζ(2k) in terms of Bernoulli numbers
        have h6 : riemannZeta (2 * (k : ℕ)) = (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1) * (Real.pi : ℂ) ^ (2 * k) * (bernoulli (2 * k) : ℂ) / ((2 * k).factorial : ℂ) := by
          -- Use the known formula for ζ(2k) in terms of Bernoulli numbers
          have h7 : (k : ℕ) ≠ 0 := by
            intro h8
            linarith
          -- Use the known formula for ζ(2k) in terms of Bernoulli numbers
          rw [riemannZeta_two_mul_nat]
          <;>
          norm_cast
        exact h6
      exact h5
    exact h4

  have h3 : riemannZeta (2 * (k : ℕ)) ≠ 0 := by
    have h4 : 1 < (2 * (k : ℕ) : ℝ) := by
      have h7 : (2 * (k : ℕ) : ℝ) ≥ 2 * (1 : ℝ) := by
        have h8 : (k : ℝ) ≥ 1 := by exact_mod_cast hk
        linarith
      have h9 : (1 : ℝ) < (2 * (k : ℕ) : ℝ) := by
        linarith
      exact h9
    have h10 : riemannZeta (2 * (k : ℕ)) ≠ 0 := by
      -- Use the property that ζ(s) ≠ 0 when Re(s) > 1
      have h11 : (1 : ℝ) < (2 * (k : ℕ) : ℝ) := h4
      have h14 : riemannZeta (2 * (k : ℕ)) ≠ 0 := by
        -- Use the fact that ζ(s) ≠ 0 when Re(s) > 1
        have h15 : riemannZeta (2 * (k : ℕ)) ≠ 0 := by
          -- Use the property of the Riemann zeta function
          have h17 : riemannZeta (2 * (k : ℕ)) ≠ 0 := by
            -- Use the property of the Riemann zeta function
            apply riemannZeta_ne_zero_of_one_lt_re
            <;> simp_all [Complex.ext_iff]
          exact h17
        exact h15
      exact h14
    exact h10

  have h4 : (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1) * (Real.pi : ℂ) ^ (2 * k) * (bernoulli (2 * k) : ℂ) / ((2 * k).factorial : ℂ) ≠ 0 := by
    have h5 : (-1 : ℂ) ^ (k + 1) ≠ 0 := by
      simp [Complex.ext_iff, pow_add, pow_one, pow_mul]
    have h6 : (2 : ℂ) ^ (2 * k - 1) ≠ 0 := by
      simp [Complex.ext_iff, pow_add, pow_one, pow_mul]
    have h7 : (Real.pi : ℂ) ^ (2 * k) ≠ 0 := by
      have h8 : (Real.pi : ℂ) ≠ 0 := by
        norm_num [Complex.ext_iff]
      have h9 : (Real.pi : ℂ) ^ (2 * k) ≠ 0 := by
        exact pow_ne_zero _ h8
      exact h9
    have h8 : (bernoulli (2 * k) : ℂ) ≠ 0 := by
      by_contra h9
      have h10 : (bernoulli (2 * k) : ℂ) = 0 := by simpa using h9
      have h11 : (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1) * (Real.pi : ℂ) ^ (2 * k) * (bernoulli (2 * k) : ℂ) / ((2 * k).factorial : ℂ) = 0 := by
        simp [h10]
      have h12 : riemannZeta (2 * (k : ℕ)) = 0 := by
        rw [h2] at *
        simp_all
      contradiction
    have h9 : ((2 * k).factorial : ℂ) ≠ 0 := by
      norm_cast
      <;>
      (try
        {
          positivity
        })
    have h10 : (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1) * (Real.pi : ℂ) ^ (2 * k) * (bernoulli (2 * k) : ℂ) / ((2 * k).factorial : ℂ) ≠ 0 := by
      intro h11
      have h12 : (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1) * (Real.pi : ℂ) ^ (2 * k) * (bernoulli (2 * k) : ℂ) = 0 := by
        field_simp [h9] at h11 ⊢
        <;>
        (try
          {
            simp_all [Complex.ext_iff, pow_add, pow_one, pow_mul]
          })
      have h13 : (-1 : ℂ) ^ (k + 1) ≠ 0 := h5
      have h14 : (2 : ℂ) ^ (2 * k - 1) ≠ 0 := h6
      have h15 : (Real.pi : ℂ) ^ (2 * k) ≠ 0 := h7
      have h16 : (bernoulli (2 * k) : ℂ) ≠ 0 := h8
      simp_all [mul_eq_mul_left_iff, h13, h14, h15, h16]
    exact h10

  have h5 : (bernoulli (2 * k) : ℂ) ≠ 0 := by
    by_contra h
    have h6 : (bernoulli (2 * k) : ℂ) = 0 := by simpa using h
    have h7 : (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1) * (Real.pi : ℂ) ^ (2 * k) * (bernoulli (2 * k) : ℂ) / ((2 * k).factorial : ℂ) = 0 := by
      rw [h6]
      simp [mul_zero, div_eq_mul_inv]
    contradiction

  have h6 : bernoulli (2 * k) ≠ 0 := by
    intro h7
    have h8 : (bernoulli (2 * k) : ℂ) = 0 := by
      norm_cast
    contradiction

  exact h6

lemma padic_val_bernoulli_nonneg_of_not_dvd (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p)
    (ih : ∀ k' < k, 1 ≤ k' → padicValRat p (bernoulli (2 * k')) ≥ -1)
    (hndvd : ¬(p - 1) ∣ (2 * k)) :
    0 ≤ padicValRat p (bernoulli (2 * k)) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  -- Get the power sum S and witness t s.t. S = p * t
  obtain ⟨t, ht⟩ := powerSum_dvd_of_not_dvd k hk p hp hndvd
  -- Show S/p = t
  have hSdivp : (∑ a ∈ Finset.range p, (a : ℚ)^(2 * k)) / p = t := by
    rw [ht]
    have hp_pos : (0 : ℚ) < p := Nat.cast_pos.mpr hp.pos
    field_simp
  -- The p-adic valuation of t (as an integer) is nonneg
  have hvt : 0 ≤ padicValRat p (t : ℚ) := by
    rw [padicValRat.of_int]
    simp only [Nat.cast_nonneg]
  -- Get nonneg valuation of S/p - B_n from Faulhaber
  have hrem := faulhaber_remainder_padic_val_nonneg k hk p hp ih
  simp only at hrem
  -- Have S / p - bernoulli n = t - bernoulli n
  have hrem' : 0 ≤ padicValRat p (↑t - bernoulli (2 * k)) := by
    convert hrem using 2
    rw [← hSdivp]
  -- Bernoulli(2k) is nonzero for k ≥ 2 ≥ 1
  have hBne : bernoulli (2 * k) ≠ 0 := bernoulli_two_mul_ne_zero k (Nat.one_le_of_lt hk)
  -- Write B = t - (t - B)
  have heq : bernoulli (2 * k) = ↑t + (-(↑t - bernoulli (2 * k))) := by ring
  -- Apply the triangle inequality: min v(t) v(-(t - B)) ≤ v(t + (-(t - B))) = v(B)
  rw [heq]
  have hne : ↑t + (-(↑t - bernoulli (2 * k))) ≠ 0 := by
    convert hBne using 1
    ring
  apply le_trans _ (padicValRat.min_le_padicValRat_add hne)
  rw [padicValRat.neg]
  exact le_min hvt hrem'

lemma powerSum_eq_neg_one_mod_of_dvd (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p)
    (hdvd : (p - 1) ∣ (2 * k)) :
    ∃ t : ℤ, (∑ a ∈ Finset.range p, (a : ℚ)^(2 * k)) = -1 + p * t := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  -- Define the integer sum
  let S : ℤ := ∑ a ∈ Finset.range p, (a : ℤ)^(2 * k)
  -- The rational sum equals the integer S
  have hS : (∑ a ∈ Finset.range p, (a : ℚ)^(2 * k)) = S := by
    simp only [S, Int.cast_sum, Int.cast_pow, Int.cast_natCast]
  -- Use powerSum_mod_eq to get the ZMod result
  have hmod : (∑ a : Fin p, (a : ZMod p)^(2 * k)) = -1 := by
    rw [powerSum_mod_eq p (2 * k) (by omega : 0 < 2 * k)]
    simp [hdvd]
  -- The integer sum cast to ZMod p equals the ZMod sum
  have hcast : (S : ZMod p) = ∑ a : Fin p, (a : ZMod p)^(2 * k) := by
    exact sum_int_cast_eq_sum_zmod p (2 * k)
  -- S ≡ -1 (mod p) in ℤ
  have hcong : (S : ZMod p) = -1 := by rw [hcast, hmod]
  -- Convert congruence to divisibility
  have hdiv : (p : ℤ) ∣ S + 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcong]
    ring
  -- Extract the quotient
  obtain ⟨t, ht⟩ := hdiv
  use t
  rw [hS]
  have : S = -1 + p * t := by omega
  simp only [this, Int.cast_add, Int.cast_neg, Int.cast_one, Int.cast_mul, Int.cast_natCast]

lemma sum_ne_zero (p : ℕ) (hp : Nat.Prime p) (t : ℤ) :
    (t : ℚ) + (-1 : ℚ) / p ≠ 0 := by
  intro h
  have h₁ : (p : ℕ) ≠ 0 := by
    have := hp.ne_zero
    simpa using this
  have h₂ : (p : ℚ) ≠ 0 := by
    norm_cast
  have h₃ : ((t : ℚ) + (-1 : ℚ) / p) = 0 := by simpa using h
  field_simp [h₂] at h₃
  ring_nf at h₃
  norm_cast at h₃
  have h₄ : (p : ℤ) ≠ 0 := by
    have := hp.ne_zero
    norm_cast at this ⊢
  have h₅ : (p : ℤ) > 1 := by
    have := Nat.Prime.one_lt hp
    norm_cast at this ⊢
  have h₆ : (t : ℤ) * p = 1 := by
    omega
  have h₇ : (t : ℤ) = 0 := by
    have h₁₀ : (t : ℤ) = 0 := by
      by_contra h₁₀
      have h₁₁ : (t : ℤ) ≠ 0 := h₁₀
      have h₁₂ : (t : ℤ) ≥ 1 ∨ (t : ℤ) ≤ -1 := by
        cases' lt_or_gt_of_ne h₁₁ with h₁₃ h₁₃
        · -- Case: t < 0
          have h₁₄ : (t : ℤ) ≤ -1 := by
            by_contra h₁₄
            linarith
          exact Or.inr h₁₄
        · -- Case: t > 0
          have h₁₄ : (t : ℤ) ≥ 1 := by
            by_contra h₁₄
            linarith
          exact Or.inl h₁₄
      cases' h₁₂ with h₁₂ h₁₂
      · -- Subcase: t ≥ 1
        have h₁₃ : (t : ℤ) * p ≥ 1 * p := by
          nlinarith
        nlinarith
      · -- Subcase: t ≤ -1
        have h₁₃ : (t : ℤ) * p ≤ -1 * p := by
          nlinarith
        nlinarith
    exact h₁₀
  have h₈ : (t : ℤ) * p = 0 := by
    rw [h₇]
    <;> simp [h₄]
  omega

lemma neg_one_div_p_ne_zero (p : ℕ) (hp : Nat.Prime p) :
    (-1 : ℚ) / p ≠ 0 := by
  have h₁ : (p : ℚ) ≠ 0 := by
    norm_cast <;>
    (try simp_all [Nat.Prime.ne_zero])

  have h₂ : (-1 : ℚ) / p ≠ 0 := by
    field_simp [h₁]
    <;>
    norm_num <;>
    (try simp_all [Nat.Prime.ne_zero])

  exact h₂

lemma padic_val_add_neg_one_div_p (p : ℕ) (hp : Nat.Prime p) (t : ℤ) (ht : t ≠ 0) :
    padicValRat p ((t : ℚ) + (-1 : ℚ) / p) = -1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hval_neg : padicValRat p ((-1 : ℚ) / p) = -1 := padic_val_neg_one_div_p p hp
  have hval_t : 0 ≤ padicValRat p (t : ℚ) := padic_val_int_cast_nonneg p t
  have hlt : padicValRat p ((-1 : ℚ) / p) < padicValRat p (t : ℚ) := by
    rw [hval_neg]
    omega
  have hsum_ne : (-1 : ℚ) / p + (t : ℚ) ≠ 0 := by
    rw [add_comm]
    exact sum_ne_zero p hp t
  have hneg_ne : (-1 : ℚ) / p ≠ 0 := neg_one_div_p_ne_zero p hp
  have ht_ne : (t : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ht
  rw [add_comm, padicValRat.add_eq_of_lt hsum_ne hneg_ne ht_ne hlt, hval_neg]

lemma padic_val_S_div_p_eq_neg_one (k : ℕ) (_hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p)
    (t : ℤ) (hS : (∑ a ∈ Finset.range p, (a : ℚ)^(2 * k)) = -1 + (p : ℚ) * t) :
    padicValRat p ((∑ a ∈ Finset.range p, (a : ℚ)^(2 * k)) / p) = -1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp_pos : (p : ℚ) ≠ 0 := by simp [hp.ne_zero]
  -- Rewrite S/p = (-1 + p*t)/p = -1/p + t
  rw [hS]
  have h_eq : (-1 + (p : ℚ) * t) / p = (t : ℚ) + (-1 : ℚ) / p := by
    field_simp
    ring
  rw [h_eq]
  -- goal: v_p(t + (-1/p)) = -1
  by_cases ht : t = 0
  · -- Case t = 0: v_p(-1/p) = -1
    simp only [ht, Int.cast_zero, zero_add]
    exact padic_val_neg_one_div_p p hp
  · -- Case t ≠ 0: apply padicValRat.add_eq_of_lt
    exact padic_val_add_neg_one_div_p p hp t ht

lemma padic_val_eq_of_diff_nonneg (p : ℕ) (hp : Nat.Prime p) (x y : ℚ)
    (hx : padicValRat p x = -1) (hdiff : 0 ≤ padicValRat p (x - y)) (hy_ne : y ≠ 0) :
    padicValRat p y = -1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  -- Case split on whether x - y = 0
  by_cases hxy : x - y = 0
  · -- If x - y = 0, then x = y, so v_p(y) = v_p(x) = -1
    have : x = y := sub_eq_zero.mp hxy
    rw [← this, hx]
  · -- If x - y ≠ 0, apply ultrametric inequality
    -- Key: y = x + (-(x-y)), and v_p(x) = -1 < 0 ≤ v_p(x-y) = v_p(-(x-y))
    have hx_ne : x ≠ 0 := by
      intro hx_eq
      rw [hx_eq, padicValRat.zero] at hx
      omega
    have hneg_ne : -(x - y) ≠ 0 := neg_ne_zero.mpr hxy
    have hy_eq : y = x + (-(x - y)) := by ring
    -- v_p(-(x-y)) = v_p(x-y) ≥ 0 > -1 = v_p(x)
    have hval_neg : padicValRat p (-(x - y)) = padicValRat p (x - y) := padicValRat.neg _
    have hlt : padicValRat p x < padicValRat p (-(x - y)) := by
      rw [hval_neg, hx]
      omega
    have hsum_ne : x + (-(x - y)) ≠ 0 := by rw [← hy_eq]; exact hy_ne
    rw [hy_eq, padicValRat.add_eq_of_lt hsum_ne hx_ne hneg_ne hlt, hx]

lemma padic_val_bernoulli_eq_neg_one_of_dvd (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p)
    (ih : ∀ k' < k, 1 ≤ k' → padicValRat p (bernoulli (2 * k')) ≥ -1)
    (hdvd : (p - 1) ∣ (2 * k)) :
    padicValRat p (bernoulli (2 * k)) = -1 := by
  -- Step 1: Get S = -1 + p * t from the divisibility hypothesis
  obtain ⟨t, hS⟩ := powerSum_eq_neg_one_mod_of_dvd k hk p hp hdvd
  -- Define S for convenience
  set S : ℚ := ∑ a ∈ Finset.range p, (a : ℚ)^(2 * k) with hS_def
  -- Step 2: v_p(S/p) = -1
  have hval_S_div : padicValRat p (S / p) = -1 := padic_val_S_div_p_eq_neg_one k hk p hp t hS
  -- Step 3: Get the Faulhaber remainder bound: v_p(S/p - B_{2k}) ≥ 0
  have hFaul := faulhaber_remainder_padic_val_nonneg k hk p hp ih
  -- Step 4: B_{2k} ≠ 0
  have hB_ne : bernoulli (2 * k) ≠ 0 := bernoulli_two_mul_ne_zero k (Nat.one_le_of_lt hk)
  -- Step 5: Apply the case-analysis lemma to conclude v_p(B_{2k}) = -1
  exact padic_val_eq_of_diff_nonneg p hp (S / p) (bernoulli (2 * k)) hval_S_div hFaul hB_ne

/-- The iff characterization for k ≥ 2 via p-adic analysis.

    From Faulhaber: S(n,p)/p - B_n ∈ Z_(p) (by faulhaber_remainder_padic_val_nonneg).
    From powerSum_mod_eq: S(n,p) ≡ -1 (mod p) if (p-1)|n, else S(n,p) ≡ 0 (mod p).

    If (p-1) ∤ n: S(n,p) = p·t for some t ∈ Z, so S(n,p)/p = t ∈ Z ⊆ Z_(p).
       Then B_n = t - (S/p - B_n) ∈ Z_(p), so v_p(B_n) ≥ 0, so p ∤ den(B_n).

    If (p-1) | n: S(n,p) = -1 + p·t for some t ∈ Z, so S(n,p)/p = t - 1/p.
       Then B_n = (t - 1/p) - (S/p - B_n) ≡ -1/p (mod Z_(p)).
       Since -1/p ∉ Z_(p), we have v_p(B_n) = -1 < 0, so p | den(B_n).

    Uses `faulhaber_remainder_padic_val_nonneg`, `powerSum_mod_eq`,
    `prime_dvd_den_imp_padic_neg`, and `padic_neg_imp_prime_dvd_den`. -/
lemma prime_dvd_bernoulli_den_iff_of_two_le (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p)
    (ih : ∀ k' < k, 1 ≤ k' → padicValRat p (bernoulli (2 * k')) ≥ -1) :
    p ∣ (bernoulli (2 * k)).den ↔ (p - 1) ∣ (2 * k) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  constructor
  · intro hdvd
    have hlt := prime_dvd_den_imp_padic_neg _ _ hp hdvd
    by_contra hndvd
    have hge := padic_val_bernoulli_nonneg_of_not_dvd k hk p hp ih hndvd
    omega
  · intro hdvd
    have heq := padic_val_bernoulli_eq_neg_one_of_dvd k hk p hp ih hdvd
    apply padic_neg_imp_prime_dvd_den _ _ hp
    omega

lemma padic_val_bernoulli_ge_neg_one_of_two_le (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p)
    (ih : ∀ k' < k, 1 ≤ k' → padicValRat p (bernoulli (2 * k')) ≥ -1) :
    padicValRat p (bernoulli (2 * k)) ≥ -1 := by
  by_cases hdvd : (p - 1) ∣ (2 * k)
  · -- Case: (p-1) | 2k, so v_p(B_{2k}) = -1 ≥ -1
    have hval := padic_val_bernoulli_eq_neg_one_of_dvd k hk p hp ih hdvd
    linarith
  · -- Case: ¬(p-1) | 2k, so v_p(B_{2k}) ≥ 0 ≥ -1
    have hval := padic_val_bernoulli_nonneg_of_not_dvd k hk p hp ih hdvd
    linarith

lemma strong_induction_predicate (k : ℕ) (hk : 1 ≤ k) :
    (∀ p : ℕ, Nat.Prime p → (p ∣ (bernoulli (2 * k)).den ↔ (p - 1) ∣ (2 * k))) ∧
    (∀ p : ℕ, Nat.Prime p → padicValRat p (bernoulli (2 * k)) ≥ -1) := by
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    rcases Nat.lt_or_eq_of_le hk with hk2 | rfl
    · -- Inductive step k ≥ 2
      have ih : ∀ k' < k, 1 ≤ k' → ∀ p : ℕ, Nat.Prime p → padicValRat p (bernoulli (2 * k')) ≥ -1 := by
        intro k' hk' hk'_pos p hp
        exact (IH k' hk' hk'_pos).2 p hp
      constructor
      · intro p hp
        exact prime_dvd_bernoulli_den_iff_of_two_le k hk2 p hp
          (fun k' hk' hk'_pos => ih k' hk' hk'_pos p hp)
      · intro p hp
        exact padic_val_bernoulli_ge_neg_one_of_two_le k hk2 p hp
          (fun k' hk' hk'_pos => ih k' hk' hk'_pos p hp)
    · -- Base case k = 1
      constructor
      · intro p hp; exact prime_dvd_bernoulli_two_den_iff p hp
      · intro p hp; exact padic_val_bernoulli_two_ge_neg_one p hp

lemma prime_dvd_bernoulli_den_iff (k : ℕ) (hk : 1 ≤ k) (p : ℕ) (hp : Nat.Prime p) :
    p ∣ (bernoulli (2 * k)).den ↔ (p - 1) ∣ (2 * k) :=
  (strong_induction_predicate k hk).1 p hp

lemma padic_val_ge_neg_one_imp_sq_not_dvd_den (q : ℚ) (p : ℕ) (hp : Nat.Prime p)
    (hv : padicValRat p q ≥ -1) : ¬(p * p ∣ q.den) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpp : p * p = p ^ 2 := by ring
  rw [hpp]
  have hden_ne_zero : q.den ≠ 0 := Nat.pos_iff_ne_zero.mp q.pos
  rw [padicValNat_dvd_iff_le hden_ne_zero]
  intro hle
  -- From 2 ≤ padicValNat p q.den, deduce p | q.den
  have hone_le : 1 ≤ padicValNat p q.den := le_trans (by norm_num : 1 ≤ 2) hle
  have hp_dvd_den : p ∣ q.den := dvd_of_one_le_padicValNat hone_le
  -- From coprimality, deduce p ∤ q.num
  have hcop : IsCoprime q.num (↑q.den : ℤ) := Rat.isCoprime_num_den q
  have hp_not_dvd_num : ¬((↑p : ℤ) ∣ q.num) := by
    intro hdvd_num
    have hdvd_den_int : (↑p : ℤ) ∣ (↑q.den : ℤ) := by exact_mod_cast hp_dvd_den
    have hunit : IsUnit (↑p : ℤ) := hcop.isUnit_of_dvd' hdvd_num hdvd_den_int
    rw [Int.isUnit_iff_natAbs_eq] at hunit
    simp only [Int.natAbs_natCast] at hunit
    exact hp.one_lt.ne' hunit
  -- From p ∤ q.num, deduce padicValInt p q.num = 0
  have hval_num_zero : padicValInt p q.num = 0 := padicValInt.eq_zero_of_not_dvd hp_not_dvd_num
  -- From padicValRat_def, padicValRat p q = -padicValNat p q.den
  have hval_eq : padicValRat p q = ↑(padicValInt p q.num) - ↑(padicValNat p q.den) := padicValRat_def p q
  rw [hval_num_zero] at hval_eq
  simp only [Int.ofNat_zero, zero_sub] at hval_eq
  -- From hle, padicValNat p q.den ≥ 2, so padicValRat p q ≤ -2
  omega

/-- No prime divides the denominator of bernoulli (2*k) with multiplicity > 1.

    This follows from the von Staudt-Clausen theorem's precise statement:
    for any prime p, the p-adic valuation v_p(B_{2k}) is exactly -1 if (p-1)|2k,
    and ≥ 0 otherwise. This means each prime appears at most once in the denominator.

    The proof uses the same p-adic analysis as prime_dvd_bernoulli_den_iff:
    the congruence p·B_{2k} ≡ ±1 (mod p) shows v_p(B_{2k}) = -1, not -2 or less.

    No direct Mathlib equivalent. Searched: bernoulli_squarefree, bernoulli_den. -/
lemma bernoulli_den_squarefree (k : ℕ) (hk : 1 ≤ k) :
    Squarefree (bernoulli (2 * k)).den := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp
  have hv := (strong_induction_predicate k hk).2 p hp
  exact padic_val_ge_neg_one_imp_sq_not_dvd_den (bernoulli (2 * k)) p hp hv

lemma vonStaudtPrimes_pairwise_isRelPrime (n : ℕ) :
    (vonStaudtPrimes n : Set ℕ).Pairwise (Function.onFun IsRelPrime (fun x => x)) := by
  have h_main : (vonStaudtPrimes n : Set ℕ).Pairwise (Function.onFun IsRelPrime (fun x => x)) := by
    rw [Set.Pairwise]
    intro p hp q hq hpq
    -- Convert the set membership to finset membership
    have h₁ : p ∈ (vonStaudtPrimes n : Finset ℕ) := by simpa using hp
    have h₂ : q ∈ (vonStaudtPrimes n : Finset ℕ) := by simpa using hq
    -- Extract the properties of p and q from the filter
    have h₃ : Nat.Prime p ∧ (p - 1) ∣ n := by
      simp only [vonStaudtPrimes, Finset.mem_filter, Finset.mem_range] at h₁
      exact h₁.2
    have h₄ : Nat.Prime q ∧ (q - 1) ∣ n := by
      simp only [vonStaudtPrimes, Finset.mem_filter, Finset.mem_range] at h₂
      exact h₂.2
    -- Deduce that p and q are primes
    have h₅ : Nat.Prime p := h₃.1
    have h₆ : Nat.Prime q := h₄.1
    -- Use the fact that distinct primes are coprime
    have h₇ : p ≠ q := by
      intro h
      apply hpq
      simp_all [h]
    have h₈ : Nat.Coprime p q := by
      have h₉ : p ≠ q := h₇
      have h₁₀ : Nat.Prime p := h₅
      have h₁₁ : Nat.Prime q := h₆
      -- Use the lemma that distinct primes are coprime
      exact Nat.coprime_primes h₁₀ h₁₁ |>.mpr h₉
    -- Convert coprimality to IsRelPrime
    have h₉ : IsRelPrime p q := by
      rw [Nat.coprime_iff_isRelPrime] at h₈
      exact h₈
    -- Conclude the proof
    simpa [Function.onFun] using h₉
  exact h_main

lemma prime_squarefree (p : ℕ) (hp : Nat.Prime p) : Squarefree p := by
  haveI : Fact p.Prime := ⟨hp⟩
  simpa [Nat.prime_iff_prime_int] using Nat.prime_iff_prime_int.mp hp |>.squarefree

lemma vonStaudtPrimes_prod_squarefree (n : ℕ) :
    Squarefree (∏ p ∈ vonStaudtPrimes n, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · exact vonStaudtPrimes_pairwise_isRelPrime n
  · intro p hp
    have hprime : Nat.Prime p := by
      simp only [vonStaudtPrimes, Finset.mem_filter, Finset.mem_range] at hp
      exact hp.2.1
    exact prime_squarefree p hprime

lemma mem_vonStaudtPrimes_iff (n p : ℕ) :
    p ∈ vonStaudtPrimes n ↔ p < n + 2 ∧ Nat.Prime p ∧ (p - 1) ∣ n := by
  simp only [vonStaudtPrimes, Finset.mem_filter, Finset.mem_range]

lemma prime_sub_one_dvd_lt (n p : ℕ) (hn : 1 ≤ n) (hp : Nat.Prime p) (hdvd : (p - 1) ∣ n) :
    p < n + 2 := by
  have h₁ : p - 1 ≤ n := Nat.le_of_dvd (by positivity) hdvd
  omega

lemma prime_mem_vonStaudtPrimes_iff (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : Nat.Prime p) :
    p ∈ vonStaudtPrimes n ↔ (p - 1) ∣ n := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2.2
  · intro h
    have h₂ : p ∈ Finset.range (n + 2) := by
      have h₃ : p < n + 2 := by
        by_contra h₄
        have h₇ : p - 1 ≤ n := Nat.le_of_dvd (by omega) h
        omega
      exact Finset.mem_range.mpr h₃
    exact Finset.mem_filter.mpr ⟨h₂, hp, h⟩

lemma squarefree_eq_of_same_prime_divisors (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hSa : Squarefree a) (hSb : Squarefree b)
    (hDiv : ∀ p : ℕ, Nat.Prime p → (p ∣ a ↔ p ∣ b)) : a = b := by
  exact (Nat.Squarefree.ext_iff hSa hSb).mpr hDiv

/-- If p divides q and both are primes, then p = q. -/
lemma prime_eq_of_prime_dvd (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hdvd : p ∣ q) : p = q := by
  cases hq.eq_one_or_self_of_dvd p hdvd with
  | inl h => exact absurd h hp.ne_one
  | inr h => exact h

lemma prime_dvd_vonStaudtPrimes_prod_iff (n p : ℕ) (hp : Nat.Prime p) :
    p ∣ ∏ q ∈ vonStaudtPrimes n, q ↔ p ∈ vonStaudtPrimes n := by
  constructor
  · intro hdvd
    rw [Prime.dvd_finset_prod_iff (Nat.Prime.prime hp) (fun x => x)] at hdvd
    obtain ⟨q, hq_mem, hpq⟩ := hdvd
    simp only [vonStaudtPrimes, Finset.mem_filter, Finset.mem_range] at hq_mem
    have hq_prime : Nat.Prime q := hq_mem.2.1
    have heq : p = q := prime_eq_of_prime_dvd p q hp hq_prime hpq
    rw [heq]; simp only [vonStaudtPrimes, Finset.mem_filter, Finset.mem_range]
    exact ⟨hq_mem.1, hq_mem.2.1, hq_mem.2.2⟩
  ·
    intro hp_mem
    exact Finset.dvd_prod_of_mem (fun x => x) hp_mem

lemma vonStaudt_clausen (k : ℕ) (hk : 1 ≤ k) :
    (bernoulli (2 * k)).den = ∏ p ∈ vonStaudtPrimes (2 * k), p := by
  have hk2 : 1 ≤ 2 * k := by omega
  apply squarefree_eq_of_same_prime_divisors
  · exact Rat.den_pos (bernoulli (2 * k))
  · exact vonStaudtPrimes_prod_pos (2 * k)
  · exact bernoulli_den_squarefree k hk
  · exact vonStaudtPrimes_prod_squarefree (2 * k)
  · intro p hp
    rw [prime_dvd_bernoulli_den_iff k hk p hp]
    rw [prime_dvd_vonStaudtPrimes_prod_iff (2 * k) p hp]
    rw [prime_mem_vonStaudtPrimes_iff (2 * k) hk2 p hp]

lemma prime_in_vonStaudt_le (n : ℕ) (p : ℕ) (hp : p ∈ vonStaudtPrimes n) :
    p ≤ n + 1 := by
  have h₁ : p ∈ (Finset.range (n + 2)).filter (fun p => Nat.Prime p ∧ (p - 1) ∣ n) := hp
  have h₂ : p ∈ Finset.range (n + 2) := Finset.mem_filter.mp h₁ |>.1
  have h₃ : p < n + 2 := Finset.mem_range.mp h₂
  have h₄ : p ≤ n + 1 := by
    omega
  exact h₄

lemma card_vonStaudt_le (n : ℕ) (hn : 1 ≤ n) :
    (vonStaudtPrimes n).card ≤ n := by
  have h₂ : (vonStaudtPrimes n) ⊆ Finset.filter (fun p => Nat.Prime p ∧ (p - 1) ∣ n) (Finset.Icc 2 (n + 1)) := by
    intro p hp
    simp only [vonStaudtPrimes, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hp ⊢
    have h₄ : p ≥ 2 := by
      by_contra h
      cases (by omega : p = 0 ∨ p = 1) with
      | inl h₅ => simp_all [h₅, Nat.Prime]
      | inr h₅ => simp_all [h₅, Nat.Prime]
    exact ⟨by omega, by aesop⟩
  have h₃ : (Finset.filter (fun p => Nat.Prime p ∧ (p - 1) ∣ n) (Finset.Icc 2 (n + 1))).card ≤ n := by
    have h₄ : (Finset.filter (fun p => Nat.Prime p ∧ (p - 1) ∣ n) (Finset.Icc 2 (n + 1))).card ≤ (Finset.Icc 2 (n + 1)).card :=
      Finset.card_mono (fun x hx => by simp at hx ⊢; aesop)
    have h₅ : (Finset.Icc 2 (n + 1)).card ≤ n := by simp [Finset.Icc_eq_empty, hn]
    omega
  have h₆ : (vonStaudtPrimes n).card ≤ (Finset.filter (fun p => Nat.Prime p ∧ (p - 1) ∣ n) (Finset.Icc 2 (n + 1))).card :=
    Finset.card_mono h₂
  omega

lemma bernoulli_denom_bound (k : ℕ) (hk : 1 ≤ k) :
    ((bernoulli (2 * k)).den : ℝ) ≤ (2 * k + 1 : ℝ) ^ (2 * k) := by
  have hvs := vonStaudt_clausen k hk
  have hcard := card_vonStaudt_le (2 * k) (by omega)
  have hbound : ∀ p ∈ vonStaudtPrimes (2 * k), p ≤ 2 * k + 1 := fun p hp =>
    prime_in_vonStaudt_le (2 * k) p hp
  -- Product of primes ≤ (2k+1)^card, and card ≤ 2k
  calc ((bernoulli (2 * k)).den : ℝ)
      = ↑(∏ p ∈ vonStaudtPrimes (2 * k), p) := by rw [hvs]
    _ = ∏ p ∈ vonStaudtPrimes (2 * k), (p : ℝ) := by
        simp only [Nat.cast_prod]
    _ ≤ ∏ _p ∈ vonStaudtPrimes (2 * k), (2 * k + 1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i _
          positivity
        · intro p hp
          have h := hbound p hp
          exact_mod_cast h
    _ = (2 * k + 1 : ℝ) ^ (vonStaudtPrimes (2 * k)).card := by
        rw [Finset.prod_const]
    _ ≤ (2 * k + 1 : ℝ) ^ (2 * k) := by
        apply pow_le_pow_right₀
        · linarith
        · exact hcard

lemma bernoulli_num_eq_abs_mul_den (k : ℕ) :
    ((bernoulli (2 * k)).num.natAbs : ℝ) = |(bernoulli (2 * k) : ℝ)| * (bernoulli (2 * k)).den := by
  set q := bernoulli (2 * k)
  rw [Nat.cast_natAbs, Rat.cast_def, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q.den)]
  simp only [Int.cast_abs]
  field_simp

lemma factorial_le_pow (k : ℕ) (hk : 1 ≤ k) :
    ((2 * k).factorial : ℝ) ≤ (2 * k : ℝ) ^ (2 * k) := by
  have h₁ : (2 * k).factorial ≤ (2 * k : ℕ) ^ (2 * k) := by
    exact Nat.factorial_le_pow (2 * k)
  -- Cast the inequality to real numbers
  have h₂ : ((2 * k).factorial : ℝ) ≤ (2 * k : ℝ) ^ (2 * k) := by
    norm_cast at h₁ ⊢
  exact h₂

lemma log_four_bound (k : ℕ) (hk : 2 ≤ k) :
    Real.log 4 + 4 * k * Real.log k ≤ 5 * k * Real.log k := by
  have h₀ : (k : ℝ) ≥ 2 := by exact_mod_cast hk
  have h₁ : Real.log 4 ≤ 1 * (k : ℝ) * Real.log k := by
    have h₂ : Real.log 4 ≤ Real.log (k ^ 1) + Real.log (k ^ 1) := by
      have h₃ : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by
        nlinarith
      have h₅ : Real.log 4 ≤ Real.log ((k : ℝ) ^ 2) := Real.log_le_log (by positivity) h₃
      have h₆ : Real.log ((k : ℝ) ^ 2) = 2 * Real.log (k : ℝ) := by
        rw [Real.log_pow]
        <;> norm_num
      have h₇ : Real.log (k ^ 1 : ℝ) = Real.log (k : ℝ) := by
        norm_num
      linarith
    have h₃ : Real.log (k ^ 1 : ℝ) = Real.log (k : ℝ) := by norm_num
    have h₇ : 2 * Real.log (k : ℝ) ≤ (k : ℝ) * Real.log k := by
      have h₈ : Real.log (k : ℝ) ≥ 0 := Real.log_nonneg (by
        linarith)
      have h₁₂ : 2 * Real.log (k : ℝ) ≤ (k : ℝ) * Real.log k := by
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      linarith
    linarith
  have h₄ : Real.log 4 + 4 * (k : ℝ) * Real.log k ≤ 5 * (k : ℝ) * Real.log k := by
    linarith
  -- Convert the inequality back to natural numbers if necessary
  norm_cast at h₄ ⊢

lemma num_bound (k : ℕ) (hk : 2 ≤ k) :
    ((bernoulli (2 * k)).num.natAbs : ℝ) ≤
      4 * (2 * k : ℝ) ^ (2 * k) * (3 * k : ℝ) ^ (2 * k) / (2 * Real.pi) ^ (2 * k) := by
  have hk1 : 1 ≤ k := Nat.one_le_of_lt (Nat.lt_of_lt_of_le Nat.one_lt_two hk)
  -- Step 1: Rewrite |num| = |B_{2k}| * den
  rw [bernoulli_num_eq_abs_mul_den]
  -- Step 2: Get the bounds on |B_{2k}| and den
  have h_abs : |(bernoulli (2 * k) : ℝ)| ≤ 4 * (2 * k).factorial / (2 * Real.pi) ^ (2 * k) :=
    bernoulli_abs_bound k hk1
  have h_den : ((bernoulli (2 * k)).den : ℝ) ≤ (2 * k + 1 : ℝ) ^ (2 * k) :=
    bernoulli_denom_bound k hk1
  -- Step 3: Get the factorial bound and (2k+1) ≤ 3k bound
  have h_fac : ((2 * k).factorial : ℝ) ≤ (2 * k : ℝ) ^ (2 * k) := factorial_le_pow k hk1
  have h_2k1 : (2 * k + 1 : ℝ) ≤ 3 * k := two_k_add_one_le k hk1
  -- Step 4: Combine bounds
  have h_abs_nonneg : 0 ≤ |(bernoulli (2 * k) : ℝ)| := abs_nonneg _
  have h_den_nonneg : (0 : ℝ) ≤ (bernoulli (2 * k)).den := Nat.cast_nonneg _
  calc |(bernoulli (2 * k) : ℝ)| * (bernoulli (2 * k)).den
      ≤ (4 * (2 * k).factorial / (2 * Real.pi) ^ (2 * k)) * (2 * k + 1 : ℝ) ^ (2 * k) := by
        apply mul_le_mul h_abs h_den h_den_nonneg
        exact le_trans h_abs_nonneg h_abs
    _ = 4 * (2 * k).factorial * (2 * k + 1 : ℝ) ^ (2 * k) / (2 * Real.pi) ^ (2 * k) := by ring
    _ ≤ 4 * (2 * k : ℝ) ^ (2 * k) * (3 * k : ℝ) ^ (2 * k) / (2 * Real.pi) ^ (2 * k) := by
        have h_2k1_pow : (2 * k + 1 : ℝ) ^ (2 * k) ≤ (3 * k : ℝ) ^ (2 * k) := by
          apply pow_le_pow_left₀
          · linarith
          · exact h_2k1
        have h_pi_pos : (0 : ℝ) < (2 * Real.pi) ^ (2 * k) := by
          apply pow_pos
          linarith [Real.pi_pos]
        apply div_le_div_of_nonneg_right _ (le_of_lt h_pi_pos)
        calc 4 * (2 * k).factorial * (2 * k + 1 : ℝ) ^ (2 * k)
            ≤ 4 * (2 * k : ℝ) ^ (2 * k) * (2 * k + 1 : ℝ) ^ (2 * k) := by
              apply mul_le_mul_of_nonneg_right
              · apply mul_le_mul_of_nonneg_left h_fac (by norm_num : (0 : ℝ) ≤ 4)
              · apply pow_nonneg; linarith
          _ ≤ 4 * (2 * k : ℝ) ^ (2 * k) * (3 * k : ℝ) ^ (2 * k) := by
              apply mul_le_mul_of_nonneg_left h_2k1_pow
              apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
              apply pow_nonneg
              linarith

lemma lhs_expansion (k : ℕ) (hk : 2 ≤ k) :
    Real.log (4 * (2 * k : ℝ) ^ (2 * k) * (3 * k : ℝ) ^ (2 * k) / (2 * Real.pi) ^ (2 * k)) =
      Real.log 4 + 4 * k * Real.log k + 2 * k * (Real.log 3 - Real.log Real.pi) := by
  have h₄ : Real.log (4 * (2 * k : ℝ) ^ (2 * k) * (3 * k : ℝ) ^ (2 * k) / (2 * Real.pi) ^ (2 * k)) =
      Real.log (4 : ℝ) + Real.log ((2 * k : ℝ) ^ (2 * k)) + Real.log ((3 * k : ℝ) ^ (2 * k)) - Real.log ((2 * Real.pi : ℝ) ^ (2 * k)) := by
    have h₅ : Real.log (4 * (2 * k : ℝ) ^ (2 * k) * (3 * k : ℝ) ^ (2 * k) / (2 * Real.pi) ^ (2 * k)) =
        Real.log (4 * (2 * k : ℝ) ^ (2 * k) * (3 * k : ℝ) ^ (2 * k)) - Real.log ((2 * Real.pi : ℝ) ^ (2 * k)) := by
      rw [Real.log_div (by positivity) (by positivity)]
    rw [h₅]
    have h₆ : Real.log (4 * (2 * k : ℝ) ^ (2 * k) * (3 * k : ℝ) ^ (2 * k)) =
        Real.log (4 : ℝ) + Real.log ((2 * k : ℝ) ^ (2 * k)) + Real.log ((3 * k : ℝ) ^ (2 * k)) := by
      have h₇ : Real.log (4 * (2 * k : ℝ) ^ (2 * k) * (3 * k : ℝ) ^ (2 * k)) =
          Real.log (4 * (2 * k : ℝ) ^ (2 * k)) + Real.log ((3 * k : ℝ) ^ (2 * k)) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      rw [h₇]
      have h₈ : Real.log (4 * (2 * k : ℝ) ^ (2 * k)) =
          Real.log (4 : ℝ) + Real.log ((2 * k : ℝ) ^ (2 * k)) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      rw [h₈]
    rw [h₆]

  rw [h₄]
  have h₅ : Real.log ((2 * k : ℝ) ^ (2 * k)) = (2 * k : ℝ) * Real.log (2 * k) := by
    rw [Real.log_pow]
    <;> norm_cast

  have h₆ : Real.log ((3 * k : ℝ) ^ (2 * k)) = (2 * k : ℝ) * Real.log (3 * k) := by
    rw [Real.log_pow]
    <;> norm_cast

  have h₇ : Real.log ((2 * Real.pi : ℝ) ^ (2 * k)) = (2 * k : ℝ) * Real.log (2 * Real.pi) := by
    rw [Real.log_pow]
    <;> norm_cast

  rw [h₅, h₆, h₇]
  have h₈ : (2 * k : ℝ) * Real.log (2 * k) = (2 * k : ℝ) * (Real.log 2 + Real.log k) := by
    have h₈₁ : Real.log (2 * k : ℝ) = Real.log 2 + Real.log k := by
      have h₈₄ : Real.log (2 * k : ℝ) = Real.log 2 + Real.log k := by
        rw [Real.log_mul (by positivity) (by positivity)]
      rw [h₈₄]
    rw [h₈₁]

  have h₉ : (2 * k : ℝ) * Real.log (3 * k) = (2 * k : ℝ) * (Real.log 3 + Real.log k) := by
    have h₉₁ : Real.log (3 * k : ℝ) = Real.log 3 + Real.log k := by
      have h₉₄ : Real.log (3 * k : ℝ) = Real.log 3 + Real.log k := by
        rw [Real.log_mul (by positivity) (by positivity)]
      rw [h₉₄]
    rw [h₉₁]

  have h₁₀ : (2 * k : ℝ) * Real.log (2 * Real.pi) = (2 * k : ℝ) * (Real.log 2 + Real.log Real.pi) := by
    have h₁₀₁ : Real.log (2 * Real.pi : ℝ) = Real.log 2 + Real.log Real.pi := by
      have h₁₀₄ : Real.log (2 * Real.pi : ℝ) = Real.log 2 + Real.log Real.pi := by
        rw [Real.log_mul (by positivity) (by positivity)]
      rw [h₁₀₄]
    rw [h₁₀₁]

  rw [h₈, h₉, h₁₀]
  have h₁₁ : Real.log 4 = 2 * Real.log 2 := by
    have h₁₁₁ : Real.log 4 = Real.log (2 ^ 2) := by norm_num
    rw [h₁₁₁]
    have h₁₁₂ : Real.log (2 ^ 2 : ℝ) = 2 * Real.log 2 := by
      rw [Real.log_pow]
      <;> norm_num
    rw [h₁₁₂]

  rw [h₁₁]
  ring_nf

/-- Since π > 3 (Mathlib's `Real.pi_gt_three : 3 < Real.pi`), we have log(3) < log(π).
    Thus log(3) - log(π) < 0.
    For k ≥ 2, we have 2k ≥ 4 > 0, so 2k*(log(3) - log(π)) ≤ 0. -/
lemma residual_term_nonpos (k : ℕ) (hk : 2 ≤ k) :
    2 * (k : ℝ) * (Real.log 3 - Real.log Real.pi) ≤ 0 := by
  have h₀ : (3 : ℝ) < Real.pi := by
    exact Real.pi_gt_three
  have h₁ : Real.log 3 < Real.log Real.pi := by
    apply Real.log_lt_log (by norm_num)
    linarith
  have h₅ : (2 : ℝ) * (k : ℝ) * (Real.log 3 - Real.log Real.pi) ≤ 0 := by
    nlinarith
  exact h₅

lemma log_bound_simplify (k : ℕ) (hk : 2 ≤ k) :
    Real.log (4 * (2 * k : ℝ) ^ (2 * k) * (3 * k : ℝ) ^ (2 * k) / (2 * Real.pi) ^ (2 * k)) ≤
      Real.log 4 + 4 * k * Real.log k := by
  rw [lhs_expansion k hk]
  have h := residual_term_nonpos k hk
  linarith

/-- For k ≥ 2, |num(B_{2k})| > 0. Needed for taking logarithms.

    Since B_{2k} ≠ 0 for k ≥ 1 (alternating non-zero), its numerator is non-zero. -/
lemma num_pos (k : ℕ) (hk : 2 ≤ k) : (0 : ℝ) < (bernoulli (2 * k)).num.natAbs := by
  have hk1 : 1 ≤ k := Nat.one_le_of_lt hk
  have h_ne : bernoulli (2 * k) ≠ 0 := bernoulli_two_mul_ne_zero k hk1
  have h_num_ne : (bernoulli (2 * k)).num ≠ 0 := Rat.num_ne_zero.mpr h_ne
  have h_natAbs_ne : (bernoulli (2 * k)).num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr h_num_ne
  exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero h_natAbs_ne)

lemma bernoulli_num_bound_combined (k : ℕ) (hk : 2 ≤ k) :
    Real.log ((bernoulli (2 * k)).num.natAbs : ℝ) ≤ 5 * k * Real.log k := by
  have h_num_bound := num_bound k hk
  have h_log_simplify := log_bound_simplify k hk
  have h_log_four := log_four_bound k hk
  have h_num_pos := num_pos k hk
  calc Real.log ((bernoulli (2 * k)).num.natAbs : ℝ)
      ≤ Real.log (4 * (2 * k : ℝ) ^ (2 * k) * (3 * k : ℝ) ^ (2 * k) / (2 * Real.pi) ^ (2 * k)) :=
        Real.log_le_log h_num_pos h_num_bound
    _ ≤ Real.log 4 + 4 * k * Real.log k := h_log_simplify
    _ ≤ 5 * k * Real.log k := h_log_four

lemma bernoulli_num_log_bound :
    ∃ A : ℝ, A > 0 ∧ ∀ k : ℕ, 2 ≤ k →
    Real.log ((bernoulli (2 * k)).num.natAbs : ℝ) ≤ A * k * Real.log k := by
  use 5
  constructor
  · norm_num
  · intro k hk
    exact bernoulli_num_bound_combined k hk

lemma small_primes_subset_singleton (α : ℝ) (k : ℕ) (X : ℝ) :
    Finset.filter (fun p => ¬(3 ≤ p)) (primeCountSet α k X) ⊆ {2} := by
  intro p hp
  have h₁ : p ∈ primeCountSet α k X := by
    simp only [Finset.mem_filter] at hp
    exact hp.1

  have h₂ : ¬(3 ≤ p) := by
    simp only [Finset.mem_filter] at hp
    exact hp.2

  have h₄ : Nat.Prime p := by
    have h₅ : p ∈ primeCountSet α k X := h₁
    simp only [primeCountSet, Finset.mem_filter, Finset.mem_Icc] at h₅
    -- Extract the property that p is prime from the filter condition
    have h₆ : Nat.Prime p := by tauto
    exact h₆

  have h₅ : 2 ≤ p := by
    have h₅₁ : Nat.Prime p := h₄
    have h₅₂ : 2 ≤ p := Nat.Prime.two_le h₅₁
    exact h₅₂

  have h₇ : p = 2 := by
    omega

  have h₈ : p ∈ ({2} : Finset ℕ) := by
    simp [h₇]

  exact h₈

lemma total_count_le_large_primes_plus_one (α : ℝ) (k : ℕ) (X : ℝ) :
    (primeCountSet α k X).card ≤ (Finset.filter (fun p => 3 ≤ p) (primeCountSet α k X)).card + 1 := by
  have h_partition := Finset.filter_card_add_filter_neg_card_eq_card (fun p => 3 ≤ p)
    (s := primeCountSet α k X)
  have h_small := small_primes_subset_singleton α k X
  have h_card_small : (Finset.filter (fun p => ¬(3 ≤ p)) (primeCountSet α k X)).card ≤ 1 := by
    calc (Finset.filter (fun p => ¬(3 ≤ p)) (primeCountSet α k X)).card
        ≤ ({2} : Finset ℕ).card := Finset.card_le_card h_small
      _ = 1 := Finset.card_singleton 2
  omega

/-- The numerator of bernoulli 2 equals 1.
    Since bernoulli 2 = 6⁻¹ = 1/6, the numerator is 1.
    This uses `bernoulli_two : bernoulli 2 = 6⁻¹ := ...`. -/
lemma bernoulli_two_num : (bernoulli 2).num = 1 := by simp

lemma count_at_k_eq_one_bounded (α : ℝ) (_hα : 1/2 < α) :
    ∃ B : ℝ, B > 0 ∧ ∀ X : ℝ, (primeCountSet α 1 X).card ≤ B := by
  use 1
  constructor
  · norm_num
  · intro X
    have hnum : (bernoulli 2).num = 1 := bernoulli_two_num
    have hempty : primeCountSet α 1 X = ∅ := by
      simp only [primeCountSet, Finset.filter_eq_empty_iff]
      intro p _
      simp only [mul_one]
      push_neg
      intro hp hdvd
      rw [hnum] at hdvd
      exact absurd (Int.natCast_dvd.mp hdvd) hp.not_dvd_one
    simp [hempty]

lemma log_pow_ge_one (α : ℝ) (hα_pos : 0 < α) (p : ℕ) (hp3 : 3 ≤ p) :
    (Real.log p) ^ α ≥ 1 := by
  have h₁ : Real.log (p : ℝ) ≥ Real.log 3 := by
    apply Real.log_le_log
    · norm_cast
    · norm_cast

  have h₂ : Real.log 3 > 1 := by
    have : Real.log 3 > Real.log (Real.exp 1) := by
      -- Prove that ln(3) > ln(e) = 1
      have : (3 : ℝ) > Real.exp 1 := by
        have := Real.exp_one_lt_d9
        norm_num at this ⊢
        <;> linarith
      -- Use the fact that the logarithm is strictly increasing
      have : Real.log 3 > Real.log (Real.exp 1) := Real.log_lt_log (by positivity) this
      exact this
    -- Simplify ln(e) to 1
    have : Real.log (Real.exp 1) = 1 := by
      rw [Real.log_exp]
    linarith

  have h₄ : (Real.log (p : ℝ)) ^ α ≥ 1 := by
    -- Use the fact that if x > 1 and y ≥ 0, then x^y ≥ 1
    have h₆ : (Real.log (p : ℝ)) ^ α ≥ 1 := by
      -- Use the property of real powers to show that if x ≥ 1 and α ≥ 0, then x^α ≥ 1
      exact Real.one_le_rpow (by linarith) (by linarith)
    exact h₆

  exact h₄

lemma sqrt_p_ge_2k (α : ℝ) (hα_pos : 0 < α) (k : ℕ) (p : ℕ) (hp3 : 3 ≤ p)
    (h_ratio : Real.sqrt p / (Real.log p) ^ α ≥ 2 * k)
    (h_log : (Real.log p) ^ α ≥ 1) :
    Real.sqrt p ≥ 2 * k := by
  have h1 : (Real.log p : ℝ) > 0 := by
    have h1 : (p : ℝ) ≥ 3 := by norm_cast
    have h2 : Real.log (p : ℝ) > 0 := by
      -- Prove that the logarithm of p is positive since p ≥ 3 > 1
      exact Real.log_pos (by linarith)
    exact h2

  have h2 : (Real.log p : ℝ) ^ α > 0 := by
    -- Since (Real.log p : ℝ) > 0 and α > 0, the power is also positive.
    positivity

  have h3 : Real.sqrt p ≥ 2 * k := by
    -- We know that (Real.log p) ^ α ≥ 1, so we can multiply the inequality by it.
    have h4 : Real.sqrt p / (Real.log p) ^ α * (Real.log p) ^ α ≥ (2 * k : ℝ) * (Real.log p) ^ α := by
      -- Multiply both sides of the ratio inequality by (Real.log p) ^ α
      calc
        Real.sqrt p / (Real.log p) ^ α * (Real.log p) ^ α ≥ (2 * k : ℝ) * (Real.log p) ^ α := by
          -- Use the fact that multiplying both sides by a positive number preserves the inequality.
          have h7 : Real.sqrt p / (Real.log p) ^ α * (Real.log p) ^ α = Real.sqrt p := by
            field_simp [h2.ne']
          rw [h7]
          have h8 : (2 * k : ℝ) * (Real.log p) ^ α ≤ Real.sqrt p := by
            -- This is not directly helpful, but we can instead use the given inequality to multiply both sides.
            have h10 : (2 * k : ℝ) * (Real.log p) ^ α ≤ (Real.sqrt p / (Real.log p) ^ α) * (Real.log p) ^ α := by
              -- Multiply both sides by (Real.log p) ^ α
              gcongr
            linarith
          linarith
        _ = (2 * k : ℝ) * (Real.log p) ^ α := by ring
    -- Simplify the left side of the inequality
    have h7 : Real.sqrt p / (Real.log p) ^ α * (Real.log p) ^ α = Real.sqrt p := by
      field_simp [h2.ne']
    have h8 : (2 * k : ℝ) * (Real.log p) ^ α ≥ (2 * k : ℝ) * 1 := by
      -- Since (Real.log p) ^ α ≥ 1 and 2 * k ≥ 0, we can multiply both sides by 2 * k
      nlinarith
    -- Combine the inequalities to get the final result
    have h13 : Real.sqrt p ≥ (2 * k : ℝ) := by linarith
    have h14 : Real.sqrt p ≥ 2 * k := by
      -- Convert the inequality back to natural numbers
      have h16 : Real.sqrt p ≥ (2 * k : ℝ) := h13
      have h17 : Real.sqrt p ≥ (2 * k : ℕ) := by
        -- Use the fact that the square root of p is at least 2 * k
        exact_mod_cast h16
      exact_mod_cast h17
    exact h14
  exact h3

lemma sq_le_of_sqrt_ge (k : ℕ) (p : ℕ) (h : Real.sqrt p ≥ 2 * k) :
    4 * k^2 ≤ p := by
  have h₁ : (2 * (k : ℝ))^2 ≤ (p : ℝ) := by
    have h₅ : (2 * (k : ℝ))^2 ≤ (p : ℝ) := by
      nlinarith [Real.sqrt_nonneg (p : ℝ), Real.sq_sqrt (by positivity : 0 ≤ (p : ℝ))]
    exact h₅
  have h₂ : (4 * k^2 : ℝ) ≤ (p : ℝ) := by
    norm_cast at h₁ ⊢
    <;> ring_nf at h₁ ⊢ <;>
    (try nlinarith)
  have h₃ : (4 * k^2 : ℕ) ≤ p := by
    norm_cast at h₂ ⊢
  exact h₃

lemma floor_ge_imp_ge_real (α : ℝ) (hα_pos : 0 < α) (k : ℕ) (hk : 1 ≤ k)
    (p : ℕ) (hp3 : 3 ≤ p) (hM : ⌊Real.sqrt p / (Real.log p) ^ α⌋₊ ≥ 2 * k) :
    Real.sqrt p / (Real.log p) ^ α ≥ 2 * k := by
  have h2k_pos : (2 * k : ℕ) ≠ 0 := by nlinarith
  have h2k_real_le : (2 * k : ℝ) ≤ Real.sqrt p / (Real.log p) ^ α := by
    have := (Nat.le_floor_iff' h2k_pos).mp hM
    simp only [Nat.cast_mul, Nat.cast_ofNat] at this
    exact this
  have h_main : Real.sqrt p / (Real.log p) ^ α ≥ 2 * k := by assumption
  assumption

theorem prime_ge_three_M_alpha_large_implies_ge_4k_sq (α : ℝ) (hα : 1/2 < α) (k : ℕ) (hk : 1 ≤ k)
    (p : ℕ) (_hp : Nat.Prime p) (hp3 : 3 ≤ p) (hM : M_alpha α p ≥ 2 * k) :
    4 * k^2 ≤ p := by
  have hα_pos : 0 < α := by linarith
  have h_ratio := floor_ge_imp_ge_real α hα_pos k hk p hp3 hM
  have h_log := log_pow_ge_one α hα_pos p hp3
  have h_sqrt := sqrt_p_ge_2k α hα_pos k p hp3 h_ratio h_log
  exact sq_le_of_sqrt_ge k p h_sqrt

lemma log_p_gt_one (p : ℕ) (hp3 : 3 ≤ p) : Real.log p > 1 := by
  have h₁ : Real.log p > 1 := by
    have h₂ : Real.log (p : ℝ) > 1 := by
      have h₃ : Real.log (p : ℝ) ≥ Real.log 3 := Real.log_le_log (by positivity) (by exact_mod_cast hp3)
      have h₄ : Real.log 3 > 1 := by
        -- Use the fact that e ≈ 2.718 < 3 to show that log 3 > 1
        have := Real.log_two_gt_d9
        have := Real.log_two_lt_d9
        have h₅ : Real.log 3 > 1 := by
          -- Prove that log 3 > 1 using numerical approximations
          have h₆ : Real.log 3 > Real.log (Real.exp 1) := by
            have h₇ : (Real.exp 1 : ℝ) < 3 := by
              have := Real.exp_one_lt_d9
              norm_num at this ⊢
              <;> linarith
            have h₈ : Real.log (Real.exp 1) < Real.log 3 := Real.log_lt_log (by positivity) (by linarith)
            linarith
          have h₉ : Real.log (Real.exp 1) = 1 := by
            rw [Real.log_exp]
          linarith
        linarith
      linarith
    exact h₂
  exact h₁

lemma primes_pairwise_coprime (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    (S : Set ℕ).Pairwise (Function.onFun IsCoprime (fun x => (x : ℤ))) := by
  have h_main : ∀ (p q : ℕ), p ∈ (S : Set ℕ) → q ∈ (S : Set ℕ) → p ≠ q → IsCoprime (p : ℤ) (q : ℤ) := by
    intro p q hp hq hpq
    have h₁ : p ∈ S := by simpa using hp
    have h₂ : q ∈ S := by simpa using hq
    have h₃ : Nat.Prime p := hS p h₁
    have h₄ : Nat.Prime q := hS q h₂
    have h₅ : Nat.Coprime p q := by
      rw [Nat.coprime_primes h₃ h₄]
      <;> aesop
    have h₆ : IsCoprime (p : ℤ) (q : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      norm_cast
    exact h₆
  have h_final : (S : Set ℕ).Pairwise (Function.onFun IsCoprime (fun x => (x : ℤ))) := by
    rw [Set.Pairwise]
    intro a ha b hb hab
    have h₁ : IsCoprime (a : ℤ) (b : ℤ) := h_main a b ha hb hab
    simpa [Function.onFun] using h₁
  exact h_final

lemma prod_primes_dvd_of_each_dvd (S : Finset ℕ) (N : ℤ) (hS : ∀ p ∈ S, Nat.Prime p)
    (hdvd : ∀ p ∈ S, (p : ℤ) ∣ N) :
    (∏ p ∈ S, (p : ℤ)) ∣ N := by
  exact Finset.prod_dvd_of_coprime (primes_pairwise_coprime S hS) hdvd

lemma prod_ge_pow_card (S : Finset ℕ) (m : ℕ) (hm : 0 < m) (hge : ∀ p ∈ S, m ≤ p) :
    (m : ℤ) ^ S.card ≤ ∏ p ∈ S, (p : ℤ) := by
  have h₁ : (m : ℕ) ^ S.card ≤ ∏ p ∈ S, p := Finset.pow_card_le_prod S (fun p => p) m hge
  calc (m : ℤ) ^ S.card = ((m ^ S.card : ℕ) : ℤ) := by simp
    _ ≤ ((∏ p ∈ S, p : ℕ) : ℤ) := by exact_mod_cast h₁
    _ = ∏ p ∈ S, (p : ℤ) := by simp [Finset.prod_natCast]

lemma log_4k_sq_ge_two_log_k (k : ℕ) (hk : 2 ≤ k) :
    Real.log (4 * k^2 : ℝ) ≥ 2 * Real.log k := by
  have h₂ : Real.log (4 * (k : ℝ)^2) = Real.log 4 + 2 * Real.log (k : ℝ) := by
    have h₃ : Real.log (4 * (k : ℝ)^2) = Real.log (4 : ℝ) + Real.log ((k : ℝ)^2) := by
      rw [Real.log_mul (by positivity) (by positivity)]
    rw [h₃]
    have h₄ : Real.log ((k : ℝ)^2) = 2 * Real.log (k : ℝ) := by
      rw [Real.log_pow]
      <;> norm_num
    rw [h₄]
  have h₃ : Real.log 4 > 0 := Real.log_pos (by norm_num)
  have h₅ : Real.log (4 * (k : ℝ)^2) ≥ 2 * Real.log (k : ℝ) := by linarith
  simpa [h₂] using h₅

lemma pow_le_prod_of_ge (S : Finset ℕ) (m : ℕ) (hm : 0 < m) (hge : ∀ p ∈ S, m ≤ p) :
    m ^ S.card ≤ ∏ p ∈ S, p := by
  have h := prod_ge_pow_card S m hm hge
  simp only [← Nat.cast_pow] at h
  exact Int.toNat_le_toNat h |>.trans (by simp)

lemma prod_le_natAbs (S : Finset ℕ) (N : ℤ) (hN : N ≠ 0)
    (hdvd : (∏ p ∈ S, (p : ℤ)) ∣ N) :
    (∏ p ∈ S, (p : ℕ)) ≤ N.natAbs := by
  have h₁ : (∏ p ∈ S, (p : ℕ)) ≤ N.natAbs := by
    have h₂ : ((∏ p ∈ S, (p : ℕ)) : ℤ) = ∏ p ∈ S, (p : ℤ) := by
      norm_cast
    have h₃ : ((∏ p ∈ S, (p : ℕ)) : ℤ) ∣ N := by
      rw [h₂]
      exact hdvd
    have h₄ : ((∏ p ∈ S, (p : ℕ)) : ℕ) ∣ N.natAbs := by
      have h₅ : ((∏ p ∈ S, (p : ℕ)) : ℤ) ∣ N := h₃
      have h₆ : ((∏ p ∈ S, (p : ℕ)) : ℕ) ∣ N.natAbs := by
        exact Int.natCast_dvd_natCast.mp (by
          simpa [Int.natAbs_dvd_natAbs] using h₅)
      exact h₆
    have h₅ : ((∏ p ∈ S, (p : ℕ)) : ℕ) ≤ N.natAbs := by
      have h₇ : N.natAbs ≠ 0 := by
        intro h₈
        have h₉ : N = 0 := by
          have h₁₀ : N.natAbs = 0 := h₈
          have h₁₁ : N = 0 := by
            simpa [Int.natAbs_eq_zero] using h₁₀
          exact h₁₁
        contradiction
      have h₈ : ((∏ p ∈ S, (p : ℕ)) : ℕ) ≤ N.natAbs := by
        have h₉ : ((∏ p ∈ S, (p : ℕ)) : ℕ) ∣ N.natAbs := h₄
        exact Nat.le_of_dvd (by
          have h₁₀ : 0 < N.natAbs := Nat.pos_of_ne_zero h₇
          exact h₁₀) h₉
      exact h₈
    exact_mod_cast h₅
  exact h₁

lemma pow_le_imp_card_le (r : ℕ) (m n : ℕ) (hm : 1 < m) (hn : 0 < n)
    (hle : m ^ r ≤ n) :
    (r : ℝ) ≤ Real.log (n : ℝ) / Real.log m := by
  have h₁ : (m : ℝ) > 1 := by exact_mod_cast hm
  have h₃ : (m : ℝ) ^ r ≤ (n : ℝ) := by exact_mod_cast hle
  have h₄ : Real.log ((m : ℝ) ^ r) ≤ Real.log (n : ℝ) := Real.log_le_log (by positivity) h₃
  have h₅ : Real.log ((m : ℝ) ^ r) = (r : ℝ) * Real.log (m : ℝ) := by
    rw [Real.log_pow]
  have h₆ : (r : ℝ) * Real.log (m : ℝ) ≤ Real.log (n : ℝ) := by linarith
  have h₇ : Real.log (m : ℝ) > 0 := Real.log_pos h₁
  have h₈ : (r : ℝ) ≤ Real.log (n : ℝ) / Real.log (m : ℝ) := by
    have h₉ : 0 < Real.log (m : ℝ) := h₇
    have h₁₀ : (r : ℝ) * Real.log (m : ℝ) / Real.log (m : ℝ) ≤ Real.log (n : ℝ) / Real.log (m : ℝ) := by
      calc
        (r : ℝ) * Real.log (m : ℝ) / Real.log (m : ℝ) ≤ Real.log (n : ℝ) / Real.log (m : ℝ) := by
          gcongr
        _ = Real.log (n : ℝ) / Real.log (m : ℝ) := by rfl
    have h₁₁ : (r : ℝ) * Real.log (m : ℝ) / Real.log (m : ℝ) = (r : ℝ) := by
      field_simp [h₉.ne']
    calc
      (r : ℝ) = (r : ℝ) * Real.log (m : ℝ) / Real.log (m : ℝ) := by rw [h₁₁]
      _ ≤ Real.log (n : ℝ) / Real.log (m : ℝ) := h₁₀
  have h₉ : Real.log (m : ℝ) = Real.log m := by norm_num
  have h₁₀ : Real.log (n : ℝ) = Real.log n := by norm_num
  have h₁₁ : (r : ℝ) ≤ Real.log (n : ℝ) / Real.log (m : ℝ) := h₈
  simpa [h₉, h₁₀] using h₁₁

lemma count_bound_via_log (S : Finset ℕ) (m : ℕ) (N : ℤ) (hN : N ≠ 0)
    (hS : ∀ p ∈ S, Nat.Prime p) (hm : 1 < m) (hge : ∀ p ∈ S, m ≤ p)
    (hdvd : ∀ p ∈ S, (p : ℤ) ∣ N) :
    (S.card : ℝ) ≤ Real.log (N.natAbs : ℝ) / Real.log m := by
  have h_prod_dvd : (∏ p ∈ S, (p : ℤ)) ∣ N := prod_primes_dvd_of_each_dvd S N hS hdvd
  have h_prod_le : (∏ p ∈ S, (p : ℕ)) ≤ N.natAbs := prod_le_natAbs S N hN h_prod_dvd
  have hm' : 0 < m := Nat.lt_trans Nat.zero_lt_one hm
  have h_pow_le_natAbs : m ^ S.card ≤ N.natAbs := calc
    m ^ S.card ≤ ∏ p ∈ S, p := pow_le_prod_of_ge S m hm' hge
    _ ≤ N.natAbs := h_prod_le
  have h_natAbs_pos : 0 < N.natAbs := Int.natAbs_pos.mpr hN
  exact pow_le_imp_card_le S.card m N.natAbs hm h_natAbs_pos h_pow_le_natAbs

lemma log_k_pos (k : ℕ) (hk : 2 ≤ k) : 0 < Real.log (k : ℝ) := by
  exact Real.log_pos (by simp +arith [*])

lemma four_k_sq_gt_one (k : ℕ) (hk : 2 ≤ k) : 1 < 4 * k^2 := by
  have h : 1 < 4 * k ^ 2 := by
    have h₂ : k ^ 2 ≥ 4 := by
      have h₃ : k * k ≥ 2 * k := by
        nlinarith
      nlinarith
    have h₆ : 1 < 4 * k ^ 2 := by
      nlinarith
    exact h₆
  exact h

lemma bound_via_log_div (r : ℕ) (logN logm Ak two_logk : ℝ)
    (hr : (r : ℝ) ≤ logN / logm)
    (hlogN_le : logN ≤ Ak)
    (hlogm_ge : logm ≥ two_logk)
    (hlogm_pos : 0 < logm)
    (htwo_logk_pos : 0 < two_logk) :
    (r : ℝ) ≤ Ak / two_logk := by
  have h1 : (r : ℝ) * logm ≤ logN := (le_div_iff₀ hlogm_pos).mp hr
  have h2 : (r : ℝ) * two_logk ≤ (r : ℝ) * logm := by nlinarith
  have h4 : (r : ℝ) * two_logk ≤ Ak := by nlinarith
  exact (le_div_iff₀ htwo_logk_pos).mpr h4

lemma count_ge_three_bound_at_fixed_k (α : ℝ) (hα : 1/2 < α) (A : ℝ) (hA : A > 0)
    (hAbound : ∀ k : ℕ, 2 ≤ k → Real.log ((bernoulli (2 * k)).num.natAbs : ℝ) ≤ A * k * Real.log k)
    (k : ℕ) (hk : 2 ≤ k) (X : ℝ) :
    ((Finset.filter (fun p => 3 ≤ p) (primeCountSet α k X)).card : ℝ) ≤ (A / 2) * k := by
  -- Let S be the filtered set
  set S := Finset.filter (fun p => 3 ≤ p) (primeCountSet α k X) with hS_def
  -- Let N = (bernoulli (2*k)).num (the numerator)
  set N := (bernoulli (2 * k)).num with hN_def
  -- Step 1: N ≠ 0 (from num_pos: 0 < N.natAbs implies N ≠ 0)
  have hN_pos : (0 : ℝ) < (N.natAbs : ℝ) := num_pos k hk
  have hN_natAbs_pos : 0 < N.natAbs := by
    rw [← Nat.cast_pos (α := ℝ)]
    exact hN_pos
  have hN_ne : N ≠ 0 := Int.natAbs_ne_zero.mp (Nat.pos_iff_ne_zero.mp hN_natAbs_pos)
  -- Step 2: All elements of S are prime
  have hS_prime : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    simp only [hS_def, primeCountSet, Finset.mem_filter, Finset.mem_Icc] at hp
    exact hp.1.2.1
  -- Step 3: 4 * k^2 > 1
  have h4k2_gt_one : 1 < 4 * k^2 := four_k_sq_gt_one k hk
  -- Step 4: All elements of S are ≥ 4k²
  have hS_ge : ∀ p ∈ S, 4 * k^2 ≤ p := by
    intro p hp
    simp only [hS_def, primeCountSet, Finset.mem_filter, Finset.mem_Icc] at hp
    exact prime_ge_three_M_alpha_large_implies_ge_4k_sq α hα k
      (Nat.one_le_of_lt hk) p hp.1.2.1 hp.2 hp.1.2.2.2.2
  -- Step 5: All elements of S divide N
  have hS_dvd : ∀ p ∈ S, (p : ℤ) ∣ N := by
    intro p hp
    simp only [hS_def, primeCountSet, Finset.mem_filter, Finset.mem_Icc] at hp
    exact hp.1.2.2.1
  -- Step 6: Apply count_bound_via_log (need to convert types)
  have hcount : (S.card : ℝ) ≤ Real.log (N.natAbs : ℝ) / Real.log (4 * k^2 : ℕ) :=
    count_bound_via_log S (4 * k^2) N hN_ne hS_prime h4k2_gt_one hS_ge hS_dvd
  -- Step 7: log N.natAbs ≤ A * k * log k (from hAbound)
  have hlogN_bound : Real.log (N.natAbs : ℝ) ≤ A * k * Real.log k := hAbound k hk
  -- Step 8: log(4k²) ≥ 2 * log k
  have hlog4k2 : Real.log (4 * (k : ℝ)^2) ≥ 2 * Real.log k := log_4k_sq_ge_two_log_k k hk
  -- Step 9: log k > 0
  have hlogk_pos : 0 < Real.log (k : ℝ) := log_k_pos k hk
  -- Step 10: log(4k²) > 0
  have hlog4k2_pos : 0 < Real.log (4 * (k : ℝ)^2) := by
    calc Real.log (4 * (k : ℝ)^2) ≥ 2 * Real.log k := hlog4k2
      _ > 0 := by linarith
  -- Step 11: 2 * log k > 0
  have htwo_logk_pos : 0 < 2 * Real.log (k : ℝ) := by linarith
  -- Step 12: Convert cast - Real.log (4 * k^2 : ℕ) = Real.log (4 * (k : ℝ)^2)
  have hcast : Real.log (4 * k^2 : ℕ) = Real.log (4 * (k : ℝ)^2) := by
    congr 1
    push_cast
    ring
  rw [hcast] at hcount
  -- Step 13: Apply bound_via_log_div
  have hfinal := bound_via_log_div S.card (Real.log (N.natAbs : ℝ)) (Real.log (4 * (k : ℝ)^2))
      (A * k * Real.log k) (2 * Real.log k) hcount hlogN_bound hlog4k2 hlog4k2_pos htwo_logk_pos
  -- Step 14: Simplify (A * k * log k) / (2 * log k) = (A/2) * k
  have hne : Real.log (k : ℝ) ≠ 0 := ne_of_gt hlogk_pos
  calc (S.card : ℝ) ≤ (A * k * Real.log k) / (2 * Real.log k) := hfinal
    _ = A * k / 2 := by field_simp
    _ = (A / 2) * k := by ring

lemma count_ge_three_bound_for_k_ge_two (α : ℝ) (hα : 1/2 < α) :
    ∃ C₀ : ℝ, C₀ > 0 ∧ ∀ k : ℕ, 2 ≤ k → ∀ X : ℝ,
    (Finset.filter (fun p => 3 ≤ p) (primeCountSet α k X)).card ≤ C₀ * k := by
  obtain ⟨A, hApos, hAbound⟩ := bernoulli_num_log_bound
  use A / 2
  constructor
  · linarith
  intro k hk X
  exact count_ge_three_bound_at_fixed_k α hα A hApos hAbound k hk X

lemma count_bound_for_k_ge_two (α : ℝ) (hα : 1/2 < α) :
    ∃ C₁ : ℝ, C₁ > 0 ∧ ∀ k : ℕ, 2 ≤ k → ∀ X : ℝ,
    (primeCountSet α k X).card ≤ C₁ * k := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := count_ge_three_bound_for_k_ge_two α hα
  use C₀ + 1
  constructor
  · linarith
  · intro k hk X
    have h1 := total_count_le_large_primes_plus_one α k X
    have h2 := hC₀ k hk X
    have hk_pos : (1 : ℝ) ≤ k := by
      have : 1 ≤ k := Nat.one_le_of_lt (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hk)
      exact Nat.one_le_cast.mpr this
    have h1' : ((primeCountSet α k X).card : ℝ) ≤
        (Finset.filter (fun p => 3 ≤ p) (primeCountSet α k X)).card + 1 := by
      exact_mod_cast h1
    calc ((primeCountSet α k X).card : ℝ)
        ≤ (Finset.filter (fun p => 3 ≤ p) (primeCountSet α k X)).card + 1 := h1'
      _ ≤ C₀ * k + 1 := by linarith
      _ ≤ C₀ * k + 1 * k := by linarith
      _ = (C₀ + 1) * k := by ring


lemma prime_divisors_of_bernoulli_uniform_bound (α : ℝ) (hα : 1/2 < α) :
    ∃ C : ℝ, C > 0 ∧
    ∀ k : ℕ, 1 ≤ k →
    ∀ X : ℝ, (Finset.filter
      (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num ∧
                p ≤ ⌊X⌋₊ ∧ M_alpha α p ≥ 2 * k)
      (Finset.Icc 1 ⌊X⌋₊)).card ≤ C * k := by
  -- Get constants for k = 1 and k ≥ 2 cases
  obtain ⟨B, hB_pos, hB⟩ := count_at_k_eq_one_bounded α hα
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := count_bound_for_k_ge_two α hα
  -- Choose C = max(B, C₁)
  use max B C₁
  constructor
  · exact lt_max_of_lt_left hB_pos
  · intro k hk X
    -- The set is exactly primeCountSet
    have hset : Finset.filter
        (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num ∧
                  p ≤ ⌊X⌋₊ ∧ M_alpha α p ≥ 2 * k)
        (Finset.Icc 1 ⌊X⌋₊) = primeCountSet α k X := rfl
    rw [hset]
    -- Split into k = 1 and k ≥ 2
    rcases eq_or_lt_of_le hk with rfl | hk2
    · -- Case k = 1
      have h := hB X
      simp only [Nat.cast_one, mul_one]
      calc ((primeCountSet α 1 X).card : ℝ) ≤ B := h
        _ ≤ max B C₁ := le_max_left B C₁
    · -- Case k ≥ 2
      have hk2' : 2 ≤ k := hk2
      have h := hC₁ k hk2' X
      have hk_cast : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hk)
      calc ((primeCountSet α k X).card : ℝ) ≤ C₁ * k := h
        _ ≤ max B C₁ * k := by nlinarith [le_max_right B C₁]

lemma sum_Icc_le_sq (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (k : ℝ)) ≤ ((n : ℝ) + 1) ^ 2 := by
  have h₁ : (∑ k ∈ Finset.Icc 1 n, (k : ℝ)) ≤ ∑ k ∈ Finset.Icc 1 n, ((n : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro k hk
    have h₂ : k ∈ Finset.Icc 1 n := hk
    have h₃ : 1 ≤ k ∧ k ≤ n := Finset.mem_Icc.mp h₂
    have h₄ : (k : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast h₃.2
    have h₅ : (k : ℝ) ≤ (n : ℝ) + 1 := by linarith
    exact h₅
  have h₂ : (∑ k ∈ Finset.Icc 1 n, ((n : ℝ) + 1)) = (n : ℝ) * ((n : ℝ) + 1) := by
    have h₃ : (∑ k ∈ Finset.Icc 1 n, ((n : ℝ) + 1)) = (n : ℕ) • ((n : ℝ) + 1) := by
      simp [Finset.sum_const, Finset.card_range]
    rw [h₃]
    <;> simp [nsmul_eq_mul]
    <;> ring_nf
  have h₃ : (n : ℝ) * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith
  calc
    (∑ k ∈ Finset.Icc 1 n, (k : ℝ)) ≤ ∑ k ∈ Finset.Icc 1 n, ((n : ℝ) + 1) := h₁
    _ = (n : ℝ) * ((n : ℝ) + 1) := by rw [h₂]
    _ ≤ ((n : ℝ) + 1) ^ 2 := h₃

lemma floor_lt_of_lt {x : ℝ} {n : ℕ} (hx : 0 ≤ x) (hxn : x < n) : ⌊x⌋₊ < n := by
  exact Nat.floor_lt hx |>.mpr hxn

lemma sqrt_lt_sub_three (p : ℕ) (hp : 6 ≤ p) : Real.sqrt p < p - 3 := by
  have h₁ : (p : ℝ) ≥ 6 := by exact_mod_cast hp
  have h₄ : (Real.sqrt (p : ℝ)) ^ 2 = (p : ℝ) := by rw [Real.sq_sqrt (by positivity)]
  have h₅ : (p : ℝ) - 3 > Real.sqrt (p : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt (p : ℝ) - 3 / 2),
      Real.sqrt_nonneg (p : ℝ),
      Real.sq_sqrt (by positivity : 0 ≤ (p : ℝ)),
      sq_nonneg ((p : ℝ) - 6)]
  have h₆ : Real.sqrt (p : ℝ) < (p : ℝ) - 3 := by linarith
  exact_mod_cast h₆

lemma sqrt_div_log_pow_lt_sqrt (α : ℝ) (hα : 0 < α) (p : ℕ) (hp : 3 ≤ p) :
    Real.sqrt p / (Real.log p) ^ α < Real.sqrt p := by
  have h₁ : (1 : ℝ) < Real.log p := by
    have h₂ : (3 : ℝ) ≤ p := by exact_mod_cast hp
    have h₃ : Real.log (3 : ℝ) ≤ Real.log p := Real.log_le_log (by positivity) h₂
    have h₄ : Real.log (3 : ℝ) > (1 : ℝ) := by
      have : Real.log (3 : ℝ) > Real.log (Real.exp 1) := by
        have : (3 : ℝ) > Real.exp 1 := by
          have := Real.exp_one_lt_d9
          norm_num at this ⊢
          <;> linarith
        have : Real.log (3 : ℝ) > Real.log (Real.exp 1) := Real.log_lt_log (by positivity) this
        linarith
      have : Real.log (Real.exp 1) = (1 : ℝ) := by
        rw [Real.log_exp]
      linarith
    linarith
  have h₂ : (1 : ℝ) < (Real.log p : ℝ) ^ α := by
    have h₅ : (1 : ℝ) < (Real.log p : ℝ) ^ α := by
      exact Real.one_lt_rpow (by linarith) (by linarith)
    exact h₅
  have h₄ : 0 < (Real.log p : ℝ) ^ α := by positivity
  have h₅ : (1 : ℝ) / (Real.log p : ℝ) ^ α < 1 := by
    rw [div_lt_one (by positivity)]
    <;> nlinarith
  have h₆ : Real.sqrt p / (Real.log p : ℝ) ^ α < Real.sqrt p := by
    calc
      Real.sqrt p / (Real.log p : ℝ) ^ α = Real.sqrt p * (1 / (Real.log p : ℝ) ^ α) := by
        field_simp [h₄.ne']
      _ < Real.sqrt p * 1 := by
        gcongr
      _ = Real.sqrt p := by ring
  have h₇ : Real.sqrt p / (Real.log p) ^ α < Real.sqrt p := by
    simpa [h₄.ne'] using h₆
  exact h₇

theorem large_prime_min_simplifies (α : ℝ) (hα : 1/2 < α) :
    ∃ P₀ : ℕ, ∀ p : ℕ, P₀ ≤ p → Nat.Prime p → M_alpha α p < p - 3 := by
  use 7
  intro p hp hprime
  have h6 : 6 ≤ p := Nat.le_of_succ_le hp
  have h3 : 3 ≤ p := Nat.le_of_succ_le (Nat.le_of_succ_le (Nat.le_of_succ_le (Nat.le_of_succ_le hp)))
  have hα_pos : 0 < α := by linarith
  have hsqrt_lt : Real.sqrt p < p - 3 := sqrt_lt_sub_three p h6
  have hdiv_lt : Real.sqrt p / (Real.log p) ^ α < Real.sqrt p :=
    sqrt_div_log_pow_lt_sqrt α hα_pos p h3
  have hge0 : 0 ≤ Real.sqrt p / (Real.log p) ^ α := by
    apply div_nonneg (Real.sqrt_nonneg _)
    apply Real.rpow_nonneg
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos'.mpr (Nat.zero_lt_of_lt hp)
    have h1p : (1 : ℝ) < p := by
      have : (1 : ℕ) < p := by omega
      exact Nat.one_lt_cast.mpr this
    exact le_of_lt (Real.log_pos h1p)
  have hlt : Real.sqrt p / (Real.log p) ^ α < p - 3 := lt_trans hdiv_lt hsqrt_lt
  have hp3 : 3 ≤ p := h3
  have hcast : (↑(p - 3) : ℝ) = ↑p - 3 := by simp [Nat.cast_sub hp3]
  have hlt' : Real.sqrt p / (Real.log p) ^ α < ↑(p - 3) := by
    rw [hcast]; exact hlt
  unfold M_alpha
  exact floor_lt_of_lt hge0 hlt'

lemma nonregular_implies_witness (α : ℝ) (hα : 1/2 < α) :
    ∃ P₀ : ℕ, ∀ p : ℕ, P₀ ≤ p → Nat.Prime p → Odd p → ¬IsRegularPrime (M_alpha α p) p →
    ∃ k : ℕ, 1 ≤ 2 * k ∧ 2 * k ≤ M_alpha α p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num := by
  have h₁ : ∃ P₀ : ℕ, ∀ p : ℕ, P₀ ≤ p → Nat.Prime p → Odd p → ¬IsRegularPrime (M_alpha α p) p → ∃ k : ℕ, 1 ≤ 2 * k ∧ 2 * k ≤ M_alpha α p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num := by
    use 1
    intro p _ hp hodd h_nonreg
    have h₂ : ¬(Nat.Prime p ∧ Odd p ∧ ∀ k : ℕ, 1 ≤ 2 * k → 2 * k ≤ min (M_alpha α p) (p - 3) → ¬((p : ℤ) ∣ (bernoulli (2 * k)).num)) := by
      simpa [IsRegularPrime] using h_nonreg
    have h₃ : ¬(∀ k : ℕ, 1 ≤ 2 * k → 2 * k ≤ min (M_alpha α p) (p - 3) → ¬((p : ℤ) ∣ (bernoulli (2 * k)).num)) := by
      by_contra h₄
      have h₅ : Nat.Prime p ∧ Odd p ∧ ∀ k : ℕ, 1 ≤ 2 * k → 2 * k ≤ min (M_alpha α p) (p - 3) → ¬((p : ℤ) ∣ (bernoulli (2 * k)).num) := by
        exact ⟨hp, hodd, h₄⟩
      exact h₂ h₅
    have h₄ : ∃ (k : ℕ), 1 ≤ 2 * k ∧ 2 * k ≤ min (M_alpha α p) (p - 3) ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num := by
      by_contra h₅
      have h₆ : ∀ (k : ℕ), 1 ≤ 2 * k → 2 * k ≤ min (M_alpha α p) (p - 3) → ¬((p : ℤ) ∣ (bernoulli (2 * k)).num) := by
        intro k hk₁ hk₂
        by_contra h₇
        have h₈ : ∃ (k : ℕ), 1 ≤ 2 * k ∧ 2 * k ≤ min (M_alpha α p) (p - 3) ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num := by
          refine' ⟨k, hk₁, hk₂, _⟩
          exact h₇
        exact h₅ h₈
      exact h₃ h₆
    obtain ⟨k, hk₁, hk₂, hk₃⟩ := h₄
    have h₅ : 2 * k ≤ M_alpha α p := by
      have h₅₂ : min (M_alpha α p) (p - 3) ≤ M_alpha α p := by
        apply min_le_left
      linarith
    refine' ⟨k, hk₁, h₅, _⟩
    exact hk₃
  exact h₁

lemma log_diff_le_div (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    Real.log t - Real.log s ≤ (t - s) / s := by
  have h₁ : 0 < t := by linarith
  have h₃ : Real.log (t / s) ≤ (t / s) - 1 := by
    have h₄ : Real.log (t / s) ≤ (t / s) - 1 := by
      apply Real.log_le_sub_one_of_pos
      positivity
    exact h₄
  have h₄ : Real.log (t / s) = Real.log t - Real.log s := by
    have h₅ : Real.log (t / s) = Real.log t - Real.log s := by
      rw [Real.log_div (by linarith) (by linarith)]
    rw [h₅]
  rw [h₄] at h₃
  have h₅ : (t / s : ℝ) - 1 = (t - s) / s := by
    field_simp
  rw [h₅] at h₃
  linarith

lemma alpha_ratio_bound (α s t : ℝ) (hα : 0 < α) (hs : 2 * α ≤ s) (hst : s ≤ t) :
    α * (t - s) / s ≤ (t - s) / 2 := by
  have h₁ : 0 < s := by
    linarith
  have h₂ : α / s ≤ 1 / 2 := by
    have h₆ : (2 : ℝ) * α / s ≤ 1 := by
      rw [div_le_one (by positivity)]
      <;> linarith
    have h₇ : (α : ℝ) / s ≤ 1 / 2 := by
      calc
        (α : ℝ) / s = (2 * α) / s / 2 := by ring
        _ ≤ 1 / 2 := by
          linarith
    exact h₇
  have h₃ : α * (t - s) / s ≤ (t - s) / 2 := by
    by_cases h₄ : (t - s : ℝ) ≥ 0
    · have h₅ : (α : ℝ) / s * (t - s) ≤ (1 / 2 : ℝ) * (t - s) := by
        nlinarith
      have h₆ : (α : ℝ) / s * (t - s) = α * (t - s) / s := by
        ring
      have h₇ : (1 / 2 : ℝ) * (t - s) = (t - s) / 2 := by
        ring
      rw [h₆] at h₅
      rw [h₇] at h₅
      linarith
    · exfalso
      linarith
  exact h₃

lemma h_monotone (α : ℝ) (hα : 0 < α) :
    ∀ s t : ℝ, 2 * α ≤ s → s ≤ t →
    s / 2 - α * Real.log s ≤ t / 2 - α * Real.log t := by
  intro s t hs hst
  have hs_pos : 0 < s := by linarith
  suffices h : α * (Real.log t - Real.log s) ≤ (t - s) / 2 by linarith
  have h1 : Real.log t - Real.log s ≤ (t - s) / s := log_diff_le_div s t hs_pos hst
  have h2 : α * (Real.log t - Real.log s) ≤ α * (t - s) / s := by
    calc α * (Real.log t - Real.log s)
        ≤ α * ((t - s) / s) := mul_le_mul_of_nonneg_left h1 (le_of_lt hα)
      _ = α * (t - s) / s := by ring
  have h3 : α * (t - s) / s ≤ (t - s) / 2 := alpha_ratio_bound α s t hα hs hst
  linarith

lemma phi_monotone (α : ℝ) (hα : 0 < α) :
    ∀ s t : ℝ, 2 * α ≤ s → s ≤ t →
    Real.exp (s / 2) / s ^ α ≤ Real.exp (t / 2) / t ^ α := by
  intro s t hs hst
  have hs_pos : 0 < s := by linarith
  have ht_pos : 0 < t := by linarith
  have eq_s : Real.exp (s / 2) / s ^ α = Real.exp (s / 2 - α * Real.log s) := by
    rw [Real.rpow_def_of_pos hs_pos, mul_comm, ← Real.exp_sub]
  have eq_t : Real.exp (t / 2) / t ^ α = Real.exp (t / 2 - α * Real.log t) := by
    rw [Real.rpow_def_of_pos ht_pos, mul_comm, ← Real.exp_sub]
  rw [eq_s, eq_t]
  exact Real.exp_le_exp.mpr (h_monotone α hα s t hs hst)

lemma sqrt_div_log_pow_eq_phi (α x : ℝ) (hx : 1 < x) :
    Real.sqrt x / (Real.log x) ^ α = Real.exp (Real.log x / 2) / (Real.log x) ^ α := by
  have h₁ : Real.sqrt x = Real.exp (Real.log x / 2) := by
    have h₂ : Real.sqrt x = Real.exp (Real.log (Real.sqrt x)) := by
      rw [Real.exp_log (Real.sqrt_pos.mpr (by linarith))]
    rw [h₂]
    have h₃ : Real.log (Real.sqrt x) = Real.log x / 2 := by
      have h₄ : Real.log (Real.sqrt x) = (Real.log x) / 2 := by
        rw [Real.log_sqrt (by positivity)]
      rw [h₄]
    rw [h₃]
  rw [h₁]

lemma sqrt_div_log_pow_monotone (α : ℝ) (hα : 1/2 < α) :
    ∃ X₀ : ℝ, ∀ x y : ℝ, X₀ ≤ x → x ≤ y →
    Real.sqrt x / (Real.log x) ^ α ≤ Real.sqrt y / (Real.log y) ^ α := by
  use Real.exp (2 * α)
  intro x y hx hxy
  have hα_pos : 0 < α := by linarith
  have h_exp_pos : 1 < Real.exp (2 * α) := by
    have : 2 * α > 1 := by linarith
    calc Real.exp (2 * α) > Real.exp 1 := Real.exp_strictMono this
      _ > 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hx1 : 1 < x := lt_of_lt_of_le h_exp_pos hx
  have hy1 : 1 < y := lt_of_lt_of_le hx1 hxy
  rw [sqrt_div_log_pow_eq_phi α x hx1, sqrt_div_log_pow_eq_phi α y hy1]
  apply phi_monotone α hα_pos
  · have : Real.log (Real.exp (2 * α)) ≤ Real.log x :=
      Real.log_le_log (Real.exp_pos _) hx
    simp only [Real.log_exp] at this
    exact this
  · exact Real.log_le_log (by linarith : 0 < x) hxy

lemma log_pow_div_rpow_tendsto_zero (α : ℝ) :
    Filter.Tendsto (fun X => (Real.log X) ^ α / X ^ (1/2 : ℝ)) Filter.atTop (nhds 0) := by
  have h₂ : (fun X => (Real.log X) ^ α) =o[Filter.atTop] (fun X => (X : ℝ) ^ (1 / 2 : ℝ)) := by
    have h₂₁ : (fun X : ℝ => (Real.log X : ℝ) ^ α) =o[Filter.atTop] (fun X : ℝ => (X : ℝ) ^ (1 / 2 : ℝ)) := by
      have h₂₂ : (fun x : ℝ => Real.log x ^ α) =o[Filter.atTop] (fun x : ℝ => (x : ℝ) ^ (1 / 2 : ℝ)) := by
        apply isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ))
        <;> norm_num
      simpa using h₂₂
    simpa using h₂₁
  have h₃ : Filter.Tendsto (fun X => (Real.log X) ^ α / X ^ (1/2 : ℝ)) Filter.atTop (nhds 0) := by
    have h₄ : Filter.Tendsto (fun X : ℝ => (Real.log X : ℝ) ^ α / (X : ℝ) ^ (1 / 2 : ℝ)) Filter.atTop (nhds 0) := by
      have h₅ : (fun X : ℝ => (Real.log X : ℝ) ^ α) =o[Filter.atTop] (fun X : ℝ => (X : ℝ) ^ (1 / 2 : ℝ)) := h₂
      have h₆ : Filter.Tendsto (fun X : ℝ => (Real.log X : ℝ) ^ α / (X : ℝ) ^ (1 / 2 : ℝ)) Filter.atTop (nhds 0) :=
        h₅.tendsto_div_nhds_zero
      exact h₆
    have h₇ : (fun X : ℝ => (Real.log X : ℝ) ^ α / (X : ℝ) ^ (1 / 2 : ℝ)) = (fun X => (Real.log X) ^ α / X ^ (1/2 : ℝ)) := by
      funext X
      <;> simp [div_eq_mul_inv]
    rw [h₇] at h₄
    exact h₄
  exact h₃

lemma log_pow_div_sqrt_eventually_pos (α : ℝ) :
    ∀ᶠ X in Filter.atTop, 0 < (Real.log X) ^ α / Real.sqrt X := by
  have h_main : ∀ᶠ (X : ℝ) in Filter.atTop, 0 < (Real.log X) ^ α / Real.sqrt X := by
    have h1 : ∀ᶠ (X : ℝ) in Filter.atTop, (2 : ℝ) ≤ X := by
      filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with X hX using hX
    filter_upwards [h1] with X hX
    have h3 : 0 < Real.log X := Real.log_pos (by linarith)
    have h4 : 0 < (Real.log X : ℝ) ^ α := Real.rpow_pos_of_pos h3 α
    have h5 : 0 < Real.sqrt X := Real.sqrt_pos.mpr (by positivity)
    have h6 : 0 < (Real.log X : ℝ) ^ α / Real.sqrt X := div_pos h4 h5
    exact h6
  exact h_main

lemma log_pow_div_sqrt_tendsto_nhdsWithin_zero (α : ℝ) (_hα : 0 < α) :
    Filter.Tendsto (fun X => (Real.log X) ^ α / Real.sqrt X) Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h1 := log_pow_div_rpow_tendsto_zero α
    have heq : (fun X => Real.log X ^ α / Real.sqrt X) =ᶠ[Filter.atTop] fun X => Real.log X ^ α / X ^ (1/2 : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop 0] with X hX
      rw [Real.sqrt_eq_rpow X]
    exact h1.congr' heq.symm
  · exact log_pow_div_sqrt_eventually_pos α

lemma sqrt_div_log_pow_tendsto_atTop (α : ℝ) (hα : 0 < α) :
    Filter.Tendsto (fun X => Real.sqrt X / (Real.log X) ^ α) Filter.atTop Filter.atTop := by
  have h := log_pow_div_sqrt_tendsto_nhdsWithin_zero α hα
  have h2 := h.inv_tendsto_nhdsGT_zero
  convert h2 using 1
  ext X
  simp only [Pi.inv_apply, div_eq_mul_inv, mul_comm (Real.sqrt X)]
  ring_nf
  simp only [inv_inv]

lemma f_bounded_on_finite_range (α : ℝ) (N : ℕ) :
    ∃ C : ℝ, ∀ p : ℕ, p ≤ N → Real.sqrt p / (Real.log p) ^ α ≤ C := by
  let f : ℕ → ℝ := fun p => Real.sqrt p / (Real.log p) ^ α
  use (Finset.Iic N).sup' (Finset.nonempty_Iic) f
  intro p hp
  exact Finset.le_sup' f (Finset.mem_Iic.mpr hp)

lemma k_le_K_max_of_cast_le (α X : ℝ) (k : ℕ)
    (hk : (k : ℝ) ≤ Real.sqrt X / (2 * (Real.log X) ^ α)) :
    k ≤ K_max α X := by
  have h₁ : (k : ℝ) ≤ Real.sqrt X / (2 * (Real.log X) ^ α) := hk
  have h₂ : k ≤ ⌊Real.sqrt X / (2 * (Real.log X) ^ α)⌋₊ := by
    apply Nat.le_floor
    <;> simp_all [K_max]
  simp_all [K_max]

lemma k_bound_large_p (α : ℝ) (X_mono : ℝ)
    (hmon : ∀ x y : ℝ, X_mono ≤ x → x ≤ y → Real.sqrt x / (Real.log x) ^ α ≤ Real.sqrt y / (Real.log y) ^ α)
    (X : ℝ) (_hX : X ≥ X_mono) (p : ℕ) (hp_large : X_mono ≤ p) (hp_le : (p : ℝ) ≤ X)
    (k : ℕ) (hk : 2 * k ≤ M_alpha α p) :
    k ≤ K_max α X := by
  apply k_le_K_max_of_cast_le
  have h2k : (2 * k : ℝ) ≤ Real.sqrt p / (Real.log p) ^ α := by
    have hnn : 0 ≤ Real.sqrt p / (Real.log p) ^ α := by positivity
    have := (Nat.le_floor_iff hnn).mp hk
    simp only [Nat.cast_mul, Nat.cast_ofNat] at this
    exact this
  have hmon_applied : Real.sqrt p / (Real.log p) ^ α ≤ Real.sqrt X / (Real.log X) ^ α :=
    hmon p X hp_large hp_le
  calc (k : ℝ) = (2 * k) / 2 := by ring
    _ ≤ (Real.sqrt p / (Real.log p) ^ α) / 2 := by linarith
    _ ≤ (Real.sqrt X / (Real.log X) ^ α) / 2 := by linarith
    _ = Real.sqrt X / (2 * (Real.log X) ^ α) := by ring

lemma two_k_le_floor_imp_k_le_half (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (h : 2 * k ≤ ⌊a⌋₊) :
    (k : ℝ) ≤ a / 2 := by
  have h₁ : (2 * k : ℝ) ≤ a := by
    have h₂ : (⌊a⌋₊ : ℝ) ≤ a := by
      exact Nat.floor_le ha
    have h₃ : (2 * k : ℝ) ≤ (⌊a⌋₊ : ℝ) := by
      norm_cast at h ⊢
    linarith
  have h₄ : (k : ℝ) ≤ a / 2 := by
    linarith
  exact h₄

lemma k_bound_small_p (α : ℝ) (X_mono C_max : ℝ)
    (hC : ∀ p : ℕ, (p : ℝ) < X_mono → Real.sqrt p / (Real.log p) ^ α ≤ C_max)
    (X : ℝ) (hX_dom : Real.sqrt X / (Real.log X) ^ α ≥ C_max)
    (p : ℕ) (hp_small : (p : ℝ) < X_mono)
    (k : ℕ) (hk : 2 * k ≤ M_alpha α p) :
    k ≤ K_max α X := by
  have h_nonneg : 0 ≤ Real.sqrt p / (Real.log p) ^ α := by positivity
  have h1 : (k : ℝ) ≤ (Real.sqrt p / (Real.log p) ^ α) / 2 :=
    two_k_le_floor_imp_k_le_half (Real.sqrt p / (Real.log p) ^ α) h_nonneg k hk
  have h2 : Real.sqrt p / (Real.log p) ^ α ≤ C_max := hC p hp_small
  have h3 : C_max ≤ Real.sqrt X / (Real.log X) ^ α := hX_dom
  have h4 : (k : ℝ) ≤ (Real.sqrt X / (Real.log X) ^ α) / 2 := by
    calc (k : ℝ) ≤ (Real.sqrt p / (Real.log p) ^ α) / 2 := h1
      _ ≤ C_max / 2 := by linarith
      _ ≤ (Real.sqrt X / (Real.log X) ^ α) / 2 := by linarith
  have h5 : (Real.sqrt X / (Real.log X) ^ α) / 2 = Real.sqrt X / (2 * (Real.log X) ^ α) := by
    ring
  rw [h5] at h4
  exact k_le_K_max_of_cast_le α X k h4

lemma f_eventually_ge (α : ℝ) (hα : 0 < α) (C : ℝ) :
    ∃ X_dom : ℝ, ∀ X ≥ X_dom, Real.sqrt X / (Real.log X) ^ α ≥ C := by
  have htend := sqrt_div_log_pow_tendsto_atTop α hα
  have hev := Filter.Tendsto.eventually_ge_atTop htend C
  rw [Filter.eventually_atTop] at hev
  exact hev

lemma nat_lt_real_imp_le_ceil (X_mono : ℝ) (p : ℕ) (h : (p : ℝ) < X_mono) : p ≤ ⌈X_mono⌉₊ := by
  have h₁ : p < ⌈(X_mono : ℝ)⌉₊ := by
    have h₃ : (p : ℝ) < ⌈(X_mono : ℝ)⌉₊ := by
      linarith [Nat.le_ceil (X_mono)]
    exact_mod_cast h₃
  have h₂ : p ≤ ⌈(X_mono : ℝ)⌉₊ := by
    linarith
  exact h₂

lemma nat_le_floor_imp_cast_le (X : ℝ) (hX : 0 ≤ X) (p : ℕ) (hp : p ≤ ⌊X⌋₊) : (p : ℝ) ≤ X := by
  have h₁ : (p : ℕ) ≤ ⌊X⌋₊ := hp
  have h₂ : (p : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
    norm_cast at h₁ ⊢
  have h₃ : (⌊X⌋₊ : ℝ) ≤ X := by
    (try exact Nat.floor_le (by linarith))
  linarith

lemma witness_bounded_by_K_max (α : ℝ) (hα : 1/2 < α) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X ≥ X₀ → ∀ p : ℕ, p ≤ ⌊X⌋₊ → ∀ k : ℕ,
    2 * k ≤ M_alpha α p → k ≤ K_max α X := by
  obtain ⟨X_mono, hmon⟩ := sqrt_div_log_pow_monotone α hα
  obtain ⟨C_max, hC_max⟩ := f_bounded_on_finite_range α ⌈X_mono⌉₊
  have hα_pos : 0 < α := by linarith
  obtain ⟨X_dom, hX_dom⟩ := f_eventually_ge α hα_pos C_max
  use max (max X_mono X_dom) 0
  intro X hX p hp k hk
  have hX_nonneg : 0 ≤ X := le_trans (le_max_right _ _) hX
  by_cases hp_case : X_mono ≤ (p : ℝ)
  · have hp_le : (p : ℝ) ≤ X := nat_le_floor_imp_cast_le X hX_nonneg p hp
    have hX_mono : X ≥ X_mono := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
    exact k_bound_large_p α X_mono hmon X hX_mono p hp_case hp_le k hk
  · push_neg at hp_case
    have hC : ∀ q : ℕ, (q : ℝ) < X_mono → Real.sqrt q / (Real.log q) ^ α ≤ C_max := by
      intro q hq
      exact hC_max q (nat_lt_real_imp_le_ceil X_mono q hq)
    have hX_ge_dom : X ≥ X_dom := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
    have hX_dom_app : Real.sqrt X / (Real.log X) ^ α ≥ C_max := hX_dom X hX_ge_dom
    exact k_bound_small_p α X_mono C_max hC X hX_dom_app p hp_case k hk

lemma prime_ge_three_is_odd (p : ℕ) (hp : Nat.Prime p) (h3 : 3 ≤ p) : Odd p := by
  have h_ne_two : p ≠ 2 := by omega
  exact Nat.Prime.odd_of_ne_two hp h_ne_two

lemma large_prime_has_witness (α : ℝ) (p : ℕ) (M P₂ : ℕ)
    (hP₂ : ∀ q : ℕ, P₂ ≤ q → Nat.Prime q → Odd q → ¬IsRegularPrime (M_alpha α q) q →
           ∃ k : ℕ, 1 ≤ 2 * k ∧ 2 * k ≤ M_alpha α q ∧ (q : ℤ) ∣ (bernoulli (2 * k)).num)
    (hM3 : 3 ≤ M) (hMP₂ : P₂ ≤ M)
    (hpM : M ≤ p) (hp : Nat.Prime p) (hnonreg : ¬IsRegularPrime (M_alpha α p) p) :
    ∃ k : ℕ, 1 ≤ 2 * k ∧ 2 * k ≤ M_alpha α p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num := by
  have hP₂_le_p : P₂ ≤ p := by
    linarith
  have hodd_p : Odd p := by
    have h₁ : p ≠ 2 := by
      by_contra h
      linarith
    have h₂ : p % 2 = 1 := by
      have h₃ := Nat.Prime.eq_two_or_odd hp
      cases h₃ with
      | inl h₃ =>
        exfalso
        exact h₁ (by linarith)
      | inr h₃ =>
        omega
    exact ⟨p / 2, by omega⟩
  have h_main : ∃ k : ℕ, 1 ≤ 2 * k ∧ 2 * k ≤ M_alpha α p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num := by
    have h₁ : P₂ ≤ p := hP₂_le_p
    have h₂ : Nat.Prime p := hp
    have h₃ : Odd p := hodd_p
    have h₄ : ¬IsRegularPrime (M_alpha α p) p := hnonreg
    have h₅ : ∃ k : ℕ, 1 ≤ 2 * k ∧ 2 * k ≤ M_alpha α p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num :=
      hP₂ p h₁ h₂ h₃ h₄
    exact h₅
  exact h_main

lemma small_primes_bounded (α : ℝ) (M : ℕ) (X : ℝ) (hXM : M ≤ ⌊X⌋₊) :
    ((Finset.Icc 1 ⌊X⌋₊).filter (fun p =>
      Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p ∧ p < M)).card ≤
    ((Finset.Icc 1 (M - 1)).filter (fun p => Nat.Prime p)).card := by
  have h_main : ((Finset.Icc 1 ⌊X⌋₊).filter (fun p => Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p ∧ p < M)) ⊆ ((Finset.Icc 1 (M - 1)).filter (fun p => Nat.Prime p)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨hp1, _⟩, hprime, _, hpM⟩ := hp
    refine ⟨⟨hp1, ?_⟩, hprime⟩
    have hM_pos : 0 < M := Nat.lt_of_lt_of_le (Nat.Prime.pos hprime) (le_of_lt hpM)
    omega
  exact Finset.card_le_card h_main

lemma witness_in_range (α : ℝ) (X₁ X : ℝ) (hX : X ≥ X₁)
    (hX₁ : ∀ Y : ℝ, Y ≥ X₁ → ∀ p : ℕ, p ≤ ⌊Y⌋₊ → ∀ k : ℕ, 2 * k ≤ M_alpha α p → k ≤ K_max α Y)
    (p : ℕ) (hp_le : p ≤ ⌊X⌋₊) (k : ℕ) (hk1 : 1 ≤ 2 * k) (hk2 : 2 * k ≤ M_alpha α p) :
    k ∈ Finset.Icc 1 (K_max α X) := by
  have h₂ : k ≤ K_max α X := by
    have h₃ : 2 * k ≤ M_alpha α p := hk2
    have h₄ : p ≤ ⌊X⌋₊ := hp_le
    have h₅ : k ≤ K_max α X := hX₁ X (by linarith) p h₄ k h₃
    exact h₅
  have h₁ : 1 ≤ k := by
    omega
  exact Finset.mem_Icc.mpr ⟨h₁, h₂⟩

lemma large_primes_subset_biUnion (α : ℝ) (X X₁ : ℝ) (M P₂ : ℕ) (hX : X ≥ X₁) (_hXM : M ≤ ⌊X⌋₊)
    (hP₂ : ∀ q : ℕ, P₂ ≤ q → Nat.Prime q → Odd q → ¬IsRegularPrime (M_alpha α q) q →
           ∃ k : ℕ, 1 ≤ 2 * k ∧ 2 * k ≤ M_alpha α q ∧ (q : ℤ) ∣ (bernoulli (2 * k)).num)
    (hX₁ : ∀ Y : ℝ, Y ≥ X₁ → ∀ p : ℕ, p ≤ ⌊Y⌋₊ → ∀ k : ℕ, 2 * k ≤ M_alpha α p → k ≤ K_max α Y)
    (hM3 : 3 ≤ M) (hMP₂ : P₂ ≤ M) :
    (Finset.Icc 1 ⌊X⌋₊).filter (fun p =>
      Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p ∧ M ≤ p) ⊆
    (Finset.Icc 1 (K_max α X)).biUnion (fun k =>
      (Finset.Icc 1 ⌊X⌋₊).filter (fun p =>
        Nat.Prime p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num ∧ p ≤ ⌊X⌋₊ ∧ M_alpha α p ≥ 2 * k)) := by
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨hp1, hpX⟩, hprime, hnonreg, hpM⟩ := hp
  have hodd : Odd p := prime_ge_three_is_odd p hprime (le_trans hM3 hpM)
  obtain ⟨k, hk1, hk2, hdiv⟩ := large_prime_has_witness α p M P₂ hP₂ hM3 hMP₂ hpM hprime hnonreg
  have hk_in_range : k ∈ Finset.Icc 1 (K_max α X) :=
    witness_in_range α X₁ X hX hX₁ p hpX k hk1 hk2
  rw [Finset.mem_biUnion]
  refine ⟨k, hk_in_range, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hp1, hpX⟩, hprime, hdiv, hpX, hk2⟩

lemma disjoint_small_large (α : ℝ) (X : ℝ) (M : ℕ) :
    Disjoint
      ((Finset.Icc 1 ⌊X⌋₊).filter (fun p => Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p ∧ p < M))
      ((Finset.Icc 1 ⌊X⌋₊).filter (fun p => Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p ∧ M ≤ p)) := by
  have h_main : ∀ (p : ℕ), p ∈ (Finset.Icc 1 ⌊X⌋₊ : Finset ℕ) → (Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p ∧ p < M) → (Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p ∧ M ≤ p) → False := by simp_all
  exact Finset.disjoint_filter.mpr h_main

lemma union_small_large_eq (α : ℝ) (X : ℝ) (M : ℕ) :
    ((Finset.Icc 1 ⌊X⌋₊).filter (fun p => Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p ∧ p < M)) ∪
    ((Finset.Icc 1 ⌊X⌋₊).filter (fun p => Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p ∧ M ≤ p)) =
    (Finset.Icc 1 ⌊X⌋₊).filter (fun p => Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p) := by
  ext p
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro (⟨hp1, hp2, hp3, _⟩ | ⟨hp1, hp2, hp3, _⟩) <;> exact ⟨hp1, hp2, hp3⟩
  · rintro ⟨hp1, hp2, hp3⟩
    by_cases h : p < M
    · left; exact ⟨hp1, hp2, hp3, h⟩
    · right; push_neg at h; exact ⟨hp1, hp2, hp3, h⟩

lemma partition_count (α : ℝ) (X : ℝ) (M : ℕ) :
    countNonRegularPrimes α X =
    ((Finset.Icc 1 ⌊X⌋₊).filter (fun p =>
      Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p ∧ p < M)).card +
    ((Finset.Icc 1 ⌊X⌋₊).filter (fun p =>
      Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p ∧ M ≤ p)).card := by
  unfold countNonRegularPrimes
  rw [← union_small_large_eq α X M]
  rw [Finset.card_union_of_disjoint (disjoint_small_large α X M)]

lemma count_bound_main (α : ℝ) (_hα : 1/2 < α)
    (P₁ : ℕ) (_hP₁ : ∀ p : ℕ, P₁ ≤ p → Nat.Prime p → M_alpha α p < p - 3)
    (P₂ : ℕ) (hP₂ : ∀ p : ℕ, P₂ ≤ p → Nat.Prime p → Odd p → ¬IsRegularPrime (M_alpha α p) p →
                   ∃ k : ℕ, 1 ≤ 2 * k ∧ 2 * k ≤ M_alpha α p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num)
    (X₁ : ℝ) (hX₁ : ∀ X : ℝ, X ≥ X₁ → ∀ p : ℕ, p ≤ ⌊X⌋₊ → ∀ k : ℕ,
                    2 * k ≤ M_alpha α p → k ≤ K_max α X) :
    ∃ C : ℝ, ∃ X₀ : ℝ, ∀ X : ℝ, X ≥ X₀ →
    (countNonRegularPrimes α X : ℝ) ≤
    C + ∑ k ∈ Finset.Icc 1 (K_max α X),
      ((Finset.filter
        (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num ∧
                  p ≤ ⌊X⌋₊ ∧ M_alpha α p ≥ 2 * k)
        (Finset.Icc 1 ⌊X⌋₊)).card : ℝ) := by
  let M := max (max P₁ P₂) 3
  let C : ℝ := ((Finset.Icc 1 (M - 1)).filter (fun p => Nat.Prime p)).card
  let X₀ := max X₁ (M : ℝ)
  use C, X₀
  intro X hX
  have hX_ge_X₁ : X ≥ X₁ := le_trans (le_max_left X₁ (M : ℝ)) hX
  have hX_ge_M : X ≥ (M : ℝ) := le_trans (le_max_right X₁ (M : ℝ)) hX
  have hXM : M ≤ ⌊X⌋₊ := Nat.le_floor hX_ge_M
  have hM3 : 3 ≤ M := le_max_right (max P₁ P₂) 3
  have hMP₁ : P₁ ≤ M := le_trans (le_max_left P₁ P₂) (le_max_left (max P₁ P₂) 3)
  have hMP₂ : P₂ ≤ M := le_trans (le_max_right P₁ P₂) (le_max_left (max P₁ P₂) 3)
  rw [partition_count α X M]
  push_cast
  have hsmall : (((Finset.Icc 1 ⌊X⌋₊).filter (fun p =>
      Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p ∧ p < M)).card : ℝ) ≤ C := by
    exact Nat.cast_le.mpr (small_primes_bounded α M X hXM)
  have hlarge : (((Finset.Icc 1 ⌊X⌋₊).filter (fun p =>
      Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p ∧ M ≤ p)).card : ℝ) ≤
      ∑ k ∈ Finset.Icc 1 (K_max α X),
        ((Finset.filter (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num ∧
              p ≤ ⌊X⌋₊ ∧ M_alpha α p ≥ 2 * k) (Finset.Icc 1 ⌊X⌋₊)).card : ℝ) := by
    have hsub := large_primes_subset_biUnion α X X₁ M P₂ hX_ge_X₁ hXM hP₂ hX₁ hM3 hMP₂
    calc (((Finset.Icc 1 ⌊X⌋₊).filter (fun p =>
            Nat.Prime p ∧ ¬IsRegularPrime (M_alpha α p) p ∧ M ≤ p)).card : ℝ)
        ≤ ((Finset.Icc 1 (K_max α X)).biUnion (fun k =>
            (Finset.Icc 1 ⌊X⌋₊).filter (fun p =>
              Nat.Prime p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num ∧
              p ≤ ⌊X⌋₊ ∧ M_alpha α p ≥ 2 * k))).card := by
          exact Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ ∑ k ∈ Finset.Icc 1 (K_max α X),
            ((Finset.Icc 1 ⌊X⌋₊).filter (fun p =>
              Nat.Prime p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num ∧
              p ≤ ⌊X⌋₊ ∧ M_alpha α p ≥ 2 * k)).card := by
          exact Nat.cast_le.mpr Finset.card_biUnion_le
      _ = ∑ k ∈ Finset.Icc 1 (K_max α X),
            ((Finset.filter (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num ∧
              p ≤ ⌊X⌋₊ ∧ M_alpha α p ≥ 2 * k) (Finset.Icc 1 ⌊X⌋₊)).card : ℝ) := by
          simp only [Nat.cast_sum]
  linarith

lemma count_bound_by_sum_over_k_eventually (α : ℝ) (hα : 1/2 < α) :
    ∃ C : ℝ, ∃ X₀ : ℝ, ∀ X : ℝ, X ≥ X₀ →
    (countNonRegularPrimes α X : ℝ) ≤
    C + ∑ k ∈ Finset.Icc 1 (K_max α X),
      ((Finset.filter
        (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num ∧
                  p ≤ ⌊X⌋₊ ∧ M_alpha α p ≥ 2 * k)
        (Finset.Icc 1 ⌊X⌋₊)).card : ℝ) := by
  obtain ⟨P₁, hP₁⟩ := large_prime_min_simplifies α hα
  obtain ⟨P₂, hP₂⟩ := nonregular_implies_witness α hα
  obtain ⟨X₁, hX₁⟩ := witness_bounded_by_K_max α hα
  exact count_bound_main α hα P₁ hP₁ P₂ hP₂ X₁ hX₁

lemma sum_linear_bound_sq (n : ℕ) (C : ℝ) (hC : C > 0) :
    (∑ k ∈ Finset.Icc 1 n, C * (k : ℝ)) ≤ C * ((n : ℝ) + 1) ^ 2 := by
  have h₁ : ∀ (k : ℕ), k ∈ Finset.Icc 1 n → (k : ℝ) ≤ ((n : ℝ) + 1) := by
    intro k hk
    have h₃ : k ≤ n := by
      simp [Finset.mem_Icc] at hk
      linarith
    have h₄ : (k : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast h₃
    linarith
  have h₂ : (∑ k ∈ Finset.Icc 1 n, (k : ℝ)) ≤ (n : ℝ) * ((n : ℝ) + 1) := by
    have h₃ : (∑ k ∈ Finset.Icc 1 n, (k : ℝ)) ≤ ∑ k ∈ Finset.Icc 1 n, ((n : ℝ) + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact h₁ i hi
    have h₄ : (∑ k ∈ Finset.Icc 1 n, ((n : ℝ) + 1 : ℝ)) = (n : ℝ) * ((n : ℝ) + 1) := by
      have h₅ : (∑ k ∈ Finset.Icc 1 n, ((n : ℝ) + 1 : ℝ)) = (n : ℕ) • ((n : ℝ) + 1 : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      rw [h₅]
      simp [nsmul_eq_mul]
      <;>
      (try ring_nf)
    linarith
  have h₅ : (∑ k ∈ Finset.Icc 1 n, C * (k : ℝ)) ≤ C * ((n : ℝ) + 1) ^ 2 := by
    have h₆ : (∑ k ∈ Finset.Icc 1 n, C * (k : ℝ)) = C * (∑ k ∈ Finset.Icc 1 n, (k : ℝ)) := by
      rw [Finset.mul_sum]
    rw [h₆]
    have h₇ : C * (∑ k ∈ Finset.Icc 1 n, (k : ℝ)) ≤ C * (((n : ℝ) + 1) ^ 2) := by
      nlinarith
    linarith
  exact h₅


lemma helper_sum_bound (n : ℕ) (C : ℝ) (hC : C > 0) :
    (∑ k ∈ Finset.Icc 1 n, C * (k : ℝ)) ≤ C * ((n : ℝ) + 1) ^ 2 := by
  rw [← Finset.mul_sum]
  have h := sum_Icc_le_sq n
  exact mul_le_mul_of_nonneg_left h (le_of_lt hC)

lemma tendsto_norm_div_log_rpow_atTop (α : ℝ) :
    Filter.Tendsto (fun X : ℝ => ‖X / (Real.log X) ^ (2 * α)‖) Filter.atTop Filter.atTop := by
  have h₂ : Filter.Tendsto (fun X : ℝ => Real.exp (Real.log X) / (Real.log X) ^ (2 * α)) Filter.atTop Filter.atTop := by
    have h₃ : Filter.Tendsto (fun X : ℝ => Real.log X) Filter.atTop Filter.atTop := Real.tendsto_log_atTop
    have h₄ : Filter.Tendsto (fun (u : ℝ) => Real.exp u / u ^ (2 * α)) Filter.atTop Filter.atTop := tendsto_exp_div_rpow_atTop (2 * α)
    have h₅ : Filter.Tendsto (fun X : ℝ => Real.exp (Real.log X) / (Real.log X) ^ (2 * α)) Filter.atTop Filter.atTop := h₄.comp h₃
    exact h₅
  have h₃ : Filter.Tendsto (fun X : ℝ => (X : ℝ) / (Real.log X) ^ (2 * α)) Filter.atTop Filter.atTop := by
    have h₅ : Filter.Tendsto (fun X : ℝ => (X : ℝ) / (Real.log X) ^ (2 * α)) Filter.atTop Filter.atTop := by
      have h₆ : ∀ (X : ℝ), X > 0 → Real.exp (Real.log X) = X := by
        intro X hX
        rw [Real.exp_log hX]
      have h₇ : ∀ᶠ (X : ℝ) in Filter.atTop, X > 0 := by
        filter_upwards [Filter.eventually_gt_atTop 0] with X hX
        exact hX
      have h₈ : Filter.Tendsto (fun X : ℝ => (X : ℝ) / (Real.log X) ^ (2 * α)) Filter.atTop Filter.atTop := by
        have h₉ : (fun X : ℝ => (X : ℝ) / (Real.log X) ^ (2 * α)) =ᶠ[Filter.atTop] (fun X : ℝ => Real.exp (Real.log X) / (Real.log X) ^ (2 * α)) := by
          filter_upwards [h₇] with X hX
          rw [h₆ X hX]
        have h₁₀ : Filter.Tendsto (fun X : ℝ => Real.exp (Real.log X) / (Real.log X) ^ (2 * α)) Filter.atTop Filter.atTop := h₂
        have h₁₁ : Filter.Tendsto (fun X : ℝ => (X : ℝ) / (Real.log X) ^ (2 * α)) Filter.atTop Filter.atTop :=
          h₁₀.congr' h₉.symm
        exact h₁₁
      exact h₈
    exact h₅
  have h₄ : Filter.Tendsto (fun X : ℝ => ‖(X : ℝ) / (Real.log X) ^ (2 * α)‖) Filter.atTop Filter.atTop := by
    have h₅ : Filter.Tendsto (fun X : ℝ => (X : ℝ) / (Real.log X) ^ (2 * α)) Filter.atTop Filter.atTop := h₃
    have h₆ : Filter.Tendsto (fun X : ℝ => ‖(X : ℝ) / (Real.log X) ^ (2 * α)‖) Filter.atTop Filter.atTop := by
      have h₇ : ∀ᶠ (X : ℝ) in Filter.atTop, (X : ℝ) / (Real.log X) ^ (2 * α) > 0 := by
        filter_upwards [Filter.eventually_gt_atTop 1] with X hX
        have h₈ : Real.log X > 0 := Real.log_pos (by linarith)
        have h₁₂ : (X : ℝ) / (Real.log X) ^ (2 * α) > 0 := by positivity
        exact h₁₂
      have h₈ : Filter.Tendsto (fun X : ℝ => (X : ℝ) / (Real.log X) ^ (2 * α)) Filter.atTop Filter.atTop := h₅
      have h₉ : Filter.Tendsto (fun X : ℝ => ‖(X : ℝ) / (Real.log X) ^ (2 * α)‖) Filter.atTop Filter.atTop := by
        have h₁₀ : Filter.Tendsto (fun X : ℝ => (X : ℝ) / (Real.log X) ^ (2 * α)) Filter.atTop Filter.atTop := h₈
        have h₁₁ : Filter.Tendsto (fun X : ℝ => ‖(X : ℝ) / (Real.log X) ^ (2 * α)‖) Filter.atTop Filter.atTop := by
          have h₁₂ : ∀ᶠ (X : ℝ) in Filter.atTop, (X : ℝ) / (Real.log X) ^ (2 * α) > 0 := h₇
          have h₁₃ : ∀ᶠ (X : ℝ) in Filter.atTop, ‖(X : ℝ) / (Real.log X) ^ (2 * α)‖ = (X : ℝ) / (Real.log X) ^ (2 * α) := by
            filter_upwards [h₁₂] with X hX
            rw [Real.norm_eq_abs]
            rw [abs_of_nonneg (le_of_lt hX)]
          have h₁₄ : Filter.Tendsto (fun X : ℝ => ‖(X : ℝ) / (Real.log X) ^ (2 * α)‖) Filter.atTop Filter.atTop := by
            have h₁₅ : Filter.Tendsto (fun X : ℝ => (X : ℝ) / (Real.log X) ^ (2 * α)) Filter.atTop Filter.atTop := h₁₀
            have h₁₆ : Filter.Tendsto (fun X : ℝ => ‖(X : ℝ) / (Real.log X) ^ (2 * α)‖) Filter.atTop Filter.atTop := by
              apply Filter.Tendsto.congr' _ h₁₅
              filter_upwards [h₁₃] with X hX
              rw [hX]
            exact h₁₆
          exact h₁₄
        exact h₁₁
      exact h₉
    exact h₆
  have h₅ : (fun X : ℝ => ‖X / (Real.log X) ^ (2 * α)‖) = (fun X : ℝ => ‖(X : ℝ) / (Real.log X) ^ (2 * α)‖) := by
    funext X
    <;> simp [div_eq_mul_inv]
  have h₆ : Filter.Tendsto (fun X : ℝ => ‖X / (Real.log X) ^ (2 * α)‖) Filter.atTop Filter.atTop := by
    rw [h₅]
    exact h₄
  exact h₆

lemma log_pow_div_sqrt_eventually_lt_one (α : ℝ) :
    ∀ᶠ (X : ℝ) in Filter.atTop, Real.log X ^ α / Real.sqrt X < 1 := by
  have htendsto := log_pow_div_rpow_tendsto_zero α
  have h := Filter.Tendsto.eventually_lt_const (by norm_num : (0 : ℝ) < 1) htendsto
  simp only [Real.sqrt_eq_rpow] at h ⊢
  exact h

lemma sqrt_eventually_pos :
    ∀ᶠ (X : ℝ) in Filter.atTop, 0 < Real.sqrt X := by
  have h : ∀ᶠ (X : ℝ) in Filter.atTop, 0 < X := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with X hX
    linarith
  filter_upwards [h] with X hX
  exact Real.sqrt_pos.mpr hX

lemma log_pow_le_sqrt_eventually (α : ℝ) (_hα : 1/2 < α) :
    ∀ᶠ (X : ℝ) in Filter.atTop, Real.log X ^ α ≤ Real.sqrt X := by
  filter_upwards [log_pow_div_sqrt_eventually_lt_one α, sqrt_eventually_pos] with X hlt hpos
  have h1 : Real.log X ^ α / Real.sqrt X * Real.sqrt X < 1 * Real.sqrt X := by
    exact mul_lt_mul_of_pos_right hlt hpos
  rw [div_mul_cancel₀ _ (ne_of_gt hpos), one_mul] at h1
  exact le_of_lt h1

lemma two_K_max_le_sqrt_div (α X : ℝ) (hX : 1 < X) (hα : 0 < α) :
    2 * (K_max α X : ℝ) ≤ Real.sqrt X / (Real.log X) ^ α := by
  have h1 : 0 ≤ Real.sqrt X / (2 * (Real.log X) ^ α) := by
    have h2 : 0 < Real.log X := Real.log_pos hX
    positivity
  have h2 : (K_max α X : ℝ) = ⌊Real.sqrt X / (2 * (Real.log X) ^ α)⌋₊ := by
    simp [K_max]
  rw [h2]
  have h3 : (⌊Real.sqrt X / (2 * (Real.log X) ^ α)⌋₊ : ℝ) ≤ Real.sqrt X / (2 * (Real.log X) ^ α) := by
    exact Nat.floor_le (by positivity)
  have h5 : 2 * (Real.sqrt X / (2 * (Real.log X) ^ α)) = Real.sqrt X / (Real.log X) ^ α := by
    have h6 : 2 ≠ 0 := by norm_num
    field_simp [h6]
  linarith

lemma sqrt_div_le_linear_div (α X : ℝ) (hX : 1 < X) (hα : 0 < α)
    (hlog : Real.log X ^ α ≤ Real.sqrt X) :
    Real.sqrt X / (Real.log X) ^ α ≤ X / (Real.log X) ^ (2 * α) := by
  have hlog_pos : 0 < Real.log X := by
    have h₂ : 0 < Real.log X := Real.log_pos (by linarith)
    exact h₂
  have hlog_rpow_pos : 0 < Real.log X ^ α := by
    have h : 0 < Real.log X := hlog_pos
    exact Real.rpow_pos_of_pos h α
  have h_main : Real.sqrt X * (Real.log X) ^ α ≤ X := by
    have h₂ : Real.sqrt X * (Real.log X) ^ α ≤ Real.sqrt X * Real.sqrt X := by
      nlinarith
    have h₃ : Real.sqrt X * Real.sqrt X = X := by
      rw [Real.mul_self_sqrt (by positivity)]
    linarith
  have h_denom_eq : (Real.log X) ^ (2 * α) = (Real.log X) ^ α * (Real.log X) ^ α := by
    have h₁ : (Real.log X) ^ (2 * α) = (Real.log X) ^ (α + α) := by ring_nf
    rw [h₁]
    have h₂ : (Real.log X) ^ (α + α) = (Real.log X) ^ α * (Real.log X) ^ α := by
      rw [Real.rpow_add (by positivity : (0 : ℝ) < Real.log X)]
    rw [h₂]
  have h_final : Real.sqrt X / (Real.log X) ^ α ≤ X / (Real.log X) ^ (2 * α) := by
    have h₁ : 0 < (Real.log X) ^ α := hlog_rpow_pos
    have h₅ : Real.sqrt X / (Real.log X) ^ α ≤ X / (Real.log X) ^ (2 * α) := by
      calc
        Real.sqrt X / (Real.log X) ^ α = (Real.sqrt X * (Real.log X) ^ α) / ((Real.log X) ^ α * (Real.log X) ^ α) := by
          field_simp [h₁.ne']
        _ ≤ X / ((Real.log X) ^ α * (Real.log X) ^ α) := by
          gcongr
        _ = X / (Real.log X) ^ (2 * α) := by
          rw [h_denom_eq]
    exact h₅
  exact h_final

lemma K_max_linear_bound (α : ℝ) (hα : 1/2 < α) :
    ∀ᶠ (X : ℝ) in Filter.atTop, 2 * (K_max α X : ℝ) ≤ X / (Real.log X) ^ (2 * α) := by
  have hα_pos : 0 < α := by linarith
  have h_log_bound := log_pow_le_sqrt_eventually α hα
  have h_gt_one : ∀ᶠ X : ℝ in Filter.atTop, 1 < X := Filter.eventually_gt_atTop 1
  apply (h_gt_one.and h_log_bound).mono
  intro X ⟨hX, hlog⟩
  calc 2 * (K_max α X : ℝ)
      ≤ Real.sqrt X / (Real.log X) ^ α := two_K_max_le_sqrt_div α X hX hα_pos
    _ ≤ X / (Real.log X) ^ (2 * α) := sqrt_div_le_linear_div α X hX hα_pos hlog

theorem K_max_linear_isBigO (α : ℝ) (hα : 1/2 < α) :
    (fun X : ℝ => 2 * (K_max α X : ℝ)) =O[Filter.atTop]
    (fun X : ℝ => X / (Real.log X) ^ (2 * α)) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [K_max_linear_bound α hα, Filter.eventually_gt_atTop 1] with X hX hX1
  simp only [one_mul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * (K_max α X : ℝ))]
  have hlogX : 0 < Real.log X := Real.log_pos hX1
  rw [Real.norm_of_nonneg (by positivity)]
  exact hX

lemma helper_const_isBigO (α : ℝ) (_hα : 1/2 < α) (c : ℝ) :
    (fun _ : ℝ => c) =O[Filter.atTop]
    (fun X : ℝ => X / (Real.log X) ^ (2 * α)) := by
  have h1 : (fun _ : ℝ => (1 : ℝ)) =o[Filter.atTop]
            (fun X : ℝ => X / (Real.log X) ^ (2 * α)) := by
    rw [Asymptotics.isLittleO_one_left_iff ℝ]
    exact tendsto_norm_div_log_rpow_atTop α
  have h2 : (fun _ : ℝ => (1 : ℝ)) =O[Filter.atTop]
            (fun X : ℝ => X / (Real.log X) ^ (2 * α)) := h1.isBigO
  calc (fun _ : ℝ => c) = (fun _ : ℝ => c * 1) := by simp
    _ =O[Filter.atTop] (fun X : ℝ => X / (Real.log X) ^ (2 * α)) := h2.const_mul_left c

lemma helper_K_max_plus_one_sq_isBigO (α : ℝ) (hα : 1/2 < α) :
    (fun X : ℝ => ((K_max α X : ℝ) + 1) ^ 2) =O[Filter.atTop]
    (fun X : ℝ => X / (Real.log X) ^ (2 * α)) := by
  have h1 : (fun X : ℝ => ((K_max α X : ℝ) + 1) ^ 2) =
            (fun X : ℝ => (K_max α X : ℝ) ^ 2 + 2 * (K_max α X : ℝ) + 1) := by
    ext X
    ring
  rw [h1]
  have hsq := K_max_sq_isBigO α hα
  have hlin := K_max_linear_isBigO α hα
  have hconst := helper_const_isBigO α hα 1
  have h12 : (fun X : ℝ => (K_max α X : ℝ) ^ 2 + 2 * (K_max α X : ℝ)) =O[Filter.atTop]
             (fun X : ℝ => X / (Real.log X) ^ (2 * α)) := by
    exact hsq.add hlin
  exact h12.add hconst

lemma helper_count_eventually_bound (α : ℝ) (hα : 1/2 < α) (C C₁ : ℝ) (hC : C > 0)
    (hCunif : ∀ k : ℕ, 1 ≤ k → ∀ X : ℝ,
      (Finset.filter (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num ∧
                p ≤ ⌊X⌋₊ ∧ M_alpha α p ≥ 2 * k)
        (Finset.Icc 1 ⌊X⌋₊)).card ≤ C * k)
    (X₀ : ℝ)
    (hbound : ∀ X : ℝ, X ≥ X₀ →
      (countNonRegularPrimes α X : ℝ) ≤
      C₁ + ∑ k ∈ Finset.Icc 1 (K_max α X),
        ((Finset.filter
          (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num ∧
                    p ≤ ⌊X⌋₊ ∧ M_alpha α p ≥ 2 * k)
          (Finset.Icc 1 ⌊X⌋₊)).card : ℝ)) :
    ∀ᶠ X in Filter.atTop,
      (countNonRegularPrimes α X : ℝ) ≤ C₁ + C * ((K_max α X : ℝ) + 1) ^ 2 := by
  rw [Filter.eventually_atTop]
  use X₀
  intro X hX
  have hstep1 := hbound X hX
  have hstep2 : (∑ k ∈ Finset.Icc 1 (K_max α X),
      ((Finset.filter
        (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num ∧
                  p ≤ ⌊X⌋₊ ∧ M_alpha α p ≥ 2 * k)
        (Finset.Icc 1 ⌊X⌋₊)).card : ℝ)) ≤
      ∑ k ∈ Finset.Icc 1 (K_max α X), C * (k : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    simp only [Finset.mem_Icc] at hk
    exact_mod_cast hCunif k hk.1 X
  have hstep3 : (∑ k ∈ Finset.Icc 1 (K_max α X), C * (k : ℝ)) ≤ C * ((K_max α X : ℝ) + 1) ^ 2 :=
    helper_sum_bound (K_max α X) C hC
  linarith

lemma count_isBigO_target (α : ℝ) (hα : 1/2 < α) :
    (fun X : ℝ => (countNonRegularPrimes α X : ℝ)) =O[Filter.atTop]
    (fun X : ℝ => X / (Real.log X) ^ (2 * α)) := by
  -- Get the uniform constant from prime_divisors_of_bernoulli_uniform_bound
  obtain ⟨C, hCpos, hCunif⟩ := prime_divisors_of_bernoulli_uniform_bound α hα
  -- Get the bound from count_bound_by_sum_over_k_eventually
  obtain ⟨C₁, X₀, hbound⟩ := count_bound_by_sum_over_k_eventually α hα
  -- The rest follows from the helper lemmas
  -- Get the eventual inequality
  have heventual := helper_count_eventually_bound α hα C C₁ hCpos hCunif X₀ hbound
  -- C₁ is O(target)
  have h1 : (fun _ : ℝ => C₁) =O[Filter.atTop] (fun X => X / (Real.log X) ^ (2 * α)) :=
    helper_const_isBigO α hα C₁
  -- C * (K_max + 1)² is O(target)
  have h2 : (fun X : ℝ => C * ((K_max α X : ℝ) + 1) ^ 2) =O[Filter.atTop]
            (fun X => X / (Real.log X) ^ (2 * α)) :=
    (helper_K_max_plus_one_sq_isBigO α hα).const_mul_left C
  -- C₁ + C * (K_max + 1)² is O(target)
  have h3 : (fun X : ℝ => C₁ + C * ((K_max α X : ℝ) + 1) ^ 2) =O[Filter.atTop]
            (fun X => X / (Real.log X) ^ (2 * α)) :=
    h1.add h2
  -- countNonRegularPrimes =O (C₁ + C * (K_max + 1)²) via the eventual bound
  have h4 : (fun X : ℝ => (countNonRegularPrimes α X : ℝ)) =O[Filter.atTop]
            (fun X : ℝ => C₁ + C * ((K_max α X : ℝ) + 1) ^ 2) := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [heventual] with X hX
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact hX
  -- Transitivity
  exact h4.trans h3


-- Main Statement
/-- For fixed `α > 1/2`, the number of primes `p ≤ X` that are not `M_α(p)`-regular is
    $O(X / (\log X)^{2α})$ as `X → +∞`. -/
theorem irregular_primes_asymptotic (α : ℝ) (hα : 1/2 < α) :
    (fun X : ℝ => (countNonRegularPrimes α X : ℝ)) =O[Filter.atTop]
    (fun X : ℝ => X / (Real.log X) ^ (2 * α)) := by
  exact count_isBigO_target α hα

end LeanPool.PartialRegularity
