/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Pochhammer.BinomialSeries
public import LeanPool.CarlsonFunctions.Pochhammer.Identities
public import LeanPool.CarlsonFunctions.Pochhammer.Vandermonde
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# The double series in Carlson's second quadratic transformation

The coefficient convolution is Carlson's calculation in Section 6.10, pp. 165–166.
Absolute convergence justifies grouping the double series by total degree. A coarse geometric
majorant suffices for the local identity, which is subsequently extended by analyticity.
-/

open Complex
open scoped Classical
@[expose] public noncomputable section
namespace DirichletTransform.TwoVariable

/-- Coefficient of the double series before grouping terms of equal total degree. -/
def quadraticSeriesCoeff (a c : ℂ) (m k : ℕ) : ℂ :=
  (ascPochhammer ℂ (2 * m + k)).eval a /
    ((ascPochhammer ℂ m).eval c * (m.factorial : ℂ) * k.factorial) * (-1) ^ k

private lemma pochhammer_ne_zero {c : ℂ} (hc : 0 < c.re) (n : ℕ) :
    (ascPochhammer ℂ n).eval c ≠ 0 := by
  rw [Ne, ascPochhammer_eval_eq_zero_iff]
  rintro ⟨k, _, hk⟩
  have h := congrArg Complex.re hk
  simp only [natCast_re, neg_re] at h
  linarith

/-- The finite convolution that collapses Carlson's double series. -/
theorem sum_antidiagonal_quadraticSeriesCoeff (a c : ℂ) (hc : 0 < c.re) (n : ℕ) :
    ∑ mk ∈ Finset.antidiagonal n, quadraticSeriesCoeff a c mk.1 mk.2 =
      (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval (a + 1 - c) /
        ((ascPochhammer ℂ n).eval c * n.factorial) := by
  have hterm (m k : ℕ) (hmk : m + k = n) :
      quadraticSeriesCoeff a c m k =
        (ascPochhammer ℂ n).eval a / ((ascPochhammer ℂ n).eval c * n.factorial) *
          ((n.choose m : ℂ) * ((ascPochhammer ℂ m).eval (a + n) *
            (ascPochhammer ℂ k).eval (1 - c - n))) := by
    have ha : (ascPochhammer ℂ (2 * m + k)).eval a =
        (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ m).eval (a + n) := by
      rw [show 2 * m + k = n + m by omega, ascPochhammer_add_eval]
    have hcm := ascPochhammer_add_eval c m k
    rw [hmk] at hcm
    have hreflect : (ascPochhammer ℂ k).eval (1 - c - n) =
        (-1 : ℂ) ^ k * (ascPochhammer ℂ k).eval (c + m) := by
      rw [show (1 : ℂ) - c - n = 1 - (c + m) - k by rw [← hmk]; push_cast; ring,
        ascPochhammer_eval_reflect]
    have hfac : (n.choose m : ℂ) * (m.factorial : ℂ) * k.factorial = n.factorial := by
      exact_mod_cast (by simpa [← hmk] using
        (Nat.choose_mul_factorial_mul_factorial (show m ≤ n by omega)))
    dsimp [quadraticSeriesCoeff]
    rw [ha, hreflect]
    have hfactorial (l : ℕ) : (l.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l
    have hchoose : (n.choose m : ℂ) = n.factorial / ((m.factorial : ℂ) * k.factorial) := by
      apply (eq_div_iff (mul_ne_zero (hfactorial m) (hfactorial k))).mpr
      simpa only [mul_assoc] using hfac
    rw [hchoose]
    field_simp [pochhammer_ne_zero hc m, pochhammer_ne_zero hc n, hfactorial]
    rw [hcm]
    ring
  simp_rw [Finset.sum_congr rfl (fun mk hmk => hterm mk.1 mk.2 (Finset.mem_antidiagonal.mp hmk))]
  rw [← Finset.mul_sum, ← ascPochhammer_eval_add]
  rw [show a + (n : ℂ) + (1 - c - n) = a + 1 - c by ring]
  ring

/-- A geometric bound for binomial coefficients, uniform in the degree. -/
private lemma norm_pochhammer_le_factorial_mul_pow (a : ℂ) (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval a‖ ≤ (n.factorial : ℝ) * (‖a‖ + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, norm_mul]
    have h : ‖a + (n : ℂ)‖ ≤ (n + 1) * (‖a‖ + 1) := by
      have h₀ := norm_add_le a (n : ℂ)
      simp only [norm_natCast] at h₀
      nlinarith [norm_nonneg a, Nat.cast_nonneg (α := ℝ) n]
    calc
      _ ≤ ((n.factorial : ℝ) * (‖a‖ + 1) ^ n) * ((n + 1) * (‖a‖ + 1)) :=
        mul_le_mul ih h (norm_nonneg _) (by positivity)
      _ = _ := by rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]; ring

/-- The half-integer Pochhammer factors are a lower bound for the denominator. -/
private lemma norm_half_pochhammer_le {c : ℂ} (hc : 1 / 2 ≤ c.re) (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval (1 / 2)‖ ≤ ‖(ascPochhammer ℂ n).eval c‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [ascPochhammer_succ_eval, norm_mul]
    apply mul_le_mul ih _ (norm_nonneg _) (norm_nonneg _)
    calc
      ‖(1 / 2 : ℂ) + n‖ = 1 / 2 + (n : ℝ) := by
        rw [show (1 / 2 : ℂ) + n = ((1 / 2 + (n : ℝ) : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ (c + n).re := by simp only [add_re, natCast_re]; linarith
      _ ≤ ‖c + n‖ := re_le_norm _

private lemma quadraticSeriesCoeff_eq_binomial (a c : ℂ) (hc : 0 < c.re) (m k : ℕ) :
    quadraticSeriesCoeff a c m k =
      ((ascPochhammer ℂ (2 * m + k)).eval a / ((2 * m + k).factorial : ℂ)) *
        ((2 * m + k).choose k : ℂ) * 4 ^ m *
        ((ascPochhammer ℂ m).eval (1 / 2) / (ascPochhammer ℂ m).eval c) * (-1) ^ k := by
  have hfac : ((2 * m + k).choose k : ℂ) * ((2 * m).factorial : ℂ) * k.factorial =
      (2 * m + k).factorial := by exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial (2 * m) k
  have hdouble : ((2 * m).factorial : ℂ) =
      4 ^ m * (ascPochhammer ℂ m).eval (1 / 2) * (m.factorial : ℂ) := by
    have H := ascPochhammer_eval_double (1 / 2 : ℂ) m
    norm_num [ascPochhammer_eval_one] at H ⊢
    exact H
  have hfactorial (l : ℕ) : (l.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l
  dsimp [quadraticSeriesCoeff]
  field_simp [pochhammer_ne_zero hc m, hfactorial]
  rw [hdouble] at hfac
  linear_combination -(ascPochhammer ℂ (2 * m + k)).eval a * hfac

/-- A coarse geometric majorant is sufficient, since the transformation is first proved
in an arbitrarily small neighborhood of equal nodes. -/
theorem norm_quadraticSeriesCoeff_le (a c : ℂ) (hc : 1 / 2 ≤ c.re) (m k : ℕ) :
    ‖quadraticSeriesCoeff a c m k‖ ≤ (4 * (‖a‖ + 1)) ^ (2 * m + k) := by
  have hcpos : 0 < c.re := by linarith
  have ha : ‖(ascPochhammer ℂ (2 * m + k)).eval a / ((2 * m + k).factorial : ℂ)‖ ≤
      (‖a‖ + 1) ^ (2 * m + k) := by
    rw [norm_div, norm_natCast, div_le_iff₀ (by positivity)]
    simpa [mul_comm] using norm_pochhammer_le_factorial_mul_pow a (2 * m + k)
  have hb : ‖(ascPochhammer ℂ m).eval (1 / 2) / (ascPochhammer ℂ m).eval c‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr (pochhammer_ne_zero hcpos m))]
    exact norm_half_pochhammer_le hc m
  have hchoose : (((2 * m + k).choose k : ℕ) : ℝ) ≤ 2 ^ (2 * m + k) := by
    exact_mod_cast Nat.choose_le_two_pow (2 * m + k) k
  have hfour : (4 : ℝ) ^ m ≤ 2 ^ (2 * m + k) := by
    calc
      _ = (2 : ℝ) ^ (2 * m) := by rw [pow_mul]; norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [quadraticSeriesCoeff_eq_binomial a c hcpos]
  simp only [norm_mul, norm_pow, norm_natCast, norm_ofNat, norm_neg, norm_one, one_pow, mul_one]
  calc
    _ ≤ (‖a‖ + 1) ^ (2 * m + k) * 2 ^ (2 * m + k) * 2 ^ (2 * m + k) * 1 := by
      gcongr
    _ = _ := by simp only [mul_one, ← mul_pow]; congr 1; ring

/-- Absolute convergence on a small disk, sufficient for analytic continuation. -/
theorem summable_norm_quadraticSeries (a c w : ℂ) (hc : 1 / 2 ≤ c.re)
    (hw : 4 * (‖a‖ + 1) * ‖w‖ < 1 / 2) :
    Summable fun mk : ℕ × ℕ =>
      ‖quadraticSeriesCoeff a c mk.1 mk.2 * w ^ (2 * (mk.1 + mk.2))‖ := by
  let B := 4 * (‖a‖ + 1)
  have hB : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg a]
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hsmall : B ^ 2 * ‖w‖ ^ 2 < 1 := by
    have h := pow_lt_one₀ (mul_nonneg hB0 (norm_nonneg w))
      (lt_trans hw (by norm_num : (1 / 2 : ℝ) < 1)) (by decide : 2 ≠ 0)
    simpa only [mul_pow] using h
  have hsmall' : B * ‖w‖ ^ 2 < 1 := by
    have hle : B * ‖w‖ ^ 2 ≤ B ^ 2 * ‖w‖ ^ 2 := by gcongr; nlinarith
    exact hle.trans_lt hsmall
  have hsum := (summable_geometric_of_lt_one (by positivity) hsmall).mul_of_nonneg
    (summable_geometric_of_lt_one (by positivity) hsmall')
    (fun _ => by positivity) (fun _ => by positivity)
  apply hsum.of_nonneg_of_le (fun _ => norm_nonneg _)
  rintro ⟨m, k⟩
  rw [norm_mul, norm_pow]
  calc
    _ ≤ B ^ (2 * m + k) * ‖w‖ ^ (2 * (m + k)) := by
      gcongr
      exact norm_quadraticSeriesCoeff_le a c hc m k
    _ = (B ^ 2 * ‖w‖ ^ 2) ^ m * (B * ‖w‖ ^ 2) ^ k := by
      simp only [pow_add, pow_mul, mul_pow]
      ring

/-- Regroup the absolutely convergent double series by its total degree. -/
theorem tsum_quadraticSeries_eq (a c w : ℂ) (hc : 1 / 2 ≤ c.re)
    (hw : 4 * (‖a‖ + 1) * ‖w‖ < 1 / 2) :
    (∑' m, ∑' k, quadraticSeriesCoeff a c m k * w ^ (2 * (m + k))) =
      ∑' n, ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval (a + 1 - c) /
        ((ascPochhammer ℂ n).eval c * n.factorial)) * w ^ (2 * n) := by
  let f : ℕ × ℕ → ℂ := fun mk => quadraticSeriesCoeff a c mk.1 mk.2 * w ^ (2 * (mk.1 + mk.2))
  have hf : Summable f := (summable_norm_quadraticSeries a c w hc hw).of_norm
  have hs : Summable (fun p : Σ n : ℕ, Finset.antidiagonal n => f p.2.1) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hf
  calc
    _ = ∑' p, f p := (hf.tsum_prod' (fun m => hf.prod_factor m)).symm
    _ = ∑' p : Σ n : ℕ, Finset.antidiagonal n, f p.2.1 :=
      (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq f).symm
    _ = ∑' n, ∑ mk ∈ Finset.antidiagonal n, f mk := by
      rw [hs.tsum_sigma']
      · congr 1
        ext n
        rw [tsum_fintype]
        change (∑ b : Finset.antidiagonal n, f b.1) = _
        exact Finset.sum_finset_coe _ _
      · intro n
        exact (hasSum_fintype _).summable
    _ = _ := by
      apply tsum_congr
      intro n
      rw [Finset.sum_congr rfl (show ∀ mk ∈ Finset.antidiagonal n, f mk =
          quadraticSeriesCoeff a c mk.1 mk.2 * w ^ (2 * n) from
        fun mk hmk => by dsimp [f]; rw [Finset.mem_antidiagonal.mp hmk])]
      rw [← Finset.sum_mul, sum_antidiagonal_quadraticSeriesCoeff a c (by linarith)]

/-- Summing a row is the ordinary binomial series used on p. 165. -/
theorem hasSum_quadraticSeries_row (a c w : ℂ) (m : ℕ) (hw : ‖w‖ < 1) :
    HasSum (fun k => quadraticSeriesCoeff a c m k * w ^ (2 * (m + k)))
      (((ascPochhammer ℂ (2 * m)).eval a /
        ((ascPochhammer ℂ m).eval c * m.factorial)) * w ^ (2 * m) /
          (1 + w ^ 2) ^ (a + (2 * m : ℕ))) := by
  have hw' : ‖-(w ^ 2)‖ < 1 := by
    rw [norm_neg, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hw (by decide)
  have H := (hasSum_ascPochhammer_mul_pow_div_factorial (a + (2 * m : ℕ))
    (-(w ^ 2)) hw').mul_left
      (((ascPochhammer ℂ (2 * m)).eval a /
        ((ascPochhammer ℂ m).eval c * m.factorial)) * w ^ (2 * m))
  convert! H using 1
  · ext k
    rw [quadraticSeriesCoeff, ascPochhammer_add_eval]
    rw [show w ^ (2 * (m + k)) = w ^ (2 * m) * w ^ (2 * k) by rw [Nat.mul_add, pow_add]]
    rw [show (-(w ^ 2)) ^ k = (-1 : ℂ) ^ k * w ^ (2 * k) by rw [neg_pow, pow_mul]]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · simp only [sub_neg_eq_add, div_eq_mul_inv, one_mul]

end DirichletTransform.TwoVariable
end
