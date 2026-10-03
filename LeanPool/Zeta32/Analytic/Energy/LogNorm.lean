/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! `∫₀^b log|u + ix| du` and the sum–integral comparison of the proof notes (5′).
-- adapted from Li2Unified/Modular/Base/LogNormIntegral.lean, LogNormMonotone.lean,
-- LogNormScaling.lean,
--   LogNormSumComparison.lean, LogNormSumError.lean (namespace changed only). -/

public section

open MeasureTheory Set
open scoped BigOperators

namespace Zeta32.Analytic.EnergyI
noncomputable section

/-- The explicit primitive; its value at zero is zero for every `x`. -/
def logNormIntegralPrimitive (x t : ℝ) : ℝ :=
  (t / 2) * Real.log (t ^ 2 + x ^ 2) - t +
    x * Real.arctan (t / x)

lemma log_norm_real_add_imag (t x : ℝ) :
    Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖ =
      (1 / 2 : ℝ) * Real.log (t ^ 2 + x ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_add_mul_I,
    Real.log_sqrt (add_nonneg (sq_nonneg t) (sq_nonneg x))]
  ring

lemma log_norm_real_add_imag_zero (t : ℝ) :
    Real.log ‖(t : ℂ) + (0 : ℂ) * Complex.I‖ = Real.log t := by
  simp [Complex.norm_real, Real.norm_eq_abs, Real.log_abs]

lemma real_add_imag_ne_zero {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (t : ℂ) + (x : ℂ) * Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  have hx0 : x = 0 := by simpa using hi
  exact hx.ne' hx0

lemma continuous_log_norm_real_add_imag {x : ℝ} (hx : 0 < x) :
    Continuous (fun t : ℝ =>
      Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) := by
  have hz : Continuous (fun t : ℝ =>
      (t : ℂ) + (x : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.add continuous_const
  exact hz.norm.log (fun t =>
    norm_ne_zero_iff.mpr (real_add_imag_ne_zero hx t))

lemma hasDerivAt_logNormIntegralPrimitive {x : ℝ}
    (hx : 0 < x) (t : ℝ) :
    HasDerivAt (logNormIntegralPrimitive x)
      (Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) t := by
  have hx0 : x ≠ 0 := hx.ne'
  have hQ : t ^ 2 + x ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg t) (pow_pos hx 2))
  have hquot : 1 + (t / x) ^ 2 = (t ^ 2 + x ^ 2) / x ^ 2 := by
    field_simp [hx0]; ring
  have hlog : HasDerivAt
      (fun s : ℝ => Real.log (s ^ 2 + x ^ 2))
      (2 * t / (t ^ 2 + x ^ 2)) t := by
    convert! (((hasDerivAt_id t).pow 2).add_const (x ^ 2)).log hQ using 1
    norm_num
  have hatan : HasDerivAt
      (fun s : ℝ => x * Real.arctan (s / x))
      (x ^ 2 / (t ^ 2 + x ^ 2)) t := by
    convert! (((hasDerivAt_id t).div_const x).arctan).const_mul x using 1
    dsimp only [id_eq]
    rw [hquot]
    field_simp [hx0, hQ]
  have h := ((((hasDerivAt_id t).div_const 2).mul hlog).sub
    (hasDerivAt_id t)).add hatan
  rw [log_norm_real_add_imag]
  convert! h using 1; dsimp [logNormIntegralPrimitive]; field_simp [hQ]; ring

lemma intervalIntegrable_log_norm_real_add_imag
    {x : ℝ} (hx : 0 ≤ x) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) volume a b := by
  by_cases hx0 : x = 0
  · subst x
    simpa only [Complex.ofReal_zero, log_norm_real_add_imag_zero] using
      (intervalIntegral.intervalIntegrable_log' (a := a) (b := b))
  · exact (continuous_log_norm_real_add_imag
      (lt_of_le_of_ne hx (Ne.symm hx0))).intervalIntegrable a b

lemma integral_log_norm_real_add_imag_of_pos
    {x : ℝ} (hx : 0 < x) (b : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..b,
      Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) =
      (b / 2) * Real.log (b ^ 2 + x ^ 2) - b +
        x * Real.arctan (b / x) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := b) (f := logNormIntegralPrimitive x)
    (f' := fun t : ℝ => Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖)
    (fun t _ => hasDerivAt_logNormIntegralPrimitive hx t)
    ((continuous_log_norm_real_add_imag hx).intervalIntegrable 0 b)
  simpa [logNormIntegralPrimitive] using h

/-- The integral from GLOBAL-INTEGRAL-v1, Section 2, with both boundary cases. -/
theorem integral_log_norm_real_add_imag
    {x b : ℝ} (hx : 0 ≤ x) :
    (∫ t : ℝ in (0 : ℝ)..b,
      Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) =
      (b / 2) * Real.log (b ^ 2 + x ^ 2) - b +
        x * Real.arctan (b / x) := by
  by_cases hb0 : b = 0
  · subst b
    simp
  by_cases hx0 : x = 0
  · subst x
    simp only [Complex.ofReal_zero, log_norm_real_add_imag_zero]
    rw [integral_log_from_zero]
    simp only [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, zero_mul]
    rw [Real.log_pow]
    ring
  · exact integral_log_norm_real_add_imag_of_pos
      (lt_of_le_of_ne hx (Ne.symm hx0)) b

/-- Integrability for every real imaginary parameter, including zero. -/
lemma intervalIntegrable_log_norm_real_add_imag_all
    (y a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖)
      volume a b := by
  simpa only [log_norm_real_add_imag, sq_abs] using
    (intervalIntegrable_log_norm_real_add_imag
      (x := |y|) (abs_nonneg y) a b)

/-- The positive real axis excludes the exceptional value `Real.log 0`. -/
lemma monotoneOn_log_norm_real_add_imag (y : ℝ) :
    MonotoneOn
      (fun t : ℝ => Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖)
      (Ioi 0) := by
  intro s hs t ht hst
  have hs0 : 0 < s := hs
  have ht0 : 0 < t := ht
  have hsquare : s ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hs0.le ht0.le).2 hst
  have hpositive : 0 < s ^ 2 + y ^ 2 :=
    add_pos_of_pos_of_nonneg (pow_pos hs0 2) (sq_nonneg y)
  simp only [log_norm_real_add_imag]
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log hpositive (by linarith only [hsquare]))
    (by norm_num)

/-- Pointwise lower and upper bounds needed for the endpoint integrals. -/
lemma log_norm_real_add_imag_bounds
    (y : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖ ∧
      Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖ ≤ Real.log (t + |y|) := by
  have ht2 : 0 < t ^ 2 := pow_pos ht 2
  have hsum : 0 < t ^ 2 + y ^ 2 :=
    add_pos_of_pos_of_nonneg ht2 (sq_nonneg y)
  have hupper : t ^ 2 + y ^ 2 ≤ (t + |y|) ^ 2 := by
    nlinarith [sq_abs y, mul_nonneg ht.le (abs_nonneg y)]
  have hlo := Real.log_le_log ht2 (le_add_of_nonneg_right (sq_nonneg y))
  have hup := Real.log_le_log hsum hupper
  norm_num only [Real.log_pow] at hlo hup
  simp only [log_norm_real_add_imag]
  constructor <;> linarith

theorem integral_log_norm_scale {c : ℝ} (hc : 0 < c) (b x : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..c * b,
      Real.log ‖(t : ℂ) + ((c * x : ℝ) : ℂ) * Complex.I‖) =
      c * b * Real.log c + c *
        (∫ t : ℝ in (0 : ℝ)..b,
          Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) := by
  have heq :
      (∫ t : ℝ in (0 : ℝ)..b,
        Real.log ‖((c * t : ℝ) : ℂ) + ((c * x : ℝ) : ℂ) * Complex.I‖) =
      ∫ t : ℝ in (0 : ℝ)..b,
        (Real.log c + Real.log ‖(t : ℂ) + (x : ℂ) * Complex.I‖) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(volume : Measure ℝ).ae_ne (0 : ℝ)] with t ht
    intro _
    have hn : (t : ℂ) + (x : ℂ) * Complex.I ≠ 0 := by
      intro h
      apply ht
      simpa using congrArg Complex.re h
    have hz : ((c * t : ℝ) : ℂ) + ((c * x : ℝ) : ℂ) * Complex.I =
        (c : ℂ) * ((t : ℂ) + (x : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hz, norm_mul, Complex.norm_of_nonneg hc.le,
      Real.log_mul hc.ne' (norm_ne_zero_iff.mpr hn)]
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ => Real.log ‖(t : ℂ) + ((c * x : ℝ) : ℂ) * Complex.I‖)
    (a := 0) (b := b) c
  simp only [mul_zero, smul_eq_mul, heq] at hs
  rw [← hs, intervalIntegral.integral_add
    (by simp) (intervalIntegrable_log_norm_real_add_imag_all x 0 b),
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- The shifted samples lie between the two integral bounds.
The first comparison uses only positive points inside each open unit cell. -/
theorem log_norm_sum_comparison (m : ℕ) (y : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..(m : ℝ),
      Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖) ≤
        (∑ i ∈ Finset.range m,
          Real.log ‖(((i : ℝ) + 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖) ∧
      (∑ i ∈ Finset.range m,
        Real.log ‖(((i : ℝ) + 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖) ≤
        (∫ t : ℝ in (3 / 2 : ℝ)..((m : ℝ) + 3 / 2),
          Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖) := by
  let g : ℝ → ℝ :=
    fun t => Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖
  have hint (a b : ℝ) : IntervalIntegrable g volume a b :=
    intervalIntegrable_log_norm_real_add_imag_all y a b
  have hmono : MonotoneOn g (Ioi 0) := monotoneOn_log_norm_real_add_imag y
  change
    (∫ t in (0 : ℝ)..(m : ℝ), g t) ≤
        (∑ i ∈ Finset.range m, g ((i : ℝ) + 3 / 2)) ∧
      (∑ i ∈ Finset.range m, g ((i : ℝ) + 3 / 2)) ≤
        (∫ t in (3 / 2 : ℝ)..((m : ℝ) + 3 / 2), g t)
  constructor
  · calc
      (∫ t in (0 : ℝ)..(m : ℝ), g t) =
          ∑ i ∈ Finset.range m,
            ∫ t in (i : ℝ)..((i + 1 : ℕ) : ℝ), g t := by
        simpa only [Nat.cast_zero] using
          (intervalIntegral.sum_integral_adjacent_intervals
            (f := g) (μ := volume)
            (a := fun i : ℕ => (i : ℝ)) (n := m)
            (fun i _ => hint (i : ℝ) ((i + 1 : ℕ) : ℝ))).symm
      _ ≤ ∑ i ∈ Finset.range m, g ((i : ℝ) + 3 / 2) := by
        apply Finset.sum_le_sum
        intro i _
        have hcell :
            (∫ t in (i : ℝ)..((i + 1 : ℕ) : ℝ), g t) ≤
              (∫ _ in (i : ℝ)..((i + 1 : ℕ) : ℝ), g ((i : ℝ) + 3 / 2)) := by
          refine intervalIntegral.integral_mono_on_of_le_Ioo
            (by exact_mod_cast Nat.le_succ i)
            (hint (i : ℝ) ((i + 1 : ℕ) : ℝ)) (by simp) ?_
          intro t ht
          have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
          have ht0 : 0 < t := lt_of_le_of_lt hi0 ht.1
          have hsample : 0 < (i : ℝ) + 3 / 2 := by positivity
          have htupper : t < (i : ℝ) + 1 := by
            simpa only [Nat.cast_add, Nat.cast_one] using ht.2
          exact hmono ht0 hsample (by linarith)
        have hlength : ((i + 1 : ℕ) : ℝ) - (i : ℝ) = 1 := by simp
        simpa only [intervalIntegral.integral_const, hlength, one_smul] using hcell
  · have hrestrict :
        MonotoneOn g (Icc (3 / 2 : ℝ) ((3 / 2 : ℝ) + (m : ℝ))) := by
      apply hmono.mono
      intro t ht
      change 0 < t
      linarith [ht.1]
    simpa only [add_comm] using
      (MonotoneOn.sum_le_integral (x₀ := (3 / 2 : ℝ)) (a := m) hrestrict)

theorem log_norm_sum_le_integral_add_error (m : ℕ) (y : ℝ) :
    (∑ i ∈ Finset.range m,
      Real.log ‖(((i : ℝ) + 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖) ≤
      (∫ t : ℝ in (0 : ℝ)..(m : ℝ),
        Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖) +
        (3 / 2 : ℝ) * Real.log ((m : ℝ) + 3 / 2 + |y|) + 3 / 2 := by
  let g : ℝ → ℝ :=
    fun t => Real.log ‖(t : ℂ) + (y : ℂ) * Complex.I‖
  have hint (a b : ℝ) : IntervalIntegrable g volume a b :=
    intervalIntegrable_log_norm_real_add_imag_all y a b
  have htail :
      (∫ t in (m : ℝ)..((m : ℝ) + 3 / 2), g t) ≤
        (3 / 2 : ℝ) * Real.log ((m : ℝ) + 3 / 2 + |y|) := by
    have hcompare :
        (∫ t in (m : ℝ)..((m : ℝ) + 3 / 2), g t) ≤
          (∫ _ in (m : ℝ)..((m : ℝ) + 3 / 2),
            Real.log ((m : ℝ) + 3 / 2 + |y|)) := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo
        (by linarith) (hint (m : ℝ) ((m : ℝ) + 3 / 2)) (by simp) ?_
      intro t ht
      have ht0 : 0 < t := lt_of_le_of_lt (Nat.cast_nonneg m) ht.1
      have htabs : 0 < t + |y| := by positivity
      exact (log_norm_real_add_imag_bounds y ht0).2.trans
        (Real.log_le_log htabs (by linarith only [ht.2]))
    have hlength : ((m : ℝ) + 3 / 2) - (m : ℝ) = (3 / 2 : ℝ) := by ring
    simpa only [intervalIntegral.integral_const, hlength, smul_eq_mul] using hcompare
  have hhead :
      -(3 / 2 : ℝ) ≤ (∫ t in (0 : ℝ)..(3 / 2 : ℝ), g t) := by
    have hcompare :
        (∫ t in (0 : ℝ)..(3 / 2 : ℝ), Real.log t) ≤
          (∫ t in (0 : ℝ)..(3 / 2 : ℝ), g t) := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo
        (by norm_num)
        (intervalIntegral.intervalIntegrable_log'
          (a := (0 : ℝ)) (b := (3 / 2 : ℝ))) (hint 0 (3 / 2)) ?_
      intro t ht
      exact (log_norm_real_add_imag_bounds y ht.1).1
    rw [integral_log_from_zero] at hcompare
    have hlog : 0 ≤ Real.log (3 / 2 : ℝ) := Real.log_nonneg (by norm_num)
    linarith only [hcompare, hlog]
  have hsplit_m := intervalIntegral.integral_add_adjacent_intervals
      (hint 0 (m : ℝ)) (hint (m : ℝ) ((m : ℝ) + 3 / 2))
  have hsplit_head := intervalIntegral.integral_add_adjacent_intervals
      (hint 0 (3 / 2)) (hint (3 / 2) ((m : ℝ) + 3 / 2))
  have hsum :
      (∑ i ∈ Finset.range m, g ((i : ℝ) + 3 / 2)) ≤
        (∫ t in (3 / 2 : ℝ)..((m : ℝ) + 3 / 2), g t) :=
    (log_norm_sum_comparison m y).2
  change
    (∑ i ∈ Finset.range m, g ((i : ℝ) + 3 / 2)) ≤
      (∫ t in (0 : ℝ)..(m : ℝ), g t) +
        (3 / 2 : ℝ) * Real.log ((m : ℝ) + 3 / 2 + |y|) + 3 / 2
  linarith only [hsum, htail, hhead, hsplit_m, hsplit_head]

end
end Zeta32.Analytic.EnergyI

end
