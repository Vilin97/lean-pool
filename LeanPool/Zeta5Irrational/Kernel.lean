/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.ZeroMass
import LeanPool.Zeta5Irrational.Gaussian
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The truncated logarithmic kernel `L_{a,b}` and its limit `log r`

* `Ltr_eq_v` : `L_{a,b}(r) = (1/2) ∫_1^{r²} (e^{-av} - e^{-bv})/v dv` for `r > 0`;
* `abs_Ltr_le` : `|L_{a,b}(r)| ≤ |log r|`;
* `continuous_Ltr` : continuity in `r`;
* `tendsto_Ltr` : `L_{1/(n+1), n+1}(r) → log r`.
-/

public section

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace Zeta5Irrational

lemma integral_exp_neg_mul' {k : ℝ} (hk : k ≠ 0) (c d : ℝ) :
    ∫ x in c..d, Real.exp (-k * x) = (Real.exp (-k * c) - Real.exp (-k * d)) / k := by
  have h : ∀ x ∈ uIcc c d, HasDerivAt (fun x => -Real.exp (-k * x) / k) (Real.exp (-k * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -k * x) (-k) x := by
      simpa using (hasDerivAt_id x).const_mul (-k)
    have h2 := (h1.exp.neg).div_const k
    refine
      HasDerivAt.congr_deriv
        (HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun _ => rfl)) ?_
    field_simp
  rw [integral_eq_sub_of_hasDerivAt h (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

/-- Fubini for interval integrals of continuous functions, arbitrary orientation. -/
lemma intervalIntegral_swap_of_continuous' {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f))
    (a b c d : ℝ) : ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
  · exact intervalIntegral_swap_of_continuous hf hab hcd
  · rw [integral_symm d c]
    simp_rw [integral_symm d c, intervalIntegral.integral_neg]
    rw [intervalIntegral_swap_of_continuous hf hab hcd]
  · rw [integral_symm b a]
    simp_rw [integral_symm b a]
    rw [intervalIntegral.integral_neg, intervalIntegral_swap_of_continuous hf hab hcd]
  · rw [integral_symm b a, integral_symm d c]
    simp_rw [integral_symm b a, integral_symm d c, intervalIntegral.integral_neg]
    rw [intervalIntegral_swap_of_continuous hf hab hcd]

/-- The substituted form of the truncated kernel. -/
lemma Ltr_eq_v {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    Ltr a b r = (1 / 2) * ∫ v in (1 : ℝ)..r ^ 2, (Real.exp (-a * v) - Real.exp (-b * v)) / v := by
  unfold Ltr
  congr 1
  have e1 :
    ∀ s ∈ uIcc a b,
      (Real.exp (-s) - Real.exp (-s * r ^ 2)) / s = ∫ v in (1 : ℝ)..r ^ 2, Real.exp (-s * v) := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    rw [integral_exp_neg_mul' (ha.trans_le hs.1).ne', mul_one]
  rw [integral_congr e1]
  rw [intervalIntegral_swap_of_continuous' (f := fun s v => Real.exp (-s * v)) (by fun_prop)]
  apply integral_congr
  intro v hv
  have hv0 : 0 < v := by
    rcases le_total 1 (r ^ 2) with h | h
    · rw [uIcc_of_le h] at hv; linarith [hv.1]
    · rw [uIcc_of_ge h] at hv; exact lt_of_lt_of_le (by positivity) hv.1
  simp only
  simp_rw [show ∀ s : ℝ, -s * v = -v * s from fun s => by ring]
  rw [integral_exp_neg_mul' hv0.ne']

lemma Ltr_integrand_bounds {a b v : ℝ} (ha : 0 < a) (hab : a ≤ b) (hv : 0 < v) :
    0 ≤ (Real.exp (-a * v) - Real.exp (-b * v)) / v ∧
      (Real.exp (-a * v) - Real.exp (-b * v)) / v ≤ 1 / v := by
  constructor
  · apply div_nonneg _ hv.le
    rw [sub_nonneg]
    apply Real.exp_le_exp.mpr
    nlinarith
  · apply div_le_div_of_nonneg_right _ hv.le
    have := Real.exp_pos (-b * v)
    have := Real.exp_le_one_iff.mpr (show -a * v ≤ 0 by nlinarith)
    linarith

lemma continuous_Ltr_integrand {a b : ℝ} (_ha : 0 < a) :
    Continuous fun v => (Real.exp (-a * v) - Real.exp (-b * v)) * (max v 1)⁻¹ := by
  have : Continuous fun v : ℝ => (max v 1)⁻¹ :=
    (continuous_id.max continuous_const).inv₀ fun v => (lt_max_of_lt_right one_pos).ne'
  fun_prop

lemma intervalIntegrable_of_pos {F : ℝ → ℝ} (hF : Continuous F) {c d : ℝ} (hc : 0 < c)
    (hd : 0 < d) : IntervalIntegrable (fun v => F v / v) volume c d := by
  apply ContinuousOn.intervalIntegrable
  refine hF.continuousOn.div continuousOn_id fun v hv => ?_
  rcases le_total c d with h | h
  · rw [uIcc_of_le h] at hv; exact (hc.trans_le hv.1).ne'
  · rw [uIcc_of_ge h] at hv; exact (hd.trans_le hv.1).ne'

lemma log_eq_half_integral {r : ℝ} (hr : 0 < r) :
    Real.log r = (1 / 2) * ∫ v in (1 : ℝ)..r ^ 2, 1 / v := by
  rw [integral_one_div_of_pos one_pos (by positivity), div_one, Real.log_pow]
  push_cast; ring

/-- `|L_{a,b}(r)| ≤ |log r|` for `r > 0`. -/
lemma abs_Ltr_le {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    |Ltr a b r| ≤ |Real.log r| := by
  rw [Ltr_eq_v ha hab hr]
  have hlog := log_eq_half_integral hr
  have hF :
    ∀ c d : ℝ,
      0 < c →
        0 < d →
          IntervalIntegrable (fun v => (Real.exp (-a * v) - Real.exp (-b * v)) / v) volume c d :=
    fun c d hc hd => intervalIntegrable_of_pos (by fun_prop) hc hd
  have hG : ∀ c d : ℝ, 0 < c → 0 < d → IntervalIntegrable (fun v : ℝ => 1 / v) volume c d :=
    fun c d hc hd => intervalIntegrable_of_pos continuous_const hc hd
  have hr2 : 0 < r ^ 2 := by positivity
  rcases le_total 1 (r ^ 2) with h | h
  · have h1 : 0 ≤ ∫ v in (1 : ℝ)..r ^ 2, (Real.exp (-a * v) - Real.exp (-b * v)) / v :=
      integral_nonneg h fun v hv => (Ltr_integrand_bounds ha hab (by linarith [hv.1])).1
    have h2 :
      (∫ v in (1 : ℝ)..r ^ 2, (Real.exp (-a * v) - Real.exp (-b * v)) / v) ≤
        ∫ v in (1 : ℝ)..r ^ 2, 1 / v :=
      integral_mono_on h (hF _ _ one_pos hr2) (hG _ _ one_pos hr2) fun v hv =>
        (Ltr_integrand_bounds ha hab (by linarith [hv.1])).2
    have hr1 : 0 ≤ Real.log r := Real.log_nonneg (by nlinarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg hr1, hlog]
    linarith
  · rw [integral_symm (r ^ 2) 1]
    rw [integral_symm (r ^ 2) 1] at hlog
    have h1 : 0 ≤ ∫ v in r ^ 2..(1 : ℝ), (Real.exp (-a * v) - Real.exp (-b * v)) / v :=
      integral_nonneg h fun v hv => (Ltr_integrand_bounds ha hab (by linarith [hv.1])).1
    have h2 :
      (∫ v in r ^ 2..(1 : ℝ), (Real.exp (-a * v) - Real.exp (-b * v)) / v) ≤
        ∫ v in r ^ 2..(1 : ℝ), 1 / v :=
      integral_mono_on h (hF _ _ hr2 one_pos) (hG _ _ hr2 one_pos) fun v hv =>
        (Ltr_integrand_bounds ha hab (by linarith [hv.1])).2
    have hr1 : Real.log r ≤ 0 := Real.log_nonpos hr.le (by nlinarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos hr1, hlog]
    linarith

/-- Continuity of the truncated kernel in `r`. -/
lemma continuous_Ltr {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : Continuous fun r => Ltr a b r := by
  simp_rw [Ltr_eq_max ha hab]
  have hinv := continuous_inv_max ha
  refine
    continuous_const.mul
      (continuous_parametric_intervalIntegral_of_continuous' (f := fun r s =>
        (Real.exp (-s) - Real.exp (-s * r ^ 2)) * (max s a)⁻¹) ?_ a b)
  have h1 : Continuous fun p : ℝ × ℝ => Real.exp (-p.2) - Real.exp (-p.2 * p.1 ^ 2) := by fun_prop
  exact h1.mul (hinv.comp continuous_snd)

/-- The difference `log r - L_{a,b}(r)` as an integral. -/
lemma log_sub_Ltr {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    Real.log r - Ltr a b r =
      (1 / 2) * ∫ v in (1 : ℝ)..r ^ 2, (1 - Real.exp (-a * v) + Real.exp (-b * v)) / v := by
  rw [Ltr_eq_v ha hab hr, log_eq_half_integral hr, ← mul_sub, ←
    integral_sub (intervalIntegrable_of_pos continuous_const one_pos (by positivity))
      (intervalIntegrable_of_pos (by fun_prop) one_pos (by positivity))]
  congr 1
  apply integral_congr
  intro v _
  simp only
  ring

lemma diff_integrand_bounds {a b m v : ℝ} (ha : 0 < a) (hab : a ≤ b) (hm : 0 < m) (hv : m ≤ v) :
    0 ≤ (1 - Real.exp (-a * v) + Real.exp (-b * v)) / v ∧
      (1 - Real.exp (-a * v) + Real.exp (-b * v)) / v ≤ a + Real.exp (-b * m) / m := by
  have hv0 : 0 < v := hm.trans_le hv
  have h1 : Real.exp (-a * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h2 : 0 < Real.exp (-b * v) := Real.exp_pos _
  have h3 : 1 - a * v ≤ Real.exp (-a * v) := by have := Real.add_one_le_exp (-a * v); linarith
  have h4 : Real.exp (-b * v) ≤ Real.exp (-b * m) := Real.exp_le_exp.mpr (by nlinarith)
  constructor
  · apply div_nonneg _ hv0.le; linarith
  · rw [div_le_iff₀ hv0]
    have h5 : Real.exp (-b * m) / m * v ≥ Real.exp (-b * m) := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hm]
      exact mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
    nlinarith

/-- `|log r - L_{a,b}(r)| ≤ (1/2) |r² - 1| (a + e^{-b m}/m)` with `m = min 1 r²`. -/
lemma abs_log_sub_Ltr_le {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    |Real.log r - Ltr a b r| ≤
      (1 / 2) * ((a + Real.exp (-b * min 1 (r ^ 2)) / min 1 (r ^ 2)) * |r ^ 2 - 1|) := by
  rw [log_sub_Ltr ha hab hr, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hm : 0 < min 1 (r ^ 2) := lt_min one_pos (by positivity)
  have :=
    norm_integral_le_of_norm_le_const (a := 1) (b := r ^ 2) (C :=
      a + Real.exp (-b * min 1 (r ^ 2)) / min 1 (r ^ 2)) (f := fun v =>
      (1 - Real.exp (-a * v) + Real.exp (-b * v)) / v)
      (fun v hv =>
        by
        have hv' : min 1 (r ^ 2) ≤ v := by
          rcases le_total 1 (r ^ 2) with h | h
          · rw [uIoc_of_le h] at hv; exact (min_le_left _ _).trans hv.1.le
          · rw [uIoc_of_ge h] at hv; exact (min_le_right _ _).trans hv.1.le
        rw [Real.norm_eq_abs, abs_of_nonneg (diff_integrand_bounds ha hab hm hv').1]
        exact (diff_integrand_bounds ha hab hm hv').2)
  rwa [Real.norm_eq_abs] at this

/-- Convergence of the truncated kernel to the logarithm. -/
lemma tendsto_Ltr {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => Ltr (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) r) atTop (𝓝 (Real.log r)) := by
  have hm : 0 < min 1 (r ^ 2) := lt_min one_pos (by positivity)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound :
    ∀ n : ℕ,
      ‖Ltr (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) r - Real.log r‖ ≤
        (1 / 2) *
          ((1 / ((n : ℝ) + 1) + Real.exp (-((n : ℝ) + 1) * min 1 (r ^ 2)) / min 1 (r ^ 2)) *
            |r ^ 2 - 1|) := by
    intro n
    rw [Real.norm_eq_abs, abs_sub_comm]
    refine abs_log_sub_Ltr_le (by positivity) ?_ hr
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 :
    Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) + 1) * min 1 (r ^ 2)) / min 1 (r ^ 2)) atTop
      (𝓝 0) := by
    have h3 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * min 1 (r ^ 2)) atTop atTop := by
      apply Tendsto.atTop_mul_const hm
      exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have := (tendsto_exp_neg_atTop_nhds_zero.comp h3).div_const (min 1 (r ^ 2))
    rw [zero_div] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    ring_nf
  have := ((h1.add h2).mul_const |r ^ 2 - 1|).const_mul (1 / 2)
  simpa using this

end Zeta5Irrational
