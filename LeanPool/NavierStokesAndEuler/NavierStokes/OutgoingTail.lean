/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingSchedule
import LeanPool.NavierStokesAndEuler.NavierStokes.FlatPrimitive
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Constructed flattening, release, and terminal power tail

This file extends the actual outgoing core.  The angular/pressure-neutral
moment edit is deliberately a separate operation: its required release datum
is used to initialize an explicitly solved scalar ODE, but is not asserted
to be the unedited angular history.
-/

@[expose] public section


noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff
open NavierStokes.OutgoingSchedule

namespace NavierStokes.OutgoingTail

/-! ## A proved, fixed bound on the actual step derivative -/

theorem edge_derivative_nonneg (x : ℝ) :
    0 ≤ 2 * FlatCutoff.edge 1 x / x ^ 3 := by
  by_cases hx : 0 < x
  · exact div_nonneg (mul_nonneg (by norm_num) (FlatCutoff.edge_nonneg 1 x))
      (pow_nonneg hx.le 3)
  · simp [FlatCutoff.edge_of_nonpos 1 (le_of_not_gt hx)]

theorem sigma_derivative_nonneg (x : ℝ) : 0 ≤ deriv sigma x := by
  have ha := FlatPrimitive.edge_hasDerivAt (by norm_num : (0 : ℝ) < 1) x
  have hb : HasDerivAt (fun y : ℝ => FlatCutoff.edge 1 (1 - y))
      (-(2 * FlatCutoff.edge 1 (1 - x) / (1 - x) ^ 3)) x := by
    convert! (FlatPrimitive.edge_hasDerivAt (by norm_num : (0 : ℝ) < 1) (1 - x)).comp x
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) using 1; ring
  have hq := ha.div (ha.fun_add hb) (sigma_denom_pos x).ne'
  change HasDerivAt sigma _ x at hq
  rw [hq.deriv]
  apply div_nonneg
  · nlinarith [mul_nonneg (edge_derivative_nonneg x) (FlatCutoff.edge_nonneg 1 (1 - x)),
      mul_nonneg (FlatCutoff.edge_nonneg 1 x) (edge_derivative_nonneg (1 - x))]
  · positivity

theorem sigma_derivative_zero_left {x : ℝ} (hx : x < 0) : deriv sigma x = 0 := by
  have he : sigma =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
    filter_upwards [gt_mem_nhds hx] with y hy
    exact sigma_zero hy.le
  rw [he.deriv_eq]
  simp

theorem sigma_derivative_zero_right {x : ℝ} (hx : 1 < x) : deriv sigma x = 0 := by
  have he : sigma =ᶠ[𝓝 x] (fun _ : ℝ => 1) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    exact sigma_one hy.le
  rw [he.deriv_eq]
  simp

theorem exists_sigma_derivative_bound :
    ∃ S : ℝ, 1 ≤ S ∧ ∀ x : ℝ, deriv sigma x ≤ S := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (sigma_contDiff.continuous_deriv (by simp)).continuousOn
  refine ⟨max C 1, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact (le_abs_self _).trans ((by simpa using hC x hx : |deriv sigma x| ≤ C).trans
      (le_max_left _ _))
  · have hx' : x < 0 ∨ 1 < x := by simpa only [mem_Icc, not_and_or, not_le] using hx
    rcases hx' with hx' | hx'
    · rw [sigma_derivative_zero_left hx']
      exact (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
    · rw [sigma_derivative_zero_right hx']
      exact (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)

/-- Step bound, given by `Classical.choose exists_sigma_derivative_bound`. -/
def stepBound : ℝ := Classical.choose exists_sigma_derivative_bound

theorem stepBound_ge_one : 1 ≤ stepBound :=
  (Classical.choose_spec exists_sigma_derivative_bound).1

theorem sigma_derivative_le (x : ℝ) : deriv sigma x ≤ stepBound :=
  (Classical.choose_spec exists_sigma_derivative_bound).2 x

/-- Flatten length, given by `10 * (stepBound + 1) * Real.log 2 + 1`. -/
def flattenLength : ℝ := 10 * (stepBound + 1) * Real.log 2 + 1

theorem flattenLength_pos : 0 < flattenLength := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold flattenLength
  nlinarith [stepBound_ge_one]

/-- Tail coefficient, given by `Real.exp (-5) / (16 * (stepBound + 1))`. -/
def tailCoefficient : ℝ := Real.exp (-5) / (16 * (stepBound + 1))

theorem tailCoefficient_pos : 0 < tailCoefficient := by
  apply div_pos (Real.exp_pos _)
  nlinarith [stepBound_ge_one]

theorem tailCoefficient_le : tailCoefficient ≤ Real.exp (-5) / 16 := by
  unfold tailCoefficient
  apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num)
  nlinarith [stepBound_ge_one]

theorem tailCoefficient_lt_one : tailCoefficient < 1 := by
  have he : Real.exp (-5 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  linarith [tailCoefficient_le]

/-- Tail data, collecting `core`, `h`, `h_pos`, `h_small`. -/
structure TailData where
  /-- Core of `TailData`, of type `OutgoingSchedule.Parameters`. -/
  core : OutgoingSchedule.Parameters
  /-- Step-size parameter of `TailData`, of type `ℝ`. -/
  h : ℝ
  h_pos : 0 < h
  h_small : 2 * h < core.lam

namespace TailData

theorem h_lt_half (d : TailData) : d.h < 1 / 2 := by
  linarith [d.h_small, d.core.lam_lt]

theorem h_lt_lam (d : TailData) : d.h < d.core.lam := by
  linarith [d.h_small, d.h_pos]

theorem one_sub_h_pos (d : TailData) : 0 < 1 - d.h := by
  linarith [d.h_lt_half]

/-- Flatten end, given by `d.core.endpoint + flattenLength`. -/
def flattenEnd (d : TailData) : ℝ := d.core.endpoint + flattenLength
/-- Uniform wait, given by `30 * Real.log (1 / d.core.lam)`. -/
def uniformWait (d : TailData) : ℝ := 30 * Real.log (1 / d.core.lam)
/-- Release start, given by `d.flattenEnd + d.uniformWait`. -/
def releaseStart (d : TailData) : ℝ := d.flattenEnd + d.uniformWait

theorem uniformWait_pos (d : TailData) : 0 < d.uniformWait := by
  unfold uniformWait
  apply mul_pos (by norm_num)
  apply Real.log_pos
  apply (lt_div_iff₀ d.core.lam_pos).mpr
  linarith [d.core.lam_lt]

/-- Long hold, given by `4 * Real.log (1 / d.h)`. -/
def longHold (d : TailData) : ℝ := 4 * Real.log (1 / d.h)
/-- Second ramp start, given by `1 + d.longHold`. -/
def secondRampStart (d : TailData) : ℝ := 1 + d.longHold
/-- Ramp end, given by `d.secondRampStart + 1`. -/
def rampEnd (d : TailData) : ℝ := d.secondRampStart + 1

theorem longHold_pos (d : TailData) : 0 < d.longHold := by
  unfold longHold
  apply mul_pos (by norm_num)
  apply Real.log_pos
  apply (lt_div_iff₀ d.h_pos).mpr
  linarith [d.h_lt_half]

theorem rampEnd_pos (d : TailData) : 0 < d.rampEnd := by
  dsimp [rampEnd, secondRampStart]
  linarith [d.longHold_pos]

/-- Rho, given by `tailCoefficient * d.h`. -/
def rho (d : TailData) : ℝ := tailCoefficient * d.h

theorem rho_pos (d : TailData) : 0 < d.rho := mul_pos tailCoefficient_pos d.h_pos

theorem rho_lt_half (d : TailData) : d.rho < 1 / 2 := by
  have hr : d.rho < d.h := by
    unfold rho
    nlinarith [tailCoefficient_lt_one, d.h_pos]
  exact hr.trans d.h_lt_half

end TailData

/-! ## The fixed terminal taper and its positive weighted debt -/

/-- Tail shape, given by `1 - d.rho + d.rho * sigma ((t - 1) / 2)`. -/
def tailShape (d : TailData) (t : ℝ) : ℝ :=
  1 - d.rho + d.rho * sigma ((t - 1) / 2)

/-- Tail shape derivative, given by `(d.rho / 2) * deriv sigma ((t - 1) / 2)`. -/
def tailShapeDeriv (d : TailData) (t : ℝ) : ℝ :=
  (d.rho / 2) * deriv sigma ((t - 1) / 2)

theorem tailShape_contDiff (d : TailData) : ContDiff ℝ ∞ (tailShape d) :=
  contDiff_const.add (contDiff_const.mul
    (sigma_contDiff.comp ((contDiff_id.sub contDiff_const).div_const 2)))

theorem tailShapeDeriv_contDiff (d : TailData) : ContDiff ℝ ∞ (tailShapeDeriv d) :=
  contDiff_const.mul (((contDiff_infty_iff_deriv.mp sigma_contDiff).2).comp
    ((contDiff_id.sub contDiff_const).div_const 2))

theorem tailShape_hasDerivAt (d : TailData) (t : ℝ) :
    HasDerivAt (tailShape d) (tailShapeDeriv d t) t := by
  have hs := (sigma_contDiff.differentiable (by simp) ((t - 1) / 2)).hasDerivAt
  have hm := (hs.comp t (((hasDerivAt_id t).sub_const 1).div_const 2)).const_mul d.rho
  convert! hm.const_add (1 - d.rho) using 1; simp [tailShapeDeriv]; ring

theorem tailShape_early (d : TailData) {t : ℝ} (ht : t ≤ 1) :
    tailShape d t = 1 - d.rho := by
  simp [tailShape, sigma_zero (by linarith : (t - 1) / 2 ≤ 0)]

theorem tailShape_late (d : TailData) {t : ℝ} (ht : 3 ≤ t) : tailShape d t = 1 := by
  rw [tailShape, sigma_one (by linarith : 1 ≤ (t - 1) / 2)]
  ring

theorem tailShape_bounds (d : TailData) (t : ℝ) :
    1 - d.rho ≤ tailShape d t ∧ tailShape d t ≤ 1 := by
  have hlo := mul_nonneg d.rho_pos.le (sigma_nonneg ((t - 1) / 2))
  have hhi := mul_le_mul_of_nonneg_left (sigma_le_one ((t - 1) / 2)) d.rho_pos.le
  unfold tailShape
  constructor <;> linarith

theorem tailShape_pos (d : TailData) (t : ℝ) : 0 < tailShape d t := by
  linarith [(tailShape_bounds d t).1, d.rho_lt_half]

theorem tailShapeDeriv_nonneg (d : TailData) (t : ℝ) : 0 ≤ tailShapeDeriv d t :=
  mul_nonneg (by exact div_nonneg d.rho_pos.le (by norm_num)) (sigma_derivative_nonneg _)

theorem tailShapeDeriv_integral (d : TailData) :
    (∫ t in (0 : ℝ)..3, tailShapeDeriv d t) = d.rho := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => tailShape_hasDerivAt d t) ((tailShapeDeriv_contDiff
        d).continuous.intervalIntegrable 0 3)
  rw [tailShape_late d (by norm_num), tailShape_early d (by norm_num)] at h
  linarith

/-- Tail log slope, given by `-d.h + tailShapeDeriv d t / tailShape d t`. -/
def tailLogSlope (d : TailData) (t : ℝ) : ℝ := -d.h + tailShapeDeriv d t / tailShape d t

/-- Tail debt, given by `(∫ t in (0 : ℝ)..3, Real.exp ((1 - d.h) * t) * tailShapeDeriv d t) / (1
- d.rho)`. -/
def tailDebt (d : TailData) : ℝ :=
  (∫ t in (0 : ℝ)..3, Real.exp ((1 - d.h) * t) * tailShapeDeriv d t) / (1 - d.rho)

theorem tailDebt_bounds (d : TailData) :
    d.rho / (1 - d.rho) ≤ tailDebt d ∧
      tailDebt d ≤ Real.exp 3 * d.rho / (1 - d.rho) := by
  have hden : 0 < 1 - d.rho := by linarith [d.rho_lt_half]
  have hc : Continuous (fun t => Real.exp ((1 - d.h) * t) * tailShapeDeriv d t) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (tailShapeDeriv_contDiff d).continuous
  have hlo := intervalIntegral.integral_mono_on (μ := volume) (a := 0) (b := 3)
    (by norm_num) ((tailShapeDeriv_contDiff d).continuous.intervalIntegrable 0 3)
    (hc.intervalIntegrable 0 3) (fun t ht => ?_)
  · have hhi := intervalIntegral.integral_mono_on (μ := volume) (a := 0) (b := 3)
      (g := fun t => Real.exp 3 * tailShapeDeriv d t)
      (by norm_num) (hc.intervalIntegrable 0 3)
      ((continuous_const.mul (tailShapeDeriv_contDiff d).continuous).intervalIntegrable 0 3)
      (fun t ht => ?_)
    · rw [tailShapeDeriv_integral] at hlo
      rw [intervalIntegral.integral_const_mul, tailShapeDeriv_integral] at hhi
      exact ⟨(div_le_div_iff_of_pos_right hden).mpr hlo,
        (div_le_div_iff_of_pos_right hden).mpr hhi⟩
    · have he : Real.exp ((1 - d.h) * t) ≤ Real.exp 3 := by
        apply Real.exp_le_exp.mpr
        nlinarith [d.h_pos, ht.1, ht.2]
      exact mul_le_mul_of_nonneg_right he (tailShapeDeriv_nonneg d t)
  · have he : 1 ≤ Real.exp ((1 - d.h) * t) :=
      Real.one_le_exp_iff.mpr (mul_nonneg d.one_sub_h_pos.le ht.1)
    nlinarith [mul_le_mul_of_nonneg_right he (tailShapeDeriv_nonneg d t)]

theorem tailDebt_pos (d : TailData) : 0 < tailDebt d :=
  (div_pos d.rho_pos (by linarith [d.rho_lt_half])).trans_le (tailDebt_bounds d).1

theorem tailDebt_small (d : TailData) : tailDebt d < Real.exp (-2) * d.h := by
  have hden : 0 < 1 - d.rho := by linarith [d.rho_lt_half]
  have hp : 0 ≤ Real.exp 3 * d.rho := mul_nonneg (Real.exp_pos _).le d.rho_pos.le
  have hdiv : Real.exp 3 * d.rho / (1 - d.rho) ≤ 2 * Real.exp 3 * d.rho := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hp (show 0 ≤ 1 - 2 * d.rho by linarith [d.rho_lt_half])]
  have hr : d.rho ≤ (Real.exp (-5) / 16) * d.h :=
    mul_le_mul_of_nonneg_right tailCoefficient_le d.h_pos.le
  have hb : tailDebt d ≤ Real.exp (-2) * d.h / 8 := by
    calc
      tailDebt d ≤ Real.exp 3 * d.rho / (1 - d.rho) := (tailDebt_bounds d).2
      _ ≤ 2 * Real.exp 3 * d.rho := hdiv
      _ ≤ 2 * Real.exp 3 * ((Real.exp (-5) / 16) * d.h) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = (Real.exp 3 * Real.exp (-5)) * d.h / 8 := by ring
      _ = Real.exp (-2) * d.h / 8 := by rw [← Real.exp_add]; norm_num
  exact hb.trans_lt (by nlinarith [mul_pos (Real.exp_pos (-2)) d.h_pos])

theorem tail_taper_log_derivative (d : TailData) (t : ℝ) :
    0 ≤ tailShapeDeriv d t / tailShape d t ∧
      tailShapeDeriv d t / tailShape d t < d.h / 4 := by
  have hS : 0 ≤ stepBound := le_trans (by norm_num) stepBound_ge_one
  have hcoef : tailCoefficient * stepBound ≤ 1 / 16 := by
    unfold tailCoefficient
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 16 * (stepBound + 1) by nlinarith)).mpr
    have he : Real.exp (-5 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right he hS]
  have hder : tailShapeDeriv d t ≤ d.rho / 2 * stepBound :=
    mul_le_mul_of_nonneg_left (sigma_derivative_le _) (by
        exact div_nonneg d.rho_pos.le (by norm_num))
  have hrS : d.rho * stepBound ≤ d.h / 16 := by
    have h := mul_le_mul_of_nonneg_right hcoef d.h_pos.le
    unfold TailData.rho
    nlinarith
  have hhalf : 1 / 2 ≤ tailShape d t := by
    linarith [(tailShape_bounds d t).1, d.rho_lt_half]
  have hratio : tailShapeDeriv d t / tailShape d t ≤ d.rho * stepBound := by
    apply (div_le_iff₀ (tailShape_pos d t)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhalf (mul_nonneg d.rho_pos.le hS)]
  exact ⟨div_nonneg (tailShapeDeriv_nonneg d t) (tailShape_pos d t).le,
    hratio.trans_lt (by linarith [d.h_pos])⟩

/-! ## Actual release coefficient and the integrating-factor solution -/

/-- Release slope, given by `-d.core.lam - (1 - d.core.lam) * sigma t + (1 - d.h) * sigma (t -
d.secondRampStart)`. -/
def releaseSlope (d : TailData) (t : ℝ) : ℝ :=
  -d.core.lam - (1 - d.core.lam) * sigma t +
    (1 - d.h) * sigma (t - d.secondRampStart)

theorem releaseSlope_contDiff (d : TailData) : ContDiff ℝ ∞ (releaseSlope d) :=
  (contDiff_const.sub (contDiff_const.mul sigma_contDiff)).add
    (contDiff_const.mul (sigma_contDiff.comp (contDiff_id.sub contDiff_const)))

theorem releaseSlope_early (d : TailData) {t : ℝ} (ht : t ≤ 0) :
    releaseSlope d t = -d.core.lam := by
  have ht' : t - d.secondRampStart ≤ 0 := by
    dsimp [TailData.secondRampStart]
    linarith [d.longHold_pos]
  simp [releaseSlope, sigma_zero ht, sigma_zero ht']

theorem releaseSlope_plateau (d : TailData) {t : ℝ} (ht : 1 ≤ t)
    (ht' : t ≤ d.secondRampStart) : releaseSlope d t = -1 := by
  rw [releaseSlope, sigma_one ht, sigma_zero (by linarith : t - d.secondRampStart ≤ 0)]
  ring

theorem releaseSlope_late (d : TailData) {t : ℝ} (ht : d.rampEnd ≤ t) :
    releaseSlope d t = -d.h := by
  have h1 : 1 ≤ t := by
    dsimp [TailData.rampEnd, TailData.secondRampStart] at ht
    linarith [d.longHold_pos]
  have h2 : 1 ≤ t - d.secondRampStart := by dsimp [TailData.rampEnd] at ht; linarith
  rw [releaseSlope, sigma_one h1, sigma_one h2]
  ring

theorem releaseSlope_bounds (d : TailData) (t : ℝ) :
    -1 ≤ releaseSlope d t ∧ releaseSlope d t ≤ -d.h := by
  have ha0 := sigma_nonneg t
  have ha1 := sigma_le_one t
  have hb0 := sigma_nonneg (t - d.secondRampStart)
  have hab : sigma (t - d.secondRampStart) ≤ sigma t := by
    apply sigma_monotone
    dsimp [TailData.secondRampStart]
    linarith [d.longHold_pos]
  have hl : 0 ≤ 1 - d.core.lam := by linarith [d.core.lam_lt]
  have hh : 0 ≤ 1 - d.h := d.one_sub_h_pos.le
  have hla := mul_le_mul_of_nonneg_left ha1 hl
  have hhb := mul_nonneg hh hb0
  have hba := mul_le_mul_of_nonneg_left hab hh
  have hgap := mul_le_mul_of_nonneg_left ha1 (sub_nonneg.mpr d.h_lt_lam.le)
  unfold releaseSlope
  constructor <;> nlinarith

/-- Release rate, given by `1 + releaseSlope d t`. -/
def releaseRate (d : TailData) (t : ℝ) : ℝ := 1 + releaseSlope d t
/-- Release source, given by `-releaseSlope d t - d.h`. -/
def releaseSource (d : TailData) (t : ℝ) : ℝ := -releaseSlope d t - d.h
/-- Initial lag, given by `(d.core.lam - d.h) / (1 - d.core.lam)`. -/
def initialLag (d : TailData) : ℝ := (d.core.lam - d.h) / (1 - d.core.lam)

theorem initialLag_gt_h (d : TailData) : d.h < initialLag d := by
  apply (lt_div_iff₀ (show 0 < 1 - d.core.lam by linarith [d.core.lam_lt])).mpr
  nlinarith [d.h_small, mul_pos d.h_pos d.core.lam_pos]

theorem releaseRate_contDiff (d : TailData) : ContDiff ℝ ∞ (releaseRate d) :=
  contDiff_const.add (releaseSlope_contDiff d)

theorem releaseSource_contDiff (d : TailData) : ContDiff ℝ ∞ (releaseSource d) :=
  (releaseSlope_contDiff d).neg.sub contDiff_const

/-- Linear lag, given by `Real.exp (-primitive a t) * (q + primitive (fun v => Real.exp
(primitive a v) * b v) t)`. -/
def linearLag (a b : ℝ → ℝ) (q : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-primitive a t) *
    (q + primitive (fun v => Real.exp (primitive a v) * b v) t)

theorem linearLag_contDiff {a b : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (q : ℝ) : ContDiff ℝ ∞ (linearLag a b q) :=
  (primitive_contDiff ha).neg.exp.mul
    (contDiff_const.add (primitive_contDiff ((primitive_contDiff ha).exp.mul hb)))

theorem linearLag_initial (a b : ℝ → ℝ) (q : ℝ) : linearLag a b q 0 = q := by
  simp [linearLag, primitive]

theorem linearLag_hasDerivAt {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (q t : ℝ) : HasDerivAt (linearLag a b q) (b t - a t * linearLag a b q t) t := by
  have hc : Continuous (fun v => Real.exp (primitive a v) * b v) :=
    (Real.continuous_exp.comp (continuous_iff_continuousAt.mpr
      (fun v => (primitive_hasDerivAt ha v).continuousAt))).mul hb
  have h := ((primitive_hasDerivAt ha t).neg.exp).mul
    ((primitive_hasDerivAt hc t).const_add q)
  have he : Real.exp (-primitive a t) * Real.exp (primitive a t) = 1 := by
    rw [← Real.exp_add]
    simp
  convert! h using 1
  dsimp [linearLag]
  nlinarith [congrArg (fun v : ℝ => v * b t) he]

/-- Release lag, given by `linearLag (releaseRate d) (releaseSource d) (initialLag d)`. -/
def releaseLag (d : TailData) : ℝ → ℝ :=
  linearLag (releaseRate d) (releaseSource d) (initialLag d)

theorem releaseLag_contDiff (d : TailData) : ContDiff ℝ ∞ (releaseLag d) :=
  linearLag_contDiff (releaseRate_contDiff d) (releaseSource_contDiff d) _

theorem releaseLag_initial (d : TailData) : releaseLag d 0 = initialLag d :=
  linearLag_initial _ _ _

theorem releaseLag_equation (d : TailData) (t : ℝ) :
    deriv (releaseLag d) t + (1 + releaseSlope d t) * releaseLag d t =
      -releaseSlope d t - d.h := by
  unfold releaseLag
  rw [(linearLag_hasDerivAt (releaseRate_contDiff d).continuous
    (releaseSource_contDiff d).continuous (initialLag d) t).deriv]
  unfold releaseRate releaseSource
  ring

theorem release_source_nonneg (d : TailData) (t : ℝ) : 0 ≤ releaseSource d t := by
  dsimp [releaseSource]
  linarith [(releaseSlope_bounds d t).2]

theorem release_rate_bounds (d : TailData) (t : ℝ) :
    0 ≤ releaseRate d t ∧ releaseRate d t ≤ 1 := by
  dsimp [releaseRate]
  constructor <;> linarith [(releaseSlope_bounds d t).1, (releaseSlope_bounds d t).2, d.h_pos]

theorem release_rate_integral_bound (d : TailData) :
    primitive (releaseRate d) d.rampEnd ≤ 2 := by
  have hc := (releaseRate_contDiff d).continuous
  have h1 : (∫ t in (0 : ℝ)..1, releaseRate d t) ≤ 1 := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (a := 0) (b := 1)
      (g := fun _ => (1 : ℝ)) (by norm_num) (hc.intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1) (fun t _ => (release_rate_bounds d t).2)
    simpa using h
  have hm : (∫ t in (1 : ℝ)..d.secondRampStart, releaseRate d t) = 0 := by
    calc
      _ = ∫ _t in (1 : ℝ)..d.secondRampStart, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' := uIcc_of_le (show 1 ≤ d.secondRampStart by
          dsimp [TailData.secondRampStart]; linarith [d.longHold_pos]) ▸ ht
        dsimp [releaseRate]
        rw [releaseSlope_plateau d ht'.1 ht'.2]
        norm_num
      _ = 0 := by simp
  have h2 : (∫ t in d.secondRampStart..d.rampEnd, releaseRate d t) ≤ 1 := by
    have hle : d.secondRampStart ≤ d.rampEnd := by dsimp [TailData.rampEnd]; linarith
    have h := intervalIntegral.integral_mono_on (μ := volume) hle
      (g := fun _ => (1 : ℝ)) (hc.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) (fun t _ => (release_rate_bounds d t).2)
    simpa [TailData.rampEnd] using h
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 1 d.secondRampStart)
  have hb := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 d.secondRampStart) (hc.intervalIntegrable d.secondRampStart d.rampEnd)
  unfold primitive
  linarith

theorem releaseLag_lower (d : TailData) :
    Real.exp (-2) * initialLag d ≤ releaseLag d d.rampEnd := by
  have hsource : 0 ≤ primitive
      (fun t => Real.exp (primitive (releaseRate d) t) * releaseSource d t) d.rampEnd :=
    intervalIntegral.integral_nonneg d.rampEnd_pos.le
      (fun t _ => mul_nonneg (Real.exp_pos _).le (release_source_nonneg d t))
  have he : Real.exp (-2) ≤ Real.exp (-primitive (releaseRate d) d.rampEnd) :=
    Real.exp_le_exp.mpr (by linarith [release_rate_integral_bound d])
  have hq : 0 ≤ initialLag d := d.h_pos.le.trans (initialLag_gt_h d).le
  unfold releaseLag linearLag
  nlinarith [mul_nonneg (Real.exp_pos (-primitive (releaseRate d) d.rampEnd)).le hsource,
    mul_le_mul_of_nonneg_right he hq]

theorem releaseLag_gt_tailDebt (d : TailData) : tailDebt d < releaseLag d d.rampEnd := by
  have h := mul_lt_mul_of_pos_left (initialLag_gt_h d) (Real.exp_pos (-2))
  exact (tailDebt_small d).trans (h.trans_le (releaseLag_lower d))

/-- Decay hold, given by `Real.log (releaseLag d d.rampEnd / tailDebt d) / (1 - d.h)`. -/
def decayHold (d : TailData) : ℝ :=
  Real.log (releaseLag d d.rampEnd / tailDebt d) / (1 - d.h)

theorem decayHold_pos (d : TailData) : 0 < decayHold d := by
  apply div_pos _ d.one_sub_h_pos
  apply Real.log_pos
  exact (one_lt_div (tailDebt_pos d)).mpr (releaseLag_gt_tailDebt d)

theorem decayHold_hits_target (d : TailData) :
    releaseLag d d.rampEnd * Real.exp (-(1 - d.h) * decayHold d) = tailDebt d := by
  have hq : 0 < releaseLag d d.rampEnd := (tailDebt_pos d).trans (releaseLag_gt_tailDebt d)
  have hd := tailDebt_pos d
  have he : -(1 - d.h) * decayHold d = -Real.log (releaseLag d d.rampEnd / tailDebt d) := by
    unfold decayHold
    field_simp [d.one_sub_h_pos.ne']
  rw [he, Real.exp_neg, Real.exp_log (div_pos hq hd)]
  field_simp

/-! ## One globally smooth positive angular profile -/

/-- Log shape, given by `Real.log (1 + eta ^ 2)`. -/
def logShape (eta : ℝ) : ℝ := Real.log (1 + eta ^ 2)

theorem logShape_contDiff : ContDiff ℝ ∞ logShape :=
  (contDiff_const.add (contDiff_id.pow 2)).log (fun eta => by positivity)

/-- Flatten factor, given by `Real.exp (sigma ((p.1 - d.core.endpoint) / flattenLength) *
(logShape p.2 - Real.log 2))`. -/
def flattenFactor (d : TailData) (p : ℝ × ℝ) : ℝ :=
  Real.exp (sigma ((p.1 - d.core.endpoint) / flattenLength) * (logShape p.2 - Real.log 2))

/-- Flattened, given by `angular d.core.P d.core.dropLength d.core.lam p * flattenFactor d p`. -/
def flattened (d : TailData) (p : ℝ × ℝ) : ℝ :=
  angular d.core.P d.core.dropLength d.core.lam p * flattenFactor d p

theorem flattenFactor_contDiff (d : TailData) : ContDiff ℝ ∞ (flattenFactor d) :=
  ((sigma_contDiff.comp ((contDiff_fst.sub contDiff_const).div_const flattenLength)).mul
    ((logShape_contDiff.comp contDiff_snd).sub contDiff_const)).exp

theorem flattened_contDiff (d : TailData) : ContDiff ℝ ∞ (flattened d) :=
  (angular_contDiff _ _ _).mul (flattenFactor_contDiff d)

theorem flattened_pos (d : TailData) (p : ℝ × ℝ) : 0 < flattened d p :=
  mul_pos (angular_pos d.core.P_pos _ _ _) (Real.exp_pos _)

theorem flattenFactor_before (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : y ≤ d.core.endpoint) : flattenFactor d (y, eta) = 1 := by
  have hs : (y - d.core.endpoint) / flattenLength ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) flattenLength_pos.le
  simp [flattenFactor, sigma_zero hs]

theorem flattened_before (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : y ≤ d.core.endpoint) :
    flattened d (y, eta) = angular d.core.P d.core.dropLength d.core.lam (y, eta) := by
  simp [flattened, flattenFactor_before d eta hy]

theorem flattened_uniform (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.flattenEnd ≤ y) :
    flattened d (y, eta) = radialAmplitude d.core.P d.core.dropLength d.core.lam y / 2 := by
  have hs : 1 ≤ (y - d.core.endpoint) / flattenLength := by
    apply (le_div_iff₀ flattenLength_pos).mpr
    dsimp [TailData.flattenEnd] at hy
    linarith
  have hp : 0 < 1 + eta ^ 2 := by positivity
  simp only [flattened, angular, flattenFactor, sigma_one hs, one_mul, logShape,
    Real.exp_sub, Real.exp_log hp, Real.exp_log (by norm_num : (0 : ℝ) < 2), shape]
  field_simp

/-- Release adjustment, given by `primitive (fun t => releaseSlope d t + d.core.lam)`. -/
def releaseAdjustment (d : TailData) : ℝ → ℝ :=
  primitive (fun t => releaseSlope d t + d.core.lam)

theorem releaseAdjustment_contDiff (d : TailData) : ContDiff ℝ ∞ (releaseAdjustment d) :=
  primitive_contDiff ((releaseSlope_contDiff d).add contDiff_const)

theorem releaseAdjustment_early (d : TailData) {t : ℝ} (ht : t ≤ 0) :
    releaseAdjustment d t = 0 := by
  unfold releaseAdjustment primitive
  calc
    _ = ∫ _v in (0 : ℝ)..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro v hv
      dsimp only
      rw [releaseSlope_early d ((uIcc_of_ge ht ▸ hv).2)]
      ring
    _ = 0 := by simp

theorem releaseAdjustment_late (d : TailData) {a t : ℝ}
    (ha : d.rampEnd ≤ a) (hat : a ≤ t) :
    releaseAdjustment d t = releaseAdjustment d a + (d.core.lam - d.h) * (t - a) := by
  have h := primitive_increment (g := fun v => releaseSlope d v + d.core.lam)
    ((releaseSlope_contDiff d).continuous.add continuous_const) a t (d.core.lam - d.h) ?_
  · simpa only [releaseAdjustment, mul_comm (t - a)] using h
  · intro v hv
    rw [releaseSlope_late d (ha.trans (uIcc_of_le hat ▸ hv).1)]
    ring

/-- Tail start, given by `d.releaseStart + d.rampEnd + decayHold d`. -/
def tailStart (d : TailData) : ℝ := d.releaseStart + d.rampEnd + decayHold d
/-- Tail end, given by `tailStart d + 3`. -/
def tailEnd (d : TailData) : ℝ := tailStart d + 3

theorem releaseStart_gt_flattenEnd (d : TailData) : d.flattenEnd < d.releaseStart := by
  dsimp [TailData.releaseStart]
  linarith [d.uniformWait_pos]

theorem flattenEnd_gt_core (d : TailData) : d.core.endpoint < d.flattenEnd := by
  dsimp [TailData.flattenEnd]
  linarith [flattenLength_pos]

theorem tailStart_gt_release (d : TailData) : d.releaseStart < tailStart d := by
  dsimp [tailStart]
  linarith [d.rampEnd_pos, decayHold_pos d]

/-- Final angular, given by `flattened d p * Real.exp (releaseAdjustment d (p.1 -
d.releaseStart)) * (tailShape d (p.1 - tailStart d) / (1 - d.rho))`. -/
def finalAngular (d : TailData) (p : ℝ × ℝ) : ℝ :=
  flattened d p * Real.exp (releaseAdjustment d (p.1 - d.releaseStart)) *
    (tailShape d (p.1 - tailStart d) / (1 - d.rho))

theorem finalAngular_contDiff (d : TailData) : ContDiff ℝ ∞ (finalAngular d) :=
  ((flattened_contDiff d).mul ((releaseAdjustment_contDiff d).comp
    (contDiff_fst.sub contDiff_const)).exp).mul
    (((tailShape_contDiff d).comp (contDiff_fst.sub contDiff_const)).div_const _)

theorem finalAngular_pos (d : TailData) (p : ℝ × ℝ) : 0 < finalAngular d p :=
  mul_pos (mul_pos (flattened_pos d p) (Real.exp_pos _))
    (div_pos (tailShape_pos d _) (by linarith [d.rho_lt_half]))

theorem finalAngular_before (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : y ≤ d.core.endpoint) :
    finalAngular d (y, eta) = angular d.core.P d.core.dropLength d.core.lam (y, eta) := by
  have hrel : y - d.releaseStart ≤ 0 := by
    linarith [flattenEnd_gt_core d, releaseStart_gt_flattenEnd d]
  have htail : y - tailStart d ≤ 1 := by linarith [tailStart_gt_release d]
  have hden : 1 - d.rho ≠ 0 := by linarith [d.rho_lt_half]
  simp [finalAngular, flattened_before d eta hy, releaseAdjustment_early d hrel,
    tailShape_early d htail, hden]

/-- Carrier, given by `(radialAmplitude d.core.P d.core.dropLength d.core.lam y / 2) * Real.exp
(releaseAdjustment d (y - d.releaseStart))`. -/
def carrier (d : TailData) (y : ℝ) : ℝ :=
  (radialAmplitude d.core.P d.core.dropLength d.core.lam y / 2) *
    Real.exp (releaseAdjustment d (y - d.releaseStart))

theorem carrier_pos (d : TailData) (y : ℝ) : 0 < carrier d y := by
  unfold carrier radialAmplitude
  exact mul_pos (div_pos (mul_pos d.core.P_pos (Real.exp_pos _)) (by norm_num)) (Real.exp_pos _)

theorem finalAngular_uniform (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.flattenEnd ≤ y) :
    finalAngular d (y, eta) = carrier d y * (tailShape d (y - tailStart d) / (1 - d.rho)) := by
  rw [finalAngular, flattened_uniform d eta hy]
  rfl

theorem finalAngular_eta_independent (d : TailData) (eta eta' : ℝ) {y : ℝ}
    (hy : d.flattenEnd ≤ y) : finalAngular d (y, eta) = finalAngular d (y, eta') := by
  rw [finalAngular_uniform d eta hy, finalAngular_uniform d eta' hy]

theorem finalAngular_uniform_wait (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.flattenEnd ≤ y) (hy' : y ≤ d.releaseStart) :
    finalAngular d (y, eta) = radialAmplitude d.core.P d.core.dropLength d.core.lam y / 2 := by
  have htail : y - tailStart d ≤ 1 := by linarith [tailStart_gt_release d]
  have hden : 1 - d.rho ≠ 0 := by linarith [d.rho_lt_half]
  rw [finalAngular_uniform d eta hy]
  simp [carrier, releaseAdjustment_early d (by linarith : y - d.releaseStart ≤ 0),
    tailShape_early d htail, hden]

theorem coreEndpoint_ge_hold (d : TailData) : d.core.holdStart ≤ d.core.endpoint := by
  have h := d.core.pulseStart_ge_hold
  dsimp [OutgoingSchedule.Parameters.endpoint]
  linarith [d.core.pulseLength_pos]

theorem carrier_late_scaling (d : TailData) {a y : ℝ}
    (ha : d.releaseStart + d.rampEnd ≤ a) (hay : a ≤ y) :
    carrier d y = carrier d a * Real.exp (-(1 / 2 + d.h) * (y - a)) := by
  have har : d.rampEnd ≤ a - d.releaseStart := by linarith
  have hat : a - d.releaseStart ≤ y - d.releaseStart := by linarith
  have hahold : d.core.holdStart ≤ a := by
    linarith [coreEndpoint_ge_hold d, flattenEnd_gt_core d, releaseStart_gt_flattenEnd d,
      d.rampEnd_pos]
  have hE := radialAmplitude_hold d.core.dropLength_pos.le hahold hay
    (P := d.core.P) (lam := d.core.lam)
  have hG := releaseAdjustment_late d har hat
  unfold carrier
  rw [hE, hG, Real.exp_add]
  have he : Real.exp (-(1 / 2 + d.core.lam) * (y - a)) *
      Real.exp ((d.core.lam - d.h) * ((y - d.releaseStart) - (a - d.releaseStart))) =
      Real.exp (-(1 / 2 + d.h) * (y - a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = ((radialAmplitude d.core.P d.core.dropLength d.core.lam a / 2) *
        Real.exp (releaseAdjustment d (a - d.releaseStart))) *
      (Real.exp (-(1 / 2 + d.core.lam) * (y - a)) *
        Real.exp ((d.core.lam - d.h) * ((y - d.releaseStart) - (a - d.releaseStart)))) := by ring
    _ = _ := by rw [he]

/-- Power constant, given by `carrier d (tailStart d) * Real.exp ((1 / 2 + d.h) * tailStart d) /
(1 - d.rho)`. -/
def powerConstant (d : TailData) : ℝ :=
  carrier d (tailStart d) * Real.exp ((1 / 2 + d.h) * tailStart d) / (1 - d.rho)

theorem powerConstant_pos (d : TailData) : 0 < powerConstant d :=
  div_pos (mul_pos (carrier_pos d _) (Real.exp_pos _)) (by linarith [d.rho_lt_half])

theorem finalAngular_tail (d : TailData) (eta : ℝ) {y : ℝ} (hy : tailStart d ≤ y) :
    finalAngular d (y, eta) =
      powerConstant d * Real.exp (-(1 / 2 + d.h) * y) * tailShape d (y - tailStart d) := by
  have hflat : d.flattenEnd ≤ y := by
    linarith [tailStart_gt_release d, releaseStart_gt_flattenEnd d]
  have hstart : d.releaseStart + d.rampEnd ≤ tailStart d := by
    dsimp [tailStart]
    linarith [decayHold_pos d]
  rw [finalAngular_uniform d eta hflat, carrier_late_scaling d hstart hy]
  have he : Real.exp (-(1 / 2 + d.h) * (y - tailStart d)) =
      Real.exp ((1 / 2 + d.h) * tailStart d) * Real.exp (-(1 / 2 + d.h) * y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  unfold powerConstant
  ring

theorem finalAngular_eventual_power (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : tailEnd d ≤ y) :
    finalAngular d (y, eta) = powerConstant d * Real.exp (-(1 / 2 + d.h) * y) := by
  have hy' : tailStart d ≤ y := by dsimp [tailEnd] at hy; linarith
  have ht : 3 ≤ y - tailStart d := by dsimp [tailEnd] at hy; linarith
  rw [finalAngular_tail d eta hy', tailShape_late d ht, mul_one]

theorem finalAngular_radial_power (d : TailData) (eta : ℝ) {X : ℝ}
    (hX : 0 < X) (hfar : tailEnd d ≤ Real.log X) :
    finalAngular d (Real.log X, eta) = powerConstant d * X ^ (-(1 / 2 + d.h)) := by
  rw [finalAngular_eventual_power d eta hfar, Real.rpow_def_of_pos hX]
  congr 2
  ring

theorem axial_product_unchanged (d : TailData) (amp : ℝ → ℝ) (eta y : ℝ) :
    finalAngular d (y, eta) * axial d.core amp (y, eta) =
      angular d.core.P d.core.dropLength d.core.lam (y, eta) * axial d.core amp (y, eta) := by
  by_cases hy : y ≤ d.core.endpoint
  · rw [finalAngular_before d eta hy]
  · rw [axial_after_pulse d.core amp eta (le_of_not_ge hy)]
    simp

/-! ## The prescribed taper is an actual backward lag solution -/

/-- Tail rate, given by `1 + tailLogSlope d t`. -/
def tailRate (d : TailData) (t : ℝ) : ℝ := 1 + tailLogSlope d t

theorem tailRate_contDiff (d : TailData) : ContDiff ℝ ∞ (tailRate d) :=
  contDiff_const.add (contDiff_const.add
    ((tailShapeDeriv_contDiff d).div (tailShape_contDiff d) (fun t => (tailShape_pos d t).ne')))

/-- Weighted tail derivative, given by `Real.exp ((1 - d.h) * t) * tailShapeDeriv d t`. -/
def weightedTailDerivative (d : TailData) (t : ℝ) : ℝ :=
  Real.exp ((1 - d.h) * t) * tailShapeDeriv d t

theorem weightedTailDerivative_contDiff (d : TailData) :
    ContDiff ℝ ∞ (weightedTailDerivative d) :=
  (contDiff_const.mul contDiff_id).exp.mul (tailShapeDeriv_contDiff d)

theorem tailRate_primitive (d : TailData) (t : ℝ) :
    primitive (tailRate d) t =
      (1 - d.h) * t + Real.log (tailShape d t) - Real.log (1 - d.rho) := by
  have hd : ∀ v : ℝ, HasDerivAt
      (fun x : ℝ => (1 - d.h) * x + Real.log (tailShape d x)) (tailRate d v) v := by
    intro v
    convert! ((hasDerivAt_id v).const_mul (1 - d.h)).add
      ((tailShape_hasDerivAt d v).log (tailShape_pos d v).ne') using 1
    unfold tailRate tailLogSlope
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
    ((tailRate_contDiff d).continuous.intervalIntegrable 0 t)
  simpa [primitive, tailShape_early d (show (0 : ℝ) ≤ 1 by norm_num)] using hi

theorem tail_integrating_factor (d : TailData) (t : ℝ) :
    Real.exp (primitive (tailRate d) t) =
      Real.exp ((1 - d.h) * t) * tailShape d t / (1 - d.rho) := by
  rw [tailRate_primitive, Real.exp_sub, Real.exp_add,
    Real.exp_log (tailShape_pos d t),
    Real.exp_log (show 0 < 1 - d.rho by linarith [d.rho_lt_half])]

/-- This is exactly the weighted integral prescribed for `Qp` in stage 5. -/
theorem tailDebt_source_formula (d : TailData) :
    tailDebt d = ∫ v in (0 : ℝ)..3,
      Real.exp (primitive (tailRate d) v) * (tailShapeDeriv d v / tailShape d v) := by
  unfold tailDebt
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [tail_integrating_factor]
  have hf := (tailShape_pos d v).ne'
  have hden : 1 - d.rho ≠ 0 := by linarith [d.rho_lt_half]
  field_simp [hf, hden]

/-- Tail numerator, given by `Real.exp (-(1 - d.h) * t) * (primitive (weightedTailDerivative d)
3 - primitive (weightedTailDerivative d) t)`. -/
def tailNumerator (d : TailData) (t : ℝ) : ℝ :=
  Real.exp (-(1 - d.h) * t) *
    (primitive (weightedTailDerivative d) 3 - primitive (weightedTailDerivative d) t)

/-- Tail lag, given by `tailNumerator d t / tailShape d t`. -/
def tailLag (d : TailData) (t : ℝ) : ℝ := tailNumerator d t / tailShape d t

theorem tailNumerator_contDiff (d : TailData) : ContDiff ℝ ∞ (tailNumerator d) :=
  (contDiff_const.mul contDiff_id).exp.mul
    (contDiff_const.sub (primitive_contDiff (weightedTailDerivative_contDiff d)))

theorem tailLag_contDiff (d : TailData) : ContDiff ℝ ∞ (tailLag d) :=
  (tailNumerator_contDiff d).div (tailShape_contDiff d) (fun t => (tailShape_pos d t).ne')

theorem tailNumerator_hasDerivAt (d : TailData) (t : ℝ) :
    HasDerivAt (tailNumerator d)
      (-(1 - d.h) * tailNumerator d t - tailShapeDeriv d t) t := by
  have h := (((hasDerivAt_id t).const_mul (-(1 - d.h))).exp).mul
    ((hasDerivAt_const t (primitive (weightedTailDerivative d) 3)).sub
      (primitive_hasDerivAt (weightedTailDerivative_contDiff d).continuous t))
  have he : Real.exp (-(1 - d.h) * t) * Real.exp ((1 - d.h) * t) = 1 := by
    rw [← Real.exp_add]
    convert! Real.exp_zero using 1; ring_nf
  convert! h using 1
  dsimp [tailNumerator, weightedTailDerivative]
  nlinarith [congrArg (fun x : ℝ => x * tailShapeDeriv d t) he]

theorem tailLag_hasDerivAt (d : TailData) (t : ℝ) :
    HasDerivAt (tailLag d)
      (-tailRate d t * tailLag d t - tailShapeDeriv d t / tailShape d t) t := by
  have h := (tailNumerator_hasDerivAt d t).div (tailShape_hasDerivAt d t)
    (tailShape_pos d t).ne'
  have hf := (tailShape_pos d t).ne'
  convert! h using 1
  dsimp [tailLag, tailRate, tailLogSlope]
  field_simp [hf]; ring

theorem tailLag_equation (d : TailData) (t : ℝ) :
    deriv (tailLag d) t + (1 + tailLogSlope d t) * tailLag d t =
      -tailLogSlope d t - d.h := by
  rw [(tailLag_hasDerivAt d t).deriv]
  unfold tailRate tailLogSlope
  ring

theorem tailLag_initial (d : TailData) : tailLag d 0 = tailDebt d := by
  simp [tailLag, tailNumerator, weightedTailDerivative, primitive, tailDebt,
    tailShape_early d (show (0 : ℝ) ≤ 1 by norm_num)]

theorem tailLag_terminal (d : TailData) : tailLag d 3 = 0 := by
  simp [tailLag, tailNumerator]

theorem tailLag_nonneg (d : TailData) {t : ℝ} (ht : t ≤ 3) : 0 ≤ tailLag d t := by
  have hc := (weightedTailDerivative_contDiff d).continuous
  have hdiff : primitive (weightedTailDerivative d) 3 - primitive (weightedTailDerivative d) t =
      ∫ v in t..3, weightedTailDerivative d v := by
    have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable 0 t) (hc.intervalIntegrable t 3)
    unfold primitive
    linarith
  unfold tailLag tailNumerator
  rw [hdiff]
  apply div_nonneg _ (tailShape_pos d t).le
  apply mul_nonneg (Real.exp_pos _).le
  exact intervalIntegral.integral_nonneg ht
    (fun v _ => mul_nonneg (Real.exp_pos _).le (tailShapeDeriv_nonneg d v))

/-- Hold lag, given by `releaseLag d d.rampEnd * Real.exp (-(1 - d.h) * t)`. -/
def holdLag (d : TailData) (t : ℝ) : ℝ :=
  releaseLag d d.rampEnd * Real.exp (-(1 - d.h) * t)

theorem holdLag_hasDerivAt (d : TailData) (t : ℝ) :
    HasDerivAt (holdLag d) (-(1 - d.h) * holdLag d t) t := by
  convert! (((hasDerivAt_id t).const_mul (-(1 - d.h))).exp).const_mul
    (releaseLag d d.rampEnd) using 1; simp [holdLag]; ring

theorem holdLag_equation (d : TailData) (t : ℝ) :
    deriv (holdLag d) t + (1 - d.h) * holdLag d t = 0 := by
  rw [(holdLag_hasDerivAt d t).deriv]
  ring

theorem holdLag_matches (d : TailData) :
    holdLag d 0 = releaseLag d d.rampEnd ∧ holdLag d (decayHold d) = tailLag d 0 := by
  constructor
  · simp [holdLag]
  · rw [tailLag_initial]
    exact decayHold_hits_target d

/-- Every existing core has the scalar parameters used in this tail construction. -/
def tailDataOfCore (c : OutgoingSchedule.Parameters) : TailData where
  core := c
  h := c.lam / 4
  h_pos := div_pos c.lam_pos (by norm_num)
  h_small := by linarith [c.lam_pos]

theorem constructed_tail (d : TailData) :
    ContDiff ℝ ∞ (finalAngular d) ∧
    (∀ p, 0 < finalAngular d p) ∧
    0 < decayHold d ∧
    holdLag d (decayHold d) = tailLag d 0 ∧
    tailLag d 3 = 0 ∧
    (∀ eta y, y ≤ d.core.endpoint →
      finalAngular d (y, eta) = angular d.core.P d.core.dropLength d.core.lam (y, eta)) ∧
    (∀ eta y, tailEnd d ≤ y →
      finalAngular d (y, eta) = powerConstant d * Real.exp (-(1 / 2 + d.h) * y)) :=
  ⟨finalAngular_contDiff d, finalAngular_pos d, decayHold_pos d, (holdLag_matches d).2,
    tailLag_terminal d, fun eta _ hy => finalAngular_before d eta hy,
    fun eta _ hy => finalAngular_eventual_power d eta hy⟩

/-! ## The exact flattening slope and the unchanged axial histories -/

/-- Flattening slope, given by `-d.core.lam + (deriv sigma ((y - d.core.endpoint) /
flattenLength) / flattenLength) * (logShape eta - Real.log 2)`. -/
def flatteningSlope (d : TailData) (y eta : ℝ) : ℝ :=
  -d.core.lam + (deriv sigma ((y - d.core.endpoint) / flattenLength) / flattenLength) *
    (logShape eta - Real.log 2)

theorem flatteningSlope_bounds (d : TailData) (y eta : ℝ) (heta : eta ^ 2 ≤ 1) :
    -d.core.lam - 1 / 10 ≤ flatteningSlope d y eta ∧
      flatteningSlope d y eta ≤ -d.core.lam := by
  have hJ0 : 0 ≤ logShape eta := Real.log_nonneg (by nlinarith [sq_nonneg eta])
  have hJ1 : logShape eta ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hD0 := sigma_derivative_nonneg ((y - d.core.endpoint) / flattenLength)
  have hD1 := sigma_derivative_le ((y - d.core.endpoint) / flattenLength)
  have hS : 0 ≤ stepBound := le_trans (by norm_num) stepBound_ge_one
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprod : deriv sigma ((y - d.core.endpoint) / flattenLength) *
      (Real.log 2 - logShape eta) ≤ stepBound * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_right hD1 (sub_nonneg.mpr hJ1)
    nlinarith [mul_nonneg hS hJ0]
  have hlen : stepBound * Real.log 2 ≤ flattenLength / 10 := by
    unfold flattenLength
    nlinarith
  have hquot : (deriv sigma ((y - d.core.endpoint) / flattenLength) *
      (Real.log 2 - logShape eta)) / flattenLength ≤ 1 / 10 := by
    apply (div_le_iff₀ flattenLength_pos).mpr
    linarith
  have hid : (deriv sigma ((y - d.core.endpoint) / flattenLength) / flattenLength) *
      (logShape eta - Real.log 2) =
      -(deriv sigma ((y - d.core.endpoint) / flattenLength) *
        (Real.log 2 - logShape eta) / flattenLength) := by ring
  have hsign := mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg hD0 flattenLength_pos.le) (sub_nonpos.mpr hJ1)
  unfold flatteningSlope
  constructor
  · rw [hid]
    linarith
  · linarith

theorem flattened_hasDerivAt (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.core.endpoint ≤ y) :
    HasDerivAt (fun t => flattened d (t, eta))
      (flattened d (y, eta) * (flatteningSlope d y eta - 1 / 2)) y := by
  have hbase := (radialAmplitude_hasDerivAt d.core.P d.core.dropLength d.core.lam y).mul_const
      (shape eta)
  have hs := (sigma_contDiff.differentiable (by simp)
    ((y - d.core.endpoint) / flattenLength)).hasDerivAt
  have hstep := hs.comp y (((hasDerivAt_id y).sub_const d.core.endpoint).div_const flattenLength)
  have hf := (hstep.mul_const (logShape eta - Real.log 2)).exp
  have hhold : d.core.dropLength + 2 ≤ y := (coreEndpoint_ge_hold d).trans hy
  have hl := slope_hold d.core.dropLength_pos.le hhold (lam := d.core.lam)
  convert! hbase.mul hf using 1
  dsimp [flattened, angular, flattenFactor, flatteningSlope]
  rw [hl]
  ring

theorem flattened_log_hasDerivAt (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.core.endpoint ≤ y) :
    HasDerivAt (fun t => Real.log (flattened d (t, eta)))
      (flatteningSlope d y eta - 1 / 2) y := by
  have hf := (flattened_pos d (y, eta)).ne'
  convert! (flattened_hasDerivAt d eta hy).log hf using 1
  field_simp

/-- Extended angular moment as an element of `ℝ`. -/
def extendedAngularMoment (d : TailData) (amp : ℝ → ℝ) (eta y : ℝ) : ℝ :=
  (5 / 2) * Real.sqrt 2 * d.core.P * eta * shape eta +
    ∫ t in (0 : ℝ)..y,
      Real.sqrt 2 * Real.exp (3 * t / 2) * finalAngular d (t, eta) * axial d.core amp (t, eta)

theorem extendedAngularMoment_eq (d : TailData) (amp : ℝ → ℝ) (eta y : ℝ) :
    extendedAngularMoment d amp eta y = angularMoment d.core amp eta y := by
  unfold extendedAngularMoment angularMoment
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  calc
    _ = (Real.sqrt 2 * Real.exp (3 * t / 2)) *
        (finalAngular d (t, eta) * axial d.core amp (t, eta)) := by ring
    _ = _ := by rw [axial_product_unchanged]; ring

theorem extended_moments_zero (d : TailData) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : d.core.endpoint ≤ y) :
    massMoment d.core amp eta y = 0 ∧ extendedAngularMoment d amp eta y = 0 := by
  rw [extendedAngularMoment_eq]
  exact ⟨massMoment_after_pulse d.core amp eta hy, angularMoment_after_pulse d.core amp eta hy⟩

theorem carrier_hasDerivAt (d : TailData) {y : ℝ} (hy : d.releaseStart ≤ y) :
    HasDerivAt (carrier d)
      (carrier d y * (releaseSlope d (y - d.releaseStart) - 1 / 2)) y := by
  have hbase := (radialAmplitude_hasDerivAt d.core.P d.core.dropLength d.core.lam y).div_const 2
  have hprim := primitive_hasDerivAt (g := fun t => releaseSlope d t + d.core.lam)
    ((releaseSlope_contDiff d).continuous.add continuous_const) (y - d.releaseStart)
  have hshift := hprim.comp y ((hasDerivAt_id y).sub_const d.releaseStart)
  have h := hbase.mul hshift.exp
  have hhold : d.core.dropLength + 2 ≤ y := by
    have h0 := coreEndpoint_ge_hold d
    dsimp [OutgoingSchedule.Parameters.holdStart] at h0
    linarith [flattenEnd_gt_core d, releaseStart_gt_flattenEnd d]
  have hs := slope_hold d.core.dropLength_pos.le hhold (lam := d.core.lam)
  convert! h using 1
  dsimp [carrier, releaseAdjustment]
  rw [hs]
  ring

/-- Profile slope, given by `releaseSlope d (y - d.releaseStart) + tailShapeDeriv d (y -
tailStart d) / tailShape d (y - tailStart d)`. -/
def profileSlope (d : TailData) (y : ℝ) : ℝ :=
  releaseSlope d (y - d.releaseStart) + tailShapeDeriv d (y - tailStart d) / tailShape d (y -
      tailStart d)

theorem finalAngular_hasDerivAt_on_release (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) :
    HasDerivAt (fun t => finalAngular d (t, eta))
      (finalAngular d (y, eta) * (profileSlope d y - 1 / 2)) y := by
  have hflat : d.flattenEnd < y := (releaseStart_gt_flattenEnd d).trans_le hy
  have hshape := ((tailShape_hasDerivAt d (y - tailStart d)).comp y
    ((hasDerivAt_id y).sub_const (tailStart d))).div_const (1 - d.rho)
  have hprod := (carrier_hasDerivAt d hy).mul hshape
  have heq : (fun t => finalAngular d (t, eta)) =ᶠ[𝓝 y]
      (fun t => carrier d t * (tailShape d (t - tailStart d) / (1 - d.rho))) := by
    filter_upwards [lt_mem_nhds hflat] with t ht
    exact finalAngular_uniform d eta ht.le
  have h' := hprod.congr_of_eventuallyEq heq
  convert! h' using 1
  rw [finalAngular_uniform d eta hflat.le]
  dsimp [profileSlope]
  have hf := (tailShape_pos d (y - tailStart d)).ne'
  have hd : 1 - d.rho ≠ 0 := by linarith [d.rho_lt_half]
  field_simp [hf, hd]; ring

theorem finalAngular_log_hasDerivAt_on_release (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) :
    HasDerivAt (fun t => Real.log (finalAngular d (t, eta)))
      (profileSlope d y - 1 / 2) y := by
  have hp := (finalAngular_pos d (y, eta)).ne'
  convert! (finalAngular_hasDerivAt_on_release d eta hy).log hp using 1
  field_simp

theorem profileSlope_tail (d : TailData) {y : ℝ} (hy : tailStart d ≤ y) :
    profileSlope d y = tailLogSlope d (y - tailStart d) := by
  have ht : d.rampEnd ≤ y - d.releaseStart := by
    dsimp [tailStart] at hy
    linarith [decayHold_pos d]
  unfold profileSlope tailLogSlope
  rw [releaseSlope_late d ht]

/-- The last four log units are available for the separate angular reset. -/
theorem uniformWait_gt_twentyseven (d : TailData) : 27 < d.uniformWait := by
  have h := Real.one_sub_inv_le_log_of_pos (one_div_pos.mpr d.core.lam_pos)
  simp only [one_div, inv_inv] at h
  dsimp [TailData.uniformWait]
  simp only [one_div]
  nlinarith [d.core.lam_lt]

theorem finalAngular_last_four (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart - 4 ≤ y) (hy' : y ≤ d.releaseStart) :
    finalAngular d (y, eta) = radialAmplitude d.core.P d.core.dropLength d.core.lam y / 2 := by
  apply finalAngular_uniform_wait d eta _ hy'
  have hw := uniformWait_gt_twentyseven d
  dsimp [TailData.releaseStart] at hy
  linarith


end NavierStokes.OutgoingTail
