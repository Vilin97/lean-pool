/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SchedulePressure
public import LeanPool.NavierStokesAndEuler.NavierStokes.UniformAngularReset
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# Uniform future-pressure bounds for the actual outgoing schedule

The estimates concern `OutgoingTail.finalAngular`, rather than a profile with an
assumed envelope.  Its clock decay is obtained directly from the prescribed
slopes, including the first unit ramp.  Angular derivatives are derivatives of
the actual improper integral.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff
open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail
open NavierStokes.SchedulePressure

namespace NavierStokes.FuturePressureBounds

/-- The logarithm of the clock factor, omitting its positive constant prefactor. -/
noncomputable def logClock (d : TailData) (y : ℝ) : ℝ :=
  logAmplitude d.core.dropLength d.core.lam y -
    sigma ((y - d.core.endpoint) / flattenLength) * Real.log 2 +
    releaseAdjustment d (y - d.releaseStart) +
    Real.log (tailShape d (y - tailStart d))

noncomputable def clockSlope (d : TailData) (y : ℝ) : ℝ :=
  slope d.core.dropLength d.core.lam y - 1 / 2 -
    deriv sigma ((y - d.core.endpoint) / flattenLength) / flattenLength * Real.log 2 +
    (releaseSlope d (y - d.releaseStart) + d.core.lam) +
    tailShapeDeriv d (y - tailStart d) / tailShape d (y - tailStart d)

theorem logClock_hasDerivAt (d : TailData) (y : ℝ) :
    HasDerivAt (logClock d) (clockSlope d y) y := by
  have hp := primitive_hasDerivAt
    (g := fun t => OutgoingSchedule.slope d.core.dropLength d.core.lam t - 1 / 2)
    ((slope_contDiff d.core.dropLength d.core.lam).continuous.sub continuous_const) y
  have hs := ((sigma_contDiff.differentiable (by simp)
    ((y - d.core.endpoint) / flattenLength)).hasDerivAt).comp y
      (((hasDerivAt_id y).sub_const d.core.endpoint).div_const flattenLength)
  have hr := (primitive_hasDerivAt
    (g := fun t => releaseSlope d t + d.core.lam)
    ((releaseSlope_contDiff d).continuous.add continuous_const)
      (y - d.releaseStart)).comp y ((hasDerivAt_id y).sub_const d.releaseStart)
  have ht0 : HasDerivAt (fun t => tailShape d (t - tailStart d))
      (tailShapeDeriv d (y - tailStart d)) y := by
    convert! (tailShape_hasDerivAt d (y - tailStart d)).comp y
      ((hasDerivAt_id y).sub_const (tailStart d)) using 1
    simp
  have ht := ht0.log (tailShape_pos d (y - tailStart d)).ne'
  convert! ((hp.sub (hs.mul_const (Real.log 2))).add hr).add ht using 1
  dsimp [logClock, clockSlope, logAmplitude, releaseAdjustment]
  ring

theorem logClock_differentiable (d : TailData) : Differentiable ℝ (logClock d) :=
  fun y => (logClock_hasDerivAt d y).differentiableAt

theorem clockSlope_le (d : TailData) (y : ℝ) : clockSlope d y ≤ 1 / 5 := by
  have hf : 0 ≤ deriv sigma ((y - d.core.endpoint) / flattenLength) /
      flattenLength * Real.log 2 := mul_nonneg
    (div_nonneg (sigma_derivative_nonneg _) flattenLength_pos.le)
    (Real.log_nonneg (by norm_num))
  have hs : slope d.core.dropLength d.core.lam y ≤ 3 / 5 := by
    have h0 := sigma_nonneg y
    have h1 := mul_nonneg d.core.lam_pos.le
      (sigma_nonneg (y - (d.core.dropLength + 1)))
    dsimp [OutgoingSchedule.slope]
    linarith
  have hr := (releaseSlope_bounds d (y - d.releaseStart)).2
  have ht := (tail_taper_log_derivative d (y - tailStart d)).2
  dsimp [clockSlope]
  linarith [d.core.lam_lt, d.h_pos]

theorem clockSlope_le_after_one (d : TailData) {y : ℝ} (hy : 1 ≤ y) :
    clockSlope d y ≤ -(2 / 5) := by
  have hf : 0 ≤ deriv sigma ((y - d.core.endpoint) / flattenLength) /
      flattenLength * Real.log 2 := mul_nonneg
    (div_nonneg (sigma_derivative_nonneg _) flattenLength_pos.le)
    (Real.log_nonneg (by norm_num))
  have hs : slope d.core.dropLength d.core.lam y ≤ 0 := by
    simp only [OutgoingSchedule.slope, sigma_one hy, sub_self, mul_zero, zero_sub]
    exact neg_nonpos.mpr (mul_nonneg d.core.lam_pos.le (sigma_nonneg _))
  have hr := (releaseSlope_bounds d (y - d.releaseStart)).2
  have ht := (tail_taper_log_derivative d (y - tailStart d)).2
  dsimp [clockSlope]
  linarith [d.core.lam_lt, d.h_pos]

theorem logClock_increment (d : TailData) {y t : ℝ} (hyt : y ≤ t) :
    logClock d t - logClock d y ≤ (1 / 5) * (t - y) := by
  exact image_sub_le_mul_sub_of_deriv_le (logClock_differentiable d)
    (fun z => by rw [(logClock_hasDerivAt d z).deriv]; exact clockSlope_le d z) hyt

theorem logClock_increment_after_one (d : TailData) {y t : ℝ}
    (hy : 1 ≤ y) (hyt : y ≤ t) :
    logClock d t - logClock d y ≤ -(2 / 5) * (t - y) := by
  apply (convex_Ici (1 : ℝ)).image_sub_le_mul_sub_of_deriv_le
    (logClock_differentiable d).continuous.continuousOn
    (logClock_differentiable d).differentiableOn
    (fun z hz => ?_) y hy t (hy.trans hyt) hyt
  rw [(logClock_hasDerivAt d z).deriv]
  exact clockSlope_le_after_one d (interior_subset hz)

/-- The first unit ramp costs at most `3/5` in the logarithmic envelope. -/
theorem logClock_future (d : TailData) {y t : ℝ} (hy : 0 ≤ y) (hyt : y ≤ t) :
    logClock d t - logClock d y ≤ 3 / 5 - (2 / 5) * (t - y) := by
  by_cases hy1 : 1 ≤ y
  · linarith [logClock_increment_after_one d hy1 hyt]
  · have hy1' : y ≤ 1 := le_of_not_ge hy1
    by_cases ht1 : t ≤ 1
    · linarith [logClock_increment d hyt]
    · have ht1' : 1 ≤ t := le_of_not_ge ht1
      linarith [logClock_increment d hy1', logClock_increment_after_one d le_rfl ht1']

theorem finalAngular_clock_eq (d : TailData) (y : ℝ) :
    finalAngular d (y, 0) =
      (d.core.P / (1 - d.rho)) * Real.exp (logClock d y) := by
  have he : Real.exp (logClock d y) =
      Real.exp (logAmplitude d.core.dropLength d.core.lam y) *
      Real.exp (sigma ((y - d.core.endpoint) / flattenLength) * (0 - Real.log 2)) *
      Real.exp (releaseAdjustment d (y - d.releaseStart)) *
      tailShape d (y - tailStart d) := by
    simp only [logClock, sub_eq_add_neg, Real.exp_add,
      Real.exp_log (tailShape_pos d _), zero_add, mul_neg]
  rw [he]
  simp only [finalAngular, flattened, angular, radialAmplitude, shape, flattenFactor,
    logShape, zero_pow (by norm_num : 2 ≠ 0), add_zero, inv_one, mul_one,
    Real.log_one]
  ring

theorem finalAngular_clock_ratio (d : TailData) (y t : ℝ) :
    finalAngular d (t, 0) = finalAngular d (y, 0) *
      Real.exp (logClock d t - logClock d y) := by
  rw [finalAngular_clock_eq d t, finalAngular_clock_eq d y,
    mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem clock_future_bound (d : TailData) {y t : ℝ} (hy : 0 ≤ y) (hyt : y ≤ t) :
    clockWeight d t ≤ clockWeight d y * Real.exp (6 / 5) *
      Real.exp (-(4 / 5) * (t - y)) := by
  have he := Real.exp_le_exp.mpr (show
    2 * (logClock d t - logClock d y) ≤ 6 / 5 - (4 / 5) * (t - y) by
      linarith [logClock_future d hy hyt])
  calc
    clockWeight d t = clockWeight d y * Real.exp (2 * (logClock d t - logClock d y)) := by
      rw [clockWeight, finalAngular_clock_ratio d y t, mul_pow, clockWeight]
      rw [show 2 * (logClock d t - logClock d y) =
        (logClock d t - logClock d y) + (logClock d t - logClock d y) by ring,
        Real.exp_add, pow_two]
      ring
    _ ≤ clockWeight d y * Real.exp (6 / 5 - (4 / 5) * (t - y)) :=
      mul_le_mul_of_nonneg_left he (clockWeight_pos d y).le
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring_nf

theorem future_clock_integral_le (d : TailData) {y : ℝ} (hy : 0 ≤ y) :
    (∫ t in Ioi y, clockWeight d t) ≤
      (5 / 4) * Real.exp (6 / 5) * clockWeight d y := by
  have hi := (TailEnergyBounds.integrableOn_shift_exp
    (by norm_num : (0 : ℝ) < 4 / 5) y).const_mul
      (clockWeight d y * Real.exp (6 / 5))
  have hb := setIntegral_mono_on (clockWeight_integrable d).integrableOn hi
    measurableSet_Ioi (fun t ht => clock_future_bound d hy ht.le)
  rw [integral_const_mul, TailEnergyBounds.integral_shift_exp
    (by norm_num : (0 : ℝ) < 4 / 5) y] at hb
  convert! hb using 1
  ring

theorem angular_square_le_clock (d : TailData) (t eta : ℝ) :
    finalAngular d (t, eta) ^ 2 ≤ clockWeight d t := by
  rw [angular_square_factorization]
  exact mul_le_of_le_one_right (clockWeight_pos d t).le
    (PressureDatum.kernel_le_one (shapeExponent_bounds d t).1 eta)

theorem clock_le_four_angular_square (d : TailData) (y : ℝ) {eta : ℝ}
    (heta : |eta| ≤ 1) : clockWeight d y ≤ 4 * finalAngular d (y, eta) ^ 2 := by
  have hs : eta ^ 2 ≤ 1 := by nlinarith [sq_abs eta, abs_nonneg eta]
  have hk : (1 / 4 : ℝ) ≤ PressureDatum.kernel (shapeExponent d y) eta := by
    apply le_trans _ (PressureDatum.kernel_antitone (shapeExponent_bounds d y).2 eta)
    rw [PressureDatum.kernel_one]
    have hi : (1 / 2 : ℝ) ≤ (1 + eta ^ 2)⁻¹ := by
      have hdiv : (1 : ℝ) / 2 ≤ 1 / (1 + eta ^ 2) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      simpa only [one_div] using hdiv
    nlinarith [sq_nonneg ((1 + eta ^ 2)⁻¹ - 1 / 2)]
  rw [angular_square_factorization]
  nlinarith [mul_le_mul_of_nonneg_left hk (clockWeight_pos d y).le]

/-- A single numerical constant, independent of every schedule parameter. -/
noncomputable def envelopeConstant : ℝ := 5 * Real.exp (6 / 5)

theorem envelopeConstant_pos : 0 < envelopeConstant := by
  unfold envelopeConstant
  positivity

theorem future_square_integral_le (d : TailData) {y eta : ℝ}
    (hy : 0 ≤ y) (heta : |eta| ≤ 1) :
    (∫ t in Ioi y, finalAngular d (t, eta) ^ 2) ≤
      envelopeConstant * finalAngular d (y, eta) ^ 2 := by
  calc
    _ ≤ ∫ t in Ioi y, clockWeight d t := setIntegral_mono_on
      (angular_square_integrable d eta).integrableOn
      (clockWeight_integrable d).integrableOn measurableSet_Ioi
      (fun t _ => angular_square_le_clock d t eta)
    _ ≤ (5 / 4) * Real.exp (6 / 5) * clockWeight d y := future_clock_integral_le d hy
    _ ≤ envelopeConstant * finalAngular d (y, eta) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left (clock_le_four_angular_square d y heta)
        (show 0 ≤ (5 / 4 : ℝ) * Real.exp (6 / 5) by positivity)
      convert! h using 1
      unfold envelopeConstant
      ring

/-- The canonical pressure from the actual future of the clean outgoing field. -/
noncomputable def Pi (d : TailData) (y eta : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * ∫ t in Ioi y, finalAngular d (t, eta) ^ 2

/-- The moment indexed by the nonnegative shape exponent. -/
noncomputable def futureMass (d : TailData) (y : ℝ) (n : ℕ) (eta : ℝ) : ℝ :=
  ∫ t in Ioi y, shapeExponent d t ^ n * finalAngular d (t, eta) ^ 2

noncomputable def futureWeight (d : TailData) (y : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (Ioi y).indicator (clockWeight d) t * shapeExponent d t ^ n

theorem futureWeight_admissible (d : TailData) (y : ℝ) (n : ℕ) :
    PressureDatum.Admissible (futureWeight d y n) (shapeExponent d) 1 := by
  induction n with
  | zero =>
    have h : PressureDatum.Admissible ((Ioi y).indicator (clockWeight d))
        (shapeExponent d) 1 := {
      cap_nonneg := by norm_num
      integrable := (clockWeight_integrable d).indicator measurableSet_Ioi
      nonneg := fun t => indicator_nonneg (fun t _ => (clockWeight_pos d t).le) t
      measurable := (shapeExponent_contDiff d).continuous.measurable
      exponent_nonneg := fun t => (shapeExponent_bounds d t).1
      exponent_le := fun t => (shapeExponent_bounds d t).2 }
    convert! h using 1
    funext t
    simp only [futureWeight, pow_zero, mul_one]
  | succ n hn =>
    convert! PressureDatum.exponent_weight_admissible hn using 1
    funext t
    simp only [futureWeight, pow_succ, mul_assoc]

theorem futureMass_eq (d : TailData) (y : ℝ) (n : ℕ) (eta : ℝ) :
    futureMass d y n eta =
      ∫ t, futureWeight d y n t * PressureDatum.kernel (shapeExponent d t) eta := by
  rw [futureMass, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Ioi y
  · simp only [futureWeight, indicator_of_mem ht, angular_square_factorization]
    ring
  · simp only [futureWeight, indicator_of_notMem ht, zero_mul]

theorem futureMass_pressure (d : TailData) (y : ℝ) (n : ℕ) :
    futureMass d y n = fun eta =>
      -2 * PressureDatum.pressure (futureWeight d y n) (shapeExponent d) eta := by
  funext eta
  rw [futureMass_eq]
  unfold PressureDatum.pressure
  ring

theorem Pi_eq_pressure (d : TailData) (y : ℝ) :
    Pi d y = PressureDatum.pressure (futureWeight d y 0) (shapeExponent d) := by
  funext eta
  have h := futureMass_eq d y 0 eta
  simp only [futureMass, pow_zero, one_mul] at h
  rw [Pi, h]
  rfl

theorem Pi_contDiff_eta (d : TailData) (y : ℝ) : ContDiff ℝ ∞ (Pi d y) := by
  rw [Pi_eq_pressure]
  exact PressureDatum.pressure_contDiff (futureWeight_admissible d y 0)

theorem futureMass_nonneg (d : TailData) (y : ℝ) (n : ℕ) (eta : ℝ) :
    0 ≤ futureMass d y n eta := by
  apply integral_nonneg
  intro t
  exact mul_nonneg (pow_nonneg (shapeExponent_bounds d t).1 n) (sq_nonneg _)

theorem futureMass_le_zero (d : TailData) (y : ℝ) (n : ℕ) (eta : ℝ) :
    futureMass d y n eta ≤ futureMass d y 0 eta := by
  rw [futureMass_eq, futureMass_eq]
  apply integral_mono
    (PressureDatum.integrable_kernel (futureWeight_admissible d y n) eta)
    (PressureDatum.integrable_kernel (futureWeight_admissible d y 0) eta)
  intro t
  have ha := pow_le_one₀ (n := n) (shapeExponent_bounds d t).1 (shapeExponent_bounds d t).2
  have hi : 0 ≤ (Ioi y).indicator (clockWeight d) t :=
    indicator_nonneg (fun t _ => (clockWeight_pos d t).le) t
  simp only [futureWeight, pow_zero, mul_one]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hi ha)
    (PressureDatum.kernel_pos _ _).le

theorem Pi_nonpos (d : TailData) (y eta : ℝ) : Pi d y eta ≤ 0 := by
  rw [Pi_eq_pressure]
  exact PressureDatum.pressure_nonpos (futureWeight_admissible d y 0) eta

theorem Pi_abs_eq (d : TailData) (y eta : ℝ) :
    |Pi d y eta| = (1 / 2) * futureMass d y 0 eta := by
  rw [abs_of_nonpos (Pi_nonpos d y eta)]
  simp only [Pi, futureMass, pow_zero, one_mul]
  ring

theorem Pi_abs_le (d : TailData) {y eta : ℝ} (hy : 0 ≤ y) (heta : |eta| ≤ 1) :
    |Pi d y eta| ≤ (envelopeConstant / 2) * finalAngular d (y, eta) ^ 2 := by
  rw [Pi_abs_eq]
  have h := mul_le_mul_of_nonneg_left (future_square_integral_le d hy heta)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
  simp only [futureMass, pow_zero, one_mul]
  convert! h using 1
  ring

theorem futureMass_hasDerivAt (d : TailData) (y : ℝ) (n : ℕ) (eta : ℝ) :
    HasDerivAt (futureMass d y n)
      ((-4 * eta / (1 + eta ^ 2)) * futureMass d y (n + 1) eta) eta := by
  have hI : (∫ t, futureWeight d y n t * shapeExponent d t *
      PressureDatum.kernel (shapeExponent d t) eta) = futureMass d y (n + 1) eta := by
    rw [futureMass_eq]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [futureWeight, pow_succ]
    ring
  rw [futureMass_pressure]
  convert! (PressureDatum.hasDerivAt_pressure (futureWeight_admissible d y n) eta).const_mul
    (-2) using 1
  rw [hI]
  ring

theorem Pi_hasDerivAt_eta (d : TailData) (y eta : ℝ) :
    HasDerivAt (Pi d y)
      ((2 * eta / (1 + eta ^ 2)) * futureMass d y 1 eta) eta := by
  rw [Pi_eq_pressure]
  convert! PressureDatum.hasDerivAt_pressure (futureWeight_admissible d y 0) eta using 1
  congr 1
  rw [futureMass_eq]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [futureWeight, pow_zero, pow_one, mul_one]

theorem Pi_deriv_eta (d : TailData) (y eta : ℝ) :
    deriv (Pi d y) eta = (2 * eta / (1 + eta ^ 2)) * futureMass d y 1 eta :=
  (Pi_hasDerivAt_eta d y eta).deriv

theorem Pi_second_hasDerivAt_eta (d : TailData) (y eta : ℝ) :
    HasDerivAt (deriv (Pi d y))
      ((2 * (1 - eta ^ 2) / (1 + eta ^ 2) ^ 2) * futureMass d y 1 eta -
        (8 * eta ^ 2 / (1 + eta ^ 2) ^ 2) * futureMass d y 2 eta) eta := by
  have hden : 1 + eta ^ 2 ≠ 0 := by positivity
  have hk : HasDerivAt (fun q : ℝ => 2 * q / (1 + q ^ 2))
      (2 * (1 - eta ^ 2) / (1 + eta ^ 2) ^ 2) eta := by
    convert! ((hasDerivAt_id eta).const_mul 2).fun_div
      ((hasDerivAt_const eta (1 : ℝ)).fun_add ((hasDerivAt_id eta).fun_pow 2)) hden using 1
    dsimp only [id]
    ring
  have hfun : deriv (Pi d y) = fun q =>
      (2 * q / (1 + q ^ 2)) * futureMass d y 1 q := funext (Pi_deriv_eta d y)
  rw [hfun]
  convert! hk.fun_mul (futureMass_hasDerivAt d y 1 eta) using 1
  norm_num
  field_simp ; ring

theorem Pi_second_deriv_eta (d : TailData) (y eta : ℝ) :
    deriv (deriv (Pi d y)) eta =
      (2 * (1 - eta ^ 2) / (1 + eta ^ 2) ^ 2) * futureMass d y 1 eta -
        (8 * eta ^ 2 / (1 + eta ^ 2) ^ 2) * futureMass d y 2 eta :=
  (Pi_second_hasDerivAt_eta d y eta).deriv

/-- The angular derivative retains its factor `|eta|` on the entire real axis. -/
theorem Pi_deriv_abs_le_pressure (d : TailData) (y eta : ℝ) :
    |deriv (Pi d y) eta| ≤ 4 * |eta| * |Pi d y eta| := by
  have hden : 0 < 1 + eta ^ 2 := by positivity
  have hc : |2 * eta / (1 + eta ^ 2)| ≤ 2 * |eta| := by
    rw [abs_div, abs_mul, abs_of_pos hden]
    norm_num
    apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg eta, abs_nonneg eta,
      mul_nonneg (sq_nonneg eta) (abs_nonneg eta)]
  rw [Pi_deriv_eta, abs_mul, abs_of_nonneg (futureMass_nonneg d y 1 eta), Pi_abs_eq]
  calc
    _ ≤ (2 * |eta|) * futureMass d y 0 eta :=
      mul_le_mul hc (futureMass_le_zero d y 1 eta)
        (futureMass_nonneg d y 1 eta) (by positivity)
    _ = _ := by ring

theorem Pi_deriv_abs_le (d : TailData) {y eta : ℝ}
    (hy : 0 ≤ y) (heta : |eta| ≤ 1) :
    |deriv (Pi d y) eta| ≤
      (2 * envelopeConstant) * |eta| * finalAngular d (y, eta) ^ 2 := by
  apply (Pi_deriv_abs_le_pressure d y eta).trans
  have h := mul_le_mul_of_nonneg_left (Pi_abs_le d hy heta)
    (show 0 ≤ 4 * |eta| by positivity)
  convert! h using 1
  ring

theorem Pi_second_deriv_abs_le_pressure (d : TailData) (y : ℝ) {eta : ℝ}
    (heta : |eta| ≤ 1) :
    |deriv (deriv (Pi d y)) eta| ≤ 20 * |Pi d y eta| := by
  have hs : eta ^ 2 ≤ 1 := by nlinarith [sq_abs eta, abs_nonneg eta]
  have hsub : 0 ≤ 1 - eta ^ 2 := sub_nonneg.mpr hs
  have hsq : (1 : ℝ) ≤ (1 + eta ^ 2) ^ 2 := by nlinarith [sq_nonneg eta]
  have hpos : 0 < (1 + eta ^ 2) ^ 2 := by positivity
  have h1 : |2 * (1 - eta ^ 2) / (1 + eta ^ 2) ^ 2| ≤ 2 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (1 - eta ^ 2) / (1 + eta ^ 2) ^ 2)]
    apply (div_le_iff₀ hpos).mpr
    nlinarith [sq_nonneg eta]
  have h2 : |8 * eta ^ 2 / (1 + eta ^ 2) ^ 2| ≤ 8 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 8 * eta ^ 2 / (1 + eta ^ 2) ^ 2)]
    apply (div_le_iff₀ hpos).mpr
    nlinarith
  rw [Pi_second_deriv_eta]
  calc
    _ ≤ |(2 * (1 - eta ^ 2) / (1 + eta ^ 2) ^ 2) * futureMass d y 1 eta| +
        |(8 * eta ^ 2 / (1 + eta ^ 2) ^ 2) * futureMass d y 2 eta| := abs_sub _ _
    _ ≤ 2 * futureMass d y 0 eta + 8 * futureMass d y 0 eta := by
      rw [abs_mul, abs_mul, abs_of_nonneg (futureMass_nonneg d y 1 eta),
        abs_of_nonneg (futureMass_nonneg d y 2 eta)]
      exact add_le_add
        (mul_le_mul h1 (futureMass_le_zero d y 1 eta) (futureMass_nonneg d y 1 eta) (by norm_num))
        (mul_le_mul h2 (futureMass_le_zero d y 2 eta) (futureMass_nonneg d y 2 eta) (by norm_num))
    _ = _ := by rw [Pi_abs_eq]; ring

theorem Pi_second_deriv_abs_le (d : TailData) {y eta : ℝ}
    (hy : 0 ≤ y) (heta : |eta| ≤ 1) :
    |deriv (deriv (Pi d y)) eta| ≤
      (10 * envelopeConstant) * finalAngular d (y, eta) ^ 2 := by
  apply (Pi_second_deriv_abs_le_pressure d y heta).trans
  have h := mul_le_mul_of_nonneg_left (Pi_abs_le d hy heta) (show (0 : ℝ) ≤ 20 by norm_num)
  convert! h using 1
  ring

/-- An exact finite-history expression, valid even when the endpoint is negative. -/
theorem Pi_increment (d : TailData) (a y eta : ℝ) :
    Pi d y eta = Pi d a eta + (1 / 2) * ∫ t in a..y, finalAngular d (t, eta) ^ 2 := by
  have hi := angular_square_integrable d eta
  have ha := intervalIntegral.integral_Iic_add_Ioi (b := a) hi.integrableOn hi.integrableOn
  have hy := intervalIntegral.integral_Iic_add_Ioi (b := y) hi.integrableOn hi.integrableOn
  have hd := intervalIntegral.integral_Iic_sub_Iic (a := a) (b := y)
    hi.integrableOn hi.integrableOn
  unfold Pi
  linarith

theorem Pi_hasDerivAt_y (d : TailData) (y eta : ℝ) :
    HasDerivAt (fun t => Pi d t eta) ((1 / 2) * finalAngular d (y, eta) ^ 2) y := by
  have hf : Continuous (fun t => finalAngular d (t, eta) ^ 2) :=
    (((finalAngular_contDiff d).continuous.comp
      (continuous_id.prodMk continuous_const)).pow 2)
  have heq : (fun t => Pi d t eta) = fun t =>
      Pi d 0 eta + (1 / 2) * primitive (fun v => finalAngular d (v, eta) ^ 2) t := by
    funext t
    exact Pi_increment d 0 t eta
  rw [heq]
  exact ((primitive_hasDerivAt hf y).const_mul (1 / 2)).const_add _

theorem Pi_deriv_y (d : TailData) (y eta : ℝ) :
    deriv (fun t => Pi d t eta) y = (1 / 2) * finalAngular d (y, eta) ^ 2 :=
  (Pi_hasDerivAt_y d y eta).deriv

theorem Pi_eq_axisPressure_add (d : TailData) (y eta : ℝ) :
    Pi d y eta = axisPressure d eta +
      (1 / 2) * ∫ t in Iic y, finalAngular d (t, eta) ^ 2 := by
  have hi := angular_square_integrable d eta
  have hsum := intervalIntegral.integral_Iic_add_Ioi (b := y)
    hi.integrableOn hi.integrableOn
  unfold Pi axisPressure
  linarith

theorem ideal_left_integral (d : TailData) (eta : ℝ) :
    (∫ t in Iic (0 : ℝ), finalAngular d (t, eta) ^ 2) =
      5 * d.core.P ^ 2 * shape eta ^ 2 := by
  calc
    _ = ∫ t in Iic (0 : ℝ),
        (d.core.P ^ 2 * Real.exp ((1 / 5 : ℝ) * t)) * shape eta ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      rw [angular_square_factorization, clockWeight_ideal d ht,
        shapeExponent_ideal d ht, PressureDatum.kernel_one]
      rfl
    _ = _ := by rw [integral_mul_const, PressureDatum.ideal_prefix_mass]

theorem Pi_zero (d : TailData) (eta : ℝ) :
    Pi d 0 eta = axisPressure d eta + (5 / 2) * d.core.P ^ 2 * shape eta ^ 2 := by
  rw [Pi_eq_axisPressure_add, ideal_left_integral]
  ring

/-- The exact bridge to the initial ramp/drop pressure history. -/
theorem Pi_eq_radial_history (d : TailData) {y : ℝ}
    (hy : 0 ≤ y) (hyend : y ≤ d.core.endpoint) (eta : ℝ) :
    Pi d y eta = axisPressure d eta + shape eta ^ 2 *
      ((5 / 2) * d.core.P ^ 2 + (1 / 2) *
        ∫ t in (0 : ℝ)..y, radialAmplitude d.core.P d.core.dropLength d.core.lam t ^ 2) := by
  have hint : (∫ t in (0 : ℝ)..y, finalAngular d (t, eta) ^ 2) =
      (∫ t in (0 : ℝ)..y,
        radialAmplitude d.core.P d.core.dropLength d.core.lam t ^ 2) * shape eta ^ 2 := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t ht
    have htend : t ≤ d.core.endpoint := ((uIcc_of_le hy ▸ ht).2).trans hyend
    dsimp only
    rw [finalAngular_before d eta htend]
    simp only [angular, mul_pow]
  rw [Pi_increment d 0 y eta, Pi_zero, hint]
  ring

/-- A future-supported edit with zero total integral has zero future integral. -/
theorem future_integral_unchanged {f g : ℝ → ℝ} {y : ℝ}
    (hf : Integrable f) (hg : Integrable g)
    (hzero : (∫ t, f t - g t) = 0) (hbefore : ∀ t ≤ y, f t = g t) :
    (∫ t in Ioi y, f t) = ∫ t in Ioi y, g t := by
  have heq : (Ioi y).indicator (fun t => f t - g t) = fun t => f t - g t := by
    funext t
    by_cases ht : t ∈ Ioi y
    · exact indicator_of_mem ht _
    · have hty : t ≤ y := le_of_not_gt ht
      simp only [indicator_of_notMem ht, hbefore t hty, sub_self]
  have hz : (∫ t in Ioi y, f t - g t) = 0 := by
    rw [← integral_indicator measurableSet_Ioi, heq]
    exact hzero
  rw [integral_sub hf.integrableOn hg.integrableOn] at hz
  exact sub_eq_zero.mp hz

theorem corrected_square_integrable {d : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness d K) (eta : ℝ) :
    Integrable (fun t => UniformAngularReset.correctedAngular d w.coefficients (t, eta) ^ 2) := by
  have hc : Continuous (fun t =>
      UniformAngularReset.correctedAngular d w.coefficients (t, eta) ^ 2) :=
    (((UniformAngularReset.correctedAngular_contDiff d w.coefficients w.smooth).continuous.comp
      (continuous_id.prodMk continuous_const)).pow 2)
  apply ((angular_square_integrable d eta).const_mul (9 / 4 : ℝ)).mono'
    hc.aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hb := abs_le.mp (w.small_jets eta (t - UniformAngularReset.correctionCenter d)).1
  have hr : (1 + AngularMomentReset.relative (w.coefficients eta)
      (t - UniformAngularReset.correctionCenter d)) ^ 2 ≤ 9 / 4 := by
    nlinarith
  simp only [UniformAngularReset.correctedAngular, mul_pow]
  exact (mul_le_mul_of_nonneg_left hr (sq_nonneg _)).trans_eq (mul_comm _ _)

/-- The actual pressure-neutral angular reset may be omitted before its support. -/
theorem corrected_future_integral_eq {d : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness d K) {y : ℝ}
    (hy : y ≤ d.releaseStart - 4) (eta : ℝ) :
    (∫ t in Ioi y, UniformAngularReset.correctedAngular d w.coefficients (t, eta) ^ 2) =
      ∫ t in Ioi y, finalAngular d (t, eta) ^ 2 := by
  apply future_integral_unchanged (corrected_square_integrable w eta)
    (angular_square_integrable d eta) (w.pressure_neutral eta)
  intro t ht
  rw [UniformAngularReset.correctedAngular_unchanged d w.coefficients eta]
  intro hmem
  exact (not_lt_of_ge (ht.trans hy)) hmem.1

theorem corrected_future_pressure_eq {d : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness d K) {y : ℝ}
    (hy : y ≤ d.releaseStart - 4) (eta : ℝ) :
    -(1 / 2 : ℝ) *
      (∫ t in Ioi y, UniformAngularReset.correctedAngular d w.coefficients (t, eta) ^ 2) =
      Pi d y eta := by
  rw [corrected_future_integral_eq w hy eta]
  rfl

/-- All three estimates use numerical constants uniform in `lambda`, `h`, and
the other choices in the constructed schedule. -/
theorem uniform_pressure_bounds (d : TailData) {y eta : ℝ}
    (hy : 0 ≤ y) (heta : |eta| ≤ 1) :
    |Pi d y eta| ≤ (envelopeConstant / 2) * finalAngular d (y, eta) ^ 2 ∧
    |deriv (Pi d y) eta| ≤
      (2 * envelopeConstant) * |eta| * finalAngular d (y, eta) ^ 2 ∧
    |deriv (deriv (Pi d y)) eta| ≤
      (10 * envelopeConstant) * finalAngular d (y, eta) ^ 2 :=
  ⟨Pi_abs_le d hy heta, Pi_deriv_abs_le d hy heta, Pi_second_deriv_abs_le d hy heta⟩

end NavierStokes.FuturePressureBounds
