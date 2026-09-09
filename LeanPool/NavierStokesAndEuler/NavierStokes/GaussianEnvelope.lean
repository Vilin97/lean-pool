/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PulseGrowth
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Gaussian bounds from a decreasing instantaneous rate

The integral is oriented: a point before the midpoint reverses the integration
limits.  The main theorem proves the same quadratic bounds on both sides,
under local differentiability and derivative bounds on a convex domain.
-/

@[expose] public section


namespace NavierStokes.GaussianEnvelope

open Set MeasureTheory

/-- Envelope normalized to one at the midpoint. -/
noncomputable def envelope (rate : ℝ → ℝ) (midpoint time : ℝ) : ℝ :=
  Real.exp (∫ x in midpoint..time, rate x)

/-- Exact integral of a centered affine rate, for either order of the endpoints. -/
theorem integral_centered_linear (k midpoint a b : ℝ) :
    (∫ x in a..b, k * (x - midpoint)) =
      k * ((b - midpoint) ^ 2 - (a - midpoint) ^ 2) / 2 := by
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub (f := fun x : ℝ => x)
    (g := fun _ : ℝ => midpoint)
    (continuous_id.intervalIntegrable a b) (continuous_const.intervalIntegrable a b)]
  rw [integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- Local derivative bounds integrate to a quadratic sandwich around a zero of the rate.

No ordering of `midpoint` and `time` is assumed.  In the backwards case, both the
pointwise comparison and the oriented integral reverse order.
-/
theorem integral_quadratic_bounds {D : Set ℝ} {rate : ℝ → ℝ}
    {midpoint time lower upper : ℝ} (hD : Convex ℝ D)
    (hcont : ContinuousOn rate D)
    (hdiff : DifferentiableOn ℝ rate (interior D))
    (hderiv : ∀ x ∈ interior D, lower ≤ deriv rate x ∧ deriv rate x ≤ upper)
    (hm : midpoint ∈ D) (ht : time ∈ D) (hzero : rate midpoint = 0) :
    lower * (time - midpoint) ^ 2 / 2 ≤ (∫ x in midpoint..time, rate x) ∧
      (∫ x in midpoint..time, rate x) ≤ upper * (time - midpoint) ^ 2 / 2 := by
  have hlo := hD.mul_sub_le_image_sub_of_le_deriv hcont hdiff
    (fun x hx => (hderiv x hx).1)
  have hhi := hD.image_sub_le_mul_sub_of_deriv_le hcont hdiff
    (fun x hx => (hderiv x hx).2)
  have hlin (k : ℝ) : Continuous (fun x : ℝ => k * (x - midpoint)) :=
    continuous_const.mul (continuous_id.sub continuous_const)
  rcases le_total midpoint time with hmt | htm
  · have hsub : Icc midpoint time ⊆ D := hD.ordConnected.out hm ht
    have hint : IntervalIntegrable rate volume midpoint time :=
      (hcont.mono hsub).intervalIntegrable_of_Icc hmt
    have hl : (∫ x in midpoint..time, lower * (x - midpoint)) ≤
        ∫ x in midpoint..time, rate x := by
      apply intervalIntegral.integral_mono_on hmt
        ((hlin lower).intervalIntegrable midpoint time) hint
      intro x hx
      simpa only [hzero, sub_zero] using hlo midpoint hm x (hsub hx) hx.1
    have hu : (∫ x in midpoint..time, rate x) ≤
        ∫ x in midpoint..time, upper * (x - midpoint) := by
      apply intervalIntegral.integral_mono_on hmt hint
        ((hlin upper).intervalIntegrable midpoint time)
      intro x hx
      simpa only [hzero, sub_zero] using hhi midpoint hm x (hsub hx) hx.1
    rw [integral_centered_linear] at hl hu
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0), sub_zero] using And.intro hl hu
  · have hsub : Icc time midpoint ⊆ D := hD.ordConnected.out ht hm
    have hint : IntervalIntegrable rate volume time midpoint :=
      (hcont.mono hsub).intervalIntegrable_of_Icc htm
    have hl : (∫ x in time..midpoint, upper * (x - midpoint)) ≤
        ∫ x in time..midpoint, rate x := by
      apply intervalIntegral.integral_mono_on htm
        ((hlin upper).intervalIntegrable time midpoint) hint
      intro x hx
      have h := hhi x (hsub hx) midpoint hm hx.2
      rw [hzero] at h
      nlinarith
    have hu : (∫ x in time..midpoint, rate x) ≤
        ∫ x in time..midpoint, lower * (x - midpoint) := by
      apply intervalIntegral.integral_mono_on htm hint
        ((hlin lower).intervalIntegrable time midpoint)
      intro x hx
      have h := hlo x (hsub hx) midpoint hm hx.2
      rw [hzero] at h
      nlinarith
    rw [integral_centered_linear] at hl hu
    rw [intervalIntegral.integral_symm time midpoint]
    constructor <;> nlinarith

/-- Gaussian upper and lower bounds with the manuscript's slot-length normalization. -/
theorem gaussian_envelope_bounds {D : Set ℝ} {rate : ℝ → ℝ}
    {midpoint time c C ell : ℝ} (hD : Convex ℝ D)
    (hcont : ContinuousOn rate D)
    (hdiff : DifferentiableOn ℝ rate (interior D))
    (hderiv : ∀ x ∈ interior D,
      -C / ell ≤ deriv rate x ∧ deriv rate x ≤ -c / ell)
    (hm : midpoint ∈ D) (ht : time ∈ D) (hzero : rate midpoint = 0) :
    Real.exp (-C * (time - midpoint) ^ 2 / (2 * ell)) ≤ envelope rate midpoint time ∧
      envelope rate midpoint time ≤ Real.exp (-c * (time - midpoint) ^ 2 / (2 * ell)) := by
  obtain ⟨hl, hu⟩ := integral_quadratic_bounds hD hcont hdiff hderiv hm ht hzero
  constructor
  · apply Real.exp_le_exp.2
    convert! hl using 1
    ring
  · apply Real.exp_le_exp.2
    convert! hu using 1
    ring

@[simp] theorem envelope_at_midpoint (rate : ℝ → ℝ) (midpoint : ℝ) :
    envelope rate midpoint midpoint = 1 := by
  simp [envelope]

theorem envelope_pos (rate : ℝ → ℝ) (midpoint time : ℝ) :
    0 < envelope rate midpoint time := Real.exp_pos _

/-- For positive `c` and slot length the midpoint is the unique maximum on the domain. -/
theorem envelope_lt_one_away_from_midpoint {D : Set ℝ} {rate : ℝ → ℝ}
    {midpoint time c C ell : ℝ} (hD : Convex ℝ D)
    (hcont : ContinuousOn rate D)
    (hdiff : DifferentiableOn ℝ rate (interior D))
    (hderiv : ∀ x ∈ interior D,
      -C / ell ≤ deriv rate x ∧ deriv rate x ≤ -c / ell)
    (hm : midpoint ∈ D) (ht : time ∈ D) (hzero : rate midpoint = 0)
    (hc : 0 < c) (hell : 0 < ell) (hne : time ≠ midpoint) :
    envelope rate midpoint time < 1 := by
  have hu := (gaussian_envelope_bounds hD hcont hdiff hderiv hm ht hzero).2
  have hsq : 0 < (time - midpoint) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.2 hne)
  have he : -c * (time - midpoint) ^ 2 / (2 * ell) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hsq)
      (mul_pos (by norm_num) hell)
  exact lt_of_le_of_lt hu (by simpa only [Real.exp_zero] using Real.exp_lt_exp.2 he)

/-- Derivative of the manuscript's scalar reference rate in its magnitude variable. -/
noncomputable def referenceSlope (lam u s : ℝ) : ℝ :=
  -lam * s / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)) -
    2 * lam * s / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2))

/-- The displayed rate derivative is an actual derivative, including at zero. -/
theorem hasDerivAt_netGrowth (lam u s : ℝ) :
    HasDerivAt (PulseGrowth.netGrowth lam u) (referenceSlope lam u s) s := by
  have hp : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_id s).pow 2).const_add 1
  have hr := hp.sqrt (ne_of_gt (PulseGrowth.one_add_sq_pos s))
  have hd := ((hasDerivAt_const s lam).div hr (ne_of_gt (PulseGrowth.radius_pos s))).sub
    ((hp.const_mul lam).div_const ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2)))
  convert! hd using 1
  unfold referenceSlope
  rw [Real.sq_sqrt (le_of_lt (PulseGrowth.one_add_sq_pos s))]
  field_simp [ne_of_gt (PulseGrowth.radius_pos s),
    ne_of_gt (PulseGrowth.one_add_sq_pos s),
    ne_of_gt (PulseGrowth.dampingDenominator_pos u)]
  ring

/-- A positive lower bound on the magnitude of the rate derivative in the slot. -/
noncomputable def referenceMinSlope (lam u : ℝ) : ℝ :=
  lam * u / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2))

/-- An upper bound on the magnitude of the rate derivative in the slot. -/
noncomputable def referenceMaxSlope (lam u : ℝ) : ℝ :=
  3 * lam * u / 2 + 3 * lam * u / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2))

theorem referenceMinSlope_pos {lam u : ℝ} (hlam : 0 < lam) (hu : 0 < u) :
    0 < referenceMinSlope lam u := by
  unfold referenceMinSlope
  exact div_pos (mul_pos hlam hu) (PulseGrowth.dampingDenominator_pos u)

theorem referenceMaxSlope_pos {lam u : ℝ} (hlam : 0 < lam) (hu : 0 < u) :
    0 < referenceMaxSlope lam u := by
  unfold referenceMaxSlope
  exact add_pos (div_pos (mul_pos (mul_pos (by norm_num) hlam) hu) (by norm_num))
    (div_pos (mul_pos (mul_pos (by norm_num) hlam) hu) (PulseGrowth.dampingDenominator_pos u))

/-- Explicit, slot-length-independent bounds on the reference derivative. -/
theorem referenceSlope_bounds {lam u s : ℝ} (hlam : 0 < lam) (hu : 0 < u)
    (hs : s ∈ Icc (u / 2) (3 * u / 2)) :
    -referenceMaxSlope lam u ≤ referenceSlope lam u s ∧
      referenceSlope lam u s ≤ -referenceMinSlope lam u := by
  have hspos : 0 < s := by linarith [hs.1]
  have hn : 0 ≤ lam * s := le_of_lt (mul_pos hlam hspos)
  have hS : 1 ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg s]
  have hroot : 1 ≤ Real.sqrt (1 + s ^ 2) := Real.one_le_sqrt.2 hS
  have hden : 1 ≤ (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) := by
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) :=
        mul_le_mul hS hroot (by norm_num) (le_of_lt (PulseGrowth.one_add_sq_pos s))
  have hfirst : lam * s / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)) ≤ lam * s := by
    apply (div_le_iff₀ (PulseGrowth.dampingDenominator_pos s)).2
    nlinarith [mul_le_mul_of_nonneg_left hden hn]
  have hfirst0 : 0 ≤ lam * s / ((1 + s ^ 2) * Real.sqrt (1 + s ^ 2)) :=
    div_nonneg hn (le_of_lt (PulseGrowth.dampingDenominator_pos s))
  have hfirstUpper : lam * s ≤ 3 * lam * u / 2 := by nlinarith [hs.2]
  have hsecondUpper : 2 * lam * s / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2)) ≤
      3 * lam * u / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2)) := by
    apply (div_le_div_iff_of_pos_right (PulseGrowth.dampingDenominator_pos u)).2
    nlinarith [hs.2]
  have hsecondLower : lam * u / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2)) ≤
      2 * lam * s / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2)) := by
    apply (div_le_div_iff_of_pos_right (PulseGrowth.dampingDenominator_pos u)).2
    nlinarith [hs.1]
  unfold referenceSlope referenceMaxSlope referenceMinSlope
  rw [neg_mul, neg_div]
  constructor <;> linarith

/-- The reference rate expressed in slot time. -/
noncomputable def referenceRate (lam u ell time : ℝ) : ℝ :=
  PulseGrowth.netGrowth lam u (PulseGrowth.slotMagnitude u ell time)

theorem hasDerivAt_referenceRate (lam u ell time : ℝ) :
    HasDerivAt (referenceRate lam u ell)
      (referenceSlope lam u (PulseGrowth.slotMagnitude u ell time) * (u / ell)) time := by
  have hs : HasDerivAt (PulseGrowth.slotMagnitude u ell) (u / ell) time := by
    change HasDerivAt (fun x : ℝ => u / 2 + u * x / ell) (u / ell) time
    convert! (((hasDerivAt_id time).const_mul u).div_const ell).const_add (u / 2) using 1
    simp
  exact (hasDerivAt_netGrowth lam u (PulseGrowth.slotMagnitude u ell time)).comp time hs

theorem slotMagnitude_mem_interval {u ell time : ℝ} (hu : 0 ≤ u) (hell : 0 < ell)
    (ht : time ∈ Icc 0 ell) :
    PulseGrowth.slotMagnitude u ell time ∈ Icc (u / 2) (3 * u / 2) := by
  have hq0 : 0 ≤ u * time / ell := div_nonneg (mul_nonneg hu ht.1) (le_of_lt hell)
  have hq1 : u * time / ell ≤ u := by
    apply (div_le_iff₀ hell).2
    exact mul_le_mul_of_nonneg_left ht.2 hu
  unfold PulseGrowth.slotMagnitude
  constructor <;> linarith

/-- Bounds on the derivative in slot time, uniformly for all positive slot lengths. -/
theorem referenceRate_deriv_bounds {lam u ell time : ℝ}
    (hlam : 0 < lam) (hu : 0 < u) (hell : 0 < ell) (ht : time ∈ Icc 0 ell) :
    -(u * referenceMaxSlope lam u) / ell ≤ deriv (referenceRate lam u ell) time ∧
      deriv (referenceRate lam u ell) time ≤ -(u * referenceMinSlope lam u) / ell := by
  have hb := referenceSlope_bounds hlam hu (slotMagnitude_mem_interval (le_of_lt hu) hell ht)
  have hpos : 0 ≤ u / ell := le_of_lt (div_pos hu hell)
  rw [(hasDerivAt_referenceRate lam u ell time).deriv]
  constructor
  · convert! mul_le_mul_of_nonneg_right hb.1 hpos using 1
    ring
  · convert! mul_le_mul_of_nonneg_right hb.2 hpos using 1
    ring

/-- Two-sided Gaussian bounds for the actual scalar reference envelope.

All analytic hypotheses of `gaussian_envelope_bounds` are proved here from the
explicit reference formula.  The constants depend on `lam` and `u`, not `ell`.
-/
theorem reference_gaussian_bounds {lam u ell time : ℝ}
    (hlam : 0 < lam) (hu : 0 < u) (hell : 0 < ell) (ht : time ∈ Icc 0 ell) :
    Real.exp (-(u * referenceMaxSlope lam u) * (time - ell / 2) ^ 2 / (2 * ell)) ≤
        envelope (referenceRate lam u ell) (ell / 2) time ∧
      envelope (referenceRate lam u ell) (ell / 2) time ≤
        Real.exp (-(u * referenceMinSlope lam u) * (time - ell / 2) ^ 2 / (2 * ell)) := by
  have hdiff : Differentiable ℝ (referenceRate lam u ell) :=
    fun x => (hasDerivAt_referenceRate lam u ell x).differentiableAt
  apply gaussian_envelope_bounds (convex_Icc (0 : ℝ) ell)
    hdiff.continuous.continuousOn hdiff.differentiableOn
  · intro x hx
    exact referenceRate_deriv_bounds hlam hu hell (interior_subset hx)
  · constructor <;> linarith
  · exact ht
  · exact PulseGrowth.netGrowth_slot_midpoint lam u ell (ne_of_gt hell)

/-- The reference envelope has positive Gaussian constants uniform in slot length. -/
theorem reference_uniform_gaussian_bounds {lam u : ℝ} (hlam : 0 < lam) (hu : 0 < u) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ell : ℝ, 0 < ell → ∀ time ∈ Icc 0 ell,
      Real.exp (-C * (time - ell / 2) ^ 2 / ell) ≤
          envelope (referenceRate lam u ell) (ell / 2) time ∧
        envelope (referenceRate lam u ell) (ell / 2) time ≤
          Real.exp (-c * (time - ell / 2) ^ 2 / ell) := by
  refine ⟨u * referenceMinSlope lam u / 2, u * referenceMaxSlope lam u / 2,
    div_pos (mul_pos hu (referenceMinSlope_pos hlam hu)) (by norm_num),
    div_pos (mul_pos hu (referenceMaxSlope_pos hlam hu)) (by norm_num), ?_⟩
  intro ell hell time ht
  have hmax : -(u * referenceMaxSlope lam u / 2) * (time - ell / 2) ^ 2 / ell =
      -(u * referenceMaxSlope lam u) * (time - ell / 2) ^ 2 / (2 * ell) := by ring
  have hmin : -(u * referenceMinSlope lam u / 2) * (time - ell / 2) ^ 2 / ell =
      -(u * referenceMinSlope lam u) * (time - ell / 2) ^ 2 / (2 * ell) := by ring
  rw [hmax, hmin]
  exact reference_gaussian_bounds hlam hu hell ht

end NavierStokes.GaussianEnvelope
