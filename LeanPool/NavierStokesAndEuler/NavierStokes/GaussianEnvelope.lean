/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
# Gaussian bounds from a decreasing instantaneous rate

The integral is oriented: a point before the midpoint reverses the integration
limits.  The main theorem proves the same quadratic bounds on both sides,
under local differentiability and derivative bounds on a convex domain.
-/

section

/-!
# Reference pulse growth

This file verifies the scalar reference growth calculation in Lemma 8.5 and
Proposition A.4 of the supplied manuscript. The denominator `(1 + u^2)^(3/2)`
is written as `(1 + u^2) * sqrt (1 + u^2)` to avoid fractional-power notation.
These results do not assert bounds on the actual variable-coefficient ODE or
on its parameter derivatives.
-/

@[expose] public section

namespace NavierStokes.PulseGrowth

/-- Scalar growth of the positive reference mode after the chosen viscous damping. -/
noncomputable def netGrowth (lam u s : ℝ) : ℝ :=
  lam / Real.sqrt (1 + s ^ 2) -
    lam * (1 + s ^ 2) / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2))

theorem one_add_sq_pos (s : ℝ) : 0 < 1 + s ^ 2 := by
  positivity

theorem radius_pos (s : ℝ) : 0 < Real.sqrt (1 + s ^ 2) :=
  Real.sqrt_pos.2 (one_add_sq_pos s)

theorem dampingDenominator_pos (u : ℝ) :
    0 < (1 + u ^ 2) * Real.sqrt (1 + u ^ 2) :=
  mul_pos (one_add_sq_pos u) (radius_pos u)

/-- The three-halves denominator is the cube of the positive square root. -/
theorem dampingDenominator_eq_radius_cube (u : ℝ) :
    (1 + u ^ 2) * Real.sqrt (1 + u ^ 2) = (Real.sqrt (1 + u ^ 2)) ^ 3 := by
  calc
    (1 + u ^ 2) * Real.sqrt (1 + u ^ 2) =
        (Real.sqrt (1 + u ^ 2)) ^ 2 * Real.sqrt (1 + u ^ 2) := by
          rw [Real.sq_sqrt (le_of_lt (one_add_sq_pos u))]
    _ = (Real.sqrt (1 + u ^ 2)) ^ 3 := by ring

/-- Squaring the proposed positive eigenvalue gives the reference discriminant. -/
theorem reference_eigenvalue_square (lam s : ℝ) :
    (lam / Real.sqrt (1 + s ^ 2)) ^ 2 = lam ^ 2 / (1 + s ^ 2) := by
  rw [div_pow, Real.sq_sqrt (le_of_lt (one_add_sq_pos s))]

/-- Characteristic equation for the two off-diagonal reference coefficients.

Here `a = 2 F₀ Nθ` and `b = -(2 F₀ Nθ + |g₀|)` in the manuscript.
The hypothesis is the manuscript's definition of the squared reference rate;
its positivity from the geometric cone is not assumed to have been established.
-/
theorem reference_characteristic_equation {a b lam s : ℝ} (hdisc : lam ^ 2 = a * b) :
    (lam / Real.sqrt (1 + s ^ 2)) ^ 2 - (a / (1 + s ^ 2)) * b = 0 := by
  rw [reference_eigenvalue_square, hdisc]
  ring

/-- Reversing the sign of the slot parameter does not change the growth. -/
theorem netGrowth_even (lam u s : ℝ) :
    netGrowth lam u (-s) = netGrowth lam u s := by
  simp [netGrowth]

/-- The prescribed damping exactly cancels growth at the threshold. -/
theorem netGrowth_at_threshold (lam u : ℝ) : netGrowth lam u u = 0 := by
  unfold netGrowth
  field_simp [ne_of_gt (one_add_sq_pos u), ne_of_gt (radius_pos u)]; ring

/-- Strict decrease in squared distance from zero, for a positive reference rate. -/
theorem netGrowth_strictAnti_sq {lam u s t : ℝ} (hlam : 0 < lam)
    (hst : s ^ 2 < t ^ 2) : netGrowth lam u t < netGrowth lam u s := by
  have hst' : 1 + s ^ 2 < 1 + t ^ 2 := by linarith
  have hr : Real.sqrt (1 + s ^ 2) < Real.sqrt (1 + t ^ 2) :=
    Real.sqrt_lt_sqrt (le_of_lt (one_add_sq_pos s)) hst'
  have hg : lam / Real.sqrt (1 + t ^ 2) < lam / Real.sqrt (1 + s ^ 2) := by
    apply (div_lt_div_iff₀ (radius_pos t) (radius_pos s)).2
    exact mul_lt_mul_of_pos_left hr hlam
  have hd : lam * (1 + s ^ 2) / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2)) <
      lam * (1 + t ^ 2) / ((1 + u ^ 2) * Real.sqrt (1 + u ^ 2)) :=
    div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hst' hlam) (dampingDenominator_pos u)
  exact sub_lt_sub hg hd

theorem netGrowth_eq_of_sq_eq {lam u s t : ℝ} (hst : s ^ 2 = t ^ 2) :
    netGrowth lam u s = netGrowth lam u t := by
  simp only [netGrowth, hst]

/-- Growth is positive strictly inside either threshold. -/
theorem netGrowth_pos_of_abs_lt {lam u s : ℝ} (hlam : 0 < lam)
    (hs : |s| < |u|) : 0 < netGrowth lam u s := by
  have h := netGrowth_strictAnti_sq (u := u) hlam (sq_lt_sq.2 hs)
  simpa only [netGrowth_at_threshold] using h

/-- Growth vanishes at both signed thresholds. -/
theorem netGrowth_zero_of_abs_eq {lam u s : ℝ} (hs : |s| = |u|) :
    netGrowth lam u s = 0 := by
  have hsq : s ^ 2 = u ^ 2 := by
    calc
      s ^ 2 = |s| ^ 2 := (sq_abs s).symm
      _ = |u| ^ 2 := by rw [hs]
      _ = u ^ 2 := sq_abs u
  rw [netGrowth_eq_of_sq_eq hsq, netGrowth_at_threshold]

/-- Growth is negative outside either threshold. -/
theorem netGrowth_neg_of_abs_gt {lam u s : ℝ} (hlam : 0 < lam)
    (hs : |u| < |s|) : netGrowth lam u s < 0 := by
  have h := netGrowth_strictAnti_sq (u := u) hlam (sq_lt_sq.2 hs)
  simpa only [netGrowth_at_threshold] using h

/-- A complete positive/zero/negative classification for a positive reference rate. -/
theorem netGrowth_sign {lam u s : ℝ} (hlam : 0 < lam) :
    (0 < netGrowth lam u s ↔ |s| < |u|) ∧
    (netGrowth lam u s = 0 ↔ |s| = |u|) ∧
    (netGrowth lam u s < 0 ↔ |u| < |s|) := by
  rcases lt_trichotomy |s| |u| with hs | hs | hs
  · have hg := netGrowth_pos_of_abs_lt (lam := lam) hlam hs
    constructor
    · exact ⟨fun _ => hs, fun _ => hg⟩
    constructor
    · constructor <;> intro h <;> linarith
    · constructor <;> intro h <;> linarith
  · have hg : netGrowth lam u s = 0 := netGrowth_zero_of_abs_eq hs
    constructor
    · constructor <;> intro h <;> linarith
    constructor
    · exact ⟨fun _ => hs, fun _ => hg⟩
    · constructor <;> intro h <;> linarith
  · have hg := netGrowth_neg_of_abs_gt (lam := lam) hlam hs
    constructor
    · constructor <;> intro h <;> linarith
    constructor
    · constructor <;> intro h <;> linarith
    · exact ⟨fun _ => hs, fun _ => hg⟩

/-- For positive magnitudes the reference growth is strictly decreasing. -/
theorem netGrowth_strictAntiOn_nonneg {lam u : ℝ} (hlam : 0 < lam) :
    StrictAntiOn (netGrowth lam u) (Set.Ici 0) := by
  intro s hs t ht hst
  have hs0 : 0 ≤ s := hs
  have ht0 : 0 ≤ t := ht
  apply netGrowth_strictAnti_sq hlam
  apply sq_lt_sq.2
  simpa only [abs_of_nonneg hs0, abs_of_nonneg ht0] using hst

/-- Magnitude of either signed schedule, in the slot-time variable. -/
noncomputable def slotMagnitude (u ell v : ℝ) : ℝ := u / 2 + u * v / ell

theorem slotMagnitude_midpoint (u ell : ℝ) (hell : ell ≠ 0) :
    slotMagnitude u ell (ell / 2) = u := by
  unfold slotMagnitude
  field_simp; ring

theorem slotMagnitude_nonneg {u ell v : ℝ} (hu : 0 ≤ u) (hell : 0 < ell)
    (hv : 0 ≤ v) : 0 ≤ slotMagnitude u ell v := by
  unfold slotMagnitude
  positivity

theorem slotMagnitude_lt_threshold {u ell v : ℝ} (hu : 0 < u) (hell : 0 < ell)
    (hv : v < ell / 2) : slotMagnitude u ell v < u := by
  have hdiv : u * v / ell < u / 2 := (div_lt_iff₀ hell).2 (by nlinarith)
  unfold slotMagnitude
  linarith

theorem slotMagnitude_gt_threshold {u ell v : ℝ} (hu : 0 < u) (hell : 0 < ell)
    (hv : ell / 2 < v) : u < slotMagnitude u ell v := by
  have hdiv : u / 2 < u * v / ell := (lt_div_iff₀ hell).2 (by nlinarith)
  unfold slotMagnitude
  linarith

/-- Positive reference growth on the first half of a slot. -/
theorem netGrowth_slot_positive {lam u ell v : ℝ} (hlam : 0 < lam) (hu : 0 < u)
    (hell : 0 < ell) (hv : 0 ≤ v) (hmid : v < ell / 2) :
    0 < netGrowth lam u (slotMagnitude u ell v) := by
  apply netGrowth_pos_of_abs_lt hlam
  rw [abs_of_nonneg (slotMagnitude_nonneg (le_of_lt hu) hell hv), abs_of_pos hu]
  exact slotMagnitude_lt_threshold hu hell hmid

/-- Zero reference growth at the slot midpoint. -/
theorem netGrowth_slot_midpoint (lam u ell : ℝ) (hell : ell ≠ 0) :
    netGrowth lam u (slotMagnitude u ell (ell / 2)) = 0 := by
  rw [slotMagnitude_midpoint u ell hell, netGrowth_at_threshold]

/-- Negative reference growth on the second half of a slot (and beyond). -/
theorem netGrowth_slot_negative {lam u ell v : ℝ} (hlam : 0 < lam) (hu : 0 < u)
    (hell : 0 < ell) (hmid : ell / 2 < v) :
    netGrowth lam u (slotMagnitude u ell v) < 0 := by
  have hv : 0 ≤ v := by linarith
  apply netGrowth_neg_of_abs_gt hlam
  rw [abs_of_pos hu, abs_of_nonneg (slotMagnitude_nonneg (le_of_lt hu) hell hv)]
  exact slotMagnitude_gt_threshold hu hell hmid

end NavierStokes.PulseGrowth

end

end

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
