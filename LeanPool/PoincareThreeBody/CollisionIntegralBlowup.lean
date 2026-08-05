/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.ResonantCollisionBoundary
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Logarithmic growth near a resonant collision

This file develops the real-variable estimate showing that the averaged Newtonian singularity
becomes unbounded when an aligned apoapsis approaches the unit primary.
-/

namespace LeanPool.PoincareThreeBody

open Filter MeasureTheory Set Topology

/-- Reciprocal distance from the resonant position to the unit primary. -/
noncomputable def resonantPrimaryInverse
    (p q : ℕ) (eccentricity orientation time : ℝ) : ℝ :=
  let position := orientedResonantEllipsePosition p q eccentricity orientation time
  1 / Real.sqrt ((position 0 - 1) ^ 2 + position 1 ^ 2)

theorem analyticAt_resonantPrimaryInverse_time
    {p q : ℕ} {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantSemimajorAxis p q * (1 + eccentricity) < 1) :
    AnalyticAt ℝ (resonantPrimaryInverse p q eccentricity orientation) time := by
  let x : ℝ → ℝ := fun argument ↦
    orientedResonantEllipsePosition p q eccentricity orientation argument 0
  let y : ℝ → ℝ := fun argument ↦
    orientedResonantEllipsePosition p q eccentricity orientation argument 1
  have hx : AnalyticAt ℝ x time :=
    analyticAt_orientedResonantEllipsePosition_coordinate p q
      heccentricity heccentricityOne 0
  have hy : AnalyticAt ℝ y time :=
    analyticAt_orientedResonantEllipsePosition_coordinate p q
      heccentricity heccentricityOne 1
  have hsquared : AnalyticAt ℝ
      (fun argument ↦ (x argument - 1) ^ 2 + y argument ^ 2) time :=
    ((hx.sub analyticAt_const).pow 2).add (hy.pow 2)
  have hne : (x time - 1) ^ 2 + y time ^ 2 ≠ 0 := by
    apply orientedResonantEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one
      heccentricity heccentricityOne
    simpa [resonantSemimajorAxis] using hapoapsis
  have hpositive : 0 < (x time - 1) ^ 2 + y time ^ 2 :=
    lt_of_le_of_ne (by positivity) (Ne.symm hne)
  exact ((analyticAt_inv_sqrt hpositive).comp
    (f := fun argument ↦ (x argument - 1) ^ 2 + y argument ^ 2) hsquared).congr (by
    filter_upwards [] with argument
    rfl)

theorem continuous_resonantPrimaryInverse
    {p q : ℕ} {eccentricity orientation : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantSemimajorAxis p q * (1 + eccentricity) < 1) :
    Continuous (resonantPrimaryInverse p q eccentricity orientation) := by
  rw [continuous_iff_continuousAt]
  intro time
  exact (analyticAt_resonantPrimaryInverse_time
    heccentricity heccentricityOne hapoapsis).continuousAt

/-- On the one-sided time interval where time displacement dominates eccentricity displacement,
the collision inverse is bounded below by a reciprocal linear function. -/
theorem one_div_two_mul_constant_mul_time_le_resonantPrimaryInverse
    {p q : ℕ} {lipConstant neighborhoodRadius eccentricity time : ℝ}
    (hlocal : ∀ parameters : ℝ × ℝ,
      dist parameters
          (resonantCollisionEccentricity p q, resonantApoapsisTime p q) <
            neighborhoodRadius →
      ‖orientedResonantEllipsePosition p q parameters.1
            (resonantCollisionOrientation p q) parameters.2 - ![(1 : ℝ), (0 : ℝ)]‖ ≤
        lipConstant *
          ‖parameters -
            (resonantCollisionEccentricity p q, resonantApoapsisTime p q)‖)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantSemimajorAxis p q * (1 + eccentricity) < 1)
    (heccentricityDisplacement :
      0 < resonantCollisionEccentricity p q - eccentricity)
    (htimeDisplacementLower :
      resonantCollisionEccentricity p q - eccentricity ≤
        time - resonantApoapsisTime p q)
    (htimeDisplacementUpper :
      time - resonantApoapsisTime p q < neighborhoodRadius) :
    1 / (2 * lipConstant * (time - resonantApoapsisTime p q)) ≤
      resonantPrimaryInverse p q eccentricity
        (resonantCollisionOrientation p q) time := by
  let center : ℝ × ℝ :=
    (resonantCollisionEccentricity p q, resonantApoapsisTime p q)
  let parameters : ℝ × ℝ := (eccentricity, time)
  let displacement := time - resonantApoapsisTime p q
  have hdisplacementPositive : 0 < displacement :=
    heccentricityDisplacement.trans_le htimeDisplacementLower
  have hparameterNorm : ‖parameters - center‖ = displacement := by
    rw [Prod.norm_def]
    change max ‖eccentricity - resonantCollisionEccentricity p q‖
      ‖time - resonantApoapsisTime p q‖ = displacement
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonpos (by linarith), abs_of_nonneg hdisplacementPositive.le]
    rw [max_eq_right]
    dsimp [displacement]
    linarith
  have hparametersNear : dist parameters center < neighborhoodRadius := by
    rw [dist_eq_norm, hparameterNorm]
    exact htimeDisplacementUpper
  let position := orientedResonantEllipsePosition p q eccentricity
    (resonantCollisionOrientation p q) time
  let offset : ActionSpace := position - ![(1 : ℝ), (0 : ℝ)]
  have hoffsetNorm : ‖offset‖ ≤ lipConstant * displacement := by
    have hbound := hlocal parameters hparametersNear
    rw [hparameterNorm] at hbound
    exact hbound
  have heccentricityResonant :
      resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1 := by
    simpa [resonantSemimajorAxis] using hapoapsis
  have hdistanceSqNe :
      (position 0 - 1) ^ 2 + position 1 ^ 2 ≠ 0 :=
    orientedResonantEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one
      heccentricity heccentricityOne heccentricityResonant
  have hdistancePositive :
      0 < Real.sqrt ((position 0 - 1) ^ 2 + position 1 ^ 2) := by
    apply Real.sqrt_pos.mpr
    exact lt_of_le_of_ne (by positivity) (Ne.symm hdistanceSqNe)
  have hoffsetZero : offset 0 = position 0 - 1 := by
    change position 0 - 1 = position 0 - 1
    rfl
  have hoffsetOne : offset 1 = position 1 := by
    change position 1 - 0 = position 1
    simp
  have hdistanceBound :
      Real.sqrt ((position 0 - 1) ^ 2 + position 1 ^ 2) ≤
        2 * lipConstant * displacement := by
    calc
      Real.sqrt ((position 0 - 1) ^ 2 + position 1 ^ 2) =
          Real.sqrt (offset 0 ^ 2 + offset 1 ^ 2) := by
        rw [hoffsetZero, hoffsetOne]
      _ ≤ 2 * ‖offset‖ := sqrt_sq_add_sq_le_two_norm offset
      _ ≤ 2 * (lipConstant * displacement) := by gcongr
      _ = 2 * lipConstant * displacement := by ring
  unfold resonantPrimaryInverse
  dsimp only
  exact one_div_le_one_div_of_le hdistancePositive hdistanceBound

/-- Integrating the pointwise collision estimate gives the explicit logarithmic lower bound. -/
theorem log_lower_bound_resonantPrimaryInverse_local_integral
    {p q : ℕ} {lipConstant neighborhoodRadius eccentricity window : ℝ}
    (hconstant : 0 < lipConstant)
    (hlocal : ∀ parameters : ℝ × ℝ,
      dist parameters
          (resonantCollisionEccentricity p q, resonantApoapsisTime p q) <
            neighborhoodRadius →
      ‖orientedResonantEllipsePosition p q parameters.1
            (resonantCollisionOrientation p q) parameters.2 - ![(1 : ℝ), (0 : ℝ)]‖ ≤
        lipConstant *
          ‖parameters -
            (resonantCollisionEccentricity p q, resonantApoapsisTime p q)‖)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantSemimajorAxis p q * (1 + eccentricity) < 1)
    (hdelta : 0 < resonantCollisionEccentricity p q - eccentricity)
    (hdeltaWindow : resonantCollisionEccentricity p q - eccentricity < window)
    (hwindow : window < neighborhoodRadius) :
    (1 / (2 * lipConstant)) *
        Real.log (window / (resonantCollisionEccentricity p q - eccentricity)) ≤
      ∫ time in
          resonantApoapsisTime p q +
              (resonantCollisionEccentricity p q - eccentricity)..
            resonantApoapsisTime p q + window,
        resonantPrimaryInverse p q eccentricity
          (resonantCollisionOrientation p q) time := by
  let apoapsisTime := resonantApoapsisTime p q
  let delta := resonantCollisionEccentricity p q - eccentricity
  let lower : ℝ → ℝ := fun time ↦ 1 / (2 * lipConstant * (time - apoapsisTime))
  have hbounds : apoapsisTime + delta ≤ apoapsisTime + window := by
    linarith
  have hlowerIntegrable : IntervalIntegrable lower volume
      (apoapsisTime + delta) (apoapsisTime + window) := by
    apply intervalIntegral.intervalIntegrable_one_div
    · intro time htime
      rw [uIcc_of_le hbounds] at htime
      have htimePositive : 0 < time - apoapsisTime := by linarith [htime.1]
      exact mul_ne_zero (mul_ne_zero two_ne_zero hconstant.ne') htimePositive.ne'
    · fun_prop
  have hprimaryIntegrable : IntervalIntegrable
      (resonantPrimaryInverse p q eccentricity (resonantCollisionOrientation p q)) volume
      (apoapsisTime + delta) (apoapsisTime + window) :=
    (continuous_resonantPrimaryInverse
      (p := p) (q := q) (eccentricity := eccentricity)
      (orientation := resonantCollisionOrientation p q)
      heccentricity heccentricityOne hapoapsis).intervalIntegrable (μ := volume)
        (apoapsisTime + delta) (apoapsisTime + window)
  have hintegralLower :
      (∫ time in apoapsisTime + delta..apoapsisTime + window, lower time) ≤
        ∫ time in apoapsisTime + delta..apoapsisTime + window,
          resonantPrimaryInverse p q eccentricity
            (resonantCollisionOrientation p q) time := by
    apply intervalIntegral.integral_mono_on hbounds hlowerIntegrable hprimaryIntegrable
    intro time htime
    apply one_div_two_mul_constant_mul_time_le_resonantPrimaryInverse
      hlocal heccentricity heccentricityOne hapoapsis hdelta
    · linarith [htime.1]
    · linarith [htime.2]
  calc
    (1 / (2 * lipConstant)) * Real.log (window / delta) =
        ∫ time in apoapsisTime + delta..apoapsisTime + window, lower time := by
      have hshift := intervalIntegral.integral_comp_sub_right
        (f := fun value : ℝ ↦ 1 / value) (a := apoapsisTime + delta)
        (b := apoapsisTime + window) apoapsisTime
      have hinverse :
          (∫ time in apoapsisTime + delta..apoapsisTime + window,
              1 / (time - apoapsisTime)) = Real.log (window / delta) := by
        rw [hshift]
        rw [show apoapsisTime + delta - apoapsisTime = delta by ring,
          show apoapsisTime + window - apoapsisTime = window by ring]
        exact integral_one_div_of_pos hdelta (hdelta.trans hdeltaWindow)
      rw [show lower = fun time ↦ (1 / (2 * lipConstant)) *
          (1 / (time - apoapsisTime)) by
        funext time
        dsimp [lower]
        field_simp [hconstant.ne']]
      rw [intervalIntegral.integral_const_mul, hinverse]
    _ ≤ _ := hintegralLower

/-- The local logarithmic estimate also bounds the inverse-distance integral over the whole
resonant period, provided the comparison window lies inside that period. -/
theorem log_lower_bound_resonantPrimaryInverse_period_integral
    {p q : ℕ} {lipConstant neighborhoodRadius eccentricity window : ℝ}
    (hconstant : 0 < lipConstant)
    (hlocal : ∀ parameters : ℝ × ℝ,
      dist parameters
          (resonantCollisionEccentricity p q, resonantApoapsisTime p q) <
            neighborhoodRadius →
      ‖orientedResonantEllipsePosition p q parameters.1
            (resonantCollisionOrientation p q) parameters.2 - ![(1 : ℝ), (0 : ℝ)]‖ ≤
        lipConstant *
          ‖parameters -
            (resonantCollisionEccentricity p q, resonantApoapsisTime p q)‖)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantSemimajorAxis p q * (1 + eccentricity) < 1)
    (hdelta : 0 < resonantCollisionEccentricity p q - eccentricity)
    (hdeltaWindow : resonantCollisionEccentricity p q - eccentricity < window)
    (hwindow : window < neighborhoodRadius)
    (hwindowPeriod : resonantApoapsisTime p q + window ≤ resonantOrbitPeriod p) :
    (1 / (2 * lipConstant)) *
        Real.log (window / (resonantCollisionEccentricity p q - eccentricity)) ≤
      ∫ time in 0..resonantOrbitPeriod p,
        resonantPrimaryInverse p q eccentricity
          (resonantCollisionOrientation p q) time := by
  let start := resonantApoapsisTime p q +
    (resonantCollisionEccentricity p q - eccentricity)
  let finish := resonantApoapsisTime p q + window
  have hstart : 0 ≤ start := by
    dsimp [start, resonantApoapsisTime]
    have hratio : 0 ≤ (p : ℝ) / (q : ℝ) := div_nonneg (by positivity) (by positivity)
    positivity
  have hstartFinish : start ≤ finish := by
    dsimp [start, finish]
    linarith
  have hfullIntegrable : IntervalIntegrable
      (resonantPrimaryInverse p q eccentricity (resonantCollisionOrientation p q)) volume
      0 (resonantOrbitPeriod p) :=
    (continuous_resonantPrimaryInverse
      (p := p) (q := q) (eccentricity := eccentricity)
      (orientation := resonantCollisionOrientation p q)
      heccentricity heccentricityOne hapoapsis).intervalIntegrable (μ := volume)
        0 (resonantOrbitPeriod p)
  have hlocalLeFull :
      (∫ time in start..finish,
          resonantPrimaryInverse p q eccentricity
            (resonantCollisionOrientation p q) time) ≤
        ∫ time in 0..resonantOrbitPeriod p,
          resonantPrimaryInverse p q eccentricity
            (resonantCollisionOrientation p q) time := by
    apply intervalIntegral.integral_mono_interval hstart hstartFinish hwindowPeriod
    · exact Filter.Eventually.of_forall (fun time ↦ by
        unfold resonantPrimaryInverse
        dsimp only
        exact one_div_nonneg.mpr (Real.sqrt_nonneg _))
    · exact hfullIntegrable
  exact (log_lower_bound_resonantPrimaryInverse_local_integral
    hconstant hlocal heccentricity heccentricityOne hapoapsis hdelta hdeltaWindow
      hwindow).trans hlocalLeFull

end LeanPool.PoincareThreeBody
