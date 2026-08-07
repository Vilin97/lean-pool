/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DisturbingRegularBound

/-!
# Blow-up of the collision-aligned disturbing average

Combining the logarithmic singular estimate with the uniform regular bound gives an explicit
upper bound on the aligned disturbing average.
-/

namespace LeanPool.PoincareThreeBody

open MeasureTheory

theorem resonantDisturbingAverage_eq_regular_sub_primary
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantSemimajorAxis p q * (1 + eccentricity) < 1) :
    resonantDisturbingAverage p q eccentricity orientation =
      (∫ time in 0..resonantOrbitPeriod p,
          resonantRegularPart p q eccentricity orientation time) -
        ∫ time in 0..resonantOrbitPeriod p,
          resonantPrimaryInverse p q eccentricity orientation time := by
  have hregular := intervalIntegrable_resonantRegularPart hp hq
    (orientation := orientation) (start := 0) (finish := resonantOrbitPeriod p)
      heccentricity heccentricityOne hapoapsis
  have hprimary := (continuous_resonantPrimaryInverse
    (p := p) (q := q) (eccentricity := eccentricity) (orientation := orientation)
    heccentricity heccentricityOne hapoapsis).intervalIntegrable
      (μ := volume) 0 (resonantOrbitPeriod p)
  unfold resonantDisturbingAverage
  calc
    (∫ time in 0..resonantOrbitPeriod p,
        resonantDisturbingFunction p q eccentricity orientation time) =
        ∫ time in 0..resonantOrbitPeriod p,
          (resonantRegularPart p q eccentricity orientation time -
            resonantPrimaryInverse p q eccentricity orientation time) := by
      apply intervalIntegral.integral_congr
      intro time _
      exact resonantDisturbingFunction_eq_regularPart_sub_primaryInverse
        p q eccentricity orientation time
    _ = _ := intervalIntegral.integral_sub hregular hprimary

/-- Explicit upper bound which tends to negative infinity as the eccentricity approaches the
collision value from below. -/
theorem resonantDisturbingAverage_collisionAligned_le
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (haxisHalf : 1 / 2 < resonantSemimajorAxis p q)
    {lipConstant neighborhoodRadius eccentricity window : ℝ}
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
    (heccentricityBoundary : eccentricity < resonantCollisionEccentricity p q)
    (hdeltaWindow : resonantCollisionEccentricity p q - eccentricity < window)
    (hwindow : window < neighborhoodRadius)
    (hwindowPeriod : resonantApoapsisTime p q + window ≤ resonantOrbitPeriod p) :
    resonantDisturbingAverage p q eccentricity
        (resonantCollisionOrientation p q) ≤
      resonantOrbitPeriod p *
          (1 / (2 * resonantSemimajorAxis p q - 1) +
            1 / (2 * resonantSemimajorAxis p q - 1) ^ 2) -
        (1 / (2 * lipConstant)) *
          Real.log (window /
            (resonantCollisionEccentricity p q - eccentricity)) := by
  let regularBound := resonantOrbitPeriod p *
    (1 / (2 * resonantSemimajorAxis p q - 1) +
      1 / (2 * resonantSemimajorAxis p q - 1) ^ 2)
  let logarithmicBound := (1 / (2 * lipConstant)) *
    Real.log (window / (resonantCollisionEccentricity p q - eccentricity))
  have hapoapsis := resonant_apoapsis_lt_one_of_eccentricity_lt_collision
    hp hq heccentricityBoundary
  have hregularAbs := abs_integral_resonantRegularPart_le_collision_bound
    hp hq haxisHalf (orientation := resonantCollisionOrientation p q)
      heccentricity heccentricityOne heccentricityBoundary
  have hregular :
      (∫ time in 0..resonantOrbitPeriod p,
        resonantRegularPart p q eccentricity
          (resonantCollisionOrientation p q) time) ≤ regularBound := by
    exact (le_abs_self _).trans hregularAbs
  have hprimary : logarithmicBound ≤
      ∫ time in 0..resonantOrbitPeriod p,
        resonantPrimaryInverse p q eccentricity
          (resonantCollisionOrientation p q) time := by
    exact log_lower_bound_resonantPrimaryInverse_period_integral
      hconstant hlocal heccentricity heccentricityOne hapoapsis
        (sub_pos.mpr heccentricityBoundary) hdeltaWindow hwindow hwindowPeriod
  rw [resonantDisturbingAverage_eq_regular_sub_primary hp hq
    heccentricity heccentricityOne hapoapsis]
  exact sub_le_sub hregular hprimary

/-- Collision alignment makes the resonant disturbing average arbitrarily negative, at an
eccentricity arbitrarily close to the collision boundary. -/
theorem exists_collisionAligned_resonantDisturbingAverage_between
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (haxisHalf : 1 / 2 < resonantSemimajorAxis p q)
    (haxisOne : resonantSemimajorAxis p q < 1)
    {lowerEccentricity : ℝ}
    (hlowerEccentricity : lowerEccentricity < resonantCollisionEccentricity p q)
    (target : ℝ) :
    ∃ eccentricity : ℝ,
      lowerEccentricity < eccentricity ∧ 0 < eccentricity ∧
        eccentricity < resonantCollisionEccentricity p q ∧ eccentricity < 1 ∧
        resonantDisturbingAverage p q eccentricity
          (resonantCollisionOrientation p q) < target := by
  rcases exists_collisionAlignedPosition_local_bound hp hq haxisHalf haxisOne with
    ⟨lipConstant, hconstant, neighborhoodRadius, hneighborhoodRadius, hlocal⟩
  let collisionEccentricity := resonantCollisionEccentricity p q
  let periodGap := resonantOrbitPeriod p - resonantApoapsisTime p q
  have hcollisionEccentricity : 0 < collisionEccentricity :=
    resonantCollisionEccentricity_pos hp hq haxisOne
  have hcollisionEccentricityOne : collisionEccentricity < 1 :=
    resonantCollisionEccentricity_lt_one hp hq haxisHalf
  have hperiodGap : 0 < periodGap := by
    dsimp [periodGap]
    exact sub_pos.mpr (resonantApoapsisTime_lt_orbitPeriod hp hq)
  let window := min (neighborhoodRadius / 2)
    (min (periodGap / 2)
      (min (collisionEccentricity / 2)
        ((collisionEccentricity - lowerEccentricity) / 2)))
  have hwindow : 0 < window := by
    dsimp [window]
    rw [lt_min_iff, lt_min_iff, lt_min_iff]
    exact ⟨by positivity, by positivity, by positivity, by
      dsimp [collisionEccentricity]
      linarith⟩
  have hwindowNeighborhood : window < neighborhoodRadius := by
    have hle : window ≤ neighborhoodRadius / 2 := min_le_left _ _
    linarith
  have hwindowGap : window ≤ periodGap / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hwindowPeriod :
      resonantApoapsisTime p q + window ≤ resonantOrbitPeriod p := by
    dsimp [periodGap] at hwindowGap
    linarith
  have hwindowEccentricity : window ≤ collisionEccentricity / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hwindowLower :
      window ≤ (collisionEccentricity - lowerEccentricity) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let regularBound := resonantOrbitPeriod p *
    (1 / (2 * resonantSemimajorAxis p q - 1) +
      1 / (2 * resonantSemimajorAxis p q - 1) ^ 2)
  let exponent := max 1 (2 * lipConstant * (regularBound - target + 1))
  have hexponent : 0 < exponent := by
    dsimp [exponent]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let delta := window / Real.exp exponent
  have hdelta : 0 < delta := div_pos hwindow (Real.exp_pos exponent)
  have hdeltaWindow : delta < window := by
    dsimp [delta]
    rw [div_lt_iff₀ (Real.exp_pos exponent)]
    have hexponential : 1 < Real.exp exponent := Real.one_lt_exp_iff.mpr hexponent
    nlinarith
  let eccentricity := collisionEccentricity - delta
  have heccentricity : 0 < eccentricity := by
    dsimp [eccentricity]
    have hdeltaHalf : delta < collisionEccentricity / 2 :=
      hdeltaWindow.trans_le hwindowEccentricity
    linarith
  have hlower : lowerEccentricity < eccentricity := by
    dsimp [eccentricity]
    have hdeltaLower :
        delta < (collisionEccentricity - lowerEccentricity) / 2 :=
      hdeltaWindow.trans_le hwindowLower
    linarith
  have heccentricityBoundary : eccentricity < resonantCollisionEccentricity p q := by
    dsimp [eccentricity, collisionEccentricity]
    linarith
  have heccentricityOne : eccentricity < 1 :=
    heccentricityBoundary.trans hcollisionEccentricityOne
  have hdifference : resonantCollisionEccentricity p q - eccentricity = delta := by
    dsimp [eccentricity, collisionEccentricity]
    ring
  have hlogarithm :
      Real.log (window /
        (resonantCollisionEccentricity p q - eccentricity)) = exponent := by
    rw [hdifference]
    have hratio : window / delta = Real.exp exponent := by
      dsimp [delta]
      field_simp [hwindow.ne', Real.exp_ne_zero]
    rw [hratio, Real.log_exp]
  have hexponentLower :
      2 * lipConstant * (regularBound - target + 1) ≤ exponent := by
    exact le_max_right _ _
  have hscaledLower :
      regularBound - target + 1 ≤ (1 / (2 * lipConstant)) * exponent := by
    calc
      regularBound - target + 1 =
          (1 / (2 * lipConstant)) *
            (2 * lipConstant * (regularBound - target + 1)) := by
        field_simp [hconstant.ne']
      _ ≤ (1 / (2 * lipConstant)) * exponent := by
        gcongr
  have hupper := resonantDisturbingAverage_collisionAligned_le hp hq haxisHalf
    hconstant hlocal heccentricity.le heccentricityOne heccentricityBoundary
      (by rw [hdifference]; exact hdeltaWindow) hwindowNeighborhood hwindowPeriod
  refine ⟨eccentricity, hlower, heccentricity, heccentricityBoundary,
    heccentricityOne, ?_⟩
  rw [hlogarithm] at hupper
  linarith

/-- In particular, a positive admissible collision-aligned eccentricity realizes every negative
target. -/
theorem exists_collisionAligned_resonantDisturbingAverage_lt
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (haxisHalf : 1 / 2 < resonantSemimajorAxis p q)
    (haxisOne : resonantSemimajorAxis p q < 1) (target : ℝ) :
    ∃ eccentricity : ℝ,
      0 ≤ eccentricity ∧ eccentricity < resonantCollisionEccentricity p q ∧
        eccentricity < 1 ∧
        resonantDisturbingAverage p q eccentricity
          (resonantCollisionOrientation p q) < target := by
  rcases exists_collisionAligned_resonantDisturbingAverage_between hp hq
      haxisHalf haxisOne (resonantCollisionEccentricity_pos hp hq haxisOne) target with
    ⟨eccentricity, heccentricityPositive, heccentricity,
      heccentricityBoundary, heccentricityOne, haverage⟩
  exact ⟨eccentricity, heccentricity.le, heccentricityBoundary,
    heccentricityOne, haverage⟩

end LeanPool.PoincareThreeBody
