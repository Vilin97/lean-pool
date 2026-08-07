/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.AnalyticCompactParameterIntegral
import LeanPool.PoincareThreeBody.DisturbingParameterAnalytic

/-!
# Analytic eccentricity dependence of the resonant disturbing average

The joint analyticity of the disturbing function and compact parameter-integral theorem imply
that averaging over one resonant period preserves real analyticity in eccentricity.
-/

namespace LeanPool.PoincareThreeBody

open Filter MeasureTheory Set Topology

/-- The resonant disturbing average is analytic in eccentricity throughout the collision-free
interior range. -/
theorem analyticAt_resonantDisturbingAverage_eccentricity
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation : ℝ}
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    AnalyticAt ℝ (fun candidate ↦
      resonantDisturbingAverage p q candidate orientation) eccentricity := by
  let admissible : Set ℝ := {candidate |
    0 < candidate ∧ candidate < 1 ∧
      resonantFirstAction p q ^ 2 * (1 + candidate) < 1}
  have hadmissibleOpen : IsOpen admissible := by
    dsimp [admissible]
    exact (isOpen_lt continuous_const continuous_id).and
      ((isOpen_lt continuous_id continuous_const).and
        (isOpen_lt (by fun_prop) continuous_const))
  have heccentricityAdmissible : eccentricity ∈ admissible :=
    ⟨heccentricity, heccentricityOne, hapoapsis⟩
  have hintegrable : ∀ᶠ candidate in 𝓝 eccentricity,
      IntegrableOn (fun time ↦
        resonantDisturbingFunction p q candidate orientation time)
        (Icc 0 (resonantOrbitPeriod p)) := by
    filter_upwards [hadmissibleOpen.mem_nhds heccentricityAdmissible]
      with candidate hcandidate
    have hcontinuous : Continuous
        (resonantDisturbingFunction p q candidate orientation) := by
      rw [continuous_iff_continuousAt]
      intro time
      exact (analyticAt_resonantDisturbingFunction_time hp hq
        hcandidate.1.le hcandidate.2.1 hcandidate.2.2).continuousAt
    exact hcontinuous.continuousOn.integrableOn_Icc
  have hsetIntegral : AnalyticAt ℝ (fun candidate ↦
      ∫ time in Icc 0 (resonantOrbitPeriod p),
        resonantDisturbingFunction p q candidate orientation time) eccentricity := by
    apply analyticAt_setIntegral_of_joint_analytic
      (function := fun parameters : ℝ × ℝ ↦
        resonantDisturbingFunction p q parameters.1 orientation parameters.2)
      (centerParameter := eccentricity)
      (timeSet := Icc 0 (resonantOrbitPeriod p)) isCompact_Icc
    · intro time _
      exact analyticAt_resonantDisturbingFunction_eccentricity_time hp hq
        heccentricity heccentricityOne hapoapsis
    · exact hintegrable
  have hperiod : 0 ≤ resonantOrbitPeriod p := by
    unfold resonantOrbitPeriod
    positivity
  apply hsetIntegral.congr
  filter_upwards [] with candidate
  unfold resonantDisturbingAverage
  rw [intervalIntegral.integral_of_le hperiod, ← integral_Icc_eq_integral_Ioc]

/-- Analyticity assembled over the entire admissible eccentricity interval. -/
theorem analyticOnNhd_resonantDisturbingAverage_eccentricity
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (orientation : ℝ) :
    AnalyticOnNhd ℝ (fun eccentricity ↦
      resonantDisturbingAverage p q eccentricity orientation)
      {eccentricity | 0 < eccentricity ∧ eccentricity < 1 ∧
        resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1} := by
  intro eccentricity heccentricity
  exact analyticAt_resonantDisturbingAverage_eccentricity hp hq
    heccentricity.1 heccentricity.2.1 heccentricity.2.2

end LeanPool.PoincareThreeBody
