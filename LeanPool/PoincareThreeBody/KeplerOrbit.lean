/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.GeneratingFunction
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Elliptic Kepler orbits in eccentric anomaly

This file gives the real elliptic Kepler orbit attached to Delaunay action `I₁` and eccentricity
`e`. It verifies the radius, radial momentum, and energy formulas directly. The mean anomaly is the
first Delaunay angle along the unperturbed flow.
-/

namespace LeanPool.PoincareThreeBody

/-- Radius of an elliptic Kepler orbit as a function of eccentric anomaly. -/
noncomputable def eccentricRadius (firstAction eccentricity anomaly : ℝ) : ℝ :=
  firstAction ^ 2 * (1 - eccentricity * Real.cos anomaly)

/-- Radial momentum of an elliptic Kepler orbit as a function of eccentric anomaly. -/
noncomputable def eccentricRadialMomentum
    (firstAction eccentricity anomaly : ℝ) : ℝ :=
  eccentricity * Real.sin anomaly /
    (firstAction * (1 - eccentricity * Real.cos anomaly))

/-- Mean anomaly as a function of eccentric anomaly (Kepler's equation). -/
noncomputable def eccentricMeanAnomaly (eccentricity anomaly : ℝ) : ℝ :=
  anomaly - eccentricity * Real.sin anomaly

/-- Physical Kepler time, normalized to vanish with the mean anomaly. -/
noncomputable def eccentricKeplerTime
    (firstAction eccentricity anomaly : ℝ) : ℝ :=
  firstAction ^ 3 * eccentricMeanAnomaly eccentricity anomaly

/-- A polar phase-space point on the elliptic Kepler orbit. Its angular coordinate is free because
the inertial Kepler energy is rotation invariant. -/
noncomputable def eccentricPolarState
    (firstAction eccentricity anomaly polarAngle : ℝ) : PolarState :=
  ![eccentricRadius firstAction eccentricity anomaly,
    polarAngle,
    eccentricRadialMomentum firstAction eccentricity anomaly,
    angularActionFromEccentricity firstAction eccentricity]

lemma one_sub_eccentricity_mul_cos_pos {eccentricity anomaly : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    0 < 1 - eccentricity * Real.cos anomaly := by
  have hcos : eccentricity * Real.cos anomaly ≤ eccentricity :=
    mul_le_of_le_one_right heccentricity (Real.cos_le_one anomaly)
  linarith

lemma eccentricRadius_pos {firstAction eccentricity anomaly : ℝ}
    (hfirstAction : firstAction ≠ 0) (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) :
    0 < eccentricRadius firstAction eccentricity anomaly := by
  unfold eccentricRadius
  exact mul_pos (sq_pos_of_ne_zero hfirstAction)
    (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne)

theorem hasDerivAt_eccentricMeanAnomaly (eccentricity anomaly : ℝ) :
    HasDerivAt (eccentricMeanAnomaly eccentricity)
      (1 - eccentricity * Real.cos anomaly) anomaly := by
  have hraw := (hasDerivAt_id anomaly).sub
    ((Real.hasDerivAt_sin anomaly).const_mul eccentricity)
  apply (hraw.congr_deriv (by ring)).congr_of_eventuallyEq
  filter_upwards [] with argument
  simp [eccentricMeanAnomaly]

theorem hasDerivAt_eccentricRadius (firstAction eccentricity anomaly : ℝ) :
    HasDerivAt (eccentricRadius firstAction eccentricity)
      (firstAction ^ 2 * eccentricity * Real.sin anomaly) anomaly := by
  have hraw := (((Real.hasDerivAt_cos anomaly).const_mul (-eccentricity)).add_const 1).const_mul
    (firstAction ^ 2)
  apply (hraw.congr_deriv (by ring)).congr_of_eventuallyEq
  filter_upwards [] with argument
  simp only [eccentricRadius]
  ring

theorem hasDerivAt_eccentricKeplerTime (firstAction eccentricity anomaly : ℝ) :
    HasDerivAt (eccentricKeplerTime firstAction eccentricity)
      (firstAction ^ 3 * (1 - eccentricity * Real.cos anomaly)) anomaly := by
  have hraw := (hasDerivAt_eccentricMeanAnomaly eccentricity anomaly).const_mul
    (firstAction ^ 3)
  apply hraw.congr_of_eventuallyEq
  filter_upwards [] with argument
  rfl

/-- The radial momentum is `dr/dt` along the eccentric-anomaly parameterization. -/
theorem eccentricRadialMomentum_eq_radiusDeriv_div_timeDeriv
    {firstAction eccentricity anomaly : ℝ} (hfirstAction : firstAction ≠ 0)
    (hdenominator : 1 - eccentricity * Real.cos anomaly ≠ 0) :
    eccentricRadialMomentum firstAction eccentricity anomaly =
      (firstAction ^ 2 * eccentricity * Real.sin anomaly) /
        (firstAction ^ 3 * (1 - eccentricity * Real.cos anomaly)) := by
  unfold eccentricRadialMomentum
  field_simp [hfirstAction, hdenominator]

theorem strictMono_eccentricMeanAnomaly {eccentricity : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    StrictMono (eccentricMeanAnomaly eccentricity) := by
  apply strictMono_of_hasDerivAt_pos (hasDerivAt_eccentricMeanAnomaly eccentricity)
  intro anomaly
  exact one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne

lemma eccentricMeanAnomaly_add_two_pi (eccentricity anomaly : ℝ) :
    eccentricMeanAnomaly eccentricity (anomaly + 2 * Real.pi) =
      eccentricMeanAnomaly eccentricity anomaly + 2 * Real.pi := by
  simp [eccentricMeanAnomaly]
  ring

lemma eccentricMeanAnomaly_add_nat_mul_two_pi
    (eccentricity anomaly : ℝ) (turns : ℕ) :
    eccentricMeanAnomaly eccentricity (anomaly + turns * (2 * Real.pi)) =
      eccentricMeanAnomaly eccentricity anomaly + turns * (2 * Real.pi) := by
  simp [eccentricMeanAnomaly]
  ring

lemma eccentricMeanAnomaly_lower_bound {eccentricity anomaly : ℝ}
    (heccentricity : 0 ≤ eccentricity) :
    anomaly - eccentricity ≤ eccentricMeanAnomaly eccentricity anomaly := by
  have hsin := mul_le_mul_of_nonneg_left (Real.sin_le_one anomaly) heccentricity
  unfold eccentricMeanAnomaly
  linarith

lemma eccentricMeanAnomaly_upper_bound {eccentricity anomaly : ℝ}
    (heccentricity : 0 ≤ eccentricity) :
    eccentricMeanAnomaly eccentricity anomaly ≤ anomaly + eccentricity := by
  have hsin := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin anomaly) heccentricity
  unfold eccentricMeanAnomaly
  linarith

theorem continuous_eccentricMeanAnomaly (eccentricity : ℝ) :
    Continuous (eccentricMeanAnomaly eccentricity) := by
  rw [continuous_iff_continuousAt]
  intro anomaly
  exact (hasDerivAt_eccentricMeanAnomaly eccentricity anomaly).continuousAt

theorem analyticAt_eccentricMeanAnomaly (eccentricity anomaly : ℝ) :
    AnalyticAt ℝ (eccentricMeanAnomaly eccentricity) anomaly := by
  have hscaled := (Real.analyticAt_sin (x := anomaly)).const_smul (c := eccentricity)
  have hraw := (analyticAt_id (z := anomaly)).sub hscaled
  apply hraw.congr
  filter_upwards [] with argument
  simp [eccentricMeanAnomaly, smul_eq_mul]

theorem surjective_eccentricMeanAnomaly {eccentricity : ℝ}
    (heccentricity : 0 ≤ eccentricity) :
    Function.Surjective (eccentricMeanAnomaly eccentricity) := by
  intro meanAnomaly
  let lower := meanAnomaly - eccentricity - 1
  let upper := meanAnomaly + eccentricity + 1
  have hlowerUpper : lower ≤ upper := by
    dsimp [lower, upper]
    linarith
  have hlower : eccentricMeanAnomaly eccentricity lower ≤ meanAnomaly := by
    calc
      eccentricMeanAnomaly eccentricity lower ≤ lower + eccentricity :=
        eccentricMeanAnomaly_upper_bound heccentricity
      _ ≤ meanAnomaly := by dsimp [lower]; linarith
  have hupper : meanAnomaly ≤ eccentricMeanAnomaly eccentricity upper := by
    calc
      meanAnomaly ≤ upper - eccentricity := by dsimp [upper]; linarith
      _ ≤ eccentricMeanAnomaly eccentricity upper :=
        eccentricMeanAnomaly_lower_bound heccentricity
  obtain ⟨anomaly, _, hanomaly⟩ := Set.mem_image _ _ _ |>.mp
    (intermediate_value_Icc hlowerUpper
      (continuous_eccentricMeanAnomaly eccentricity).continuousOn ⟨hlower, hupper⟩)
  exact ⟨anomaly, hanomaly⟩

theorem bijective_eccentricMeanAnomaly {eccentricity : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    Function.Bijective (eccentricMeanAnomaly eccentricity) :=
  ⟨(strictMono_eccentricMeanAnomaly heccentricity heccentricityOne).injective,
    surjective_eccentricMeanAnomaly heccentricity⟩

/-- The unique eccentric anomaly solving Kepler's equation for a given mean anomaly. -/
noncomputable def eccentricAnomaly (eccentricity meanAnomaly : ℝ) : ℝ :=
  Function.invFun (eccentricMeanAnomaly eccentricity) meanAnomaly

theorem eccentricMeanAnomaly_eccentricAnomaly {eccentricity : ℝ}
    (heccentricity : 0 ≤ eccentricity) (meanAnomaly : ℝ) :
    eccentricMeanAnomaly eccentricity (eccentricAnomaly eccentricity meanAnomaly) =
      meanAnomaly := by
  exact Function.rightInverse_invFun (surjective_eccentricMeanAnomaly heccentricity) meanAnomaly

theorem eccentricAnomaly_eccentricMeanAnomaly {eccentricity : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (anomaly : ℝ) :
    eccentricAnomaly eccentricity (eccentricMeanAnomaly eccentricity anomaly) = anomaly := by
  exact Function.leftInverse_invFun
    (strictMono_eccentricMeanAnomaly heccentricity heccentricityOne).injective anomaly

theorem eccentricAnomaly_add_two_pi {eccentricity meanAnomaly : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    eccentricAnomaly eccentricity (meanAnomaly + 2 * Real.pi) =
      eccentricAnomaly eccentricity meanAnomaly + 2 * Real.pi := by
  apply (strictMono_eccentricMeanAnomaly heccentricity heccentricityOne).injective
  rw [eccentricMeanAnomaly_eccentricAnomaly heccentricity,
    eccentricMeanAnomaly_add_two_pi,
    eccentricMeanAnomaly_eccentricAnomaly heccentricity]

theorem eccentricAnomaly_add_nat_mul_two_pi
    {eccentricity meanAnomaly : ℝ} (turns : ℕ)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    eccentricAnomaly eccentricity (meanAnomaly + turns * (2 * Real.pi)) =
      eccentricAnomaly eccentricity meanAnomaly + turns * (2 * Real.pi) := by
  apply (strictMono_eccentricMeanAnomaly heccentricity heccentricityOne).injective
  rw [eccentricMeanAnomaly_eccentricAnomaly heccentricity,
    eccentricMeanAnomaly_add_nat_mul_two_pi,
    eccentricMeanAnomaly_eccentricAnomaly heccentricity]

theorem continuous_eccentricAnomaly {eccentricity : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    Continuous (eccentricAnomaly eccentricity) := by
  let anomalyIso : ℝ ≃o ℝ :=
    (strictMono_eccentricMeanAnomaly heccentricity heccentricityOne).orderIsoOfSurjective
      (eccentricMeanAnomaly eccentricity) (surjective_eccentricMeanAnomaly heccentricity)
  have hinverse : eccentricAnomaly eccentricity = anomalyIso.symm := by
    funext meanAnomaly
    apply (strictMono_eccentricMeanAnomaly heccentricity heccentricityOne).injective
    rw [eccentricMeanAnomaly_eccentricAnomaly heccentricity]
    exact (anomalyIso.apply_symm_apply meanAnomaly).symm
  rw [hinverse]
  exact anomalyIso.symm.continuous

theorem hasDerivAt_eccentricAnomaly {eccentricity meanAnomaly : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    HasDerivAt (eccentricAnomaly eccentricity)
      (1 / (1 - eccentricity *
        Real.cos (eccentricAnomaly eccentricity meanAnomaly))) meanAnomaly := by
  have hpositive := one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne
    (anomaly := eccentricAnomaly eccentricity meanAnomaly)
  have hraw := HasDerivAt.of_local_left_inverse
    (continuous_eccentricAnomaly heccentricity heccentricityOne).continuousAt
    (hasDerivAt_eccentricMeanAnomaly eccentricity
      (eccentricAnomaly eccentricity meanAnomaly)) hpositive.ne'
    (Filter.Eventually.of_forall
      (eccentricMeanAnomaly_eccentricAnomaly heccentricity))
  exact hraw.congr_deriv (by simp [one_div])

theorem analyticAt_eccentricAnomaly {eccentricity meanAnomaly : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    AnalyticAt ℝ (eccentricAnomaly eccentricity) meanAnomaly := by
  let anomaly := eccentricAnomaly eccentricity meanAnomaly
  have hright : eccentricMeanAnomaly eccentricity anomaly = meanAnomaly :=
    eccentricMeanAnomaly_eccentricAnomaly heccentricity meanAnomaly
  have hforward := analyticAt_eccentricMeanAnomaly eccentricity anomaly
  have hderiv : deriv (eccentricMeanAnomaly eccentricity) anomaly ≠ 0 := by
    rw [(hasDerivAt_eccentricMeanAnomaly eccentricity anomaly).deriv]
    exact (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne).ne'
  rw [← hright]
  apply (analyticAt_comp_iff_of_deriv_ne_zero hforward hderiv).mp
  apply analyticAt_id.congr
  filter_upwards [] with argument
  exact (eccentricAnomaly_eccentricMeanAnomaly heccentricity heccentricityOne argument).symm

/-- Radius expressed as a function of the first Delaunay angle. -/
noncomputable def delaunayRadius
    (firstAction eccentricity meanAnomaly : ℝ) : ℝ :=
  eccentricRadius firstAction eccentricity (eccentricAnomaly eccentricity meanAnomaly)

lemma delaunayRadius_pos {firstAction eccentricity meanAnomaly : ℝ}
    (hfirstAction : firstAction ≠ 0) (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) :
    0 < delaunayRadius firstAction eccentricity meanAnomaly := by
  exact eccentricRadius_pos hfirstAction heccentricity heccentricityOne

lemma delaunayRadius_add_two_pi {firstAction eccentricity meanAnomaly : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    delaunayRadius firstAction eccentricity (meanAnomaly + 2 * Real.pi) =
      delaunayRadius firstAction eccentricity meanAnomaly := by
  unfold delaunayRadius eccentricRadius
  rw [eccentricAnomaly_add_two_pi heccentricity heccentricityOne]
  simp

lemma delaunayRadius_add_nat_mul_two_pi
    {firstAction eccentricity meanAnomaly : ℝ} (turns : ℕ)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    delaunayRadius firstAction eccentricity (meanAnomaly + turns * (2 * Real.pi)) =
      delaunayRadius firstAction eccentricity meanAnomaly := by
  unfold delaunayRadius eccentricRadius
  rw [eccentricAnomaly_add_nat_mul_two_pi turns heccentricity heccentricityOne]
  simp

theorem analyticAt_delaunayRadius {firstAction eccentricity meanAnomaly : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    AnalyticAt ℝ (delaunayRadius firstAction eccentricity) meanAnomaly := by
  have hanomaly := analyticAt_eccentricAnomaly
    (meanAnomaly := meanAnomaly) heccentricity heccentricityOne
  have hcos := Real.analyticAt_cos.comp hanomaly
  have hscaled := hcos.const_smul (c := eccentricity)
  have hone : AnalyticAt ℝ (fun _ : ℝ ↦ (1 : ℝ)) meanAnomaly := analyticAt_const
  have honeSub := hone.sub hscaled
  have hraw := honeSub.const_smul (c := firstAction ^ 2)
  apply hraw.congr
  filter_upwards [] with argument
  simp [delaunayRadius, eccentricRadius, smul_eq_mul]

/-- The eccentric-anomaly formulas lie on the inertial Kepler energy shell
`-1 / (2 * I₁²)`. -/
theorem polarKeplerEnergy_eccentricPolarState {firstAction eccentricity anomaly polarAngle : ℝ}
    (hfirstAction : firstAction ≠ 0) (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) :
    polarKeplerEnergy
        (eccentricPolarState firstAction eccentricity anomaly polarAngle) =
      -1 / (2 * firstAction ^ 2) := by
  have hdenominator : 1 - eccentricity * Real.cos anomaly ≠ 0 :=
    (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne).ne'
  have hsqrt : (Real.sqrt (1 - eccentricity ^ 2)) ^ 2 = 1 - eccentricity ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith
  have htrig := Real.sin_sq_add_cos_sq anomaly
  have hunit :
      eccentricity ^ 2 * Real.sin anomaly ^ 2 +
          eccentricity ^ 2 * Real.cos anomaly ^ 2 +
        (Real.sqrt (1 - eccentricity ^ 2)) ^ 2 = 1 := by
    rw [hsqrt]
    nlinarith
  have hscaled := congrArg (fun value : ℝ ↦ firstAction ^ 4 * value) hunit
  ring_nf at hscaled
  change
    ((eccentricRadialMomentum firstAction eccentricity anomaly) ^ 2 +
          (angularActionFromEccentricity firstAction eccentricity) ^ 2 /
            (eccentricRadius firstAction eccentricity anomaly) ^ 2) /
          2 -
        1 / eccentricRadius firstAction eccentricity anomaly =
      -1 / (2 * firstAction ^ 2)
  unfold eccentricRadialMomentum angularActionFromEccentricity eccentricRadius
  field_simp [hfirstAction, hdenominator]
  nlinarith only [hunit, hscaled]

end LeanPool.PoincareThreeBody
