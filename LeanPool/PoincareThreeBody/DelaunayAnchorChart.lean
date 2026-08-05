/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.GlobalEnergySection
import LeanPool.PoincareThreeBody.ActionFactorization
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# A local Delaunay chart at the rational elliptic anchor

We combine the two Delaunay actions, eccentric anomaly, and apsidal orientation into a
four-dimensional chart.  Its derivative at the rational anchor is nonsingular, so its image
contains a phase-space neighborhood of the anchor.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

/-- Action and angle variables for the local four-dimensional chart. -/
abbrev DelaunayAnchorParameters := ActionSpace × (ℝ × ℝ)

/-- The action pair at the rational energy `-2` anchor. -/
noncomputable def delaunayAnchorAction : ActionSpace :=
  ![1 / Real.sqrt 3, (1 / 2 : ℝ)]

/-- Parameters corresponding to the rational phase point `(0, 1/6, -3, 0)`. -/
noncomputable def delaunayAnchorParameters : DelaunayAnchorParameters :=
  (delaunayAnchorAction, 0, Real.pi / 2)

/-- Full local Delaunay chart using eccentric anomaly as its first angle. -/
noncomputable def delaunayAnchorChart
    (parameters : DelaunayAnchorParameters) : PhaseSpace :=
  delaunayActionSectionAtAnomaly parameters.2.1 parameters.2.2 parameters.1

theorem delaunayAnchorAction_prograde :
    delaunayAnchorAction ∈ ProgradeEllipticActions := by
  rw [delaunayAnchorAction,
    ← cartesianDelaunayActions_globalEnergySection_neg_two]
  exact globalEnergySection_neg_two_action_prograde

theorem eccentricityFromActions_delaunayAnchorAction :
    eccentricityFromActions delaunayAnchorAction = (1 / 2 : ℝ) := by
  rw [delaunayAnchorAction,
    ← cartesianDelaunayActions_globalEnergySection_neg_two]
  exact eccentricityFromActions_globalEnergySection_neg_two

theorem delaunayAnchorChart_anchor :
    delaunayAnchorChart delaunayAnchorParameters = globalEnergySection (-2) := by
  rw [globalEnergySection_neg_two_eq_liftedDelaunayPhasePoint]
  unfold delaunayAnchorChart
  change delaunayActionSectionAtAnomaly 0 (Real.pi / 2) delaunayAnchorAction =
    liftedDelaunayPhasePoint (1 / Real.sqrt 3) (1 / 2) 0 (Real.pi / 2)
  rw [delaunayActionSectionAtAnomaly_eq_liftedDelaunayPhasePoint
    delaunayAnchorAction_prograde]
  rw [eccentricityFromActions_delaunayAnchorAction]
  simp only [Matrix.cons_val_zero, eccentricMeanAnomaly,
    Real.sin_zero, mul_zero, sub_zero, delaunayAnchorAction]

/-- The full action/anomaly/orientation chart is analytic at the rational anchor. -/
theorem analyticAt_delaunayAnchorChart :
    AnalyticAt ℝ delaunayAnchorChart delaunayAnchorParameters := by
  let eccentricity : DelaunayAnchorParameters → ℝ := fun parameters ↦
    eccentricityFromActions parameters.1
  let firstAction : DelaunayAnchorParameters → ℝ := fun parameters ↦ parameters.1 0
  let anomaly : DelaunayAnchorParameters → ℝ := fun parameters ↦ parameters.2.1
  let orientation : DelaunayAnchorParameters → ℝ := fun parameters ↦ parameters.2.2
  let denominator : DelaunayAnchorParameters → ℝ := fun parameters ↦
    1 - eccentricity parameters * Real.cos (anomaly parameters)
  let sqrtOneMinusSquare : DelaunayAnchorParameters → ℝ := fun parameters ↦
    Real.sqrt (1 - eccentricity parameters ^ 2)
  let inverseCube : DelaunayAnchorParameters → ℝ := fun parameters ↦
    1 / firstAction parameters ^ 3
  have hfst : AnalyticAt ℝ (fun parameters : DelaunayAnchorParameters ↦ parameters.1)
      delaunayAnchorParameters :=
    (ContinuousLinearMap.fst ℝ ActionSpace (ℝ × ℝ)).analyticAt _
  have heccentricity : AnalyticAt ℝ eccentricity delaunayAnchorParameters := by
    change AnalyticAt ℝ (fun parameters : DelaunayAnchorParameters ↦
      eccentricityFromActions parameters.1) delaunayAnchorParameters
    convert (analyticAt_eccentricityFromActions delaunayAnchorAction_prograde).comp
      (f := fun parameters : DelaunayAnchorParameters ↦ parameters.1) hfst using 1
    rfl
  have hfirstAction : AnalyticAt ℝ firstAction delaunayAnchorParameters :=
    ((ContinuousLinearMap.proj 0 : ActionSpace →L[ℝ] ℝ).analyticAt _).comp hfst
  have hanomaly : AnalyticAt ℝ anomaly delaunayAnchorParameters := by
    exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ActionSpace (ℝ × ℝ))).analyticAt _
  have horientation : AnalyticAt ℝ orientation delaunayAnchorParameters := by
    exact ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ActionSpace (ℝ × ℝ))).analyticAt _
  have hfirstActionNe : firstAction delaunayAnchorParameters ≠ 0 := by
    dsimp only [firstAction, delaunayAnchorParameters, delaunayAnchorAction]
    exact one_div_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hdenominator : AnalyticAt ℝ denominator delaunayAnchorParameters := by
    dsimp only [denominator]
    exact analyticAt_const.sub (heccentricity.mul (Real.analyticAt_cos.comp hanomaly))
  have hdenominatorNe : denominator delaunayAnchorParameters ≠ 0 := by
    dsimp only [denominator, eccentricity, anomaly, delaunayAnchorParameters]
    rw [eccentricityFromActions_delaunayAnchorAction]
    norm_num
  have hsqrt : AnalyticAt ℝ sqrtOneMinusSquare delaunayAnchorParameters := by
    have hargument : AnalyticAt ℝ
        (fun parameters : DelaunayAnchorParameters ↦
          1 - eccentricity parameters ^ 2) delaunayAnchorParameters :=
      analyticAt_const.sub (heccentricity.pow 2)
    have hargumentPos :
        0 < 1 - eccentricity delaunayAnchorParameters ^ 2 := by
      dsimp only [eccentricity, delaunayAnchorParameters]
      rw [eccentricityFromActions_delaunayAnchorAction]
      norm_num
    exact (analyticAt_sqrt_of_pos hargumentPos).comp
      (f := fun parameters : DelaunayAnchorParameters ↦
        1 - eccentricity parameters ^ 2) hargument
  have hinverseCube : AnalyticAt ℝ inverseCube delaunayAnchorParameters := by
    dsimp only [inverseCube]
    exact analyticAt_const.div (hfirstAction.pow 3)
      (pow_ne_zero 3 hfirstActionNe)
  let positionX : DelaunayAnchorParameters → ℝ := fun parameters ↦
    firstAction parameters ^ 2 *
      (Real.cos (anomaly parameters) - eccentricity parameters)
  let positionY : DelaunayAnchorParameters → ℝ := fun parameters ↦
    firstAction parameters ^ 2 * sqrtOneMinusSquare parameters *
      Real.sin (anomaly parameters)
  let momentumX : DelaunayAnchorParameters → ℝ := fun parameters ↦
    -firstAction parameters ^ 2 * inverseCube parameters *
      Real.sin (anomaly parameters) / denominator parameters
  let momentumY : DelaunayAnchorParameters → ℝ := fun parameters ↦
    firstAction parameters ^ 2 * inverseCube parameters *
      sqrtOneMinusSquare parameters * Real.cos (anomaly parameters) /
        denominator parameters
  have hpositionX : AnalyticAt ℝ positionX delaunayAnchorParameters := by
    exact (hfirstAction.pow 2).mul
      ((Real.analyticAt_cos.comp hanomaly).sub heccentricity)
  have hpositionY : AnalyticAt ℝ positionY delaunayAnchorParameters := by
    exact (((hfirstAction.pow 2).mul hsqrt).mul
      (Real.analyticAt_sin.comp hanomaly))
  have hmomentumX : AnalyticAt ℝ momentumX delaunayAnchorParameters := by
    exact ((((hfirstAction.pow 2).neg.mul hinverseCube).mul
      (Real.analyticAt_sin.comp hanomaly)).div hdenominator hdenominatorNe)
  have hmomentumY : AnalyticAt ℝ momentumY delaunayAnchorParameters := by
    exact (((((hfirstAction.pow 2).mul hinverseCube).mul hsqrt).mul
      (Real.analyticAt_cos.comp hanomaly)).div hdenominator hdenominatorNe)
  rw [analyticAt_pi_iff]
  intro coordinate
  fin_cases coordinate
  · change AnalyticAt ℝ (fun parameters ↦
      Real.cos (-orientation parameters) * positionX parameters +
        Real.sin (-orientation parameters) * positionY parameters)
      delaunayAnchorParameters
    exact (((Real.analyticAt_cos.comp horientation.neg).mul hpositionX).add
      ((Real.analyticAt_sin.comp horientation.neg).mul hpositionY))
  · change AnalyticAt ℝ (fun parameters ↦
      -Real.sin (-orientation parameters) * positionX parameters +
        Real.cos (-orientation parameters) * positionY parameters)
      delaunayAnchorParameters
    exact (((Real.analyticAt_sin.comp horientation.neg).neg.mul hpositionX).add
      ((Real.analyticAt_cos.comp horientation.neg).mul hpositionY))
  · change AnalyticAt ℝ (fun parameters ↦
      Real.cos (-orientation parameters) * momentumX parameters +
        Real.sin (-orientation parameters) * momentumY parameters)
      delaunayAnchorParameters
    exact (((Real.analyticAt_cos.comp horientation.neg).mul hmomentumX).add
      ((Real.analyticAt_sin.comp horientation.neg).mul hmomentumY))
  · change AnalyticAt ℝ (fun parameters ↦
      -Real.sin (-orientation parameters) * momentumX parameters +
        Real.cos (-orientation parameters) * momentumY parameters)
      delaunayAnchorParameters
    exact (((Real.analyticAt_sin.comp horientation.neg).neg.mul hmomentumX).add
      ((Real.analyticAt_cos.comp horientation.neg).mul hmomentumY))

end LeanPool.PoincareThreeBody
