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

/-- Near the anchor, applying the physical action map to the chart recovers exactly the two
action parameters. -/
theorem cartesianDelaunayActions_delaunayAnchorChart_eventuallyEq :
    (fun parameters ↦ cartesianDelaunayActions (delaunayAnchorChart parameters))
      =ᶠ[nhds delaunayAnchorParameters]
        fun parameters : DelaunayAnchorParameters ↦ parameters.1 := by
  have hfirst : AnalyticAt ℝ
      (fun parameters : DelaunayAnchorParameters ↦ parameters.1)
      delaunayAnchorParameters :=
    (ContinuousLinearMap.fst ℝ ActionSpace (ℝ × ℝ)).analyticAt _
  have hprograde : ∀ᶠ parameters in nhds delaunayAnchorParameters,
      parameters.1 ∈ ProgradeEllipticActions :=
    hfirst.continuousAt.eventually
      (isOpen_progradeEllipticActions.mem_nhds delaunayAnchorAction_prograde)
  filter_upwards [hprograde] with parameters hparameters
  exact cartesianDelaunayActions_delaunayActionSectionAtAnomaly
    hparameters parameters.2.1 parameters.2.2

/-- The action component of the anchor-chart derivative is the projection to the two action
parameters.  This is the first half of nonsingularity of Delaunay coordinates. -/
theorem fderiv_cartesianDelaunayActions_comp_delaunayAnchorChart :
    (fderiv ℝ cartesianDelaunayActions
      (delaunayAnchorChart delaunayAnchorParameters)).comp
        (fderiv ℝ delaunayAnchorChart delaunayAnchorParameters) =
      ContinuousLinearMap.fst ℝ ActionSpace (ℝ × ℝ) := by
  have hposition :
      (globalEnergySection (-2) 0) ^ 2 + (globalEnergySection (-2) 1) ^ 2 ≠ 0 := by
    rw [globalEnergySection_neg_two]
    norm_num
  have henergy :
      cartesianKeplerEnergy (globalEnergySection (-2)) < 0 := by
    rw [cartesianKeplerEnergy_globalEnergySection_neg_two]
    norm_num
  have hactions : AnalyticAt ℝ cartesianDelaunayActions
      (delaunayAnchorChart delaunayAnchorParameters) := by
    rw [delaunayAnchorChart_anchor]
    exact analyticAt_cartesianDelaunayActions hposition henergy
  have hcomp := hactions.differentiableAt.hasFDerivAt.comp
    delaunayAnchorParameters analyticAt_delaunayAnchorChart.differentiableAt.hasFDerivAt
  rw [show
      (fderiv ℝ cartesianDelaunayActions
        (delaunayAnchorChart delaunayAnchorParameters)).comp
          (fderiv ℝ delaunayAnchorChart delaunayAnchorParameters) =
        fderiv ℝ
          (fun parameters ↦
            cartesianDelaunayActions (delaunayAnchorChart parameters))
          delaunayAnchorParameters by
      exact hcomp.fderiv.symm]
  rw [cartesianDelaunayActions_delaunayAnchorChart_eventuallyEq.fderiv_eq]
  exact fderiv_fst

/-- The same anchor torus, parametrized by mean anomaly and apsidal orientation. -/
noncomputable def delaunayAnchorMeanAngleChart (angles : ℝ × ℝ) : PhaseSpace :=
  liftedDelaunayPhasePoint (1 / Real.sqrt 3) (1 / 2) angles.1 angles.2

/-- The angle pair at the rational anchor. -/
noncomputable def delaunayAnchorMeanAngles : ℝ × ℝ :=
  (0, Real.pi / 2)

theorem analyticAt_delaunayAnchorMeanAngleChart :
    AnalyticAt ℝ delaunayAnchorMeanAngleChart delaunayAnchorMeanAngles := by
  exact analyticAt_liftedDelaunayPhasePoint_angles (by norm_num) (by norm_num) _

theorem delaunayAnchorMeanAngleChart_anchor :
    delaunayAnchorMeanAngleChart delaunayAnchorMeanAngles =
      globalEnergySection (-2) := by
  exact globalEnergySection_neg_two_eq_liftedDelaunayPhasePoint.symm

/-- Hamiltonian vectors commute with pulling an action covector back along an action
derivative. -/
theorem phaseHamiltonianVector_actionCovector_comp
    (actionDerivative : PhaseSpace →L[ℝ] ActionSpace) (vector : ActionSpace) :
    phaseHamiltonianVector ((actionCovector vector).comp actionDerivative) =
      actionHamiltonianTangentMap actionDerivative vector := by
  have hcovector : (actionCovector vector).comp actionDerivative =
      vector 0 • actionDerivativeCovector actionDerivative 0 +
        vector 1 • actionDerivativeCovector actionDerivative 1 := by
    apply ContinuousLinearMap.ext
    intro direction
    simp [actionCovector, actionDerivativeCovector]
    ring
  rw [hcovector, phaseHamiltonianVector_add,
    phaseHamiltonianVector_smul, phaseHamiltonianVector_smul]
  rfl

/-- The Hamiltonian vector of the mass-zero Hamiltonian differential is its explicit rotating
Kepler vector field. -/
theorem phaseHamiltonianVector_fderiv_hamiltonian_zero
    {state : PhaseSpace} (hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0) :
    phaseHamiltonianVector (fderiv ℝ (hamiltonian 0) state) =
      rotatingKeplerVectorField state := by
  rw [fderiv_hamiltonian_zero hposition]
  funext coordinate
  fin_cases coordinate <;>
    simp [phaseHamiltonianVector, rotatingKeplerDifferential,
      rotatingKeplerVectorField, coordinateVector] <;> ring

/-- The second angle direction is the Hamiltonian vector of angular momentum. -/
theorem fderiv_delaunayAnchorMeanAngleChart_orientation :
    fderiv ℝ delaunayAnchorMeanAngleChart delaunayAnchorMeanAngles (0, 1) =
      angularActionVectorField (globalEnergySection (-2)) := by
  have hline : HasDerivAt
      (fun angle : ℝ ↦ ((0 : ℝ), angle)) ((0 : ℝ), 1) (Real.pi / 2) :=
    (hasDerivAt_const (Real.pi / 2) (0 : ℝ)).prodMk
      (hasDerivAt_id (Real.pi / 2))
  have hchain :=
    analyticAt_delaunayAnchorMeanAngleChart.differentiableAt.hasFDerivAt.comp_hasDerivAt
      (Real.pi / 2) hline
  have hknown :=
    hasDerivAt_liftedDelaunayPhasePoint_periapsisAngle
      (1 / Real.sqrt 3) (1 / 2) 0 (Real.pi / 2)
  have hderivative := hchain.unique hknown
  simpa only [delaunayAnchorMeanAngleChart, delaunayAnchorMeanAngles,
    globalEnergySection_neg_two_eq_liftedDelaunayPhasePoint] using hderivative

/-- Advancing mean anomaly at Kepler frequency while decreasing the apsidal angle at unit speed
is the mass-zero Hamiltonian vector field. -/
theorem fderiv_delaunayAnchorMeanAngleChart_frequency :
    fderiv ℝ delaunayAnchorMeanAngleChart delaunayAnchorMeanAngles
        (1 / (1 / Real.sqrt 3) ^ 3, -1) =
      rotatingKeplerVectorField (globalEnergySection (-2)) := by
  let firstAction : ℝ := 1 / Real.sqrt 3
  have hfirstAction : firstAction ≠ 0 := by
    dsimp only [firstAction]
    exact one_div_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hmean : HasDerivAt
      (fun time : ℝ ↦ time / firstAction ^ 3)
      (1 / firstAction ^ 3) 0 :=
    (hasDerivAt_id 0).div_const (firstAction ^ 3)
  have horientation : HasDerivAt
      (fun time : ℝ ↦ Real.pi / 2 - time) (-1) 0 := by
    have hraw :=
      (hasDerivAt_const (x := 0) (Real.pi / 2)).sub (hasDerivAt_id 0)
    apply (hraw.congr_deriv (by ring)).congr_of_eventuallyEq
    filter_upwards [] with time
    rfl
  have hline : HasDerivAt
      (fun time : ℝ ↦
        (time / firstAction ^ 3, Real.pi / 2 - time))
      (1 / firstAction ^ 3, -1) 0 :=
    hmean.prodMk horientation
  have houter : HasFDerivAt delaunayAnchorMeanAngleChart
      (fderiv ℝ delaunayAnchorMeanAngleChart delaunayAnchorMeanAngles)
      (0 / firstAction ^ 3, Real.pi / 2 - 0) := by
    simpa only [zero_div, sub_zero, delaunayAnchorMeanAngles] using
      analyticAt_delaunayAnchorMeanAngleChart.differentiableAt.hasFDerivAt
  have hchain := houter.comp_hasDerivAt 0 hline
  have hknown := hasDerivAt_liftedDelaunayFlowLine
    (firstAction := firstAction) (eccentricity := (1 / 2 : ℝ))
    (meanAnomaly := 0) (periapsisAngle := Real.pi / 2) (time := 0)
    hfirstAction (by norm_num) (by norm_num)
  have hfunction :
      liftedDelaunayFlowLine firstAction (1 / 2) 0 (Real.pi / 2) =
        delaunayAnchorMeanAngleChart ∘
          (fun time : ℝ ↦
            (time / firstAction ^ 3, Real.pi / 2 - time)) := by
    funext time
    simp only [liftedDelaunayFlowLine, delaunayAnchorMeanAngleChart,
      Function.comp_apply, zero_add, firstAction]
  rw [hfunction] at hknown
  have hderivative := hchain.unique hknown
  have hderivative' :
      fderiv ℝ delaunayAnchorMeanAngleChart delaunayAnchorMeanAngles
          (1 / firstAction ^ 3, -1) =
        rotatingKeplerVectorField
          (delaunayAnchorMeanAngleChart delaunayAnchorMeanAngles) := by
    simpa only [Function.comp_apply, zero_div, sub_zero,
      delaunayAnchorMeanAngles] using hderivative
  rw [delaunayAnchorMeanAngleChart_anchor] at hderivative'
  simpa only [firstAction] using hderivative'

/-- At the anchor, the second basis vector of the action Hamiltonian tangent map is the angular
action flow. -/
theorem actionHamiltonianTangentMap_anchor_orientation :
    actionHamiltonianTangentMap
        (fderiv ℝ cartesianDelaunayActions (globalEnergySection (-2)))
        ![(0 : ℝ), 1] =
      angularActionVectorField (globalEnergySection (-2)) := by
  rw [actionHamiltonianTangentMap_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_smul,
    one_smul, zero_add]
  rw [globalEnergySection_neg_two_eq_liftedDelaunayPhasePoint]
  exact phaseHamiltonianVector_actionDerivativeCovector_one
    (by positivity) (by norm_num) (by norm_num)

/-- At the anchor, the Kepler frequency vector maps to the rotating Kepler flow. -/
theorem actionHamiltonianTangentMap_anchor_frequency :
    actionHamiltonianTangentMap
        (fderiv ℝ cartesianDelaunayActions (globalEnergySection (-2)))
        ![1 / (1 / Real.sqrt 3) ^ 3, (-1 : ℝ)] =
      rotatingKeplerVectorField (globalEnergySection (-2)) := by
  have hposition :
      (globalEnergySection (-2) 0) ^ 2 + (globalEnergySection (-2) 1) ^ 2 ≠ 0 := by
    rw [globalEnergySection_neg_two]
    norm_num
  have henergy : cartesianKeplerEnergy (globalEnergySection (-2)) < 0 := by
    rw [cartesianKeplerEnergy_globalEnergySection_neg_two]
    norm_num
  have hhamiltonian :=
    fderiv_hamiltonian_zero_eq_frequencyCovector_comp_actions hposition henergy
  have hvector := congrArg phaseHamiltonianVector hhamiltonian
  rw [phaseHamiltonianVector_fderiv_hamiltonian_zero hposition,
    phaseHamiltonianVector_actionCovector_comp] at hvector
  rw [cartesianDelaunayActions_globalEnergySection_neg_two] at hvector
  simpa only [delaunayFrequency, Matrix.cons_val_zero] using hvector.symm

theorem actionHamiltonianTangentMap_anchor_injective :
    Function.Injective
      (actionHamiltonianTangentMap
        (fderiv ℝ cartesianDelaunayActions (globalEnergySection (-2)))) := by
  have hright := fderiv_cartesianDelaunayActions_comp_sectionAtAnomaly
    delaunayAnchorAction_prograde 0 (Real.pi / 2)
  have hstate :
      delaunayActionSectionAtAnomaly 0 (Real.pi / 2) delaunayAnchorAction =
        globalEnergySection (-2) := by
    simpa only [delaunayAnchorChart, delaunayAnchorParameters] using
      delaunayAnchorChart_anchor
  rw [hstate] at hright
  exact actionHamiltonianTangentMap_injective_of_rightInverse hright

/-- The two mean-angle directions are linearly independent at the anchor. -/
theorem injective_fderiv_delaunayAnchorMeanAngleChart :
    Function.Injective
      (fderiv ℝ delaunayAnchorMeanAngleChart delaunayAnchorMeanAngles) := by
  let angleDerivative :=
    fderiv ℝ delaunayAnchorMeanAngleChart delaunayAnchorMeanAngles
  let actionDerivative :=
    fderiv ℝ cartesianDelaunayActions (globalEnergySection (-2))
  let tangentMap := actionHamiltonianTangentMap actionDerivative
  let meanMotion : ℝ := 1 / (1 / Real.sqrt 3) ^ 3
  have hmeanMotion : meanMotion ≠ 0 := by
    dsimp only [meanMotion]
    have hsqrt : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    positivity
  have htangentInjective : Function.Injective tangentMap := by
    exact actionHamiltonianTangentMap_anchor_injective
  intro first second hequal
  let difference : ℝ × ℝ := first - second
  let flowCoefficient : ℝ := difference.1 / meanMotion
  let rotationCoefficient : ℝ := difference.2 + flowCoefficient
  have hdifference : angleDerivative difference = 0 := by
    dsimp only [difference]
    rw [map_sub, hequal, sub_self]
  have hdecompose : difference =
      flowCoefficient • (meanMotion, (-1 : ℝ)) +
        rotationCoefficient • ((0 : ℝ), 1) := by
    apply Prod.ext
    · dsimp only [flowCoefficient, rotationCoefficient]
      change difference.1 =
        difference.1 / meanMotion * meanMotion +
          (difference.2 + difference.1 / meanMotion) * 0
      field_simp
      ring
    · dsimp only [flowCoefficient, rotationCoefficient]
      change difference.2 =
        difference.1 / meanMotion * (-1) +
          (difference.2 + difference.1 / meanMotion) * 1
      ring
  have hflow : angleDerivative (meanMotion, (-1 : ℝ)) =
      rotatingKeplerVectorField (globalEnergySection (-2)) := by
    exact fderiv_delaunayAnchorMeanAngleChart_frequency
  have hrotation : angleDerivative ((0 : ℝ), 1) =
      angularActionVectorField (globalEnergySection (-2)) := by
    exact fderiv_delaunayAnchorMeanAngleChart_orientation
  have htangentFlow : tangentMap ![meanMotion, (-1 : ℝ)] =
      rotatingKeplerVectorField (globalEnergySection (-2)) := by
    exact actionHamiltonianTangentMap_anchor_frequency
  have htangentRotation : tangentMap ![(0 : ℝ), 1] =
      angularActionVectorField (globalEnergySection (-2)) := by
    exact actionHamiltonianTangentMap_anchor_orientation
  have htangentZero : tangentMap
      (flowCoefficient • ![meanMotion, (-1 : ℝ)] +
        rotationCoefficient • ![(0 : ℝ), 1]) = 0 := by
    rw [map_add, map_smul, map_smul, htangentFlow, htangentRotation]
    rw [hdecompose, map_add, map_smul, map_smul, hflow, hrotation] at hdifference
    exact hdifference
  have hcoefficients :
      flowCoefficient • ![meanMotion, (-1 : ℝ)] +
        rotationCoefficient • ![(0 : ℝ), 1] = 0 := by
    apply htangentInjective
    simpa using htangentZero
  have hflowCoefficient : flowCoefficient = 0 := by
    have hcoordinate := congrFun hcoefficients 0
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero,
      smul_eq_mul, mul_zero, add_zero, Pi.zero_apply] at hcoordinate
    exact (mul_eq_zero.mp hcoordinate).resolve_right hmeanMotion
  have hrotationCoefficient : rotationCoefficient = 0 := by
    have hcoordinate := congrFun hcoefficients 1
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.cons_val_one,
      smul_eq_mul, Pi.zero_apply] at hcoordinate
    rw [hflowCoefficient] at hcoordinate
    simpa using hcoordinate
  have hdifferenceZero : difference = 0 := by
    rw [hdecompose, hflowCoefficient, hrotationCoefficient]
    simp
  exact sub_eq_zero.mp hdifferenceZero

/-- Convert eccentric anomaly to mean anomaly at the anchor eccentricity. -/
noncomputable def delaunayAnchorMeanFromEccentricAngles
    (angles : ℝ × ℝ) : ℝ × ℝ :=
  (eccentricMeanAnomaly (1 / 2) angles.1, angles.2)

/-- The angle slice of the full anchor chart. -/
noncomputable def delaunayAnchorEccentricAngleChart
    (angles : ℝ × ℝ) : PhaseSpace :=
  delaunayAnchorChart (delaunayAnchorAction, angles)

theorem delaunayAnchorEccentricAngleChart_eq_mean :
    delaunayAnchorEccentricAngleChart =
      delaunayAnchorMeanAngleChart ∘ delaunayAnchorMeanFromEccentricAngles := by
  funext angles
  unfold delaunayAnchorEccentricAngleChart delaunayAnchorChart
  rw [delaunayActionSectionAtAnomaly_eq_liftedDelaunayPhasePoint
    delaunayAnchorAction_prograde]
  rw [eccentricityFromActions_delaunayAnchorAction]
  rfl

theorem analyticAt_delaunayAnchorEccentricAngleChart :
    AnalyticAt ℝ delaunayAnchorEccentricAngleChart delaunayAnchorMeanAngles := by
  have hembedding : AnalyticAt ℝ
      (fun angles : ℝ × ℝ ↦ (delaunayAnchorAction, angles))
      delaunayAnchorMeanAngles :=
    analyticAt_const.prod analyticAt_id
  exact analyticAt_delaunayAnchorChart.comp
    (f := fun angles : ℝ × ℝ ↦ (delaunayAnchorAction, angles)) hembedding

theorem hasFDerivAt_delaunayAnchorMeanFromEccentricAngles :
    HasFDerivAt delaunayAnchorMeanFromEccentricAngles
      (((ContinuousLinearMap.toSpanSingleton ℝ (1 / 2 : ℝ)).comp
          (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ))
      delaunayAnchorMeanAngles := by
  have hmeanScalar : HasDerivAt (eccentricMeanAnomaly (1 / 2))
      (1 / 2 : ℝ) 0 := by
    convert hasDerivAt_eccentricMeanAnomaly (1 / 2) 0 using 1
    norm_num
  have hfst : HasFDerivAt (fun angles : ℝ × ℝ ↦ angles.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) delaunayAnchorMeanAngles :=
    hasFDerivAt_fst
  have hmean := hmeanScalar.hasFDerivAt.comp
    delaunayAnchorMeanAngles hfst
  exact hmean.prodMk hasFDerivAt_snd

theorem injective_fderiv_delaunayAnchorMeanFromEccentricAngles :
    Function.Injective
      (fderiv ℝ delaunayAnchorMeanFromEccentricAngles
        delaunayAnchorMeanAngles) := by
  rw [hasFDerivAt_delaunayAnchorMeanFromEccentricAngles.fderiv]
  intro first second hequal
  apply Prod.ext
  · have hfirst := congrArg Prod.fst hequal
    simpa using hfirst
  · have hsecond := congrArg Prod.snd hequal
    simpa using hsecond

/-- Replacing eccentric anomaly by mean anomaly preserves nonsingularity of the two angle
directions. -/
theorem injective_fderiv_delaunayAnchorEccentricAngleChart :
    Function.Injective
      (fderiv ℝ delaunayAnchorEccentricAngleChart
        delaunayAnchorMeanAngles) := by
  have houter : DifferentiableAt ℝ delaunayAnchorMeanAngleChart
      (delaunayAnchorMeanFromEccentricAngles delaunayAnchorMeanAngles) := by
    simpa only [delaunayAnchorMeanFromEccentricAngles,
      delaunayAnchorMeanAngles, eccentricMeanAnomaly, Real.sin_zero,
      mul_zero, sub_zero] using
        analyticAt_delaunayAnchorMeanAngleChart.differentiableAt
  have hinner :=
    hasFDerivAt_delaunayAnchorMeanFromEccentricAngles.differentiableAt
  have hchain :
      fderiv ℝ delaunayAnchorEccentricAngleChart delaunayAnchorMeanAngles =
        (fderiv ℝ delaunayAnchorMeanAngleChart delaunayAnchorMeanAngles).comp
          (fderiv ℝ delaunayAnchorMeanFromEccentricAngles
            delaunayAnchorMeanAngles) := by
    rw [delaunayAnchorEccentricAngleChart_eq_mean]
    have hresult := fderiv_comp delaunayAnchorMeanAngles houter hinner
    have hmapAnchor :
        delaunayAnchorMeanFromEccentricAngles delaunayAnchorMeanAngles =
          delaunayAnchorMeanAngles := by
      simp [delaunayAnchorMeanFromEccentricAngles,
        delaunayAnchorMeanAngles, eccentricMeanAnomaly]
    rw [hmapAnchor] at hresult
    exact hresult
  rw [hchain]
  exact injective_fderiv_delaunayAnchorMeanAngleChart.comp
    injective_fderiv_delaunayAnchorMeanFromEccentricAngles

/-- Restricting the full chart derivative to pure angle directions gives the derivative of the
two-angle slice. -/
theorem fderiv_delaunayAnchorChart_comp_angleEmbedding :
    (fderiv ℝ delaunayAnchorChart delaunayAnchorParameters).comp
        ((0 : (ℝ × ℝ) →L[ℝ] ActionSpace).prod
          (ContinuousLinearMap.id ℝ (ℝ × ℝ))) =
      fderiv ℝ delaunayAnchorEccentricAngleChart
        delaunayAnchorMeanAngles := by
  have hembedding : HasFDerivAt
      (fun angles : ℝ × ℝ ↦ (delaunayAnchorAction, angles))
      ((0 : (ℝ × ℝ) →L[ℝ] ActionSpace).prod
        (ContinuousLinearMap.id ℝ (ℝ × ℝ)))
      delaunayAnchorMeanAngles :=
    (hasFDerivAt_const delaunayAnchorAction delaunayAnchorMeanAngles).prodMk
      (ContinuousLinearMap.id ℝ (ℝ × ℝ)).hasFDerivAt
  have houter : HasFDerivAt delaunayAnchorChart
      (fderiv ℝ delaunayAnchorChart delaunayAnchorParameters)
      (delaunayAnchorAction, delaunayAnchorMeanAngles) := by
    simpa only [delaunayAnchorParameters, delaunayAnchorMeanAngles] using
      analyticAt_delaunayAnchorChart.differentiableAt.hasFDerivAt
  have hchain := houter.comp delaunayAnchorMeanAngles hembedding
  rw [show delaunayAnchorEccentricAngleChart =
      delaunayAnchorChart ∘
        (fun angles : ℝ × ℝ ↦ (delaunayAnchorAction, angles)) by rfl]
  exact hchain.fderiv.symm

/-- The full four-dimensional Delaunay chart has injective derivative at the rational anchor. -/
theorem injective_fderiv_delaunayAnchorChart :
    Function.Injective
      (fderiv ℝ delaunayAnchorChart delaunayAnchorParameters) := by
  let chartDerivative :=
    fderiv ℝ delaunayAnchorChart delaunayAnchorParameters
  intro first second hequal
  let difference : DelaunayAnchorParameters := first - second
  have hdifference : chartDerivative difference = 0 := by
    dsimp only [difference]
    rw [map_sub, hequal, sub_self]
  have hactionZero : difference.1 = 0 := by
    have happly := congrArg
      (fun derivative : DelaunayAnchorParameters →L[ℝ] ActionSpace ↦
        derivative difference)
      fderiv_cartesianDelaunayActions_comp_delaunayAnchorChart
    dsimp only [chartDerivative] at hdifference
    rw [ContinuousLinearMap.comp_apply, hdifference, map_zero] at happly
    simpa using happly.symm
  have hangleDerivative :
      fderiv ℝ delaunayAnchorEccentricAngleChart
          delaunayAnchorMeanAngles difference.2 = 0 := by
    have happly := congrArg
      (fun derivative : (ℝ × ℝ) →L[ℝ] PhaseSpace ↦
        derivative difference.2)
      fderiv_delaunayAnchorChart_comp_angleEmbedding
    have hembedding :
        ((0 : (ℝ × ℝ) →L[ℝ] ActionSpace).prod
          (ContinuousLinearMap.id ℝ (ℝ × ℝ))) difference.2 =
            difference := by
      apply Prod.ext
      · simpa using hactionZero.symm
      · rfl
    rw [ContinuousLinearMap.comp_apply, hembedding] at happly
    dsimp only [chartDerivative] at hdifference
    rw [hdifference] at happly
    exact happly.symm
  have hangleZero : difference.2 = 0 := by
    apply injective_fderiv_delaunayAnchorEccentricAngleChart
    simpa using hangleDerivative
  have hdifferenceZero : difference = 0 := by
    apply Prod.ext
    · exact hactionZero
    · exact hangleZero
  exact sub_eq_zero.mp hdifferenceZero

/-- The full derivative is onto because its four-dimensional domain and codomain have equal
finite dimension. -/
theorem surjective_fderiv_delaunayAnchorChart :
    Function.Surjective
      (fderiv ℝ delaunayAnchorChart delaunayAnchorParameters) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ)
    (V := DelaunayAnchorParameters) (V₂ := PhaseSpace) ?_).mp
  · exact injective_fderiv_delaunayAnchorChart
  · simp [DelaunayAnchorParameters, ActionSpace, PhaseSpace,
      Module.finrank_prod]

/-- The analytic anchor chart maps the parameter-space neighborhood filter onto the phase-space
neighborhood filter.  Thus any identity proved for all nearby Delaunay parameters holds on an
actual open phase-space neighborhood of the rational anchor. -/
theorem map_delaunayAnchorChart_nhds :
    Filter.map delaunayAnchorChart (nhds delaunayAnchorParameters) =
      nhds (globalEnergySection (-2)) := by
  rw [← delaunayAnchorChart_anchor]
  have hsmooth : ContDiffAt ℝ 1 delaunayAnchorChart delaunayAnchorParameters :=
    analyticAt_delaunayAnchorChart.contDiffAt
  apply (hsmooth.hasStrictFDerivAt (by norm_num)).map_nhds_eq_of_surj
  exact LinearMap.range_eq_top.mpr surjective_fderiv_delaunayAnchorChart

end LeanPool.PoincareThreeBody
