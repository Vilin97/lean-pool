/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DelaunayActions
import LeanPool.PoincareThreeBody.DelaunayFlow
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# An analytic periapsis section of the planar Delaunay action map

For prograde elliptic actions `0 < G < L`, eccentricity is
`sqrt (1 - (G / L)²)`.  Setting eccentric anomaly and periapsis angle to zero gives an explicit
Cartesian phase point depending analytically on `(L,G)`.  This section is a right inverse of the
physical action map and supplies the action-space representative of the leading candidate
integral.
-/

namespace LeanPool.PoincareThreeBody


/-- Eccentricity reconstructed from prograde planar actions `(L,G)`. -/
noncomputable def eccentricityFromActions (action : ActionSpace) : ℝ :=
  Real.sqrt (1 - (action 1 / action 0) ^ 2)

/-- The open prograde elliptic action region. -/
def ProgradeEllipticActions : Set ActionSpace :=
  {action | 0 < action 1 ∧ action 1 < action 0}

lemma isOpen_progradeEllipticActions : IsOpen ProgradeEllipticActions := by
  exact (isOpen_lt continuous_const (continuous_apply 1)).inter
    (isOpen_lt (continuous_apply 1) (continuous_apply 0))

lemma eccentricityFromActions_nonneg (action : ActionSpace) :
    0 ≤ eccentricityFromActions action :=
  Real.sqrt_nonneg _

lemma ratio_actions_pos {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions) :
    0 < action 1 / action 0 := by
  exact div_pos haction.1 (haction.1.trans haction.2)

lemma ratio_actions_lt_one {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions) :
    action 1 / action 0 < 1 := by
  exact (div_lt_one (haction.1.trans haction.2)).2 haction.2

lemma eccentricityFromActions_pos {action : ActionSpace}
    (haction : action ∈ ProgradeEllipticActions) :
    0 < eccentricityFromActions action := by
  unfold eccentricityFromActions
  have hratioPos := ratio_actions_pos haction
  have hratioOne := ratio_actions_lt_one haction
  exact Real.sqrt_pos.2 (by nlinarith)

lemma eccentricityFromActions_lt_one {action : ActionSpace}
    (haction : action ∈ ProgradeEllipticActions) :
    eccentricityFromActions action < 1 := by
  unfold eccentricityFromActions
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
  nlinarith [sq_pos_of_pos (ratio_actions_pos haction)]

lemma eccentricityFromActions_sq {action : ActionSpace}
    (haction : action ∈ ProgradeEllipticActions) :
    eccentricityFromActions action ^ 2 = 1 - (action 1 / action 0) ^ 2 := by
  unfold eccentricityFromActions
  rw [Real.sq_sqrt]
  have hratioPos := ratio_actions_pos haction
  have hratioOne := ratio_actions_lt_one haction
  nlinarith

/-- Reconstructed eccentricity varies analytically throughout the prograde elliptic action
region. -/
theorem analyticAt_eccentricityFromActions
    {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions) :
    AnalyticAt ℝ eccentricityFromActions action := by
  have hcoordinate : ∀ coordinate : Fin 2,
      AnalyticAt ℝ (fun candidate : ActionSpace ↦ candidate coordinate) action :=
    fun coordinate ↦
      (ContinuousLinearMap.proj coordinate : ActionSpace →L[ℝ] ℝ).analyticAt action
  have hfirstAction : action 0 ≠ 0 := (haction.1.trans haction.2).ne'
  have hratio : AnalyticAt ℝ
      (fun candidate : ActionSpace ↦ candidate 1 / candidate 0) action :=
    (hcoordinate 1).div (hcoordinate 0) hfirstAction
  have hargument : AnalyticAt ℝ
      (fun candidate : ActionSpace ↦ 1 - (candidate 1 / candidate 0) ^ 2) action :=
    analyticAt_const.sub (hratio.pow 2)
  have hargumentPos : 0 < 1 - (action 1 / action 0) ^ 2 := by
    have hratioPos := ratio_actions_pos haction
    have hratioOne := ratio_actions_lt_one haction
    nlinarith
  unfold eccentricityFromActions
  exact (analyticAt_sqrt_of_pos hargumentPos).comp
    (f := fun candidate : ActionSpace ↦ 1 - (candidate 1 / candidate 0) ^ 2)
    hargument

/-- Recovering eccentricity from the actions of an ellipse returns its original eccentricity. -/
theorem eccentricityFromActions_angularActionFromEccentricity
    {firstAction eccentricity : ℝ} (hfirstAction : 0 < firstAction)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    eccentricityFromActions
        ![firstAction, angularActionFromEccentricity firstAction eccentricity] =
      eccentricity := by
  have hquotient :
      angularActionFromEccentricity firstAction eccentricity / firstAction =
        Real.sqrt (1 - eccentricity ^ 2) := by
    unfold angularActionFromEccentricity
    field_simp [hfirstAction.ne']
  have hsqrt : (Real.sqrt (1 - eccentricity ^ 2)) ^ 2 =
      1 - eccentricity ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith
  simp only [eccentricityFromActions, Matrix.cons_val_zero, Matrix.cons_val_one,
    hquotient, hsqrt]
  rw [show 1 - (1 - eccentricity ^ 2) = eccentricity ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_nonneg heccentricity]

/-- Reconstructing eccentricity from a prograde action pair and then rebuilding the angular
action returns the original pair. -/
theorem actions_from_eccentricityFromActions
    {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions) :
    ![action 0,
      angularActionFromEccentricity (action 0) (eccentricityFromActions action)] = action := by
  have heSquare := eccentricityFromActions_sq haction
  have hratioPos := ratio_actions_pos haction
  have hsqrt : Real.sqrt (1 - eccentricityFromActions action ^ 2) =
      action 1 / action 0 := by
    rw [heSquare, show 1 - (1 - (action 1 / action 0) ^ 2) =
      (action 1 / action 0) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos hratioPos]
  funext coordinate
  fin_cases coordinate
  · rfl
  · change action 0 * Real.sqrt (1 - eccentricityFromActions action ^ 2) = action 1
    rw [hsqrt]
    field_simp [(haction.1.trans haction.2).ne']

/-- Zero mean anomaly has zero eccentric anomaly throughout the elliptic range. -/
lemma eccentricAnomaly_zero {eccentricity : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    eccentricAnomaly eccentricity 0 = 0 := by
  have hinverse := eccentricAnomaly_eccentricMeanAnomaly
    heccentricity heccentricityOne 0
  simpa [eccentricMeanAnomaly] using hinverse

/-- Explicit phase point at periapsis, used as a section of the action map. -/
noncomputable def delaunayActionSection (action : ActionSpace) : PhaseSpace :=
  let eccentricity := eccentricityFromActions action
  positionMomentumPhasePoint
    (inertialEllipsePosition (action 0) eccentricity 0)
    (inertialEllipseVelocity (action 0) eccentricity (1 / action 0 ^ 3) 0)

/-- On the prograde elliptic region, the explicit section is the lifted Delaunay point with both
angles zero. -/
theorem delaunayActionSection_eq_liftedDelaunayPhasePoint
    {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions) :
    delaunayActionSection action =
      liftedDelaunayPhasePoint
        (action 0) (eccentricityFromActions action) 0 0 := by
  have heccentricity := eccentricityFromActions_nonneg action
  have heccentricityOne := eccentricityFromActions_lt_one haction
  have hanomaly := eccentricAnomaly_zero heccentricity heccentricityOne
  unfold delaunayActionSection liftedDelaunayPhasePoint liftedDelaunayPosition
    liftedDelaunayMomentum liftedDelaunayEccentricAnomaly
  rw [hanomaly]
  simp [positionInRotatingFrame, positionMomentumPhasePoint]

/-- The periapsis section realizes the prescribed action pair. -/
theorem cartesianDelaunayActions_delaunayActionSection
    {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions) :
    cartesianDelaunayActions (delaunayActionSection action) = action := by
  have hfirstAction : 0 < action 0 := haction.1.trans haction.2
  have heccentricity := eccentricityFromActions_nonneg action
  have heccentricityOne := eccentricityFromActions_lt_one haction
  rw [delaunayActionSection_eq_liftedDelaunayPhasePoint haction,
    cartesianDelaunayActions_liftedDelaunayPhasePoint hfirstAction
      heccentricity heccentricityOne]
  funext coordinate
  fin_cases coordinate
  · rfl
  · change angularActionFromEccentricity
      (action 0) (eccentricityFromActions action) = action 1
    unfold angularActionFromEccentricity
    have heSquare := eccentricityFromActions_sq haction
    have hratioPos := ratio_actions_pos haction
    have hfirstActionNe : action 0 ≠ 0 := hfirstAction.ne'
    have hsqrt : Real.sqrt (1 - eccentricityFromActions action ^ 2) =
        action 1 / action 0 := by
      rw [heSquare, show 1 - (1 - (action 1 / action 0) ^ 2) =
        (action 1 / action 0) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_pos hratioPos]
    rw [hsqrt]
    field_simp

/-- The explicit periapsis section is analytic on the prograde elliptic action region. -/
theorem analyticAt_delaunayActionSection
    {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions) :
    AnalyticAt ℝ delaunayActionSection action := by
  let eccentricity : ActionSpace → ℝ := eccentricityFromActions
  have heccentricity : AnalyticAt ℝ eccentricity action :=
    analyticAt_eccentricityFromActions haction
  have hfirstAction : AnalyticAt ℝ
      (fun candidate : ActionSpace ↦ candidate 0) action :=
    (ContinuousLinearMap.proj 0 : ActionSpace →L[ℝ] ℝ).analyticAt action
  have hfirstActionNe : action 0 ≠ 0 := (haction.1.trans haction.2).ne'
  have hdenominator : AnalyticAt ℝ
      (fun candidate : ActionSpace ↦ 1 - eccentricity candidate) action :=
    analyticAt_const.sub heccentricity
  have hdenominatorNe : 1 - eccentricity action ≠ 0 := by
    have := eccentricityFromActions_lt_one haction
    dsimp only [eccentricity]
    linarith
  have honeMinusSquare : AnalyticAt ℝ
      (fun candidate : ActionSpace ↦ 1 - eccentricity candidate ^ 2) action :=
    analyticAt_const.sub (heccentricity.pow 2)
  have honeMinusSquarePos : 0 < 1 - eccentricity action ^ 2 := by
    have heNonneg := eccentricityFromActions_nonneg action
    have heOne := eccentricityFromActions_lt_one haction
    dsimp only [eccentricity]
    nlinarith
  have hsqrt : AnalyticAt ℝ
      (fun candidate : ActionSpace ↦ Real.sqrt (1 - eccentricity candidate ^ 2)) action :=
    (analyticAt_sqrt_of_pos honeMinusSquarePos).comp
      (f := fun candidate : ActionSpace ↦ 1 - eccentricity candidate ^ 2)
      honeMinusSquare
  have hinverseCube : AnalyticAt ℝ
      (fun candidate : ActionSpace ↦ 1 / candidate 0 ^ 3) action :=
    analyticAt_const.div (hfirstAction.pow 3) (pow_ne_zero 3 hfirstActionNe)
  rw [analyticAt_pi_iff]
  intro coordinate
  fin_cases coordinate
  · simp only [delaunayActionSection, positionMomentumPhasePoint,
      inertialEllipsePosition, Matrix.cons_val_zero, Real.cos_zero]
    change AnalyticAt ℝ
      (fun candidate : ActionSpace ↦
        candidate 0 ^ 2 * (1 - eccentricity candidate)) action
    exact (hfirstAction.pow 2).mul hdenominator
  · simp only [delaunayActionSection, positionMomentumPhasePoint,
      inertialEllipsePosition, Matrix.cons_val_one, Real.sin_zero, mul_zero]
    change AnalyticAt ℝ (fun _ : ActionSpace ↦ (0 : ℝ)) action
    exact analyticAt_const
  · simp only [delaunayActionSection, positionMomentumPhasePoint,
      inertialEllipseVelocity, Matrix.cons_val_zero, Real.sin_zero, mul_zero,
      zero_div]
    change AnalyticAt ℝ (fun _ : ActionSpace ↦ (0 : ℝ)) action
    exact analyticAt_const
  · simp only [delaunayActionSection, positionMomentumPhasePoint,
      inertialEllipseVelocity, Matrix.cons_val_one, Real.cos_zero, mul_one]
    change AnalyticAt ℝ
      (fun candidate : ActionSpace ↦
        candidate 0 ^ 2 * (1 / candidate 0 ^ 3) *
          Real.sqrt (1 - eccentricity candidate ^ 2) /
            (1 - eccentricity candidate)) action
    exact ((((hfirstAction.pow 2).mul hinverseCube).mul hsqrt).div
      hdenominator hdenominatorNe)

/-- An action section through a prescribed eccentric anomaly and periapsis angle.  Fixing the
eccentric anomaly, rather than the mean anomaly, makes the dependence on the two actions
explicitly analytic. -/
noncomputable def delaunayActionSectionAtAnomaly
    (anomaly periapsisAngle : ℝ) (action : ActionSpace) : PhaseSpace :=
  let eccentricity := eccentricityFromActions action
  positionMomentumPhasePoint
    (positionInRotatingFrame (-periapsisAngle)
      (inertialEllipsePosition (action 0) eccentricity anomaly))
    (positionInRotatingFrame (-periapsisAngle)
      (inertialEllipseVelocity (action 0) eccentricity
        (1 / action 0 ^ 3) anomaly))

/-- The fixed-eccentric-anomaly section is a lifted Delaunay point whose mean anomaly is obtained
from Kepler's equation. -/
theorem delaunayActionSectionAtAnomaly_eq_liftedDelaunayPhasePoint
    {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions)
    (anomaly periapsisAngle : ℝ) :
    delaunayActionSectionAtAnomaly anomaly periapsisAngle action =
      liftedDelaunayPhasePoint (action 0) (eccentricityFromActions action)
        (eccentricMeanAnomaly (eccentricityFromActions action) anomaly)
        periapsisAngle := by
  have heccentricity := eccentricityFromActions_nonneg action
  have heccentricityOne := eccentricityFromActions_lt_one haction
  have hinverse := eccentricAnomaly_eccentricMeanAnomaly
    heccentricity heccentricityOne anomaly
  unfold delaunayActionSectionAtAnomaly liftedDelaunayPhasePoint
    liftedDelaunayPosition liftedDelaunayMomentum liftedDelaunayEccentricAnomaly
  rw [hinverse]

/-- Every fixed-eccentric-anomaly section is a right inverse of the Cartesian action map. -/
theorem cartesianDelaunayActions_delaunayActionSectionAtAnomaly
    {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions)
    (anomaly periapsisAngle : ℝ) :
    cartesianDelaunayActions
        (delaunayActionSectionAtAnomaly anomaly periapsisAngle action) = action := by
  have hfirstAction : 0 < action 0 := haction.1.trans haction.2
  have heccentricity := eccentricityFromActions_nonneg action
  have heccentricityOne := eccentricityFromActions_lt_one haction
  rw [delaunayActionSectionAtAnomaly_eq_liftedDelaunayPhasePoint haction,
    cartesianDelaunayActions_liftedDelaunayPhasePoint hfirstAction
      heccentricity heccentricityOne]
  funext coordinate
  fin_cases coordinate
  · rfl
  · change angularActionFromEccentricity
      (action 0) (eccentricityFromActions action) = action 1
    unfold angularActionFromEccentricity
    have heSquare := eccentricityFromActions_sq haction
    have hratioPos := ratio_actions_pos haction
    have hsqrt : Real.sqrt (1 - eccentricityFromActions action ^ 2) =
        action 1 / action 0 := by
      rw [heSquare, show 1 - (1 - (action 1 / action 0) ^ 2) =
        (action 1 / action 0) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_pos hratioPos]
    rw [hsqrt]
    field_simp

/-- With anomaly and periapsis held fixed, the moving action section is analytic throughout the
prograde elliptic action region. -/
theorem analyticAt_delaunayActionSectionAtAnomaly
    {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions)
    (anomaly periapsisAngle : ℝ) :
    AnalyticAt ℝ (delaunayActionSectionAtAnomaly anomaly periapsisAngle) action := by
  let eccentricity : ActionSpace → ℝ := eccentricityFromActions
  let firstAction : ActionSpace → ℝ := fun candidate ↦ candidate 0
  let denominator : ActionSpace → ℝ := fun candidate ↦
    1 - eccentricity candidate * Real.cos anomaly
  let sqrtOneMinusSquare : ActionSpace → ℝ := fun candidate ↦
    Real.sqrt (1 - eccentricity candidate ^ 2)
  let inverseCube : ActionSpace → ℝ := fun candidate ↦
    1 / firstAction candidate ^ 3
  have heccentricity : AnalyticAt ℝ eccentricity action :=
    analyticAt_eccentricityFromActions haction
  have hfirstAction : AnalyticAt ℝ firstAction action :=
    (ContinuousLinearMap.proj 0 : ActionSpace →L[ℝ] ℝ).analyticAt action
  have hfirstActionNe : firstAction action ≠ 0 :=
    (haction.1.trans haction.2).ne'
  have hdenominator : AnalyticAt ℝ denominator action := by
    dsimp only [denominator]
    exact analyticAt_const.sub (heccentricity.mul analyticAt_const)
  have hdenominatorNe : denominator action ≠ 0 := by
    dsimp only [denominator, eccentricity]
    exact (one_sub_eccentricity_mul_cos_pos
      (eccentricityFromActions_nonneg action)
      (eccentricityFromActions_lt_one haction)).ne'
  have hsqrt : AnalyticAt ℝ sqrtOneMinusSquare action := by
    have hargument : AnalyticAt ℝ
        (fun candidate : ActionSpace ↦ 1 - eccentricity candidate ^ 2) action :=
      analyticAt_const.sub (heccentricity.pow 2)
    have hargumentPos : 0 < 1 - eccentricity action ^ 2 := by
      have heNonneg := eccentricityFromActions_nonneg action
      have heOne := eccentricityFromActions_lt_one haction
      dsimp only [eccentricity]
      nlinarith
    exact (analyticAt_sqrt_of_pos hargumentPos).comp
      (f := fun candidate : ActionSpace ↦ 1 - eccentricity candidate ^ 2)
      hargument
  have hinverseCube : AnalyticAt ℝ inverseCube action := by
    dsimp only [inverseCube]
    exact analyticAt_const.div (hfirstAction.pow 3)
      (pow_ne_zero 3 hfirstActionNe)
  let positionX : ActionSpace → ℝ := fun candidate ↦
    firstAction candidate ^ 2 * (Real.cos anomaly - eccentricity candidate)
  let positionY : ActionSpace → ℝ := fun candidate ↦
    firstAction candidate ^ 2 * sqrtOneMinusSquare candidate * Real.sin anomaly
  let momentumX : ActionSpace → ℝ := fun candidate ↦
    -firstAction candidate ^ 2 * inverseCube candidate * Real.sin anomaly /
      denominator candidate
  let momentumY : ActionSpace → ℝ := fun candidate ↦
    firstAction candidate ^ 2 * inverseCube candidate *
      sqrtOneMinusSquare candidate * Real.cos anomaly / denominator candidate
  have hpositionX : AnalyticAt ℝ positionX action := by
    dsimp only [positionX]
    exact (hfirstAction.pow 2).mul (analyticAt_const.sub heccentricity)
  have hpositionY : AnalyticAt ℝ positionY action := by
    dsimp only [positionY]
    exact ((hfirstAction.pow 2).mul hsqrt).mul analyticAt_const
  have hmomentumX : AnalyticAt ℝ momentumX action := by
    dsimp only [momentumX]
    exact ((((hfirstAction.pow 2).neg.mul hinverseCube).mul
      analyticAt_const).div hdenominator hdenominatorNe)
  have hmomentumY : AnalyticAt ℝ momentumY action := by
    dsimp only [momentumY]
    exact (((((hfirstAction.pow 2).mul hinverseCube).mul hsqrt).mul
      analyticAt_const).div hdenominator hdenominatorNe)
  rw [analyticAt_pi_iff]
  intro coordinate
  fin_cases coordinate
  · change AnalyticAt ℝ
      (fun candidate ↦ Real.cos (-periapsisAngle) * positionX candidate +
        Real.sin (-periapsisAngle) * positionY candidate) action
    exact (analyticAt_const.mul hpositionX).add (analyticAt_const.mul hpositionY)
  · change AnalyticAt ℝ
      (fun candidate ↦ -Real.sin (-periapsisAngle) * positionX candidate +
        Real.cos (-periapsisAngle) * positionY candidate) action
    exact (analyticAt_const.mul hpositionX).add (analyticAt_const.mul hpositionY)
  · change AnalyticAt ℝ
      (fun candidate ↦ Real.cos (-periapsisAngle) * momentumX candidate +
        Real.sin (-periapsisAngle) * momentumY candidate) action
    exact (analyticAt_const.mul hmomentumX).add (analyticAt_const.mul hmomentumY)
  · change AnalyticAt ℝ
      (fun candidate ↦ -Real.sin (-periapsisAngle) * momentumX candidate +
        Real.cos (-periapsisAngle) * momentumY candidate) action
    exact (analyticAt_const.mul hmomentumX).add (analyticAt_const.mul hmomentumY)

/-- Choosing the anomaly of a lifted point makes the moving action section pass through that
point. -/
theorem delaunayActionSectionAtAnomaly_liftedDelaunayActions
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1) :
    delaunayActionSectionAtAnomaly
        (eccentricAnomaly eccentricity meanAnomaly) periapsisAngle
        ![firstAction, angularActionFromEccentricity firstAction eccentricity] =
      liftedDelaunayPhasePoint firstAction eccentricity meanAnomaly periapsisAngle := by
  let action : ActionSpace :=
    ![firstAction, angularActionFromEccentricity firstAction eccentricity]
  have haction : action ∈ ProgradeEllipticActions :=
    ⟨angularActionFromEccentricity_pos hfirstAction heccentricity heccentricityOne,
      angularActionFromEccentricity_lt_firstAction hfirstAction heccentricity⟩
  have heRecover : eccentricityFromActions action = eccentricity :=
    eccentricityFromActions_angularActionFromEccentricity hfirstAction
      heccentricity.le heccentricityOne
  rw [delaunayActionSectionAtAnomaly_eq_liftedDelaunayPhasePoint haction]
  change liftedDelaunayPhasePoint firstAction (eccentricityFromActions action)
      (eccentricMeanAnomaly (eccentricityFromActions action)
        (eccentricAnomaly eccentricity meanAnomaly)) periapsisAngle = _
  rw [heRecover, eccentricMeanAnomaly_eccentricAnomaly heccentricity.le]

/-- The derivative of every moving action section is a linear right inverse of the derivative of
the physical action map. -/
theorem fderiv_cartesianDelaunayActions_comp_sectionAtAnomaly
    {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions)
    (anomaly periapsisAngle : ℝ) :
    (fderiv ℝ cartesianDelaunayActions
      (delaunayActionSectionAtAnomaly anomaly periapsisAngle action)).comp
        (fderiv ℝ (delaunayActionSectionAtAnomaly anomaly periapsisAngle) action) =
      ContinuousLinearMap.id ℝ ActionSpace := by
  let movingSection := delaunayActionSectionAtAnomaly anomaly periapsisAngle
  let state := movingSection action
  have hsection : AnalyticAt ℝ movingSection action :=
    analyticAt_delaunayActionSectionAtAnomaly haction anomaly periapsisAngle
  have hfirstAction : 0 < action 0 := haction.1.trans haction.2
  have heccentricity := eccentricityFromActions_nonneg action
  have heccentricityOne := eccentricityFromActions_lt_one haction
  have hstate : state = liftedDelaunayPhasePoint (action 0)
      (eccentricityFromActions action)
      (eccentricMeanAnomaly (eccentricityFromActions action) anomaly)
      periapsisAngle :=
    delaunayActionSectionAtAnomaly_eq_liftedDelaunayPhasePoint haction _ _
  have hactions : AnalyticAt ℝ cartesianDelaunayActions state :=
    hstate.symm ▸ analyticAt_cartesianDelaunayActions_liftedDelaunayPhasePoint
      hfirstAction heccentricity heccentricityOne
  have hcomp := hactions.differentiableAt.hasFDerivAt.comp action
    hsection.differentiableAt.hasFDerivAt
  have heventual : (fun candidate ↦ cartesianDelaunayActions (movingSection candidate))
      =ᶠ[nhds action] id := by
    filter_upwards [isOpen_progradeEllipticActions.mem_nhds haction] with candidate hcandidate
    exact cartesianDelaunayActions_delaunayActionSectionAtAnomaly
      hcandidate anomaly periapsisAngle
  rw [show (fderiv ℝ cartesianDelaunayActions state).comp
      (fderiv ℝ movingSection action) =
        fderiv ℝ (fun candidate ↦ cartesianDelaunayActions (movingSection candidate)) action by
      exact hcomp.fderiv.symm]
  rw [heventual.fderiv_eq]
  exact fderiv_id

/-- The leading, mass-zero candidate integral represented on the explicit action section. -/
noncomputable def leadingActionCoefficient
    (F : ℝ → PhaseSpace → ℝ) (action : ActionSpace) : ℝ :=
  F 0 (delaunayActionSection action)

/-- On an interior prograde elliptic action, the leading action coefficient is analytic. -/
theorem IsJointlyAnalytic.analyticAt_leadingActionCoefficient
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F)
    {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions)
    (hapoapsis : action 0 ^ 2 * (1 + eccentricityFromActions action) < 1) :
    AnalyticAt ℝ (leadingActionCoefficient F) action := by
  let eccentricity := eccentricityFromActions action
  let state := delaunayActionSection action
  have hfirstAction : 0 < action 0 := haction.1.trans haction.2
  have heccentricity : 0 ≤ eccentricity := eccentricityFromActions_nonneg action
  have heccentricityOne : eccentricity < 1 := eccentricityFromActions_lt_one haction
  have hsectionIdentity : state =
      liftedDelaunayPhasePoint (action 0) eccentricity 0 0 :=
    delaunayActionSection_eq_liftedDelaunayPhasePoint haction
  have hcollision : (0, state) ∈ collisionFree := by
    rw [hsectionIdentity]
    exact liftedDelaunayPhasePoint_collisionFree_mass_zero hfirstAction.ne'
      heccentricity heccentricityOne hapoapsis
  have hdomain : (0, state) ∈ parameterDomain δ :=
    ⟨by simpa using hδ, hcollision⟩
  have hcandidate : AnalyticAt ℝ (F 0) state := by
    have hjoint := hanalytic (0, state) hdomain
    have hembedding : AnalyticAt ℝ
        (fun phase : PhaseSpace ↦ ((0 : ℝ), phase)) state :=
      analyticAt_const.prod analyticAt_id
    exact hjoint.comp hembedding
  unfold leadingActionCoefficient
  exact hcandidate.comp (analyticAt_delaunayActionSection haction)

/-- The action-section representative equals the leading candidate on every lifted point with the
same prograde elliptic actions. -/
theorem IsFirstIntegralFamily.leadingActionCoefficient_eq_liftedDelaunayPhasePoint
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {firstAction eccentricity : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1)
    (angles : ℝ × ℝ) :
    leadingActionCoefficient F
        ![firstAction, angularActionFromEccentricity firstAction eccentricity] =
      F 0 (liftedDelaunayPhasePoint
        firstAction eccentricity angles.1 angles.2) := by
  let action : ActionSpace :=
    ![firstAction, angularActionFromEccentricity firstAction eccentricity]
  have hangularPos : 0 < angularActionFromEccentricity firstAction eccentricity :=
    angularActionFromEccentricity_pos hfirstAction heccentricity heccentricityOne
  have hangularLt : angularActionFromEccentricity firstAction eccentricity < firstAction :=
    angularActionFromEccentricity_lt_firstAction hfirstAction heccentricity
  have haction : action ∈ ProgradeEllipticActions := ⟨hangularPos, hangularLt⟩
  have heRecover : eccentricityFromActions action = eccentricity :=
    eccentricityFromActions_angularActionFromEccentricity hfirstAction
      heccentricity.le heccentricityOne
  unfold leadingActionCoefficient
  rw [delaunayActionSection_eq_liftedDelaunayPhasePoint haction]
  change F 0 (liftedDelaunayPhasePoint
      firstAction (eccentricityFromActions action) 0 0) = _
  rw [heRecover]
  exact IsFirstIntegralFamily.mass_zero_liftedDelaunayPhasePoint_eq
    hδ hanalytic hfirstIntegral hfirstAction heccentricity.le
    heccentricityOne hapoapsis (0, 0) angles

/-- The coordinate vector representing the differential of the leading action coefficient. -/
noncomputable def leadingActionDifferential
    (F : ℝ → PhaseSpace → ℝ) (action : ActionSpace) : ActionSpace :=
  ![fderiv ℝ (leadingActionCoefficient F) action (actionCoordinateVector 0),
    fderiv ℝ (leadingActionCoefficient F) action (actionCoordinateVector 1)]

/-- The Fréchet differential of the leading action coefficient is its represented Euclidean
action covector. -/
theorem fderiv_leadingActionCoefficient_eq_actionCovector
    (F : ℝ → PhaseSpace → ℝ) (action : ActionSpace) :
    fderiv ℝ (leadingActionCoefficient F) action =
      actionCovector (leadingActionDifferential F action) := by
  apply ContinuousLinearMap.ext
  intro direction
  have hdecompose : direction =
      direction 0 • actionCoordinateVector 0 +
        direction 1 • actionCoordinateVector 1 := by
    funext coordinate
    fin_cases coordinate <;> simp [actionCoordinateVector]
  rw [hdecompose, map_add, map_smul, map_smul]
  simp only [actionCovector_apply, dot_eq, leadingActionDifferential,
    Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  simp [actionCoordinateVector]
  ring

/-- The represented leading differential varies continuously at every interior prograde action. -/
theorem IsJointlyAnalytic.continuousAt_leadingActionDifferential
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F)
    {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions)
    (hapoapsis : action 0 ^ 2 * (1 + eccentricityFromActions action) < 1) :
    ContinuousAt (leadingActionDifferential F) action := by
  have hsmooth : ContDiffAt ℝ 2 (leadingActionCoefficient F) action :=
    (IsJointlyAnalytic.analyticAt_leadingActionCoefficient
      hδ hanalytic haction hapoapsis).contDiffAt
  have hderivative : ContinuousAt
      (fun candidate ↦ fderiv ℝ (leadingActionCoefficient F) candidate) action :=
    hsmooth.continuousAt_fderiv (by norm_num)
  rw [continuousAt_pi]
  intro coordinate
  fin_cases coordinate
  · exact continuousAt_clm_apply.mp hderivative (actionCoordinateVector 0)
  · exact continuousAt_clm_apply.mp hderivative (actionCoordinateVector 1)

/-- The represented leading differential is itself analytic on the interior action region. -/
theorem IsJointlyAnalytic.analyticAt_leadingActionDifferential
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F)
    {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions)
    (hapoapsis : action 0 ^ 2 * (1 + eccentricityFromActions action) < 1) :
    AnalyticAt ℝ (leadingActionDifferential F) action := by
  have hderivative := (IsJointlyAnalytic.analyticAt_leadingActionCoefficient
    hδ hanalytic haction hapoapsis).fderiv
  rw [analyticAt_pi_iff]
  intro coordinate
  fin_cases coordinate
  · exact ((ContinuousLinearMap.apply ℝ ℝ (actionCoordinateVector 0)).analyticAt _).comp
      hderivative
  · exact ((ContinuousLinearMap.apply ℝ ℝ (actionCoordinateVector 1)).analyticAt _).comp
      hderivative

/-- The action pair `(L, L sqrt(1-e²))` along a fixed-eccentricity family. -/
noncomputable def fixedEccentricityAction
    (eccentricity firstAction : ℝ) : ActionSpace :=
  ![firstAction, angularActionFromEccentricity firstAction eccentricity]

/-- The leading action differential restricted to a fixed-eccentricity interior family. -/
noncomputable def leadingActionDifferentialAtEccentricity
    (F : ℝ → PhaseSpace → ℝ) (eccentricity : ℝ)
    (firstAction : InteriorPositiveAction eccentricity) : ActionSpace :=
  leadingActionDifferential F
    (fixedEccentricityAction eccentricity firstAction.1.1)

/-- Along every fixed noncircular eccentricity family inside the unit primary orbit, the leading
action differential is continuous in `L`. -/
theorem IsJointlyAnalytic.continuous_leadingActionDifferentialAtEccentricity
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F)
    {eccentricity : ℝ} (heccentricity : 0 < eccentricity)
    (heccentricityOne : eccentricity < 1) :
    Continuous (leadingActionDifferentialAtEccentricity F eccentricity) := by
  rw [continuous_iff_continuousAt]
  intro firstAction
  let action := fixedEccentricityAction eccentricity firstAction.1.1
  have hfirstAction : 0 < firstAction.1.1 := firstAction.1.2
  have haction : action ∈ ProgradeEllipticActions := by
    exact ⟨angularActionFromEccentricity_pos hfirstAction heccentricity
        heccentricityOne,
      angularActionFromEccentricity_lt_firstAction hfirstAction heccentricity⟩
  have heRecover : eccentricityFromActions action = eccentricity :=
    eccentricityFromActions_angularActionFromEccentricity hfirstAction
      heccentricity.le heccentricityOne
  have hapoapsis : action 0 ^ 2 * (1 + eccentricityFromActions action) < 1 := by
    rw [heRecover]
    exact firstAction.2
  have hdifferential := IsJointlyAnalytic.continuousAt_leadingActionDifferential
    hδ hanalytic haction hapoapsis
  have hcurve : ContinuousAt
      (fun candidate : InteriorPositiveAction eccentricity ↦
        fixedEccentricityAction eccentricity candidate.1.1) firstAction := by
    unfold fixedEccentricityAction angularActionFromEccentricity
    fun_prop
  change ContinuousAt
    (fun candidate : InteriorPositiveAction eccentricity ↦
      leadingActionDifferential F
        (fixedEccentricityAction eccentricity candidate.1.1)) firstAction
  exact hdifferential.comp hcurve

end LeanPool.PoincareThreeBody
