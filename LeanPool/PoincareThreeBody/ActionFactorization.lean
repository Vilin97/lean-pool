/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.ActionPoisson

/-!
# Pointwise factorization of the leading integral through the Delaunay actions

The mass-zero leading coefficient is constant on every interior Kepler torus.  This file upgrades
that value-level statement to a differential identity: at every noncircular elliptic point, its
phase differential is the pullback of the differential of the action-space representative.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

/-- The rows of the derivative of the physical action map are the derivatives of its two scalar
components. -/
theorem actionDerivativeCovector_cartesianDelaunayActions
    {state : PhaseSpace} (hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0)
    (henergy : cartesianKeplerEnergy state < 0) (coordinate : Fin 2) :
    actionDerivativeCovector (fderiv ℝ cartesianDelaunayActions state) coordinate =
      fderiv ℝ (fun candidate ↦ cartesianDelaunayActions candidate coordinate) state := by
  apply ContinuousLinearMap.ext
  intro direction
  exact fderiv_cartesianDelaunayActions_coordinate hposition henergy coordinate

/-- The Hamiltonian vector of the angular-action differential is simultaneous planar rotation. -/
theorem phaseHamiltonianVector_fderiv_cartesianAngularAction (state : PhaseSpace) :
    phaseHamiltonianVector (fderiv ℝ cartesianAngularAction state) =
      angularActionVectorField state := by
  rw [fderiv_cartesianAngularAction]
  funext coordinate
  fin_cases coordinate <;>
    simp [phaseHamiltonianVector, angularActionVectorField, coordinateVector]

/-- At a lifted elliptic point, the Hamiltonian vector of the second row of the action derivative
is the angular-action vector field. -/
theorem phaseHamiltonianVector_actionDerivativeCovector_one
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    let state := liftedDelaunayPhasePoint
      firstAction eccentricity meanAnomaly periapsisAngle
    phaseHamiltonianVector
        (actionDerivativeCovector (fderiv ℝ cartesianDelaunayActions state) 1) =
      angularActionVectorField state := by
  let state := liftedDelaunayPhasePoint
    firstAction eccentricity meanAnomaly periapsisAngle
  have hradius : 0 < eccentricRadius firstAction eccentricity
      (liftedDelaunayEccentricAnomaly eccentricity meanAnomaly) :=
    eccentricRadius_pos hfirstAction.ne' heccentricity heccentricityOne
  have hpositionSq : state 0 ^ 2 + state 1 ^ 2 =
      eccentricRadius firstAction eccentricity
        (liftedDelaunayEccentricAnomaly eccentricity meanAnomaly) ^ 2 := by
    unfold state liftedDelaunayPhasePoint liftedDelaunayPosition
      positionMomentumPhasePoint
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [positionInRotatingFrame_sq,
      inertialEllipsePosition_sq heccentricity heccentricityOne.le]
  have hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0 := by
    rw [hpositionSq]
    positivity
  have henergyIdentity : cartesianKeplerEnergy state =
      -1 / (2 * firstAction ^ 2) :=
    cartesianKeplerEnergy_liftedDelaunayPhasePoint hfirstAction.ne'
      heccentricity heccentricityOne
  have henergy : cartesianKeplerEnergy state < 0 := by
    rw [henergyIdentity]
    exact div_neg_of_neg_of_pos (by norm_num)
      (mul_pos (by norm_num) (sq_pos_of_pos hfirstAction))
  dsimp only
  rw [actionDerivativeCovector_cartesianDelaunayActions hposition henergy 1]
  change phaseHamiltonianVector (fderiv ℝ cartesianAngularAction state) = _
  exact phaseHamiltonianVector_fderiv_cartesianAngularAction state

/-- The physical action derivative kills the angular-action Hamiltonian vector at every lifted
elliptic point. -/
theorem fderiv_cartesianDelaunayActions_angularActionVectorField_eq_zero
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    let state := liftedDelaunayPhasePoint
      firstAction eccentricity meanAnomaly periapsisAngle
    fderiv ℝ cartesianDelaunayActions state
        (angularActionVectorField state) = 0 := by
  let state := liftedDelaunayPhasePoint
    firstAction eccentricity meanAnomaly periapsisAngle
  let curve : ℝ → PhaseSpace := fun angle ↦
    liftedDelaunayPhasePoint firstAction eccentricity meanAnomaly angle
  have hactions : DifferentiableAt ℝ cartesianDelaunayActions state :=
    (analyticAt_cartesianDelaunayActions_liftedDelaunayPhasePoint
      hfirstAction heccentricity heccentricityOne).differentiableAt
  have hcurve : HasDerivAt curve (angularActionVectorField state) periapsisAngle :=
    hasDerivAt_liftedDelaunayPhasePoint_periapsisAngle
      firstAction eccentricity meanAnomaly periapsisAngle
  have hcomp := hactions.hasFDerivAt.comp_hasDerivAt periapsisAngle hcurve
  have hconstant : (fun angle ↦ cartesianDelaunayActions (curve angle)) =
      fun _ ↦ ![firstAction,
        angularActionFromEccentricity firstAction eccentricity] := by
    funext angle
    exact cartesianDelaunayActions_liftedDelaunayPhasePoint
      hfirstAction heccentricity heccentricityOne
  dsimp only
  rw [← hcomp.deriv]
  change deriv (fun angle ↦ cartesianDelaunayActions (curve angle)) periapsisAngle = 0
  rw [hconstant]
  simp

/-- The two rows of the physical action derivative are symplectically orthogonal on every lifted
elliptic point. -/
theorem phasePoissonPairing_actionDerivativeCovectors_eq_zero
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    let state := liftedDelaunayPhasePoint
      firstAction eccentricity meanAnomaly periapsisAngle
    phasePoissonPairing
        (actionDerivativeCovector (fderiv ℝ cartesianDelaunayActions state) 0)
        (actionDerivativeCovector (fderiv ℝ cartesianDelaunayActions state) 1) = 0 := by
  let state := liftedDelaunayPhasePoint
    firstAction eccentricity meanAnomaly periapsisAngle
  dsimp only
  rw [phasePoissonPairing_eq_apply_phaseHamiltonianVector,
    phaseHamiltonianVector_actionDerivativeCovector_one hfirstAction
      heccentricity heccentricityOne]
  rw [actionDerivativeCovector_apply,
    fderiv_cartesianDelaunayActions_angularActionVectorField_eq_zero
      hfirstAction heccentricity heccentricityOne]
  rfl

/-- Pairing a phase differential with a row of the physical action derivative recovers the
corresponding component of the action Poisson vector. -/
theorem phasePoissonPairing_actionDerivativeCovector_eq_actionPoissonVector
    {state : PhaseSpace} (hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0)
    (henergy : cartesianKeplerEnergy state < 0)
    (f : PhaseSpace → ℝ) (coordinate : Fin 2) :
    phasePoissonPairing (fderiv ℝ f state)
        (actionDerivativeCovector
          (fderiv ℝ cartesianDelaunayActions state) coordinate) =
      actionPoissonVector f state coordinate := by
  rw [actionDerivativeCovector_cartesianDelaunayActions
    hposition henergy coordinate]
  fin_cases coordinate
  · rfl
  · rfl

/-- Once an observable differential factors through the action map, its bracket with any second
observable is contraction against the negative action Poisson vector of that observable. -/
theorem poissonBracket_eq_neg_dot_actionPoissonVector_of_fderiv_factors
    {state : PhaseSpace} (hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0)
    (henergy : cartesianKeplerEnergy state < 0)
    {f h : PhaseSpace → ℝ} {differential : ActionSpace}
    (hfactor : fderiv ℝ f state =
      (actionCovector differential).comp
        (fderiv ℝ cartesianDelaunayActions state)) :
    poissonBracket f h state =
      -dot differential (actionPoissonVector h state) := by
  rw [poissonBracket_eq_phasePoissonPairing, hfactor,
    phasePoissonPairing_skew,
    phasePoissonPairing_actionCovector_comp_actions hposition henergy]
  rfl

/-- The differential of the leading integral factors through the physical action derivative at
every interior noncircular lifted elliptic point.  This form records the factor using an explicit
moving action section through the point. -/
theorem IsFirstIntegralFamily.fderiv_mass_zero_factors_through_actions_section
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1) :
    let state := liftedDelaunayPhasePoint
      firstAction eccentricity meanAnomaly periapsisAngle
    let action : ActionSpace :=
      ![firstAction, angularActionFromEccentricity firstAction eccentricity]
    let movingSection := delaunayActionSectionAtAnomaly
      (eccentricAnomaly eccentricity meanAnomaly) periapsisAngle
    fderiv ℝ (F 0) state =
      ((fderiv ℝ (F 0) state).comp (fderiv ℝ movingSection action)).comp
        (fderiv ℝ cartesianDelaunayActions state) := by
  let state := liftedDelaunayPhasePoint
    firstAction eccentricity meanAnomaly periapsisAngle
  let action : ActionSpace :=
    ![firstAction, angularActionFromEccentricity firstAction eccentricity]
  let anomaly := eccentricAnomaly eccentricity meanAnomaly
  let movingSection := delaunayActionSectionAtAnomaly anomaly periapsisAngle
  have haction : action ∈ ProgradeEllipticActions :=
    ⟨angularActionFromEccentricity_pos hfirstAction heccentricity heccentricityOne,
      angularActionFromEccentricity_lt_firstAction hfirstAction heccentricity⟩
  have hthrough : movingSection action = state := by
    exact delaunayActionSectionAtAnomaly_liftedDelaunayActions
      hfirstAction heccentricity heccentricityOne
  have hright := fderiv_cartesianDelaunayActions_comp_sectionAtAnomaly
    haction anomaly periapsisAngle
  change (fderiv ℝ cartesianDelaunayActions (movingSection action)).comp
      (fderiv ℝ movingSection action) = _ at hright
  rw [hthrough] at hright
  have hisotropic :=
    phasePoissonPairing_actionDerivativeCovectors_eq_zero
      (meanAnomaly := meanAnomaly) (periapsisAngle := periapsisAngle)
      hfirstAction heccentricity.le heccentricityOne
  dsimp only at hisotropic
  have hcollision : (0, state) ∈ collisionFree :=
    liftedDelaunayPhasePoint_collisionFree_mass_zero hfirstAction.ne'
      heccentricity.le heccentricityOne hapoapsis
  have hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0 := by
    simpa [secondPrimaryDistanceSq] using hcollision.2
  have henergyIdentity : cartesianKeplerEnergy state =
      -1 / (2 * firstAction ^ 2) :=
    cartesianKeplerEnergy_liftedDelaunayPhasePoint hfirstAction.ne'
      heccentricity.le heccentricityOne
  have henergy : cartesianKeplerEnergy state < 0 := by
    rw [henergyIdentity]
    exact div_neg_of_neg_of_pos (by norm_num)
      (mul_pos (by norm_num) (sq_pos_of_pos hfirstAction))
  have hactionPoisson :=
    IsFirstIntegralFamily.actionPoissonVector_mass_zero_eq_zero
      (meanAnomaly := meanAnomaly) (periapsisAngle := periapsisAngle)
      hδ hanalytic hfirstIntegral hfirstAction heccentricity.le
      heccentricityOne hapoapsis
  have hzero : ∀ coordinate : Fin 2,
      phasePoissonPairing (fderiv ℝ (F 0) state)
        (actionDerivativeCovector
          (fderiv ℝ cartesianDelaunayActions state) coordinate) = 0 := by
    intro coordinate
    rw [phasePoissonPairing_actionDerivativeCovector_eq_actionPoissonVector
      hposition henergy]
    exact congrFun hactionPoisson coordinate
  dsimp only
  exact phaseCovector_eq_comp_actionDerivative hright hisotropic
    (fderiv ℝ (F 0) state) hzero

/-- Differentiating the moving action section through a lifted point gives exactly the
differential of the action-space leading coefficient. -/
theorem IsFirstIntegralFamily.fderiv_mass_zero_comp_section_eq_leadingActionCoefficient
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1) :
    let state := liftedDelaunayPhasePoint
      firstAction eccentricity meanAnomaly periapsisAngle
    let action : ActionSpace :=
      ![firstAction, angularActionFromEccentricity firstAction eccentricity]
    let movingSection := delaunayActionSectionAtAnomaly
      (eccentricAnomaly eccentricity meanAnomaly) periapsisAngle
    (fderiv ℝ (F 0) state).comp (fderiv ℝ movingSection action) =
      fderiv ℝ (leadingActionCoefficient F) action := by
  let state := liftedDelaunayPhasePoint
    firstAction eccentricity meanAnomaly periapsisAngle
  let action : ActionSpace :=
    ![firstAction, angularActionFromEccentricity firstAction eccentricity]
  let anomaly := eccentricAnomaly eccentricity meanAnomaly
  let movingSection := delaunayActionSectionAtAnomaly anomaly periapsisAngle
  have haction : action ∈ ProgradeEllipticActions :=
    ⟨angularActionFromEccentricity_pos hfirstAction heccentricity heccentricityOne,
      angularActionFromEccentricity_lt_firstAction hfirstAction heccentricity⟩
  have heRecover : eccentricityFromActions action = eccentricity :=
    eccentricityFromActions_angularActionFromEccentricity hfirstAction
      heccentricity.le heccentricityOne
  have hthrough : movingSection action = state := by
    exact delaunayActionSectionAtAnomaly_liftedDelaunayActions
      hfirstAction heccentricity heccentricityOne
  have hcollision : (0, state) ∈ collisionFree :=
    liftedDelaunayPhasePoint_collisionFree_mass_zero hfirstAction.ne'
      heccentricity.le heccentricityOne hapoapsis
  have hdomain : (0, state) ∈ parameterDomain δ :=
    ⟨by simpa using hδ, hcollision⟩
  have hcandidate : DifferentiableAt ℝ (F 0) state := by
    have hjoint := hanalytic (0, state) hdomain
    have hembedding : AnalyticAt ℝ
        (fun phase : PhaseSpace ↦ ((0 : ℝ), phase)) state :=
      analyticAt_const.prod analyticAt_id
    exact (hjoint.comp hembedding).differentiableAt
  have hsection : DifferentiableAt ℝ movingSection action :=
    (analyticAt_delaunayActionSectionAtAnomaly haction anomaly periapsisAngle).differentiableAt
  have hcandidateMoving : DifferentiableAt ℝ (F 0) (movingSection action) := by
    rw [hthrough]
    exact hcandidate
  have hchain := hcandidateMoving.hasFDerivAt.comp action hsection.hasFDerivAt
  have hcoordinate : AnalyticAt ℝ (fun candidate : ActionSpace ↦ candidate 0) action :=
    (ContinuousLinearMap.proj 0 : ActionSpace →L[ℝ] ℝ).analyticAt action
  have heccentricityAnalytic : AnalyticAt ℝ eccentricityFromActions action :=
    analyticAt_eccentricityFromActions haction
  have hapoapsisContinuous : ContinuousAt
      (fun candidate : ActionSpace ↦
        candidate 0 ^ 2 * (1 + eccentricityFromActions candidate)) action :=
    ((hcoordinate.pow 2).mul
      (analyticAt_const.add heccentricityAnalytic)).continuousAt
  have hapoapsisAt :
      action 0 ^ 2 * (1 + eccentricityFromActions action) < 1 := by
    simpa [action, heRecover] using hapoapsis
  have hapoapsisEventually : ∀ᶠ candidate in nhds action,
      candidate 0 ^ 2 * (1 + eccentricityFromActions candidate) < 1 :=
    hapoapsisContinuous.eventually_lt continuousAt_const hapoapsisAt
  have heventual : (fun candidate ↦ F 0 (movingSection candidate))
      =ᶠ[nhds action] leadingActionCoefficient F := by
    filter_upwards [isOpen_progradeEllipticActions.mem_nhds haction,
      hapoapsisEventually] with candidate hcandidateAction hcandidateApoapsis
    have hcandidateFirst : 0 < candidate 0 :=
      hcandidateAction.1.trans hcandidateAction.2
    have hcandidateEccentricity : 0 < eccentricityFromActions candidate :=
      eccentricityFromActions_pos hcandidateAction
    have hcandidateEccentricityOne : eccentricityFromActions candidate < 1 :=
      eccentricityFromActions_lt_one hcandidateAction
    have hvalue :=
      IsFirstIntegralFamily.leadingActionCoefficient_eq_liftedDelaunayPhasePoint
        hδ hanalytic hfirstIntegral hcandidateFirst hcandidateEccentricity
        hcandidateEccentricityOne hcandidateApoapsis
        (eccentricMeanAnomaly (eccentricityFromActions candidate) anomaly,
          periapsisAngle)
    rw [actions_from_eccentricityFromActions hcandidateAction] at hvalue
    change F 0 (delaunayActionSectionAtAnomaly anomaly periapsisAngle candidate) = _
    rw [delaunayActionSectionAtAnomaly_eq_liftedDelaunayPhasePoint
      hcandidateAction]
    simpa using hvalue.symm
  dsimp only
  calc
    (fderiv ℝ (F 0) state).comp (fderiv ℝ movingSection action) =
        (fderiv ℝ (F 0) (movingSection action)).comp
          (fderiv ℝ movingSection action) := by rw [hthrough]
    _ =
        fderiv ℝ (F 0 ∘ movingSection) action := hchain.fderiv.symm
    _ = fderiv ℝ (fun candidate ↦ F 0 (movingSection candidate)) action := rfl
    _ = fderiv ℝ (leadingActionCoefficient F) action := heventual.fderiv_eq

/-- Pointwise differential form of angle-independence: the leading phase differential is the
pullback of the represented action differential. -/
theorem IsFirstIntegralFamily.fderiv_mass_zero_eq_actionDifferential_comp_actions
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1) :
    let state := liftedDelaunayPhasePoint
      firstAction eccentricity meanAnomaly periapsisAngle
    let action : ActionSpace :=
      ![firstAction, angularActionFromEccentricity firstAction eccentricity]
    fderiv ℝ (F 0) state =
      (actionCovector (leadingActionDifferential F action)).comp
        (fderiv ℝ cartesianDelaunayActions state) := by
  let state := liftedDelaunayPhasePoint
    firstAction eccentricity meanAnomaly periapsisAngle
  let action : ActionSpace :=
    ![firstAction, angularActionFromEccentricity firstAction eccentricity]
  let movingSection := delaunayActionSectionAtAnomaly
    (eccentricAnomaly eccentricity meanAnomaly) periapsisAngle
  have hfactor :=
    IsFirstIntegralFamily.fderiv_mass_zero_factors_through_actions_section
      (meanAnomaly := meanAnomaly) (periapsisAngle := periapsisAngle)
      hδ hanalytic hfirstIntegral hfirstAction heccentricity
      heccentricityOne hapoapsis
  have hcoefficient :=
    IsFirstIntegralFamily.fderiv_mass_zero_comp_section_eq_leadingActionCoefficient
      (meanAnomaly := meanAnomaly) (periapsisAngle := periapsisAngle)
      hδ hanalytic hfirstIntegral hfirstAction heccentricity
      heccentricityOne hapoapsis
  dsimp only at hfactor hcoefficient ⊢
  rw [hfactor, hcoefficient,
    fderiv_leadingActionCoefficient_eq_actionCovector]

end LeanPool.PoincareThreeBody
