/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DelaunaySection

/-!
# Poisson brackets and the Cartesian Delaunay action map

This file rewrites the physical Poisson bracket with the zero-mass Hamiltonian as contraction of
the Kepler frequency with the two Poisson brackets against the Cartesian actions `(L,G)`.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

/-- Canonical symplectic pairing of two phase covectors. -/
def phasePoissonPairing
    (first second : PhaseSpace →L[ℝ] ℝ) : ℝ :=
  first (coordinateVector 0) * second (coordinateVector 2) -
      first (coordinateVector 2) * second (coordinateVector 0) +
    (first (coordinateVector 1) * second (coordinateVector 3) -
      first (coordinateVector 3) * second (coordinateVector 1))

lemma poissonBracket_eq_phasePoissonPairing
    (f g : PhaseSpace → ℝ) (state : PhaseSpace) :
    poissonBracket f g state =
      phasePoissonPairing (fderiv ℝ f state) (fderiv ℝ g state) :=
  rfl

/-- The two Poisson brackets of an observable with the reconstructed actions. -/
noncomputable def actionPoissonVector
    (f : PhaseSpace → ℝ) (state : PhaseSpace) : ActionSpace :=
  ![poissonBracket f cartesianFirstAction state,
    poissonBracket f cartesianAngularAction state]

/-- Hamiltonian vector field of the angular action. -/
def angularActionVectorField (state : PhaseSpace) : PhaseSpace :=
  ![-state 1, state 0, -state 3, state 2]

/-- Varying the negated rotation angle generates the angular-action Hamiltonian flow. -/
theorem hasDerivAt_positionInRotatingFrame_neg
    (angle : ℝ) (vector : ActionSpace) :
    HasDerivAt (fun argument ↦ positionInRotatingFrame (-argument) vector)
      ![-positionInRotatingFrame (-angle) vector 1,
        positionInRotatingFrame (-angle) vector 0] angle := by
  rw [hasDerivAt_pi]
  intro coordinate
  fin_cases coordinate
  · have hneg : HasDerivAt (fun argument : ℝ ↦ -argument) (-1) angle :=
      (hasDerivAt_id' angle).neg
    have hcos := (Real.hasDerivAt_cos (-angle)).comp angle hneg
    have hsin := (Real.hasDerivAt_sin (-angle)).comp angle hneg
    have hraw := (hcos.const_mul (vector 0)).add (hsin.const_mul (vector 1))
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with argument
      simp [positionInRotatingFrame]
      ring
    · simp [positionInRotatingFrame]
      ring
  · have hneg : HasDerivAt (fun argument : ℝ ↦ -argument) (-1) angle :=
      (hasDerivAt_id' angle).neg
    have hsin := (Real.hasDerivAt_sin (-angle)).comp angle hneg
    have hcos := (Real.hasDerivAt_cos (-angle)).comp angle hneg
    have hraw := (hsin.neg.const_mul (vector 0)).add (hcos.const_mul (vector 1))
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with argument
      simp [positionInRotatingFrame]
      ring
    · simp [positionInRotatingFrame]
      ring

/-- Varying the lifted periapsis angle follows the angular-action Hamiltonian vector field. -/
theorem hasDerivAt_liftedDelaunayPhasePoint_periapsisAngle
    (firstAction eccentricity meanAnomaly periapsisAngle : ℝ) :
    HasDerivAt
      (fun angle ↦ liftedDelaunayPhasePoint
        firstAction eccentricity meanAnomaly angle)
      (angularActionVectorField
        (liftedDelaunayPhasePoint
          firstAction eccentricity meanAnomaly periapsisAngle))
      periapsisAngle := by
  have hposition := hasDerivAt_positionInRotatingFrame_neg periapsisAngle
    (inertialEllipsePosition firstAction eccentricity
      (liftedDelaunayEccentricAnomaly eccentricity meanAnomaly))
  have hmomentum := hasDerivAt_positionInRotatingFrame_neg periapsisAngle
    (inertialEllipseVelocity firstAction eccentricity (1 / firstAction ^ 3)
      (liftedDelaunayEccentricAnomaly eccentricity meanAnomaly))
  rw [hasDerivAt_pi]
  intro coordinate
  fin_cases coordinate
  · exact (hasDerivAt_pi.mp hposition) 0
  · exact (hasDerivAt_pi.mp hposition) 1
  · exact (hasDerivAt_pi.mp hmomentum) 0
  · exact (hasDerivAt_pi.mp hmomentum) 1

/-- Differential of the Cartesian angular action. -/
theorem fderiv_cartesianAngularAction (state : PhaseSpace) :
    fderiv ℝ cartesianAngularAction state =
      ((state 0) • (ContinuousLinearMap.proj 3 : PhaseSpace →L[ℝ] ℝ) +
        (state 3) • (ContinuousLinearMap.proj 0 : PhaseSpace →L[ℝ] ℝ) -
        ((state 1) • (ContinuousLinearMap.proj 2 : PhaseSpace →L[ℝ] ℝ) +
          (state 2) • (ContinuousLinearMap.proj 1 : PhaseSpace →L[ℝ] ℝ))) := by
  have hcoordinate : ∀ i, HasFDerivAt
      (fun candidate : PhaseSpace ↦ candidate i)
      (ContinuousLinearMap.proj i) state := fun i ↦
    (ContinuousLinearMap.proj i : PhaseSpace →L[ℝ] ℝ).hasFDerivAt
  have hraw := ((hcoordinate 0).mul (hcoordinate 3)).sub
    ((hcoordinate 1).mul (hcoordinate 2))
  have hfunction : cartesianAngularAction =
      fun candidate : PhaseSpace ↦
        candidate 0 * candidate 3 - candidate 1 * candidate 2 := rfl
  rw [hfunction]
  exact hraw.fderiv

/-- Bracketing with angular action differentiates along simultaneous rotation of position and
momentum. -/
theorem poissonBracket_cartesianAngularAction
    (f : PhaseSpace → ℝ) (state : PhaseSpace) :
    poissonBracket f cartesianAngularAction state =
      fderiv ℝ f state (angularActionVectorField state) := by
  have hvector : angularActionVectorField state =
      (-state 1) • coordinateVector 0 + state 0 • coordinateVector 1 +
        (-state 3) • coordinateVector 2 + state 2 • coordinateVector 3 := by
    funext coordinate
    fin_cases coordinate <;> simp [angularActionVectorField, coordinateVector]
  rw [poissonBracket_eq_phasePoissonPairing]
  rw [fderiv_cartesianAngularAction]
  rw [hvector, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
  unfold phasePoissonPairing coordinateVector
  simp
  ring

lemma fderiv_cartesianDelaunayActions_coordinate
    {state direction : PhaseSpace}
    (hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0)
    (henergy : cartesianKeplerEnergy state < 0) (coordinate : Fin 2) :
    fderiv ℝ cartesianDelaunayActions state direction coordinate =
      fderiv ℝ (fun candidate ↦ cartesianDelaunayActions candidate coordinate)
        state direction := by
  have hdifferentiable : ∀ coordinate : Fin 2,
      DifferentiableAt ℝ
        (fun candidate ↦ cartesianDelaunayActions candidate coordinate) state := by
    intro index
    have hprojection : AnalyticAt ℝ
        (fun value : ActionSpace ↦ value index)
        (cartesianDelaunayActions state) :=
      (ContinuousLinearMap.proj index : ActionSpace →L[ℝ] ℝ).analyticAt _
    exact (hprojection.comp
      (analyticAt_cartesianDelaunayActions hposition henergy)).differentiableAt
  have hpi := fderiv_pi hdifferentiable
  have happly := congrArg (fun derivative : PhaseSpace →L[ℝ] ActionSpace ↦
    derivative direction coordinate) hpi
  simpa using happly

/-- Pairing a phase covector with a pulled-back action covector contracts the represented action
vector with the two action Poisson brackets. -/
theorem phasePoissonPairing_actionCovector_comp_actions
    {state : PhaseSpace} (hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0)
    (henergy : cartesianKeplerEnergy state < 0)
    (phaseCovector : PhaseSpace →L[ℝ] ℝ) (vector : ActionSpace) :
    phasePoissonPairing phaseCovector
        ((actionCovector vector).comp
          (fderiv ℝ cartesianDelaunayActions state)) =
      dot vector
        ![phasePoissonPairing phaseCovector
            (fderiv ℝ cartesianFirstAction state),
          phasePoissonPairing phaseCovector
            (fderiv ℝ cartesianAngularAction state)] := by
  have hzero : ∀ direction,
      fderiv ℝ cartesianDelaunayActions state direction 0 =
        fderiv ℝ cartesianFirstAction state direction := by
    intro direction
    exact fderiv_cartesianDelaunayActions_coordinate hposition henergy 0
  have hone : ∀ direction,
      fderiv ℝ cartesianDelaunayActions state direction 1 =
        fderiv ℝ cartesianAngularAction state direction := by
    intro direction
    exact fderiv_cartesianDelaunayActions_coordinate hposition henergy 1
  unfold phasePoissonPairing
  simp only [ContinuousLinearMap.comp_apply, actionCovector_apply, dot_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hzero, hzero, hzero, hzero, hone, hone, hone, hone]
  ring

/-- Bracketing any observable with the zero-mass Hamiltonian is contraction of the Delaunay
frequency with its two action brackets. -/
theorem poissonBracket_hamiltonian_zero_eq_frequency_dot_actionPoisson
    {state : PhaseSpace} (hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0)
    (henergy : cartesianKeplerEnergy state < 0) (f : PhaseSpace → ℝ) :
    poissonBracket f (hamiltonian 0) state =
      dot (delaunayFrequency (cartesianDelaunayActions state 0))
        (actionPoissonVector f state) := by
  rw [poissonBracket_eq_phasePoissonPairing,
    fderiv_hamiltonian_zero_eq_frequencyCovector_comp_actions
      hposition henergy,
    phasePoissonPairing_actionCovector_comp_actions hposition henergy]
  rfl

/-- Angle-independence of the leading candidate implies that it Poisson-commutes with angular
action at every interior lifted elliptic point. -/
theorem IsFirstIntegralFamily.poissonBracket_cartesianAngularAction_mass_zero
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1) :
    poissonBracket (F 0) cartesianAngularAction
      (liftedDelaunayPhasePoint
        firstAction eccentricity meanAnomaly periapsisAngle) = 0 := by
  let state := liftedDelaunayPhasePoint
    firstAction eccentricity meanAnomaly periapsisAngle
  let observable : ℝ → ℝ := fun angle ↦
    F 0 (liftedDelaunayPhasePoint
      firstAction eccentricity meanAnomaly angle)
  have hcollision : (0, state) ∈ collisionFree :=
    liftedDelaunayPhasePoint_collisionFree_mass_zero hfirstAction.ne'
      heccentricity heccentricityOne hapoapsis
  have hdomain : (0, state) ∈ parameterDomain δ :=
    ⟨by simpa using hδ, hcollision⟩
  have hcandidate : DifferentiableAt ℝ (F 0) state := by
    have hjoint := hanalytic (0, state) hdomain
    have hembedding : AnalyticAt ℝ
        (fun phase : PhaseSpace ↦ ((0 : ℝ), phase)) state :=
      analyticAt_const.prod analyticAt_id
    exact (hjoint.comp hembedding).differentiableAt
  have hchain := hcandidate.hasFDerivAt.comp_hasDerivAt periapsisAngle
    (hasDerivAt_liftedDelaunayPhasePoint_periapsisAngle
      firstAction eccentricity meanAnomaly periapsisAngle)
  have hconstant : observable = fun _ ↦ observable periapsisAngle := by
    funext angle
    exact IsFirstIntegralFamily.mass_zero_liftedDelaunayPhasePoint_eq
      hδ hanalytic hfirstIntegral hfirstAction heccentricity
      heccentricityOne hapoapsis (meanAnomaly, angle)
      (meanAnomaly, periapsisAngle)
  calc
    poissonBracket (F 0) cartesianAngularAction state =
        fderiv ℝ (F 0) state (angularActionVectorField state) :=
      poissonBracket_cartesianAngularAction _ _
    _ = deriv observable periapsisAngle := hchain.deriv.symm
    _ = 0 := by rw [hconstant]; simp

/-- The leading candidate Poisson-commutes with both reconstructed Delaunay actions throughout
the interior elliptic chart. -/
theorem IsFirstIntegralFamily.actionPoissonVector_mass_zero_eq_zero
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1) :
    actionPoissonVector (F 0)
      (liftedDelaunayPhasePoint
        firstAction eccentricity meanAnomaly periapsisAngle) = 0 := by
  let state := liftedDelaunayPhasePoint
    firstAction eccentricity meanAnomaly periapsisAngle
  have hcollision : (0, state) ∈ collisionFree :=
    liftedDelaunayPhasePoint_collisionFree_mass_zero hfirstAction.ne'
      heccentricity heccentricityOne hapoapsis
  have hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0 := by
    simpa [secondPrimaryDistanceSq] using hcollision.2
  have henergyIdentity : cartesianKeplerEnergy state =
      -1 / (2 * firstAction ^ 2) :=
    cartesianKeplerEnergy_liftedDelaunayPhasePoint hfirstAction.ne'
      heccentricity heccentricityOne
  have henergy : cartesianKeplerEnergy state < 0 := by
    rw [henergyIdentity]
    exact div_neg_of_neg_of_pos (by norm_num)
      (mul_pos (by norm_num) (sq_pos_of_pos hfirstAction))
  have hactions : cartesianDelaunayActions state =
      ![firstAction, angularActionFromEccentricity firstAction eccentricity] :=
    cartesianDelaunayActions_liftedDelaunayPhasePoint hfirstAction
      heccentricity heccentricityOne
  have hhamiltonian : poissonBracket (F 0) (hamiltonian 0) state = 0 :=
    IsFirstIntegralFamily.poissonBracket_zero_at_mass_zero
      hδ hfirstIntegral hcollision
  have hfrequency := poissonBracket_hamiltonian_zero_eq_frequency_dot_actionPoisson
    hposition henergy (F 0)
  have hangular :=
    IsFirstIntegralFamily.poissonBracket_cartesianAngularAction_mass_zero
      (meanAnomaly := meanAnomaly) (periapsisAngle := periapsisAngle)
      hδ hanalytic hfirstIntegral hfirstAction heccentricity
      heccentricityOne hapoapsis
  rw [hhamiltonian, hactions] at hfrequency
  change poissonBracket (F 0) cartesianAngularAction state = 0 at hangular
  have hfirst : poissonBracket (F 0) cartesianFirstAction state = 0 := by
    rw [dot_eq] at hfrequency
    simp only [delaunayFrequency, actionPoissonVector, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hfrequency
    rw [hangular] at hfrequency
    have hproduct : 1 / firstAction ^ 3 *
        poissonBracket (F 0) cartesianFirstAction state = 0 := by
      simpa using hfrequency.symm
    have hcoefficient : 1 / firstAction ^ 3 ≠ 0 := by
      exact one_div_ne_zero (pow_ne_zero 3 hfirstAction.ne')
    exact (mul_eq_zero.mp hproduct).resolve_left hcoefficient
  funext coordinate
  fin_cases coordinate
  · exact hfirst
  · exact hangular

end LeanPool.PoincareThreeBody
