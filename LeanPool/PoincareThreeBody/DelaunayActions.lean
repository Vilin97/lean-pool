/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DelaunayChart
import LeanPool.PoincareThreeBody.KeplerHamiltonian

/-!
# Physical realization of the planar Delaunay actions

This file identifies the two actions carried by the explicit lifted ellipse.  The second action is
Cartesian angular momentum, while the first action is determined by the negative inertial Kepler
energy.  Consequently the physical mass-zero Hamiltonian pulls back to the displayed Delaunay
Hamiltonian.
-/

namespace LeanPool.PoincareThreeBody


/-- A frequency vector regarded as the corresponding Euclidean action covector. -/
noncomputable def actionCovector (vector : ActionSpace) : ActionSpace →L[ℝ] ℝ :=
  ((ContinuousLinearMap.proj 0 : ActionSpace →L[ℝ] ℝ).smulRight (vector 0)) +
    ((ContinuousLinearMap.proj 1 : ActionSpace →L[ℝ] ℝ).smulRight (vector 1))

lemma actionCovector_apply (vector direction : ActionSpace) :
    actionCovector vector direction = dot vector direction := by
  rw [dot_eq]
  simp [actionCovector, mul_comm]

/-- Coordinate tangent vectors in the two-dimensional action space. -/
def actionCoordinateVector (coordinate : Fin 2) : ActionSpace :=
  fun index ↦ if index = coordinate then 1 else 0

/-- Inertial Kepler energy written in rotating Cartesian canonical variables. -/
noncomputable def cartesianKeplerEnergy (state : PhaseSpace) : ℝ :=
  ((state 2) ^ 2 + (state 3) ^ 2) / 2 -
    1 / Real.sqrt ((state 0) ^ 2 + (state 1) ^ 2)

/-- The first Delaunay action reconstructed from negative inertial Kepler energy. -/
noncomputable def cartesianFirstAction (state : PhaseSpace) : ℝ :=
  1 / Real.sqrt (-2 * cartesianKeplerEnergy state)

/-- The planar angular action `G = x pᵧ - y pₓ`. -/
def cartesianAngularAction (state : PhaseSpace) : ℝ :=
  state 0 * state 3 - state 1 * state 2

/-- Both Cartesian Delaunay actions, ordered as `(L, G)`. -/
noncomputable def cartesianDelaunayActions (state : PhaseSpace) : ActionSpace :=
  ![cartesianFirstAction state, cartesianAngularAction state]

/-- The inertial Kepler energy is analytic away from the central collision. -/
theorem analyticAt_cartesianKeplerEnergy
    {state : PhaseSpace} (hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0) :
    AnalyticAt ℝ cartesianKeplerEnergy state := by
  have hcoordinate : ∀ coordinate : Fin 4,
      AnalyticAt ℝ (fun candidate : PhaseSpace ↦ candidate coordinate) state :=
    fun coordinate ↦
      (ContinuousLinearMap.proj coordinate : PhaseSpace →L[ℝ] ℝ).analyticAt state
  have hnormSq : AnalyticAt ℝ
      (fun candidate : PhaseSpace ↦ candidate 0 ^ 2 + candidate 1 ^ 2) state :=
    ((hcoordinate 0).pow 2).add ((hcoordinate 1).pow 2)
  have hnormSqPos : 0 < state 0 ^ 2 + state 1 ^ 2 := by positivity
  have hinverseRadius : AnalyticAt ℝ
      (fun candidate : PhaseSpace ↦
        1 / Real.sqrt (candidate 0 ^ 2 + candidate 1 ^ 2)) state :=
    (analyticAt_inv_sqrt hnormSqPos).comp
      (f := fun candidate : PhaseSpace ↦ candidate 0 ^ 2 + candidate 1 ^ 2) hnormSq
  have hkinetic : AnalyticAt ℝ
      (fun candidate : PhaseSpace ↦
        ((candidate 2) ^ 2 + (candidate 3) ^ 2) / 2) state := by
    exact ((((hcoordinate 2).pow 2).add ((hcoordinate 3).pow 2)).const_smul
      (c := (1 / 2 : ℝ))).congr (by
        filter_upwards [] with candidate
        simp [smul_eq_mul]
        ring)
  unfold cartesianKeplerEnergy
  exact hkinetic.sub hinverseRadius

/-- Angular action is an analytic polynomial in Cartesian phase variables. -/
theorem analyticAt_cartesianAngularAction (state : PhaseSpace) :
    AnalyticAt ℝ cartesianAngularAction state := by
  have hcoordinate : ∀ coordinate : Fin 4,
      AnalyticAt ℝ (fun candidate : PhaseSpace ↦ candidate coordinate) state :=
    fun coordinate ↦
      (ContinuousLinearMap.proj coordinate : PhaseSpace →L[ℝ] ℝ).analyticAt state
  unfold cartesianAngularAction
  exact ((hcoordinate 0).mul (hcoordinate 3)).sub
    ((hcoordinate 1).mul (hcoordinate 2))

/-- The reconstructed first action is analytic wherever the central distance is nonzero and the
inertial Kepler energy is negative. -/
theorem analyticAt_cartesianFirstAction
    {state : PhaseSpace} (hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0)
    (henergy : cartesianKeplerEnergy state < 0) :
    AnalyticAt ℝ cartesianFirstAction state := by
  have henergyAnalytic := analyticAt_cartesianKeplerEnergy hposition
  have hargument : AnalyticAt ℝ
      (fun candidate : PhaseSpace ↦ -2 * cartesianKeplerEnergy candidate) state :=
    analyticAt_const.mul henergyAnalytic
  have hpositive : 0 < -2 * cartesianKeplerEnergy state := by linarith
  unfold cartesianFirstAction
  exact (analyticAt_inv_sqrt hpositive).comp
    (f := fun candidate : PhaseSpace ↦ -2 * cartesianKeplerEnergy candidate) hargument

/-- The Cartesian Delaunay action map is analytic on the negative-energy, noncollision region. -/
theorem analyticAt_cartesianDelaunayActions
    {state : PhaseSpace} (hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0)
    (henergy : cartesianKeplerEnergy state < 0) :
    AnalyticAt ℝ cartesianDelaunayActions state := by
  rw [analyticAt_pi_iff]
  intro coordinate
  fin_cases coordinate
  · exact analyticAt_cartesianFirstAction hposition henergy
  · exact analyticAt_cartesianAngularAction state

/-- A common planar rotation preserves the determinant of two vectors. -/
lemma positionInRotatingFrame_cross
    (angle : ℝ) (first second : ActionSpace) :
    positionInRotatingFrame angle first 0 * positionInRotatingFrame angle second 1 -
        positionInRotatingFrame angle first 1 * positionInRotatingFrame angle second 0 =
      first 0 * second 1 - first 1 * second 0 := by
  have htrig := Real.sin_sq_add_cos_sq angle
  simp only [positionInRotatingFrame, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (first 0 * second 1 - first 1 * second 0) * htrig

/-- A common planar rotation preserves the squared norm. -/
lemma positionInRotatingFrame_momentum_sq
    (angle : ℝ) (momentum : ActionSpace) :
    (positionInRotatingFrame angle momentum 0) ^ 2 +
        (positionInRotatingFrame angle momentum 1) ^ 2 =
      (momentum 0) ^ 2 + (momentum 1) ^ 2 :=
  positionInRotatingFrame_sq angle momentum

/-- The eccentric-anomaly position and velocity carry angular action
`L * sqrt (1 - e²)`. -/
lemma inertialEllipsePosition_velocity_cross
    {firstAction eccentricity anomaly : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    inertialEllipsePosition firstAction eccentricity anomaly 0 *
          inertialEllipseVelocity firstAction eccentricity (1 / firstAction ^ 3) anomaly 1 -
        inertialEllipsePosition firstAction eccentricity anomaly 1 *
          inertialEllipseVelocity firstAction eccentricity (1 / firstAction ^ 3) anomaly 0 =
      angularActionFromEccentricity firstAction eccentricity := by
  have hdenominator : 1 - eccentricity * Real.cos anomaly ≠ 0 :=
    (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne).ne'
  have hdenominator' : 1 - Real.cos anomaly * eccentricity ≠ 0 := by
    simpa [mul_comm] using hdenominator
  have htrig := Real.sin_sq_add_cos_sq anomaly
  simp only [inertialEllipsePosition, inertialEllipseVelocity,
    angularActionFromEccentricity, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hfirstAction, hdenominator, hdenominator']
  ring_nf
  linear_combination Real.sqrt (1 - eccentricity ^ 2) * htrig

/-- The velocity norm on an elliptic Kepler orbit has the vis-viva value needed for its energy
shell. -/
lemma inertialEllipseVelocity_energy_identity
    {firstAction eccentricity anomaly : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    ((inertialEllipseVelocity firstAction eccentricity (1 / firstAction ^ 3) anomaly 0) ^ 2 +
          (inertialEllipseVelocity firstAction eccentricity
            (1 / firstAction ^ 3) anomaly 1) ^ 2) / 2 -
        1 / eccentricRadius firstAction eccentricity anomaly =
      -1 / (2 * firstAction ^ 2) := by
  have hdenominator : 1 - eccentricity * Real.cos anomaly ≠ 0 :=
    (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne).ne'
  have hsqrt : (Real.sqrt (1 - eccentricity ^ 2)) ^ 2 =
      1 - eccentricity ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith
  have htrig := Real.sin_sq_add_cos_sq anomaly
  simp only [inertialEllipseVelocity, eccentricRadius,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hfirstAction, hdenominator]
  nlinarith

/-- The explicit lifted Delaunay chart realizes its prescribed second action. -/
theorem cartesianAngularAction_liftedDelaunayPhasePoint
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    cartesianAngularAction
        (liftedDelaunayPhasePoint
          firstAction eccentricity meanAnomaly periapsisAngle) =
      angularActionFromEccentricity firstAction eccentricity := by
  unfold cartesianAngularAction liftedDelaunayPhasePoint liftedDelaunayPosition
    liftedDelaunayMomentum positionMomentumPhasePoint
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change
    positionInRotatingFrame (-periapsisAngle)
          (inertialEllipsePosition firstAction eccentricity
            (liftedDelaunayEccentricAnomaly eccentricity meanAnomaly)) 0 *
        positionInRotatingFrame (-periapsisAngle)
          (inertialEllipseVelocity firstAction eccentricity (1 / firstAction ^ 3)
            (liftedDelaunayEccentricAnomaly eccentricity meanAnomaly)) 1 -
      positionInRotatingFrame (-periapsisAngle)
          (inertialEllipsePosition firstAction eccentricity
            (liftedDelaunayEccentricAnomaly eccentricity meanAnomaly)) 1 *
        positionInRotatingFrame (-periapsisAngle)
          (inertialEllipseVelocity firstAction eccentricity (1 / firstAction ^ 3)
            (liftedDelaunayEccentricAnomaly eccentricity meanAnomaly)) 0 = _
  rw [positionInRotatingFrame_cross]
  exact inertialEllipsePosition_velocity_cross hfirstAction heccentricity heccentricityOne

/-- The first action of the lifted chart is its negative Kepler energy action. -/
theorem cartesianKeplerEnergy_liftedDelaunayPhasePoint
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    cartesianKeplerEnergy
        (liftedDelaunayPhasePoint
          firstAction eccentricity meanAnomaly periapsisAngle) =
      -1 / (2 * firstAction ^ 2) := by
  let anomaly := liftedDelaunayEccentricAnomaly eccentricity meanAnomaly
  have hradius : 0 < eccentricRadius firstAction eccentricity anomaly :=
    eccentricRadius_pos hfirstAction heccentricity heccentricityOne
  have hpositionSq :
      (liftedDelaunayPosition firstAction eccentricity meanAnomaly periapsisAngle 0) ^ 2 +
          (liftedDelaunayPosition firstAction eccentricity meanAnomaly periapsisAngle 1) ^ 2 =
        eccentricRadius firstAction eccentricity anomaly ^ 2 := by
    unfold liftedDelaunayPosition
    rw [positionInRotatingFrame_sq,
      inertialEllipsePosition_sq heccentricity heccentricityOne.le]
  have hmomentumSq :
      (liftedDelaunayMomentum firstAction eccentricity meanAnomaly periapsisAngle 0) ^ 2 +
          (liftedDelaunayMomentum firstAction eccentricity meanAnomaly periapsisAngle 1) ^ 2 =
        (inertialEllipseVelocity firstAction eccentricity
            (1 / firstAction ^ 3) anomaly 0) ^ 2 +
          (inertialEllipseVelocity firstAction eccentricity
            (1 / firstAction ^ 3) anomaly 1) ^ 2 := by
    exact positionInRotatingFrame_momentum_sq _ _
  unfold cartesianKeplerEnergy liftedDelaunayPhasePoint positionMomentumPhasePoint
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change
    ((liftedDelaunayMomentum firstAction eccentricity meanAnomaly periapsisAngle 0) ^ 2 +
          (liftedDelaunayMomentum firstAction eccentricity meanAnomaly periapsisAngle 1) ^ 2) /
        2 -
      1 / Real.sqrt
        ((liftedDelaunayPosition firstAction eccentricity meanAnomaly periapsisAngle 0) ^ 2 +
          (liftedDelaunayPosition firstAction eccentricity meanAnomaly periapsisAngle 1) ^ 2) = _
  rw [hpositionSq, hmomentumSq, Real.sqrt_sq_eq_abs, abs_of_pos hradius]
  exact inertialEllipseVelocity_energy_identity hfirstAction
    heccentricity heccentricityOne

/-- Reconstructing the first action from the energy of a positive-action lifted ellipse returns
the original `L`. -/
theorem cartesianFirstAction_liftedDelaunayPhasePoint
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    cartesianFirstAction
        (liftedDelaunayPhasePoint
          firstAction eccentricity meanAnomaly periapsisAngle) =
      firstAction := by
  rw [cartesianFirstAction,
    cartesianKeplerEnergy_liftedDelaunayPhasePoint hfirstAction.ne'
      heccentricity heccentricityOne]
  have hinverseSquare : -2 * (-1 / (2 * firstAction ^ 2)) =
      (1 / firstAction) ^ 2 := by
    field_simp [hfirstAction.ne']
  rw [hinverseSquare, Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hfirstAction)]
  field_simp [hfirstAction.ne']

/-- The complete Cartesian action map is a left inverse of the lifted Delaunay chart. -/
theorem cartesianDelaunayActions_liftedDelaunayPhasePoint
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    cartesianDelaunayActions
        (liftedDelaunayPhasePoint
          firstAction eccentricity meanAnomaly periapsisAngle) =
      ![firstAction, angularActionFromEccentricity firstAction eccentricity] := by
  funext coordinate
  fin_cases coordinate
  · exact cartesianFirstAction_liftedDelaunayPhasePoint hfirstAction
      heccentricity heccentricityOne
  · exact cartesianAngularAction_liftedDelaunayPhasePoint hfirstAction.ne'
      heccentricity heccentricityOne

/-- The Cartesian action map is analytic at every nondegenerate lifted elliptic point. -/
theorem analyticAt_cartesianDelaunayActions_liftedDelaunayPhasePoint
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    AnalyticAt ℝ cartesianDelaunayActions
      (liftedDelaunayPhasePoint
        firstAction eccentricity meanAnomaly periapsisAngle) := by
  let anomaly := liftedDelaunayEccentricAnomaly eccentricity meanAnomaly
  let state := liftedDelaunayPhasePoint
    firstAction eccentricity meanAnomaly periapsisAngle
  have hradius : 0 < eccentricRadius firstAction eccentricity anomaly :=
    eccentricRadius_pos hfirstAction.ne' heccentricity heccentricityOne
  have hpositionSq : state 0 ^ 2 + state 1 ^ 2 =
      eccentricRadius firstAction eccentricity anomaly ^ 2 := by
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
  exact analyticAt_cartesianDelaunayActions hposition henergy

/-- The Delaunay Hamiltonian is analytic whenever its first action is nonzero. -/
theorem analyticAt_delaunayHamiltonian
    {action : ActionSpace} (hfirstAction : action 0 ≠ 0) :
    AnalyticAt ℝ delaunayHamiltonian action := by
  have hcoordinate : ∀ coordinate : Fin 2,
      AnalyticAt ℝ (fun candidate : ActionSpace ↦ candidate coordinate) action :=
    fun coordinate ↦
      (ContinuousLinearMap.proj coordinate : ActionSpace →L[ℝ] ℝ).analyticAt action
  have hdenominator : AnalyticAt ℝ
      (fun candidate : ActionSpace ↦ 2 * candidate 0 ^ 2) action :=
    analyticAt_const.mul ((hcoordinate 0).pow 2)
  have hdenominatorNe : 2 * action 0 ^ 2 ≠ 0 := by positivity
  unfold delaunayHamiltonian
  exact (analyticAt_const.div hdenominator hdenominatorNe).sub (hcoordinate 1)

/-- The Fréchet differential of the Delaunay Hamiltonian is the covector represented by its
frequency vector. -/
theorem fderiv_delaunayHamiltonian_eq_actionCovector
    {action : ActionSpace} (hfirstAction : action 0 ≠ 0) :
    fderiv ℝ delaunayHamiltonian action =
      actionCovector (delaunayFrequency (action 0)) := by
  have hdifferentiable : DifferentiableAt ℝ delaunayHamiltonian action :=
    (analyticAt_delaunayHamiltonian hfirstAction).differentiableAt
  have hlineZero : HasDerivAt
      (fun value : ℝ ↦ ![value, action 1]) (actionCoordinateVector 0) (action 0) := by
    rw [hasDerivAt_pi]
    intro coordinate
    fin_cases coordinate
    · simpa [actionCoordinateVector] using hasDerivAt_id' (action 0)
    · simpa [actionCoordinateVector] using hasDerivAt_const (action 0) (action 1)
  have hlineOne : HasDerivAt
      (fun value : ℝ ↦ ![action 0, value]) (actionCoordinateVector 1) (action 1) := by
    rw [hasDerivAt_pi]
    intro coordinate
    fin_cases coordinate
    · simpa [actionCoordinateVector] using hasDerivAt_const (action 1) (action 0)
    · simpa [actionCoordinateVector] using hasDerivAt_id' (action 1)
  have hvectorZero : ![action 0, action 1] = action := by
    funext coordinate
    fin_cases coordinate <;> simp
  have houterZero : HasFDerivAt delaunayHamiltonian
      (fderiv ℝ delaunayHamiltonian action) ![action 0, action 1] := by
    rw [hvectorZero]
    exact hdifferentiable.hasFDerivAt
  have hzeroChain := houterZero.comp_hasDerivAt (action 0) hlineZero
  have honeChain := houterZero.comp_hasDerivAt (action 1) hlineOne
  have hzero : fderiv ℝ delaunayHamiltonian action (actionCoordinateVector 0) =
      1 / action 0 ^ 3 := by
    have hchainDeriv := hzeroChain.deriv
    have hexplicit := deriv_delaunayHamiltonian_firstAction hfirstAction (action 1)
    have hfunction :
        (delaunayHamiltonian ∘ fun value : ℝ ↦ ![value, action 1]) =
          fun value ↦ -1 / (2 * value ^ 2) - action 1 := by
      funext value
      rfl
    rw [hfunction] at hchainDeriv
    rw [hexplicit] at hchainDeriv
    exact hchainDeriv.symm
  have hone : fderiv ℝ delaunayHamiltonian action (actionCoordinateVector 1) = -1 := by
    have hchainDeriv := honeChain.deriv
    have hexplicit := deriv_delaunayHamiltonian_secondAction (action 0) (action 1)
    have hfunction :
        (delaunayHamiltonian ∘ fun value : ℝ ↦ ![action 0, value]) =
          fun value ↦ -1 / (2 * action 0 ^ 2) - value := by
      funext value
      rfl
    rw [hfunction] at hchainDeriv
    rw [hexplicit] at hchainDeriv
    exact hchainDeriv.symm
  apply ContinuousLinearMap.ext
  intro direction
  have hdecompose : direction =
      direction 0 • actionCoordinateVector 0 +
        direction 1 • actionCoordinateVector 1 := by
    funext coordinate
    fin_cases coordinate <;> simp [actionCoordinateVector]
  rw [hdecompose, map_add, map_smul, map_smul, hzero, hone]
  simp only [actionCovector_apply, dot_eq, delaunayFrequency,
    Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  simp [actionCoordinateVector]
  ring

/-- At every noncentral phase point, the zero-mass rotating Hamiltonian is inertial Kepler energy
minus angular action. -/
theorem hamiltonian_zero_eq_cartesianKeplerEnergy_sub_angularAction
    (state : PhaseSpace) :
    hamiltonian 0 state =
      cartesianKeplerEnergy state - cartesianAngularAction state := by
  rw [hamiltonian_zero]
  unfold cartesianKeplerEnergy cartesianAngularAction
  ring

/-- On the negative-energy region, the Cartesian action reconstruction puts the physical
Hamiltonian into Delaunay normal form. -/
theorem delaunayHamiltonian_cartesianDelaunayActions
    {state : PhaseSpace} (henergy : cartesianKeplerEnergy state < 0) :
    delaunayHamiltonian (cartesianDelaunayActions state) = hamiltonian 0 state := by
  have hpositive : 0 < -2 * cartesianKeplerEnergy state := by linarith
  have hroot : 0 < Real.sqrt (-2 * cartesianKeplerEnergy state) :=
    Real.sqrt_pos.mpr hpositive
  have hrootSquare : (Real.sqrt (-2 * cartesianKeplerEnergy state)) ^ 2 =
      -2 * cartesianKeplerEnergy state := Real.sq_sqrt hpositive.le
  rw [hamiltonian_zero_eq_cartesianKeplerEnergy_sub_angularAction]
  simp only [delaunayHamiltonian, cartesianDelaunayActions,
    cartesianFirstAction, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hroot.ne']
  ring_nf at hrootSquare ⊢
  nlinarith

/-- The physical and action-coordinate zero-mass Hamiltonians agree on a whole neighborhood of
every negative-energy, noncentral phase point. -/
theorem hamiltonian_zero_eventuallyEq_delaunayHamiltonian_comp_actions
    {state : PhaseSpace} (hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0)
    (henergy : cartesianKeplerEnergy state < 0) :
    hamiltonian 0 =ᶠ[nhds state]
      fun candidate ↦ delaunayHamiltonian (cartesianDelaunayActions candidate) := by
  have henergyContinuous :=
    (analyticAt_cartesianKeplerEnergy hposition).continuousAt
  have heventually : ∀ᶠ candidate in nhds state,
      cartesianKeplerEnergy candidate < 0 :=
    henergyContinuous.eventually (Iio_mem_nhds henergy)
  filter_upwards [heventually] with candidate hcandidate
  exact (delaunayHamiltonian_cartesianDelaunayActions hcandidate).symm

/-- Differential form of the action-coordinate normal form for the zero-mass Hamiltonian. -/
theorem fderiv_hamiltonian_zero_eq_delaunay_comp_actions
    {state : PhaseSpace} (hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0)
    (henergy : cartesianKeplerEnergy state < 0) :
    fderiv ℝ (hamiltonian 0) state =
      (fderiv ℝ delaunayHamiltonian (cartesianDelaunayActions state)).comp
        (fderiv ℝ cartesianDelaunayActions state) := by
  have hactionFirst : cartesianDelaunayActions state 0 ≠ 0 := by
    change 1 / Real.sqrt (-2 * cartesianKeplerEnergy state) ≠ 0
    have hpositive : 0 < -2 * cartesianKeplerEnergy state := by linarith
    positivity
  have houter : DifferentiableAt ℝ delaunayHamiltonian
      (cartesianDelaunayActions state) :=
    (analyticAt_delaunayHamiltonian hactionFirst).differentiableAt
  have hinner : DifferentiableAt ℝ cartesianDelaunayActions state :=
    (analyticAt_cartesianDelaunayActions hposition henergy).differentiableAt
  calc
    fderiv ℝ (hamiltonian 0) state =
        fderiv ℝ
          (fun candidate ↦ delaunayHamiltonian (cartesianDelaunayActions candidate)) state :=
      (hamiltonian_zero_eventuallyEq_delaunayHamiltonian_comp_actions
        hposition henergy).fderiv_eq
    _ = (fderiv ℝ delaunayHamiltonian (cartesianDelaunayActions state)).comp
          (fderiv ℝ cartesianDelaunayActions state) := by
      rw [show (fun candidate ↦
        delaunayHamiltonian (cartesianDelaunayActions candidate)) =
          delaunayHamiltonian ∘ cartesianDelaunayActions by rfl]
      exact fderiv_comp state houter hinner

/-- The physical Hamiltonian differential is the pullback of the Kepler frequency covector by the
Cartesian action map. -/
theorem fderiv_hamiltonian_zero_eq_frequencyCovector_comp_actions
    {state : PhaseSpace} (hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0)
    (henergy : cartesianKeplerEnergy state < 0) :
    fderiv ℝ (hamiltonian 0) state =
      (actionCovector (delaunayFrequency (cartesianDelaunayActions state 0))).comp
        (fderiv ℝ cartesianDelaunayActions state) := by
  rw [fderiv_hamiltonian_zero_eq_delaunay_comp_actions hposition henergy]
  have hfirstAction : cartesianDelaunayActions state 0 ≠ 0 := by
    change 1 / Real.sqrt (-2 * cartesianKeplerEnergy state) ≠ 0
    have hpositive : 0 < -2 * cartesianKeplerEnergy state := by linarith
    positivity
  rw [fderiv_delaunayHamiltonian_eq_actionCovector hfirstAction]

/-- The physical zero-mass Hamiltonian pulls back to the Delaunay Hamiltonian. -/
theorem hamiltonian_zero_liftedDelaunayPhasePoint
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : firstAction ≠ 0)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    hamiltonian 0
        (liftedDelaunayPhasePoint
          firstAction eccentricity meanAnomaly periapsisAngle) =
      delaunayHamiltonian
        ![firstAction, angularActionFromEccentricity firstAction eccentricity] := by
  let state := liftedDelaunayPhasePoint
    firstAction eccentricity meanAnomaly periapsisAngle
  have hdecompose : hamiltonian 0 state =
      cartesianKeplerEnergy state - cartesianAngularAction state := by
    rw [hamiltonian_zero]
    unfold cartesianKeplerEnergy cartesianAngularAction
    ring
  have henergy := cartesianKeplerEnergy_liftedDelaunayPhasePoint
    (meanAnomaly := meanAnomaly) (periapsisAngle := periapsisAngle)
    hfirstAction heccentricity heccentricityOne
  have hangular := cartesianAngularAction_liftedDelaunayPhasePoint
    (meanAnomaly := meanAnomaly) (periapsisAngle := periapsisAngle)
    hfirstAction heccentricity heccentricityOne
  rw [hdecompose, henergy, hangular]
  rfl

end LeanPool.PoincareThreeBody
