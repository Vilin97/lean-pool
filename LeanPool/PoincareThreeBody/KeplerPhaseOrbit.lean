/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DisturbingFunction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Full phase-space Kepler orbits

The disturbing function only depends on position, so earlier files used zero placeholders for the
momenta.  The homological equation must instead be evaluated on a genuine Hamiltonian orbit.  This
file supplies the canonical rotating-frame momentum and embeds the resonant ellipse into the full
four-dimensional phase space.
-/

namespace LeanPool.PoincareThreeBody


/-- Inertial Cartesian velocity of the eccentric-anomaly ellipse when the mean anomaly advances
at rate `meanMotion`. -/
noncomputable def inertialEllipseVelocity
    (firstAction eccentricity meanMotion anomaly : ℝ) : ActionSpace :=
  ![-firstAction ^ 2 * meanMotion * Real.sin anomaly /
      (1 - eccentricity * Real.cos anomaly),
    firstAction ^ 2 * meanMotion * Real.sqrt (1 - eccentricity ^ 2) * Real.cos anomaly /
      (1 - eccentricity * Real.cos anomaly)]

/-- Canonical momentum of an oriented resonant ellipse in rotating coordinates. -/
noncomputable def orientedResonantEllipseMomentum
    (p q : ℕ) (eccentricity orientation time : ℝ) : ActionSpace :=
  positionInRotatingFrame (time - orientation)
    (inertialEllipseVelocity (resonantFirstAction p q) eccentricity
      (resonantMeanMotion p q)
      (resonantEccentricAnomaly p q eccentricity time))

/-- Embed planar position and canonical momentum into `(x,y,pₓ,pᵧ)` phase space. -/
def positionMomentumPhasePoint (position momentum : ActionSpace) : PhaseSpace :=
  ![position 0, position 1, momentum 0, momentum 1]

/-- The genuine full phase-space orbit underlying the oriented resonant disturbing function. -/
noncomputable def orientedResonantKeplerPhasePoint
    (p q : ℕ) (eccentricity orientation time : ℝ) : PhaseSpace :=
  positionMomentumPhasePoint
    (orientedResonantEllipsePosition p q eccentricity orientation time)
    (orientedResonantEllipseMomentum p q eccentricity orientation time)

/-- Every coordinate of the true rotating-frame momentum is analytic in time. -/
theorem analyticAt_orientedResonantEllipseMomentum_coordinate
    (p q : ℕ) {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (coordinate : Fin 2) :
    AnalyticAt ℝ (fun argument ↦
      orientedResonantEllipseMomentum p q eccentricity orientation argument coordinate) time := by
  let anomaly : ℝ → ℝ := resonantEccentricAnomaly p q eccentricity
  let denominator : ℝ → ℝ := fun argument ↦
    1 - eccentricity * Real.cos (anomaly argument)
  have hanomaly : AnalyticAt ℝ anomaly time :=
    analyticAt_resonantEccentricAnomaly p q heccentricity heccentricityOne
  have hsinAnomaly : AnalyticAt ℝ (fun argument ↦ Real.sin (anomaly argument)) time :=
    Real.analyticAt_sin.comp hanomaly
  have hcosAnomaly : AnalyticAt ℝ (fun argument ↦ Real.cos (anomaly argument)) time :=
    Real.analyticAt_cos.comp hanomaly
  have hdenominator : AnalyticAt ℝ denominator time := by
    exact analyticAt_const.sub (analyticAt_const.mul hcosAnomaly)
  have hdenominatorNe : denominator time ≠ 0 :=
    (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne).ne'
  have hinverseDenominator : AnalyticAt ℝ (fun argument ↦ (denominator argument)⁻¹) time :=
    hdenominator.inv hdenominatorNe
  let velocityX : ℝ → ℝ := fun argument ↦
    -resonantFirstAction p q ^ 2 * resonantMeanMotion p q *
      Real.sin (anomaly argument) * (denominator argument)⁻¹
  let velocityY : ℝ → ℝ := fun argument ↦
    resonantFirstAction p q ^ 2 * resonantMeanMotion p q *
      Real.sqrt (1 - eccentricity ^ 2) * Real.cos (anomaly argument) *
        (denominator argument)⁻¹
  have hvelocityX : AnalyticAt ℝ velocityX time := by
    dsimp only [velocityX]
    exact ((hsinAnomaly.const_smul
      (c := -resonantFirstAction p q ^ 2 * resonantMeanMotion p q)).congr (by
        filter_upwards [] with argument
        simp [smul_eq_mul])).mul hinverseDenominator
  have hvelocityY : AnalyticAt ℝ velocityY time := by
    dsimp only [velocityY]
    exact ((hcosAnomaly.const_smul
      (c := resonantFirstAction p q ^ 2 * resonantMeanMotion p q *
        Real.sqrt (1 - eccentricity ^ 2))).congr (by
        filter_upwards [] with argument
        simp [smul_eq_mul])).mul hinverseDenominator
  have hangle : AnalyticAt ℝ (fun argument ↦ argument - orientation) time :=
    analyticAt_id.sub analyticAt_const
  have hcosAngle : AnalyticAt ℝ (fun argument ↦ Real.cos (argument - orientation)) time :=
    Real.analyticAt_cos.comp hangle
  have hsinAngle : AnalyticAt ℝ (fun argument ↦ Real.sin (argument - orientation)) time :=
    Real.analyticAt_sin.comp hangle
  fin_cases coordinate
  · change AnalyticAt ℝ (fun argument ↦
      Real.cos (argument - orientation) * velocityX argument +
        Real.sin (argument - orientation) * velocityY argument) time
    exact (hcosAngle.mul hvelocityX).add (hsinAngle.mul hvelocityY)
  · change AnalyticAt ℝ (fun argument ↦
      -Real.sin (argument - orientation) * velocityX argument +
        Real.cos (argument - orientation) * velocityY argument) time
    exact (hsinAngle.neg.mul hvelocityX).add (hcosAngle.mul hvelocityY)

/-- The genuine full resonant phase-space trajectory is analytic in time. -/
theorem analyticAt_orientedResonantKeplerPhasePoint
    (p q : ℕ) {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    AnalyticAt ℝ (orientedResonantKeplerPhasePoint p q eccentricity orientation) time := by
  rw [analyticAt_pi_iff]
  intro coordinate
  fin_cases coordinate
  · exact analyticAt_orientedResonantEllipsePosition_coordinate p q heccentricity
      heccentricityOne 0
  · exact analyticAt_orientedResonantEllipsePosition_coordinate p q heccentricity
      heccentricityOne 1
  · exact analyticAt_orientedResonantEllipseMomentum_coordinate p q heccentricity
      heccentricityOne 0
  · exact analyticAt_orientedResonantEllipseMomentum_coordinate p q heccentricity
      heccentricityOne 1

theorem hasDerivAt_resonantMeanAnomaly (p q : ℕ) (time : ℝ) :
    HasDerivAt (resonantMeanAnomaly p q) (resonantMeanMotion p q) time := by
  have h := (hasDerivAt_id time).const_mul (resonantMeanMotion p q)
  apply (h.congr_deriv (by ring)).congr_of_eventuallyEq
  filter_upwards [] with argument
  simp [resonantMeanAnomaly]

theorem hasDerivAt_resonantEccentricAnomaly
    (p q : ℕ) {eccentricity time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    HasDerivAt (resonantEccentricAnomaly p q eccentricity)
      (resonantMeanMotion p q /
        (1 - eccentricity *
          Real.cos (resonantEccentricAnomaly p q eccentricity time))) time := by
  have h := (hasDerivAt_eccentricAnomaly
      (meanAnomaly := resonantMeanAnomaly p q time) heccentricity heccentricityOne).comp
    time (hasDerivAt_resonantMeanAnomaly p q time)
  apply h.congr_deriv
  simp [resonantEccentricAnomaly, div_eq_mul_inv, mul_comm]

/-- The position part of the full resonant state satisfies the first two canonical Hamilton
equations in the rotating frame. -/
theorem hasDerivAt_orientedResonantKeplerPhasePoint_position
    (p q : ℕ) {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    HasDerivAt
        (fun t ↦ orientedResonantKeplerPhasePoint p q eccentricity orientation t 0)
        (orientedResonantKeplerPhasePoint p q eccentricity orientation time 2 +
          orientedResonantKeplerPhasePoint p q eccentricity orientation time 1) time ∧
      HasDerivAt
        (fun t ↦ orientedResonantKeplerPhasePoint p q eccentricity orientation t 1)
        (orientedResonantKeplerPhasePoint p q eccentricity orientation time 3 -
          orientedResonantKeplerPhasePoint p q eccentricity orientation time 0) time := by
  let anomaly : ℝ → ℝ := resonantEccentricAnomaly p q eccentricity
  let denominator : ℝ → ℝ := fun t ↦ 1 - eccentricity * Real.cos (anomaly t)
  let xInertial : ℝ → ℝ := fun t ↦
    resonantFirstAction p q ^ 2 * (Real.cos (anomaly t) - eccentricity)
  let yInertial : ℝ → ℝ := fun t ↦
    resonantFirstAction p q ^ 2 * Real.sqrt (1 - eccentricity ^ 2) *
      Real.sin (anomaly t)
  let vxInertial : ℝ → ℝ := fun t ↦
    -resonantFirstAction p q ^ 2 * resonantMeanMotion p q *
      Real.sin (anomaly t) / denominator t
  let vyInertial : ℝ → ℝ := fun t ↦
    resonantFirstAction p q ^ 2 * resonantMeanMotion p q *
      Real.sqrt (1 - eccentricity ^ 2) * Real.cos (anomaly t) / denominator t
  let angle : ℝ → ℝ := fun t ↦ t - orientation
  have hdenominator : denominator time ≠ 0 :=
    (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne).ne'
  have hanomaly : HasDerivAt anomaly
      (resonantMeanMotion p q / denominator time) time :=
    hasDerivAt_resonantEccentricAnomaly p q heccentricity heccentricityOne
  have hxInertial : HasDerivAt xInertial (vxInertial time) time := by
    have hraw := ((Real.hasDerivAt_cos (anomaly time)).comp time hanomaly
      |>.sub_const eccentricity).const_mul (resonantFirstAction p q ^ 2)
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      dsimp [xInertial]
    · dsimp [vxInertial, denominator]
      field_simp [hdenominator]
  have hyInertial : HasDerivAt yInertial (vyInertial time) time := by
    have hraw := ((Real.hasDerivAt_sin (anomaly time)).comp time hanomaly).const_mul
      (resonantFirstAction p q ^ 2 * Real.sqrt (1 - eccentricity ^ 2))
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      dsimp [yInertial]
    · dsimp [vyInertial, denominator]
      field_simp [hdenominator]
  have hangle : HasDerivAt angle 1 time := by
    simpa [angle] using (hasDerivAt_id time).sub_const orientation
  have hcos := (Real.hasDerivAt_cos (angle time)).comp time hangle
  have hsin := (Real.hasDerivAt_sin (angle time)).comp time hangle
  constructor
  · have hraw := (hcos.mul hxInertial).add (hsin.mul hyInertial)
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      simp only [orientedResonantKeplerPhasePoint, positionMomentumPhasePoint,
        orientedResonantEllipsePosition, orientedResonantEllipseMomentum,
        positionInRotatingFrame, inertialEllipsePosition, inertialEllipseVelocity,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [xInertial, yInertial, anomaly, angle]
    · simp only [orientedResonantKeplerPhasePoint, positionMomentumPhasePoint,
        orientedResonantEllipsePosition, orientedResonantEllipseMomentum,
        positionInRotatingFrame, inertialEllipsePosition, inertialEllipseVelocity,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [xInertial, yInertial, vxInertial, vyInertial, denominator, anomaly, angle]
      ring
  · have hraw := (hsin.neg.mul hxInertial).add (hcos.mul hyInertial)
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      simp only [orientedResonantKeplerPhasePoint, positionMomentumPhasePoint,
        orientedResonantEllipsePosition, orientedResonantEllipseMomentum,
        positionInRotatingFrame, inertialEllipsePosition, inertialEllipseVelocity,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [xInertial, yInertial, anomaly, angle]
    · simp only [orientedResonantKeplerPhasePoint, positionMomentumPhasePoint,
        orientedResonantEllipsePosition, orientedResonantEllipseMomentum,
        positionInRotatingFrame, inertialEllipsePosition, inertialEllipseVelocity,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [xInertial, yInertial, vxInertial, vyInertial, denominator, anomaly, angle]
      ring

/-- In inertial coordinates, the resonant ellipse satisfies Newton's inverse-square acceleration
law. -/
theorem hasDerivAt_inertialEllipseVelocity_resonant
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (coordinate : Fin 2) :
    HasDerivAt
      (fun t ↦ inertialEllipseVelocity (resonantFirstAction p q) eccentricity
        (resonantMeanMotion p q) (resonantEccentricAnomaly p q eccentricity t) coordinate)
      (-inertialEllipsePosition (resonantFirstAction p q) eccentricity
          (resonantEccentricAnomaly p q eccentricity time) coordinate /
        eccentricRadius (resonantFirstAction p q) eccentricity
          (resonantEccentricAnomaly p q eccentricity time) ^ 3) time := by
  let firstAction := resonantFirstAction p q
  let meanMotion := resonantMeanMotion p q
  let anomaly : ℝ → ℝ := resonantEccentricAnomaly p q eccentricity
  let denominator : ℝ → ℝ := fun t ↦ 1 - eccentricity * Real.cos (anomaly t)
  have hfirstAction : firstAction ≠ 0 := (resonantFirstAction_pos hp hq).ne'
  have hmeanMotion : meanMotion = 1 / firstAction ^ 3 := by
    simpa [meanMotion, firstAction, delaunayFrequency] using
      resonantMeanMotion_eq_delaunayFrequency hp hq
  have hdenominator : denominator time ≠ 0 :=
    (one_sub_eccentricity_mul_cos_pos heccentricity heccentricityOne).ne'
  have hanomaly : HasDerivAt anomaly (meanMotion / denominator time) time :=
    hasDerivAt_resonantEccentricAnomaly p q heccentricity heccentricityOne
  have hsin := (Real.hasDerivAt_sin (anomaly time)).comp time hanomaly
  have hcos := (Real.hasDerivAt_cos (anomaly time)).comp time hanomaly
  have hdenominatorDeriv : HasDerivAt denominator
      (eccentricity * Real.sin (anomaly time) * (meanMotion / denominator time)) time := by
    have hraw := (hasDerivAt_const time 1).sub (hcos.const_mul eccentricity)
    apply (hraw.congr_deriv (by ring)).congr_of_eventuallyEq
    filter_upwards [] with t
    simp [denominator]
  fin_cases coordinate
  · have hnumerator := hsin.const_mul (-firstAction ^ 2 * meanMotion)
    have hquotient := hnumerator.div hdenominatorDeriv hdenominator
    apply (hquotient.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      rfl
    · have halgebra :
          ((-firstAction ^ 2 * meanMotion *
                (Real.cos (anomaly time) * (meanMotion / denominator time)) *
              denominator time -
            (-firstAction ^ 2 * meanMotion * Real.sin (anomaly time)) *
              (eccentricity * Real.sin (anomaly time) *
                (meanMotion / denominator time))) / denominator time ^ 2) =
            -(firstAction ^ 2 * (Real.cos (anomaly time) - eccentricity)) /
              (firstAction ^ 2 * denominator time) ^ 3 := by
        rw [hmeanMotion]
        field_simp [hfirstAction, hdenominator]
        dsimp [denominator]
        nlinarith [Real.sin_sq_add_cos_sq (anomaly time)]
      simpa [firstAction, meanMotion, anomaly, denominator,
        inertialEllipsePosition, eccentricRadius] using halgebra
  · have hnumerator := hcos.const_mul
      (firstAction ^ 2 * meanMotion * Real.sqrt (1 - eccentricity ^ 2))
    have hquotient := hnumerator.div hdenominatorDeriv hdenominator
    apply (hquotient.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      rfl
    · have halgebra :
          ((firstAction ^ 2 * meanMotion * Real.sqrt (1 - eccentricity ^ 2) *
                (-Real.sin (anomaly time) * (meanMotion / denominator time)) *
              denominator time -
            (firstAction ^ 2 * meanMotion * Real.sqrt (1 - eccentricity ^ 2) *
              Real.cos (anomaly time)) *
              (eccentricity * Real.sin (anomaly time) *
                (meanMotion / denominator time))) / denominator time ^ 2) =
            -(firstAction ^ 2 * Real.sqrt (1 - eccentricity ^ 2) *
                Real.sin (anomaly time)) /
              (firstAction ^ 2 * denominator time) ^ 3 := by
        rw [hmeanMotion]
        field_simp [hfirstAction, hdenominator]
        ring
      simpa [firstAction, meanMotion, anomaly, denominator,
        inertialEllipsePosition, eccentricRadius] using halgebra

/-- The momentum part of the rotating resonant state satisfies the remaining two Kepler
Hamilton equations. -/
theorem hasDerivAt_orientedResonantKeplerPhasePoint_momentum
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1) :
    let radius := eccentricRadius (resonantFirstAction p q) eccentricity
      (resonantEccentricAnomaly p q eccentricity time)
    HasDerivAt
        (fun t ↦ orientedResonantKeplerPhasePoint p q eccentricity orientation t 2)
        (orientedResonantKeplerPhasePoint p q eccentricity orientation time 3 -
          orientedResonantKeplerPhasePoint p q eccentricity orientation time 0 / radius ^ 3)
        time ∧
      HasDerivAt
        (fun t ↦ orientedResonantKeplerPhasePoint p q eccentricity orientation t 3)
        (-orientedResonantKeplerPhasePoint p q eccentricity orientation time 2 -
          orientedResonantKeplerPhasePoint p q eccentricity orientation time 1 / radius ^ 3)
        time := by
  let anomaly : ℝ → ℝ := resonantEccentricAnomaly p q eccentricity
  let xInertial : ℝ → ℝ := fun t ↦
    inertialEllipsePosition (resonantFirstAction p q) eccentricity (anomaly t) 0
  let yInertial : ℝ → ℝ := fun t ↦
    inertialEllipsePosition (resonantFirstAction p q) eccentricity (anomaly t) 1
  let vxInertial : ℝ → ℝ := fun t ↦
    inertialEllipseVelocity (resonantFirstAction p q) eccentricity
      (resonantMeanMotion p q) (anomaly t) 0
  let vyInertial : ℝ → ℝ := fun t ↦
    inertialEllipseVelocity (resonantFirstAction p q) eccentricity
      (resonantMeanMotion p q) (anomaly t) 1
  let radius : ℝ := eccentricRadius (resonantFirstAction p q) eccentricity (anomaly time)
  let angle : ℝ → ℝ := fun t ↦ t - orientation
  have hvx : HasDerivAt vxInertial (-xInertial time / radius ^ 3) time :=
    hasDerivAt_inertialEllipseVelocity_resonant hp hq heccentricity heccentricityOne 0
  have hvy : HasDerivAt vyInertial (-yInertial time / radius ^ 3) time :=
    hasDerivAt_inertialEllipseVelocity_resonant hp hq heccentricity heccentricityOne 1
  have hangle : HasDerivAt angle 1 time := by
    simpa [angle] using (hasDerivAt_id time).sub_const orientation
  have hcos := (Real.hasDerivAt_cos (angle time)).comp time hangle
  have hsin := (Real.hasDerivAt_sin (angle time)).comp time hangle
  constructor
  · have hraw := (hcos.mul hvx).add (hsin.mul hvy)
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      simp only [orientedResonantKeplerPhasePoint, positionMomentumPhasePoint,
        orientedResonantEllipseMomentum, positionInRotatingFrame,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [vxInertial, vyInertial, anomaly, angle]
    · simp only [orientedResonantKeplerPhasePoint, positionMomentumPhasePoint,
        orientedResonantEllipsePosition, orientedResonantEllipseMomentum,
        positionInRotatingFrame, Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [xInertial, yInertial, vxInertial, vyInertial, anomaly, radius, angle]
      ring
  · have hraw := (hsin.neg.mul hvx).add (hcos.mul hvy)
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq
    · filter_upwards [] with t
      simp only [orientedResonantKeplerPhasePoint, positionMomentumPhasePoint,
        orientedResonantEllipseMomentum, positionInRotatingFrame,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [vxInertial, vyInertial, anomaly, angle]
    · simp only [orientedResonantKeplerPhasePoint, positionMomentumPhasePoint,
        orientedResonantEllipsePosition, orientedResonantEllipseMomentum,
        positionInRotatingFrame, Matrix.cons_val_zero, Matrix.cons_val_one]
      dsimp [xInertial, yInertial, vxInertial, vyInertial, anomaly, radius, angle]
      ring
@[simp] lemma orientedResonantKeplerPhasePoint_position_zero
    (p q : ℕ) (eccentricity orientation time : ℝ) :
    orientedResonantKeplerPhasePoint p q eccentricity orientation time 0 =
      orientedResonantEllipsePosition p q eccentricity orientation time 0 := rfl

@[simp] lemma orientedResonantKeplerPhasePoint_position_one
    (p q : ℕ) (eccentricity orientation time : ℝ) :
    orientedResonantKeplerPhasePoint p q eccentricity orientation time 1 =
      orientedResonantEllipsePosition p q eccentricity orientation time 1 := rfl

/-- Adding the common resonant period preserves the true canonical momentum. -/
lemma orientedResonantEllipseMomentum_add_period {p q : ℕ} (hp : 0 < p)
    {eccentricity orientation : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) (time : ℝ) :
    orientedResonantEllipseMomentum p q eccentricity orientation
        (time + resonantOrbitPeriod p) =
      orientedResonantEllipseMomentum p q eccentricity orientation time := by
  unfold orientedResonantEllipseMomentum positionInRotatingFrame
  rw [resonantEccentricAnomaly_add_period hp heccentricity heccentricityOne]
  unfold resonantOrbitPeriod
  have hangle : time + 2 * Real.pi * (p : ℝ) - orientation =
      (time - orientation) + (p : ℝ) * (2 * Real.pi) := by ring
  rw [hangle]
  funext coordinate
  fin_cases coordinate <;> simp [inertialEllipseVelocity]

/-- The full resonant phase-space trajectory has the common period. -/
lemma orientedResonantKeplerPhasePoint_add_period {p q : ℕ} (hp : 0 < p)
    {eccentricity orientation : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) (time : ℝ) :
    orientedResonantKeplerPhasePoint p q eccentricity orientation
        (time + resonantOrbitPeriod p) =
      orientedResonantKeplerPhasePoint p q eccentricity orientation time := by
  unfold orientedResonantKeplerPhasePoint positionMomentumPhasePoint
  rw [orientedResonantEllipsePosition_add_period hp heccentricity heccentricityOne,
    orientedResonantEllipseMomentum_add_period hp heccentricity heccentricityOne]

/-- Replacing the momentum placeholder by the true momentum does not change the first mass
perturbation. -/
lemma firstMassPerturbation_orientedResonantKeplerPhasePoint
    (p q : ℕ) (eccentricity orientation time : ℝ) :
    firstMassPerturbation
        (orientedResonantKeplerPhasePoint p q eccentricity orientation time) =
      resonantDisturbingFunction p q eccentricity orientation time := by
  simp [firstMassPerturbation, resonantDisturbingFunction,
    orientedResonantEllipsePhasePoint, orientedResonantKeplerPhasePoint,
    positionMomentumPhasePoint, positionPhasePoint]

/-- Collision-freeness at mass zero depends only on the position, so the full phase-space orbit
inherits the collision exclusion proved for the interior ellipse. -/
lemma orientedResonantKeplerPhasePoint_collisionFree_mass_zero
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    (0, orientedResonantKeplerPhasePoint p q eccentricity orientation time) ∈
      collisionFree := by
  constructor
  · simpa [firstPrimaryDistanceSq] using
      orientedResonantEllipse_primaryDistance_ne_zero_of_apoapsis_lt_one
        heccentricity heccentricityOne hapoapsis
  · have hfirstAction : resonantFirstAction p q ≠ 0 :=
      (resonantFirstAction_pos hp hq).ne'
    have hradius := eccentricRadius_pos (anomaly :=
        resonantEccentricAnomaly p q eccentricity time) hfirstAction heccentricity
      heccentricityOne
    have hpositionSq := orientedResonantEllipsePosition_sq
      (p := p) (q := q) (orientation := orientation) (time := time)
      heccentricity heccentricityOne.le
    unfold secondPrimaryDistanceSq
    simp only [orientedResonantKeplerPhasePoint_position_zero,
      orientedResonantKeplerPhasePoint_position_one, add_zero]
    rw [hpositionSq]
    exact (sq_pos_of_pos hradius).ne'

end LeanPool.PoincareThreeBody
