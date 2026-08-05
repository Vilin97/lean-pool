/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.ActionFactorization
import LeanPool.PoincareThreeBody.DisturbingFunction
import LeanPool.PoincareThreeBody.OrbitHomologicalEquation

/-!
# The resonant action form of the first homological obstruction

This file connects the exact first homological equation to the derivative of Poincaré's resonant
disturbing average.  The bridge is the pointwise factorization of the leading differential through
the physical Delaunay action map.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody MeasureTheory Set
open scoped Interval

/-- The perturbation's two Poisson brackets with the physical actions along a resonant ellipse. -/
noncomputable def resonantPerturbationActionPoisson
    (p q : ℕ) (eccentricity orientation time : ℝ) : ActionSpace :=
  actionPoissonVector firstMassPerturbation
    (orientedResonantKeplerPhasePoint p q eccentricity orientation time)

/-- Varying the inertial orientation at fixed time follows the angular-action Hamiltonian vector
field on the full resonant phase trajectory. -/
theorem hasDerivAt_orientedResonantKeplerPhasePoint_orientation
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (eccentricity orientation time : ℝ) :
    HasDerivAt
      (fun phase ↦ orientedResonantKeplerPhasePoint
        p q eccentricity phase time)
      (angularActionVectorField
        (orientedResonantKeplerPhasePoint
          p q eccentricity orientation time)) orientation := by
  let firstAction := resonantFirstAction p q
  let meanAnomaly := resonantMeanAnomaly p q time
  let chartCurve : ℝ → PhaseSpace := fun phase ↦
    liftedDelaunayPhasePoint firstAction eccentricity meanAnomaly (phase - time)
  have hargument : HasDerivAt (fun phase : ℝ ↦ phase - time) 1 orientation :=
    (hasDerivAt_id orientation).sub_const time
  have hchart :=
    (hasDerivAt_liftedDelaunayPhasePoint_periapsisAngle
      firstAction eccentricity meanAnomaly (orientation - time)).scomp
      orientation hargument
  have hcurve : chartCurve = fun phase ↦
      orientedResonantKeplerPhasePoint p q eccentricity phase time := by
    funext phase
    exact liftedDelaunayPhasePoint_resonant hp hq eccentricity phase time
  have hstate : chartCurve orientation =
      orientedResonantKeplerPhasePoint p q eccentricity orientation time :=
    congrFun hcurve orientation
  rw [← hstate]
  simpa [chartCurve] using hchart.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun phase ↦ (congrFun hcurve phase).symm)

/-- The first mass perturbation is differentiable at every collision-free point of an interior
resonant ellipse. -/
theorem differentiableAt_firstMassPerturbation_orientedResonantKeplerPhasePoint
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    DifferentiableAt ℝ firstMassPerturbation
      (orientedResonantKeplerPhasePoint p q eccentricity orientation time) := by
  let state := orientedResonantKeplerPhasePoint p q eccentricity orientation time
  have hcollision : (0, state) ∈ collisionFree :=
    orientedResonantKeplerPhasePoint_collisionFree_mass_zero hp hq heccentricity
      heccentricityOne hapoapsis
  have hcoefficient : ContDiffAt ℝ 1
      (parameterCoefficient (Function.uncurry hamiltonian)) state :=
    contDiffAt_parameterCoefficient (hamiltonian_analyticAt hcollision).contDiffAt
  exact (hcoefficient.congr_of_eventuallyEq
    (parameterCoefficient_hamiltonian_eventuallyEq hcollision).symm).differentiableAt
      (by norm_num)

/-- The angular component of the perturbation action vector is the explicit orientation
derivative used in the disturbing average. -/
theorem resonantPerturbationActionPoisson_one
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    resonantPerturbationActionPoisson p q eccentricity orientation time 1 =
      resonantDisturbingOrientationDerivative
        p q eccentricity orientation time := by
  let state := orientedResonantKeplerPhasePoint p q eccentricity orientation time
  have hperturbation : DifferentiableAt ℝ firstMassPerturbation state :=
    differentiableAt_firstMassPerturbation_orientedResonantKeplerPhasePoint
      hp hq heccentricity heccentricityOne hapoapsis
  have horientation :=
    hasDerivAt_orientedResonantKeplerPhasePoint_orientation
      hp hq eccentricity orientation time
  have hchain := hperturbation.hasFDerivAt.comp_hasDerivAt orientation horientation
  have hbracket : poissonBracket firstMassPerturbation cartesianAngularAction state =
      fderiv ℝ firstMassPerturbation state (angularActionVectorField state) :=
    poissonBracket_cartesianAngularAction _ _
  have hchainBracket : HasDerivAt
      (fun phase ↦ firstMassPerturbation
        (orientedResonantKeplerPhasePoint p q eccentricity phase time))
      (poissonBracket firstMassPerturbation cartesianAngularAction state)
      orientation :=
    hchain.congr_deriv hbracket.symm
  have hfunction : (fun phase ↦ firstMassPerturbation
      (orientedResonantKeplerPhasePoint p q eccentricity phase time)) =
      fun phase ↦ resonantDisturbingFunction p q eccentricity phase time := by
    funext phase
    exact firstMassPerturbation_orientedResonantKeplerPhasePoint
      p q eccentricity phase time
  have hchainDisturbing : HasDerivAt
      (fun phase ↦ resonantDisturbingFunction p q eccentricity phase time)
      (poissonBracket firstMassPerturbation cartesianAngularAction state)
      orientation := by
    rw [← hfunction]
    exact hchainBracket
  have hexplicit := hasDerivAt_resonantDisturbingFunction_orientation
    (orientation := orientation) (time := time)
    hp hq heccentricity heccentricityOne hapoapsis
  unfold resonantPerturbationActionPoisson actionPoissonVector
  change poissonBracket firstMassPerturbation cartesianAngularAction state = _
  exact hchainDisturbing.unique hexplicit

/-- Along the unperturbed resonant flow, the time derivative of the disturbing function is the
Kepler frequency contracted with the perturbation action Poisson vector. -/
theorem hasDerivAt_resonantDisturbingFunction_time_actionPoisson
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    HasDerivAt (resonantDisturbingFunction p q eccentricity orientation)
      (dot (delaunayFrequency (resonantFirstAction p q))
        (resonantPerturbationActionPoisson
          p q eccentricity orientation time)) time := by
  let state := orientedResonantKeplerPhasePoint p q eccentricity orientation time
  have hperturbation : DifferentiableAt ℝ firstMassPerturbation state :=
    differentiableAt_firstMassPerturbation_orientedResonantKeplerPhasePoint
      hp hq heccentricity heccentricityOne hapoapsis
  have htime := DifferentiableAt.hasDerivAt_comp_orientedResonantKeplerPhasePoint
    hp hq heccentricity heccentricityOne hperturbation
  have hcollision : (0, state) ∈ collisionFree :=
    orientedResonantKeplerPhasePoint_collisionFree_mass_zero hp hq heccentricity
      heccentricityOne hapoapsis
  have hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0 := by
    simpa [secondPrimaryDistanceSq] using hcollision.2
  have hstateLifted : state = liftedDelaunayPhasePoint
      (resonantFirstAction p q) eccentricity (resonantMeanAnomaly p q time)
      (orientation - time) :=
    (liftedDelaunayPhasePoint_resonant hp hq eccentricity orientation time).symm
  have henergyIdentity : cartesianKeplerEnergy state =
      -1 / (2 * resonantFirstAction p q ^ 2) := by
    rw [hstateLifted]
    exact cartesianKeplerEnergy_liftedDelaunayPhasePoint
      (resonantFirstAction_pos hp hq).ne' heccentricity heccentricityOne
  have henergy : cartesianKeplerEnergy state < 0 := by
    rw [henergyIdentity]
    exact div_neg_of_neg_of_pos (by norm_num)
      (mul_pos (by norm_num) (sq_pos_of_pos (resonantFirstAction_pos hp hq)))
  have hbracket := poissonBracket_hamiltonian_zero_eq_frequency_dot_actionPoisson
    hposition henergy firstMassPerturbation
  have hfirstActionIdentity : cartesianDelaunayActions state 0 =
      resonantFirstAction p q := by
    rw [hstateLifted, cartesianDelaunayActions_liftedDelaunayPhasePoint
      (resonantFirstAction_pos hp hq) heccentricity heccentricityOne]
    rfl
  rw [hfirstActionIdentity] at hbracket
  have htimeFrequency : HasDerivAt
      (fun argument ↦ firstMassPerturbation
        (orientedResonantKeplerPhasePoint p q eccentricity orientation argument))
      (dot (delaunayFrequency (resonantFirstAction p q))
        (resonantPerturbationActionPoisson p q eccentricity orientation time)) time := by
    apply htime.congr_deriv
    simpa [state, resonantPerturbationActionPoisson] using hbracket
  have hfunction : (fun argument ↦ firstMassPerturbation
      (orientedResonantKeplerPhasePoint p q eccentricity orientation argument)) =
      resonantDisturbingFunction p q eccentricity orientation := by
    funext argument
    exact firstMassPerturbation_orientedResonantKeplerPhasePoint
      p q eccentricity orientation argument
  rw [← hfunction]
  exact htimeFrequency

/-- The candidate forcing is the negative contraction of its leading action differential with
the perturbation action Poisson vector. -/
theorem IsFirstIntegralFamily.resonantCandidateForcing_eq_neg_dot_actionPoisson
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    resonantCandidateForcing F p q eccentricity orientation time =
      -dot
        (leadingActionDifferential F
          ![resonantFirstAction p q,
            angularActionFromEccentricity (resonantFirstAction p q) eccentricity])
        (resonantPerturbationActionPoisson
          p q eccentricity orientation time) := by
  let state := orientedResonantKeplerPhasePoint p q eccentricity orientation time
  let differential := leadingActionDifferential F
    ![resonantFirstAction p q,
      angularActionFromEccentricity (resonantFirstAction p q) eccentricity]
  have hfirstAction : 0 < resonantFirstAction p q := resonantFirstAction_pos hp hq
  have hfactor :=
    IsFirstIntegralFamily.fderiv_mass_zero_eq_actionDifferential_comp_actions
      (meanAnomaly := resonantMeanAnomaly p q time)
      (periapsisAngle := orientation - time)
      hδ hanalytic hfirstIntegral hfirstAction heccentricity
      heccentricityOne hapoapsis
  dsimp only at hfactor
  rw [liftedDelaunayPhasePoint_resonant hp hq eccentricity orientation time] at hfactor
  have hcollision : (0, state) ∈ collisionFree :=
    orientedResonantKeplerPhasePoint_collisionFree_mass_zero hp hq heccentricity.le
      heccentricityOne hapoapsis
  have hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0 := by
    simpa [secondPrimaryDistanceSq] using hcollision.2
  have hstateLifted : state = liftedDelaunayPhasePoint
      (resonantFirstAction p q) eccentricity (resonantMeanAnomaly p q time)
      (orientation - time) :=
    (liftedDelaunayPhasePoint_resonant hp hq eccentricity orientation time).symm
  have henergyIdentity : cartesianKeplerEnergy state =
      -1 / (2 * resonantFirstAction p q ^ 2) := by
    rw [hstateLifted]
    exact cartesianKeplerEnergy_liftedDelaunayPhasePoint hfirstAction.ne'
      heccentricity.le heccentricityOne
  have henergy : cartesianKeplerEnergy state < 0 := by
    rw [henergyIdentity]
    exact div_neg_of_neg_of_pos (by norm_num)
      (mul_pos (by norm_num) (sq_pos_of_pos hfirstAction))
  unfold resonantCandidateForcing
  exact poissonBracket_eq_neg_dot_actionPoissonVector_of_fderiv_factors
    hposition henergy hfactor

/-- The leading action differential at the actions carried by a resonant eccentric ellipse. -/
noncomputable def resonantLeadingActionDifferential
    (F : ℝ → PhaseSpace → ℝ) (p q : ℕ) (eccentricity : ℝ) : ActionSpace :=
  leadingActionDifferential F
    ![resonantFirstAction p q,
      angularActionFromEccentricity (resonantFirstAction p q) eccentricity]

/-- The correction whose derivative isolates the resonant orientation forcing. -/
noncomputable def resonantCombinedCorrection
    (F : ℝ → PhaseSpace → ℝ) (p q : ℕ)
    (eccentricity orientation time : ℝ) : ℝ :=
  (p : ℝ) * (resonantLeadingActionDifferential F p q eccentricity 0) *
      resonantDisturbingFunction p q eccentricity orientation time -
    (q : ℝ) * resonantCandidateCorrection F p q eccentricity orientation time

/-- Displayed derivative of the combined resonant correction. -/
noncomputable def resonantCombinedCorrectionDerivative
    (F : ℝ → PhaseSpace → ℝ) (p q : ℕ)
    (eccentricity orientation time : ℝ) : ℝ :=
  (p : ℝ) * (resonantLeadingActionDifferential F p q eccentricity 0) *
      deriv (resonantDisturbingFunction p q eccentricity orientation) time -
    (q : ℝ) * poissonBracket
      (parameterCoefficient (Function.uncurry F)) (hamiltonian 0)
      (orientedResonantKeplerPhasePoint p q eccentricity orientation time)

/-- The combined correction has the displayed derivative. -/
theorem IsJointlyAnalytic.hasDerivAt_resonantCombinedCorrection
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    HasDerivAt (resonantCombinedCorrection F p q eccentricity orientation)
      (resonantCombinedCorrectionDerivative F p q eccentricity orientation time) time := by
  have hdisturbing : DifferentiableAt ℝ
      (resonantDisturbingFunction p q eccentricity orientation) time :=
    (analyticAt_resonantDisturbingFunction_time hp hq heccentricity
      heccentricityOne hapoapsis).differentiableAt
  have hcorrection := IsJointlyAnalytic.hasDerivAt_resonantCandidateCorrection
    (orientation := orientation) (time := time)
    hδ hanalytic hp hq heccentricity heccentricityOne hapoapsis
  have hfirst := hdisturbing.hasDerivAt.const_mul
    ((p : ℝ) * resonantLeadingActionDifferential F p q eccentricity 0)
  have hsecond := hcorrection.const_mul (q : ℝ)
  exact hfirst.sub hsecond

/-- The derivative of the combined correction is continuous, hence interval integrable. -/
theorem continuous_resonantCombinedCorrectionDerivative
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    Continuous (resonantCombinedCorrectionDerivative
      F p q eccentricity orientation) := by
  have hdisturbingSmooth : ContDiff ℝ 1
      (resonantDisturbingFunction p q eccentricity orientation) := by
    rw [contDiff_iff_contDiffAt]
    intro time
    exact (analyticAt_resonantDisturbingFunction_time hp hq heccentricity
      heccentricityOne hapoapsis).contDiffAt
  have hdisturbingDerivative : Continuous
      (deriv (resonantDisturbingFunction p q eccentricity orientation)) :=
    hdisturbingSmooth.continuous_deriv_one
  have hcorrectionDerivative :=
    continuous_resonantCandidateCorrectionDerivative
      (orientation := orientation) hδ hanalytic hp hq
      heccentricity heccentricityOne hapoapsis
  unfold resonantCombinedCorrectionDerivative
  fun_prop

/-- The combined correction inherits the common resonant period. -/
lemma resonantCombinedCorrection_periodic
    (F : ℝ → PhaseSpace → ℝ) {p q : ℕ} (hp : 0 < p)
    {eccentricity orientation : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) :
    resonantCombinedCorrection F p q eccentricity orientation (resonantOrbitPeriod p) =
      resonantCombinedCorrection F p q eccentricity orientation 0 := by
  unfold resonantCombinedCorrection
  rw [show resonantOrbitPeriod p = 0 + resonantOrbitPeriod p by ring,
    resonantDisturbingFunction_add_period hp heccentricity heccentricityOne]
  simp only [zero_add]
  rw [resonantCandidateCorrection_periodic F hp heccentricity heccentricityOne]

/-- The exact homological equation, after combining its time-derivative part with the perturbation
time derivative, has coefficient `k · d f₀` multiplying the orientation forcing. -/
theorem IsFirstIntegralFamily.resonantCombinedHomologicalEquation
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    resonantCombinedCorrectionDerivative F p q eccentricity orientation time +
        dot (resonanceVector p q)
          (resonantLeadingActionDifferential F p q eccentricity) *
        resonantDisturbingOrientationDerivative p q eccentricity orientation time = 0 := by
  let differential := resonantLeadingActionDifferential F p q eccentricity
  let vector := resonantPerturbationActionPoisson p q eccentricity orientation time
  let correctionDerivative := poissonBracket
    (parameterCoefficient (Function.uncurry F)) (hamiltonian 0)
    (orientedResonantKeplerPhasePoint p q eccentricity orientation time)
  have hhomological :=
    IsFirstIntegralFamily.firstHomologicalEquation_on_resonantKeplerOrbit
      hδ hanalytic hfirstIntegral hp hq heccentricity.le heccentricityOne hapoapsis
      (orientation := orientation) (time := time)
  have hcandidate :=
    IsFirstIntegralFamily.resonantCandidateForcing_eq_neg_dot_actionPoisson
      hδ hanalytic hfirstIntegral hp hq heccentricity heccentricityOne hapoapsis
      (orientation := orientation) (time := time)
  change resonantCandidateForcing F p q eccentricity orientation time =
      -dot differential vector at hcandidate
  change correctionDerivative +
      resonantCandidateForcing F p q eccentricity orientation time = 0 at hhomological
  rw [hcandidate, dot_eq] at hhomological
  have htime := (hasDerivAt_resonantDisturbingFunction_time_actionPoisson
    hp hq heccentricity.le heccentricityOne hapoapsis
    (orientation := orientation) (time := time)).deriv
  change deriv (resonantDisturbingFunction p q eccentricity orientation) time =
      dot (delaunayFrequency (resonantFirstAction p q)) vector at htime
  have hone := resonantPerturbationActionPoisson_one hp hq heccentricity.le
    heccentricityOne hapoapsis (orientation := orientation) (time := time)
  change vector 1 =
      resonantDisturbingOrientationDerivative p q eccentricity orientation time at hone
  unfold resonantCombinedCorrectionDerivative
  change (p : ℝ) * differential 0 *
      deriv (resonantDisturbingFunction p q eccentricity orientation) time -
      (q : ℝ) * correctionDerivative +
    dot (resonanceVector p q) differential *
      resonantDisturbingOrientationDerivative p q eccentricity orientation time = 0
  rw [htime, ← hone, dot_eq, dot_eq]
  simp only [delaunayFrequency, resonanceVector, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [resonantFirstAction_cube hp hq]
  have hpReal : (p : ℝ) ≠ 0 := by positivity
  field_simp [hpReal]
  linear_combination -(q : ℝ) * hhomological

/-- A nonzero derivative of Poincaré's disturbing average forces the leading action differential
to annihilate the integer resonance vector. -/
theorem IsFirstIntegralFamily.resonantLeadingDifferential_orthogonal
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation : ℝ}
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1)
    (haverageDeriv : deriv (resonantDisturbingAverage p q eccentricity) orientation ≠ 0) :
    dot (resonanceVector p q)
      (resonantLeadingActionDifferential F p q eccentricity) = 0 := by
  apply coefficient_eq_zero_of_averaged_homologicalEquation
    (correction := resonantCombinedCorrection F p q eccentricity orientation)
    (correctionDerivative :=
      resonantCombinedCorrectionDerivative F p q eccentricity orientation)
    (forcing := resonantDisturbingOrientationDerivative
      p q eccentricity orientation)
    (period := resonantOrbitPeriod p)
  · intro time _
    exact IsJointlyAnalytic.hasDerivAt_resonantCombinedCorrection
      hδ hanalytic hp hq heccentricity.le heccentricityOne hapoapsis
  · exact (continuous_resonantCombinedCorrectionDerivative hδ hanalytic hp hq
      heccentricity.le heccentricityOne hapoapsis).intervalIntegrable _ _
  · exact intervalIntegrable_resonantDisturbingOrientationDerivative hp hq
      heccentricity.le heccentricityOne hapoapsis
  · exact resonantCombinedCorrection_periodic F hp heccentricity.le heccentricityOne
  · rwa [← deriv_resonantDisturbingAverage hp hq heccentricity.le
      heccentricityOne hapoapsis]
  · intro time _
    exact IsFirstIntegralFamily.resonantCombinedHomologicalEquation
      hδ hanalytic hfirstIntegral hp hq heccentricity heccentricityOne hapoapsis

/-- A nonzero derivative of Poincaré's disturbing average forces dependence of the Hamiltonian
and leading-integral differentials at that resonant action. -/
theorem IsFirstIntegralFamily.resonantLeadingDifferential_obstruction
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation : ℝ}
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1)
    (haverageDeriv : deriv (resonantDisturbingAverage p q eccentricity) orientation ≠ 0) :
    ¬LinearIndependent ℝ
      ![delaunayFrequency (resonantFirstAction p q),
        resonantLeadingActionDifferential F p q eccentricity] := by
  apply rationalKeplerResonance_obstruction hp hq
  exact IsFirstIntegralFamily.resonantLeadingDifferential_orthogonal
    hδ hanalytic hfirstIntegral hp hq heccentricity heccentricityOne
    hapoapsis haverageDeriv

end LeanPool.PoincareThreeBody
