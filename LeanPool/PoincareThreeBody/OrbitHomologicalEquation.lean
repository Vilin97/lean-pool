/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.Averaging
import LeanPool.PoincareThreeBody.HamiltonianMixedPartials
import LeanPool.PoincareThreeBody.KeplerHamiltonian

/-!
# The first homological equation on a resonant Kepler orbit

This file restricts the homological equation forced by the exact challenge hypotheses to the true
periodic Kepler flow.  Its first term becomes a time derivative, so its integral over one resonant
period vanishes.
-/

namespace LeanPool.PoincareThreeBody

open MeasureTheory Set
open scoped Interval

/-- The first mass coefficient of a candidate integral, restricted to a resonant Kepler orbit. -/
noncomputable def resonantCandidateCorrection
    (F : ℝ → PhaseSpace → ℝ) (p q : ℕ) (eccentricity orientation time : ℝ) : ℝ :=
  parameterCoefficient (Function.uncurry F)
    (orientedResonantKeplerPhasePoint p q eccentricity orientation time)

/-- The remaining forcing term in the first homological equation, restricted to the same orbit. -/
noncomputable def resonantCandidateForcing
    (F : ℝ → PhaseSpace → ℝ) (p q : ℕ) (eccentricity orientation time : ℝ) : ℝ :=
  poissonBracket (F 0) firstMassPerturbation
    (orientedResonantKeplerPhasePoint p q eccentricity orientation time)

/-- A Poisson bracket of two `C¹` observables varies continuously along a continuous phase-space
curve. -/
theorem continuousAt_poissonBracket_comp
    {f g : PhaseSpace → ℝ} {orbit : ℝ → PhaseSpace} {time : ℝ}
    (hf : ContDiffAt ℝ 1 f (orbit time)) (hg : ContDiffAt ℝ 1 g (orbit time))
    (horbit : ContinuousAt orbit time) :
    ContinuousAt (fun argument ↦ poissonBracket f g (orbit argument)) time := by
  have hdf : ContinuousAt (fun argument ↦ fderiv ℝ f (orbit argument)) time :=
    (hf.continuousAt_fderiv (by norm_num)).comp horbit
  have hdg : ContinuousAt (fun argument ↦ fderiv ℝ g (orbit argument)) time :=
    (hg.continuousAt_fderiv (by norm_num)).comp horbit
  have hdf0 := continuousAt_clm_apply.mp hdf (coordinateVector 0)
  have hdf1 := continuousAt_clm_apply.mp hdf (coordinateVector 1)
  have hdf2 := continuousAt_clm_apply.mp hdf (coordinateVector 2)
  have hdf3 := continuousAt_clm_apply.mp hdf (coordinateVector 3)
  have hdg0 := continuousAt_clm_apply.mp hdg (coordinateVector 0)
  have hdg1 := continuousAt_clm_apply.mp hdg (coordinateVector 1)
  have hdg2 := continuousAt_clm_apply.mp hdg (coordinateVector 2)
  have hdg3 := continuousAt_clm_apply.mp hdg (coordinateVector 3)
  unfold poissonBracket
  convert ((hdf0.mul hdg2).sub (hdf2.mul hdg0)).add
      ((hdf1.mul hdg3).sub (hdf3.mul hdg1)) using 1
  funext argument
  rfl

/-- The exact challenge hypotheses imply the explicit first homological equation at every point
of an interior resonant Kepler ellipse. -/
theorem IsFirstIntegralFamily.firstHomologicalEquation_on_resonantKeplerOrbit
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    poissonBracket (parameterCoefficient (Function.uncurry F)) (hamiltonian 0)
        (orientedResonantKeplerPhasePoint p q eccentricity orientation time) +
      resonantCandidateForcing F p q eccentricity orientation time = 0 := by
  exact IsFirstIntegralFamily.firstHomologicalEquation_mass_zero hδ hanalytic hfirstIntegral
    (orientedResonantKeplerPhasePoint_collisionFree_mass_zero hp hq heccentricity
      heccentricityOne hapoapsis)

/-- The correction term in the resonant homological equation has the expected Poisson bracket as
its time derivative. -/
theorem IsJointlyAnalytic.hasDerivAt_resonantCandidateCorrection
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation time : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    HasDerivAt (resonantCandidateCorrection F p q eccentricity orientation)
      (poissonBracket (parameterCoefficient (Function.uncurry F)) (hamiltonian 0)
        (orientedResonantKeplerPhasePoint p q eccentricity orientation time)) time := by
  let state := orientedResonantKeplerPhasePoint p q eccentricity orientation time
  have hcollision : (0, state) ∈ collisionFree :=
    orientedResonantKeplerPhasePoint_collisionFree_mass_zero hp hq heccentricity
      heccentricityOne hapoapsis
  have hdomain : (0, state) ∈ parameterDomain δ := ⟨by simpa using hδ, hcollision⟩
  have hsmooth : ContDiffAt ℝ 2 (Function.uncurry F) (0, state) :=
    (hanalytic (0, state) hdomain).contDiffAt
  have hcoefficient : DifferentiableAt ℝ (parameterCoefficient (Function.uncurry F)) state :=
    differentiableAt_parameterCoefficient hsmooth
  exact DifferentiableAt.hasDerivAt_comp_orientedResonantKeplerPhasePoint hp hq
    heccentricity heccentricityOne hcoefficient

/-- The correction is periodic because it is a scalar observable evaluated on the periodic
Kepler phase trajectory. -/
lemma resonantCandidateCorrection_periodic
    (F : ℝ → PhaseSpace → ℝ) {p q : ℕ} (hp : 0 < p)
    {eccentricity orientation : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity < 1) :
    resonantCandidateCorrection F p q eccentricity orientation (resonantOrbitPeriod p) =
      resonantCandidateCorrection F p q eccentricity orientation 0 := by
  unfold resonantCandidateCorrection
  rw [show resonantOrbitPeriod p = 0 + resonantOrbitPeriod p by ring,
    orientedResonantKeplerPhasePoint_add_period hp heccentricity heccentricityOne]

/-- The derivative term in the restricted homological equation is continuous in time. -/
theorem continuous_resonantCandidateCorrectionDerivative
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    Continuous (fun time ↦
      poissonBracket (parameterCoefficient (Function.uncurry F)) (hamiltonian 0)
        (orientedResonantKeplerPhasePoint p q eccentricity orientation time)) := by
  rw [continuous_iff_continuousAt]
  intro time
  let state := orientedResonantKeplerPhasePoint p q eccentricity orientation time
  have hcollision : (0, state) ∈ collisionFree :=
    orientedResonantKeplerPhasePoint_collisionFree_mass_zero hp hq heccentricity
      heccentricityOne hapoapsis
  have hdomain : (0, state) ∈ parameterDomain δ := ⟨by simpa using hδ, hcollision⟩
  have hcoefficient : ContDiffAt ℝ 1 (parameterCoefficient (Function.uncurry F)) state :=
    contDiffAt_parameterCoefficient ((hanalytic (0, state) hdomain).contDiffAt)
  have hhamiltonian : ContDiffAt ℝ 1 (hamiltonian 0) state := by
    have hjoint := hamiltonian_analyticAt hcollision
    have hembedding : AnalyticAt ℝ (fun phase : PhaseSpace ↦ ((0 : ℝ), phase)) state :=
      analyticAt_const.prod analyticAt_id
    exact (hjoint.comp hembedding).contDiffAt
  have horbit : ContinuousAt
      (orientedResonantKeplerPhasePoint p q eccentricity orientation) time :=
    (analyticAt_orientedResonantKeplerPhasePoint p q heccentricity
      heccentricityOne).continuousAt
  exact continuousAt_poissonBracket_comp hcoefficient hhamiltonian horbit

/-- The forcing term in the restricted homological equation is continuous in time. -/
theorem continuous_resonantCandidateForcing
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    Continuous (resonantCandidateForcing F p q eccentricity orientation) := by
  rw [continuous_iff_continuousAt]
  intro time
  let state := orientedResonantKeplerPhasePoint p q eccentricity orientation time
  have hcollision : (0, state) ∈ collisionFree :=
    orientedResonantKeplerPhasePoint_collisionFree_mass_zero hp hq heccentricity
      heccentricityOne hapoapsis
  have hdomain : (0, state) ∈ parameterDomain δ := ⟨by simpa using hδ, hcollision⟩
  have hcandidate : ContDiffAt ℝ 1 (F 0) state := by
    have hjoint := hanalytic (0, state) hdomain
    have hembedding : AnalyticAt ℝ (fun phase : PhaseSpace ↦ ((0 : ℝ), phase)) state :=
      analyticAt_const.prod analyticAt_id
    exact (hjoint.comp hembedding).contDiffAt
  have hperturbation : ContDiffAt ℝ 1 firstMassPerturbation state := by
    have hcoefficient : ContDiffAt ℝ 1
        (parameterCoefficient (Function.uncurry hamiltonian)) state :=
      contDiffAt_parameterCoefficient (hamiltonian_analyticAt hcollision).contDiffAt
    exact hcoefficient.congr_of_eventuallyEq
      (parameterCoefficient_hamiltonian_eventuallyEq hcollision).symm
  have horbit : ContinuousAt
      (orientedResonantKeplerPhasePoint p q eccentricity orientation) time :=
    (analyticAt_orientedResonantKeplerPhasePoint p q heccentricity
      heccentricityOne).continuousAt
  exact continuousAt_poissonBracket_comp hcandidate hperturbation horbit

/-- Averaging the exact first homological equation along a resonant Kepler orbit forces the
candidate's perturbative forcing to have zero period integral.  The two interval-integrability
hypotheses are isolated here so that later analytic estimates can discharge them independently. -/
theorem IsFirstIntegralFamily.integral_resonantCandidateForcing_eq_zero_of_intervalIntegrable
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1)
    (hcorrectionIntegrable : IntervalIntegrable
      (fun time ↦ poissonBracket (parameterCoefficient (Function.uncurry F)) (hamiltonian 0)
        (orientedResonantKeplerPhasePoint p q eccentricity orientation time))
      volume 0 (resonantOrbitPeriod p))
    (hforcingIntegrable : IntervalIntegrable
      (resonantCandidateForcing F p q eccentricity orientation)
      volume 0 (resonantOrbitPeriod p)) :
    ∫ time in 0..resonantOrbitPeriod p,
      resonantCandidateForcing F p q eccentricity orientation time = 0 := by
  apply intervalIntegral_forcing_eq_zero_of_homologicalEquation
    (correction := resonantCandidateCorrection F p q eccentricity orientation)
    (correctionDerivative := fun time ↦
      poissonBracket (parameterCoefficient (Function.uncurry F)) (hamiltonian 0)
        (orientedResonantKeplerPhasePoint p q eccentricity orientation time))
    (forcing := resonantCandidateForcing F p q eccentricity orientation)
    (period := resonantOrbitPeriod p)
  · intro time _
    exact IsJointlyAnalytic.hasDerivAt_resonantCandidateCorrection hδ hanalytic hp hq
      heccentricity heccentricityOne hapoapsis
  · exact hcorrectionIntegrable
  · exact hforcingIntegrable
  · exact resonantCandidateCorrection_periodic F hp heccentricity heccentricityOne
  · intro time _
    exact IsFirstIntegralFamily.firstHomologicalEquation_on_resonantKeplerOrbit hδ hanalytic
      hfirstIntegral hp hq heccentricity heccentricityOne hapoapsis

/-- Every candidate satisfying the exact analytic first-integral hypotheses has zero averaged
first-order forcing on every interior resonant Kepler ellipse. -/
theorem IsFirstIntegralFamily.integral_resonantCandidateForcing_eq_zero
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) (hfirstIntegral : IsFirstIntegralFamily δ F)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {eccentricity orientation : ℝ}
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1) :
    ∫ time in 0..resonantOrbitPeriod p,
      resonantCandidateForcing F p q eccentricity orientation time = 0 := by
  apply IsFirstIntegralFamily.integral_resonantCandidateForcing_eq_zero_of_intervalIntegrable
    hδ hanalytic hfirstIntegral hp hq heccentricity heccentricityOne hapoapsis
  · exact (continuous_resonantCandidateCorrectionDerivative hδ hanalytic hp hq
      heccentricity heccentricityOne hapoapsis).intervalIntegrable _ _
  · exact (continuous_resonantCandidateForcing hδ hanalytic hp hq heccentricity
      heccentricityOne hapoapsis).intervalIntegrable _ _

end LeanPool.PoincareThreeBody
