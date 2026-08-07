/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.EnergyLeafObstruction
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Analytic coefficient normalization in the mass parameter

Poincaré's induction subtracts a function of the Hamiltonian from a candidate integral and then
divides by the mass parameter.  The differentiable slope `dslope` supplies the removable value at
mass zero.  This file establishes the analytic one-variable division theorem and applies it to
each phase-space slice of the normalized residual.
-/

namespace LeanPool.PoincareThreeBody


/-- The differentiable slope of an analytic one-variable function is analytic at its base point.
This is the analytic form of division by a linear factor. -/
theorem AnalyticAt.analyticAt_dslope
    {f : ℝ → ℝ} {base : ℝ} (hf : AnalyticAt ℝ f base) :
    AnalyticAt ℝ (dslope f base) base := by
  rcases hf with ⟨series, hseries⟩
  exact hseries.has_fpower_series_dslope_fslope.analyticAt

/-- If an analytic function vanishes at the base point, its differentiable slope reconstructs it
after multiplication by the corresponding linear factor. -/
theorem sub_mul_dslope_eq_of_eq_zero
    {f : ℝ → ℝ} {base : ℝ} (hzero : f base = 0) (argument : ℝ) :
    (argument - base) * dslope f base argument = f argument := by
  simpa only [smul_eq_mul] using sub_smul_dslope_of_zero hzero argument

/-- The residual obtained after subtracting a one-variable function of the Hamiltonian. -/
noncomputable def normalizationResidual
    (F : ℝ → PhaseSpace → ℝ) (energyFunction : ℝ → ℝ)
    (mass : ℝ) (state : PhaseSpace) : ℝ :=
  F mass state - energyFunction (hamiltonian mass state)

/-- The mass-normalized residual, with the removable value at zero supplied by `dslope`. -/
noncomputable def massNormalizedCandidate
    (F : ℝ → PhaseSpace → ℝ) (energyFunction : ℝ → ℝ)
    (mass : ℝ) (state : PhaseSpace) : ℝ :=
  dslope (fun candidateMass ↦
    normalizationResidual F energyFunction candidateMass state) 0 mass

/-- Domain-correct normalization.  Away from zero it is the literal residual quotient, so its
value does not depend on the unconstrained values of `F 0` at the two states excluded from the
mass-zero domain.  At zero it uses the removable `dslope` value. -/
noncomputable def domainMassNormalizedCandidate
    (F : ℝ → PhaseSpace → ℝ) (energyFunction : ℝ → ℝ)
    (mass : ℝ) (state : PhaseSpace) : ℝ :=
  if mass = 0 then massNormalizedCandidate F energyFunction 0 state
  else normalizationResidual F energyFunction mass state / mass

@[simp] theorem domainMassNormalizedCandidate_zero
    (F : ℝ → PhaseSpace → ℝ) (energyFunction : ℝ → ℝ) (state : PhaseSpace) :
    domainMassNormalizedCandidate F energyFunction 0 state =
      massNormalizedCandidate F energyFunction 0 state := by
  simp [domainMassNormalizedCandidate]

theorem domainMassNormalizedCandidate_eq_div
    {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    {mass : ℝ} (hmass : mass ≠ 0) (state : PhaseSpace) :
    domainMassNormalizedCandidate F energyFunction mass state =
      normalizationResidual F energyFunction mass state / mass := by
  simp [domainMassNormalizedCandidate, hmass]

/-- Exact reconstruction of a residual whose zeroth mass coefficient has been cancelled. -/
theorem mass_mul_massNormalizedCandidate
    {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ} {state : PhaseSpace}
    (hzero : F 0 state = energyFunction (hamiltonian 0 state)) (mass : ℝ) :
    mass * massNormalizedCandidate F energyFunction mass state =
      normalizationResidual F energyFunction mass state := by
  change mass * dslope
    (fun candidateMass ↦ normalizationResidual F energyFunction candidateMass state)
      0 mass = normalizationResidual F energyFunction mass state
  simpa using sub_mul_dslope_eq_of_eq_zero
    (f := fun candidateMass ↦
      normalizationResidual F energyFunction candidateMass state)
    (base := 0) (by simp [normalizationResidual, hzero]) mass

/-- At nonzero mass the normalized candidate is the ordinary quotient of the residual by mass. -/
theorem massNormalizedCandidate_eq_div
    {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    {mass : ℝ} (hmass : mass ≠ 0) {state : PhaseSpace}
    (hzero : F 0 state = energyFunction (hamiltonian 0 state)) :
    massNormalizedCandidate F energyFunction mass state =
      normalizationResidual F energyFunction mass state / mass := by
  rw [massNormalizedCandidate, dslope_of_ne _ hmass]
  simp [slope, normalizationResidual, hzero, div_eq_mul_inv, mul_comm]

/-- On a phase point where the zeroth coefficient cancels, the domain-correct and `dslope`
normalizations coincide. -/
theorem domainMassNormalizedCandidate_eq_massNormalizedCandidate
    {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    {mass : ℝ} {state : PhaseSpace}
    (hzero : F 0 state = energyFunction (hamiltonian 0 state)) :
    domainMassNormalizedCandidate F energyFunction mass state =
      massNormalizedCandidate F energyFunction mass state := by
  by_cases hmass : mass = 0
  · subst hmass
    simp
  · rw [domainMassNormalizedCandidate_eq_div hmass,
      massNormalizedCandidate_eq_div hmass hzero]

/-- Away from the removable hypersurface `mass = 0`, the domain-correct normalized candidate is
jointly analytic by ordinary analytic division.  Thus the genuinely parameterized content of the
Hadamard division step is confined to points whose mass coordinate is zero. -/
theorem analyticAt_uncurry_domainMassNormalizedCandidate_of_mass_ne
    {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    {z : ℝ × PhaseSpace}
    (hmass : z.1 ≠ 0)
    (hcandidate : AnalyticAt ℝ (Function.uncurry F) z)
    (hhamiltonian : AnalyticAt ℝ (Function.uncurry hamiltonian) z)
    (henergyFunction : AnalyticAt ℝ energyFunction (hamiltonian z.1 z.2)) :
    AnalyticAt ℝ
      (Function.uncurry (domainMassNormalizedCandidate F energyFunction)) z := by
  have hresidual : AnalyticAt ℝ
      (fun w : ℝ × PhaseSpace ↦
        normalizationResidual F energyFunction w.1 w.2) z := by
    exact hcandidate.sub (henergyFunction.comp
      (f := Function.uncurry hamiltonian) hhamiltonian)
  have hquotient : AnalyticAt ℝ
      (fun w : ℝ × PhaseSpace ↦
        normalizationResidual F energyFunction w.1 w.2 / w.1) z :=
    hresidual.div analyticAt_fst hmass
  have heventual : ∀ᶠ w in nhds z, w.1 ≠ 0 :=
    continuousAt_fst.eventually_ne hmass
  apply hquotient.congr
  filter_upwards [heventual] with w hw
  exact (domainMassNormalizedCandidate_eq_div hw w.2).symm

/-- To prove joint analyticity of the normalized family on the full parameter domain, it is
enough to prove the removable extension at the mass-zero slice.  All nonzero-mass points follow
from ordinary analytic division. -/
theorem isJointlyAnalytic_domainMassNormalizedCandidate_of_mass_zero
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    (hanalytic : IsJointlyAnalytic δ F)
    (henergyFunction : ∀ energy, AnalyticAt ℝ energyFunction energy)
    (hmassZero : ∀ state, (0, state) ∈ collisionFree →
      AnalyticAt ℝ
        (Function.uncurry (domainMassNormalizedCandidate F energyFunction)) (0, state)) :
    IsJointlyAnalytic δ (domainMassNormalizedCandidate F energyFunction) := by
  rintro z hz
  rcases z with ⟨mass, state⟩
  by_cases hmass : mass = 0
  · subst hmass
    exact hmassZero state hz.2
  · exact analyticAt_uncurry_domainMassNormalizedCandidate_of_mass_ne
      hmass (hanalytic (mass, state) hz) (hamiltonian_analyticAt hz.2)
      (henergyFunction (hamiltonian mass state))

/-- Exact reconstruction for the domain-correct normalization. -/
theorem mass_mul_domainMassNormalizedCandidate
    {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ} {state : PhaseSpace}
    (hzero : F 0 state = energyFunction (hamiltonian 0 state)) (mass : ℝ) :
    mass * domainMassNormalizedCandidate F energyFunction mass state =
      normalizationResidual F energyFunction mass state := by
  rw [domainMassNormalizedCandidate_eq_massNormalizedCandidate hzero]
  exact mass_mul_massNormalizedCandidate hzero mass

/-- Joint analyticity of the candidate and analyticity of the energy function make every fixed
phase slice of the residual analytic in mass. -/
theorem analyticAt_normalizationResidual_massSlice
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    (hanalytic : IsJointlyAnalytic δ F) {state : PhaseSpace}
    (hdomain : (0, state) ∈ parameterDomain δ)
    (henergyFunction : AnalyticAt ℝ energyFunction (hamiltonian 0 state)) :
    AnalyticAt ℝ
      (fun mass ↦ normalizationResidual F energyFunction mass state) 0 := by
  have hembedding : AnalyticAt ℝ (fun mass : ℝ ↦ (mass, state)) 0 :=
    analyticAt_id.prod analyticAt_const
  have hcandidate : AnalyticAt ℝ (fun mass ↦ F mass state) 0 :=
    (hanalytic (0, state) hdomain).comp
      (f := fun mass : ℝ ↦ (mass, state)) hembedding
  have hhamiltonian : AnalyticAt ℝ (fun mass ↦ hamiltonian mass state) 0 :=
    (hamiltonian_analyticAt hdomain.2).comp
      (f := fun mass : ℝ ↦ (mass, state)) hembedding
  unfold normalizationResidual
  exact hcandidate.sub (henergyFunction.comp
    (f := fun mass ↦ hamiltonian mass state) hhamiltonian)

/-- The removable mass quotient is analytic at zero on every fixed collision-free phase slice. -/
theorem analyticAt_massNormalizedCandidate_massSlice
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    (hanalytic : IsJointlyAnalytic δ F) {state : PhaseSpace}
    (hdomain : (0, state) ∈ parameterDomain δ)
    (henergyFunction : AnalyticAt ℝ energyFunction (hamiltonian 0 state)) :
    AnalyticAt ℝ (fun mass ↦
      massNormalizedCandidate F energyFunction mass state) 0 := by
  exact AnalyticAt.analyticAt_dslope
    (analyticAt_normalizationResidual_massSlice
      hanalytic hdomain henergyFunction)

/-- At mass zero the normalized candidate is exactly the first parameter coefficient of the
joint residual. -/
theorem massNormalizedCandidate_zero_eq_parameterCoefficient
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    (hanalytic : IsJointlyAnalytic δ F) {state : PhaseSpace}
    (hdomain : (0, state) ∈ parameterDomain δ)
    (henergyFunction : AnalyticAt ℝ energyFunction (hamiltonian 0 state)) :
    massNormalizedCandidate F energyFunction 0 state =
      parameterCoefficient
        (Function.uncurry (normalizationResidual F energyFunction)) state := by
  rw [massNormalizedCandidate, dslope_same]
  have hcandidate : AnalyticAt ℝ (Function.uncurry F) (0, state) :=
    hanalytic (0, state) hdomain
  have hhamiltonian : AnalyticAt ℝ
      (Function.uncurry hamiltonian) (0, state) :=
    hamiltonian_analyticAt hdomain.2
  have hcomposition : AnalyticAt ℝ
      (fun z : ℝ × PhaseSpace ↦ energyFunction (hamiltonian z.1 z.2))
      (0, state) :=
    henergyFunction.comp (f := Function.uncurry hamiltonian) hhamiltonian
  have hjoint : DifferentiableAt ℝ
      (Function.uncurry (normalizationResidual F energyFunction)) (0, state) := by
    exact (hcandidate.sub hcomposition).differentiableAt
  simpa [Function.uncurry] using
    (deriv_curry_left
      (G := Function.uncurry (normalizationResidual F energyFunction)) hjoint)

/-- Explicit coefficient bookkeeping for one normalization step: the new zeroth coefficient is
the old first mass coefficient minus the energy derivative times the Hamiltonian perturbation. -/
theorem parameterCoefficient_normalizationResidual
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    (hanalytic : IsJointlyAnalytic δ F) {state : PhaseSpace}
    (hdomain : (0, state) ∈ parameterDomain δ)
    (henergyFunction : AnalyticAt ℝ energyFunction (hamiltonian 0 state)) :
    parameterCoefficient
        (Function.uncurry (normalizationResidual F energyFunction)) state =
      parameterCoefficient (Function.uncurry F) state -
        deriv energyFunction (hamiltonian 0 state) * firstMassPerturbation state := by
  have hcandidateJoint : AnalyticAt ℝ (Function.uncurry F) (0, state) :=
    hanalytic (0, state) hdomain
  have hhamiltonianJoint : AnalyticAt ℝ
      (Function.uncurry hamiltonian) (0, state) :=
    hamiltonian_analyticAt hdomain.2
  have hcompositionJoint : AnalyticAt ℝ
      (fun z : ℝ × PhaseSpace ↦ energyFunction (hamiltonian z.1 z.2))
      (0, state) :=
    henergyFunction.comp (f := Function.uncurry hamiltonian) hhamiltonianJoint
  have hresidualJoint : DifferentiableAt ℝ
      (Function.uncurry (normalizationResidual F energyFunction)) (0, state) :=
    (hcandidateJoint.sub hcompositionJoint).differentiableAt
  have hcandidateSlice : DifferentiableAt ℝ (fun mass ↦ F mass state) 0 :=
    (analyticAt_mass_zero_of_jointlyAnalytic (by
      exact lt_of_le_of_lt (abs_nonneg (0 : ℝ)) hdomain.1) hanalytic hdomain.2).differentiableAt
  have hhamiltonianSlice : DifferentiableAt ℝ
      (fun mass ↦ hamiltonian mass state) 0 :=
    (hamiltonian_analyticAt_mass_zero hdomain.2).differentiableAt
  have hcompositionSlice : HasDerivAt
      (fun mass ↦ energyFunction (hamiltonian mass state))
      (deriv energyFunction (hamiltonian 0 state) *
        deriv (fun mass ↦ hamiltonian mass state) 0) 0 := by
    exact henergyFunction.differentiableAt.hasDerivAt.comp 0
      hhamiltonianSlice.hasDerivAt
  have hresidualSlice :
      deriv (fun mass ↦ normalizationResidual F energyFunction mass state) 0 =
        deriv (fun mass ↦ F mass state) 0 -
          deriv energyFunction (hamiltonian 0 state) *
            deriv (fun mass ↦ hamiltonian mass state) 0 := by
    exact (hcandidateSlice.hasDerivAt.sub hcompositionSlice).deriv
  have hcandidateCoefficient :
      deriv (fun mass ↦ F mass state) 0 =
        parameterCoefficient (Function.uncurry F) state := by
    simpa [Function.uncurry] using
      (deriv_curry_left hcandidateJoint.differentiableAt)
  rw [← deriv_curry_left hresidualJoint]
  change deriv (fun mass ↦ normalizationResidual F energyFunction mass state) 0 = _
  rw [hresidualSlice, hcandidateCoefficient,
    deriv_hamiltonian_mass_zero hdomain.2]

/-- Explicit value of the removable quotient at mass zero. -/
theorem massNormalizedCandidate_zero_eq_nextCoefficient
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    (hanalytic : IsJointlyAnalytic δ F) {state : PhaseSpace}
    (hdomain : (0, state) ∈ parameterDomain δ)
    (henergyFunction : AnalyticAt ℝ energyFunction (hamiltonian 0 state)) :
    massNormalizedCandidate F energyFunction 0 state =
      parameterCoefficient (Function.uncurry F) state -
        deriv energyFunction (hamiltonian 0 state) * firstMassPerturbation state := by
  rw [massNormalizedCandidate_zero_eq_parameterCoefficient
      hanalytic hdomain henergyFunction,
    parameterCoefficient_normalizationResidual
      hanalytic hdomain henergyFunction]

end LeanPool.PoincareThreeBody
