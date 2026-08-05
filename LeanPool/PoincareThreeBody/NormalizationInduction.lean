/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.AnalyticMinors

/-!
# Iterated Poincaré normalization

This file packages the algebra common to every order of Poincaré's coefficient induction.  At
each step one subtracts a function of the Hamiltonian and divides by the mass.  Exact finite-order
expansions then express the original candidate as a function of the Hamiltonian modulo an
arbitrarily high power of the mass parameter.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

/-- The sequence obtained by repeatedly subtracting a chosen energy function and dividing by the
mass parameter. -/
noncomputable def iteratedMassNormalization
    (F : ℝ → PhaseSpace → ℝ) (energyFunction : ℕ → ℝ → ℝ) :
    ℕ → ℝ → PhaseSpace → ℝ
  | 0 => F
  | n + 1 => massNormalizedCandidate
      (iteratedMassNormalization F energyFunction n) (energyFunction n)

@[simp] theorem iteratedMassNormalization_zero
    (F : ℝ → PhaseSpace → ℝ) (energyFunction : ℕ → ℝ → ℝ) :
    iteratedMassNormalization F energyFunction 0 = F := rfl

@[simp] theorem iteratedMassNormalization_succ
    (F : ℝ → PhaseSpace → ℝ) (energyFunction : ℕ → ℝ → ℝ) (n : ℕ) :
    iteratedMassNormalization F energyFunction (n + 1) =
      massNormalizedCandidate (iteratedMassNormalization F energyFunction n)
        (energyFunction n) := rfl

/-- The finite sum of energy-dependent terms accumulated through order `n - 1`. -/
noncomputable def accumulatedEnergy
    (energyFunction : ℕ → ℝ → ℝ) (n : ℕ) (mass energy : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, mass ^ k * energyFunction k energy

@[simp] theorem accumulatedEnergy_zero
    (energyFunction : ℕ → ℝ → ℝ) (mass energy : ℝ) :
    accumulatedEnergy energyFunction 0 mass energy = 0 := by
  simp [accumulatedEnergy]

theorem accumulatedEnergy_succ
    (energyFunction : ℕ → ℝ → ℝ) (n : ℕ) (mass energy : ℝ) :
    accumulatedEnergy energyFunction (n + 1) mass energy =
      accumulatedEnergy energyFunction n mass energy +
        mass ^ n * energyFunction n energy := by
  simp [accumulatedEnergy, Finset.sum_range_succ]

/-- If every normalization step cancels its zeroth coefficient, the original candidate has an
exact expansion through every finite order, with the next normalized candidate as remainder. -/
theorem iteratedMassNormalization_exact_expansion
    {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℕ → ℝ → ℝ}
    (hcancel : ∀ n state,
      iteratedMassNormalization F energyFunction n 0 state =
        energyFunction n (hamiltonian 0 state))
    (n : ℕ) (mass : ℝ) (state : PhaseSpace) :
    F mass state =
      accumulatedEnergy energyFunction n mass (hamiltonian mass state) +
        mass ^ n * iteratedMassNormalization F energyFunction n mass state := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ih, accumulatedEnergy_succ]
      have hreconstruct := mass_mul_massNormalizedCandidate
        (F := iteratedMassNormalization F energyFunction n)
        (energyFunction := energyFunction n) (state := state)
        (hcancel n state) mass
      have hstep :
          iteratedMassNormalization F energyFunction n mass state =
            energyFunction n (hamiltonian mass state) +
              mass * massNormalizedCandidate
                (iteratedMassNormalization F energyFunction n)
                (energyFunction n) mass state := by
        unfold normalizationResidual at hreconstruct
        linarith
      rw [iteratedMassNormalization_succ]
      rw [hstep]
      ring

/-- The expansion remainder is divisible by `mass ^ n` after subtracting the accumulated function
of the Hamiltonian. -/
theorem iteratedMassNormalization_remainder
    {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℕ → ℝ → ℝ}
    (hcancel : ∀ n state,
      iteratedMassNormalization F energyFunction n 0 state =
        energyFunction n (hamiltonian 0 state))
    (n : ℕ) (mass : ℝ) (state : PhaseSpace) :
    F mass state -
        accumulatedEnergy energyFunction n mass (hamiltonian mass state) =
      mass ^ n * iteratedMassNormalization F energyFunction n mass state := by
  rw [iteratedMassNormalization_exact_expansion hcancel n mass state]
  ring

/-- Differentiability of each energy coefficient makes their finite accumulated sum
differentiable in energy. -/
theorem differentiableAt_accumulatedEnergy
    {energyFunction : ℕ → ℝ → ℝ} {n : ℕ} {mass energy : ℝ}
    (henergy : ∀ k < n, DifferentiableAt ℝ (energyFunction k) energy) :
    DifferentiableAt ℝ (accumulatedEnergy energyFunction n mass) energy := by
  unfold accumulatedEnergy
  fun_prop (disch := aesop)

/-- At every finite normalization order, each differential minor of the original candidate is a
power of the mass times the corresponding minor of the normalized remainder. -/
theorem massDifferentialMinor_eq_pow_mul_iteratedNormalization
    {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℕ → ℝ → ℝ}
    (hcancel : ∀ n state,
      iteratedMassNormalization F energyFunction n 0 state =
        energyFunction n (hamiltonian 0 state))
    {n : ℕ} {mass : ℝ} {state : PhaseSpace}
    (hhamiltonian : DifferentiableAt ℝ (hamiltonian mass) state)
    (hnormalized : DifferentiableAt ℝ
      (iteratedMassNormalization F energyFunction n mass) state)
    (henergy : ∀ k < n,
      DifferentiableAt ℝ (energyFunction k) (hamiltonian mass state))
    (i j : Fin 4) :
    massDifferentialMinor F i j mass state =
      mass ^ n * phaseCovectorMinor (fderiv ℝ (hamiltonian mass) state)
        (fderiv ℝ (iteratedMassNormalization F energyFunction n mass) state) i j := by
  let accumulated := accumulatedEnergy energyFunction n mass
  let normalized := iteratedMassNormalization F energyFunction n mass
  have haccumulated : DifferentiableAt ℝ accumulated (hamiltonian mass state) :=
    differentiableAt_accumulatedEnergy henergy
  have hcomposition : DifferentiableAt ℝ
      (fun candidate ↦ accumulated (hamiltonian mass candidate)) state :=
    haccumulated.comp state hhamiltonian
  have hscaled : DifferentiableAt ℝ
      (fun candidate ↦ mass ^ n * normalized candidate) state :=
    hnormalized.const_mul _
  have hfunction : F mass = fun candidate ↦
      accumulated (hamiltonian mass candidate) + mass ^ n * normalized candidate := by
    funext candidate
    exact iteratedMassNormalization_exact_expansion
      hcancel n mass candidate
  have hderivative : fderiv ℝ (F mass) state =
      fderiv ℝ (fun candidate ↦ accumulated (hamiltonian mass candidate)) state +
        mass ^ n • fderiv ℝ normalized state := by
    rw [hfunction]
    change fderiv ℝ
      ((fun candidate ↦ accumulated (hamiltonian mass candidate)) +
        fun candidate ↦ mass ^ n * normalized candidate) state = _
    rw [fderiv_add hcomposition hscaled, fderiv_const_mul hnormalized]
  have hfunctionMinor := phaseCovectorMinor_comp_self_eq_zero
    hhamiltonian haccumulated i j
  unfold massDifferentialMinor
  rw [hderivative]
  unfold phaseCovectorMinor at hfunctionMinor ⊢
  simp only [add_apply, smul_apply, smul_eq_mul]
  dsimp only [normalized]
  linear_combination hfunctionMinor

/-- A germ divisible by a strictly higher power than the requested derivative order has that
derivative equal to zero. -/
theorem iteratedDeriv_eq_zero_of_eventually_eq_pow_mul
    {f g : ℝ → ℝ} {order power : ℕ} (horder : order < power)
    (hg : ContDiffAt ℝ order g 0)
    (heq : f =ᶠ[nhds 0] fun mass ↦ mass ^ power * g mass) :
    iteratedDeriv order f 0 = 0 := by
  rw [heq.iteratedDeriv_eq order]
  change iteratedDeriv order ((fun mass : ℝ ↦ mass ^ power) * g) 0 = 0
  rw [iteratedDeriv_mul (by fun_prop) hg]
  simp only [iteratedDeriv_fun_pow_zero]
  apply Finset.sum_eq_zero
  intro derivativeOrder hderivativeOrder
  have hne : derivativeOrder ≠ power := by
    have hle : derivativeOrder ≤ order := by
      simpa using hderivativeOrder
    omega
  simp [hne]

/-- If every normalized remainder stays jointly analytic and every zeroth coefficient is removed
as a function of the Hamiltonian, every mass derivative of every original differential minor
vanishes at zero.  This is the formal infinite-order conclusion of Poincaré's induction. -/
theorem massDifferentialMinor_flat_of_iterated_normalizations
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    {energyFunction : ℕ → ℝ → ℝ}
    (hδ : 0 < δ)
    (hnormalized : ∀ n,
      IsJointlyAnalytic δ (iteratedMassNormalization F energyFunction n))
    (henergy : ∀ n energy, AnalyticAt ℝ (energyFunction n) energy)
    (hcancel : ∀ n state,
      iteratedMassNormalization F energyFunction n 0 state =
        energyFunction n (hamiltonian 0 state))
    {state : PhaseSpace} (hcollision : (0, state) ∈ collisionFree)
    (i j : Fin 4) (order : ℕ) :
    iteratedDeriv order (fun mass ↦ massDifferentialMinor F i j mass state) 0 = 0 := by
  let power := order + 1
  let normalized := iteratedMassNormalization F energyFunction power
  let remainder : ℝ → ℝ := fun mass ↦
    massDifferentialMinor normalized i j mass state
  have hdomainZero : (0, state) ∈ parameterDomain δ :=
    ⟨by simpa using hδ, hcollision⟩
  have hremainderAnalytic : AnalyticAt ℝ remainder 0 := by
    exact IsJointlyAnalytic.analyticAt_massDifferentialMinor_massSlice
      (hnormalized power) hdomainZero i j
  have hremainderSmooth : ContDiffAt ℝ order remainder 0 :=
    hremainderAnalytic.contDiffAt
  have hsmall : ∀ᶠ mass in nhds (0 : ℝ), |mass| < δ := by
    have habs : ContinuousAt (fun mass : ℝ ↦ |mass|) 0 := by fun_prop
    exact habs.eventually (Iio_mem_nhds (by simpa using hδ))
  have hfirstCollision : ∀ᶠ mass in nhds (0 : ℝ),
      firstPrimaryDistanceSq mass state ≠ 0 := by
    have hcontinuous : Continuous (fun mass ↦ firstPrimaryDistanceSq mass state) := by
      unfold firstPrimaryDistanceSq
      fun_prop
    exact hcontinuous.continuousAt.eventually_ne hcollision.1
  have hsecondCollision : ∀ᶠ mass in nhds (0 : ℝ),
      secondPrimaryDistanceSq mass state ≠ 0 := by
    have hcontinuous : Continuous (fun mass ↦ secondPrimaryDistanceSq mass state) := by
      unfold secondPrimaryDistanceSq
      fun_prop
    exact hcontinuous.continuousAt.eventually_ne hcollision.2
  have hdomain : ∀ᶠ mass in nhds (0 : ℝ),
      (mass, state) ∈ parameterDomain δ := by
    filter_upwards [hsmall, hfirstCollision, hsecondCollision]
      with mass hmass hfirst hsecond
    exact ⟨hmass, hfirst, hsecond⟩
  have hfactor :
      (fun mass ↦ massDifferentialMinor F i j mass state) =ᶠ[nhds 0]
        fun mass ↦ mass ^ power * remainder mass := by
    filter_upwards [hdomain] with mass hmass
    have hhamiltonian : DifferentiableAt ℝ (hamiltonian mass) state := by
      have hembedding : AnalyticAt ℝ
          (fun candidate : PhaseSpace ↦ (mass, candidate)) state :=
        analyticAt_const.prod analyticAt_id
      exact ((hamiltonian_analyticAt hmass.2).comp
        (f := fun candidate : PhaseSpace ↦ (mass, candidate))
        hembedding).differentiableAt
    have hnormalizedPhase : DifferentiableAt ℝ (normalized mass) state := by
      have hembedding : AnalyticAt ℝ
          (fun candidate : PhaseSpace ↦ (mass, candidate)) state :=
        analyticAt_const.prod analyticAt_id
      exact (((hnormalized power) (mass, state) hmass).comp
        (f := fun candidate : PhaseSpace ↦ (mass, candidate))
        hembedding).differentiableAt
    exact massDifferentialMinor_eq_pow_mul_iteratedNormalization
      hcancel hhamiltonian hnormalizedPhase
      (fun k _ ↦ (henergy k (hamiltonian mass state)).differentiableAt) i j
  exact iteratedDeriv_eq_zero_of_eventually_eq_pow_mul
    (by simp [power]) hremainderSmooth hfactor

/-- The infinite normalization conclusion rules out independence at every point off the horizontal
axis.  For such a phase point, its whole mass interval avoids both collision cylinders and hence
lies in one connected mass fiber. -/
theorem not_linearIndependent_of_iterated_normalizations_of_vertical_ne_zero
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    {energyFunction : ℕ → ℝ → ℝ}
    (hδ : 0 < δ)
    (hnormalized : ∀ n,
      IsJointlyAnalytic δ (iteratedMassNormalization F energyFunction n))
    (henergy : ∀ n energy, AnalyticAt ℝ (energyFunction n) energy)
    (hcancel : ∀ n state,
      iteratedMassNormalization F energyFunction n 0 state =
        energyFunction n (hamiltonian 0 state))
    {mass : ℝ} (hmass : |mass| < δ) {state : PhaseSpace}
    (hvertical : state 1 ≠ 0) :
    ¬LinearIndependent ℝ
      ![fderiv ℝ (hamiltonian mass) state, fderiv ℝ (F mass) state] := by
  have hanalytic : IsJointlyAnalytic δ F := by
    simpa using hnormalized 0
  let massSet := Set.Ioo (-δ) δ
  have hpreconnected : IsPreconnected massSet :=
    (convex_Ioo (-δ) δ).isPreconnected
  have hzero : 0 ∈ massSet := by
    exact ⟨by linarith, hδ⟩
  have hdomain : ∀ candidateMass ∈ massSet,
      (candidateMass, state) ∈ parameterDomain δ := by
    intro candidateMass hcandidateMass
    have habs : |candidateMass| < δ := by
      rw [abs_lt]
      exact ⟨by linarith [hcandidateMass.1], hcandidateMass.2⟩
    have hfirst : firstPrimaryDistanceSq candidateMass state ≠ 0 := by
      intro hzeroDistance
      have hy : 0 < state 1 ^ 2 := sq_pos_of_ne_zero hvertical
      unfold firstPrimaryDistanceSq at hzeroDistance
      nlinarith [sq_nonneg (state 0 - 1 + candidateMass)]
    have hsecond : secondPrimaryDistanceSq candidateMass state ≠ 0 := by
      intro hzeroDistance
      have hy : 0 < state 1 ^ 2 := sq_pos_of_ne_zero hvertical
      unfold secondPrimaryDistanceSq at hzeroDistance
      nlinarith [sq_nonneg (state 0 + candidateMass)]
    exact ⟨habs, hfirst, hsecond⟩
  have hflat : ∀ i j : Fin 4, ∀ order : ℕ,
      iteratedDeriv order
        (fun candidateMass ↦
          massDifferentialMinor F i j candidateMass state) 0 = 0 := by
    intro i j order
    exact massDifferentialMinor_flat_of_iterated_normalizations
      hδ hnormalized henergy hcancel (hdomain 0 hzero).2 i j order
  apply IsJointlyAnalytic.not_independent_on_preconnected_massFiber_of_minors_flat
    hanalytic hpreconnected hzero hdomain hflat
  rw [show mass ∈ massSet ↔ |mass| < δ by
    simp only [massSet, Set.mem_Ioo, abs_lt]]
  exact hmass

/-- Perturb only the vertical position coordinate. -/
def verticalPerturbation (state : PhaseSpace) (offset : ℝ) : PhaseSpace :=
  state + offset • coordinateVector 1

@[simp] theorem verticalPerturbation_vertical (state : PhaseSpace) (offset : ℝ) :
    verticalPerturbation state offset 1 = state 1 + offset := by
  simp [verticalPerturbation]

/-- The full abstract endpoint of the infinite coefficient induction.  Independence at a point
on the horizontal axis persists under a small vertical perturbation, reducing it to the connected
mass-fiber result above. -/
theorem not_isIndependentSomewhere_of_iterated_normalizations
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    {energyFunction : ℕ → ℝ → ℝ}
    (hδ : 0 < δ)
    (hnormalized : ∀ n,
      IsJointlyAnalytic δ (iteratedMassNormalization F energyFunction n))
    (henergy : ∀ n energy, AnalyticAt ℝ (energyFunction n) energy)
    (hcancel : ∀ n state,
      iteratedMassNormalization F energyFunction n 0 state =
        energyFunction n (hamiltonian 0 state)) :
    ¬IsIndependentSomewhere δ F := by
  rintro ⟨z, hz, hindependent⟩
  have hanalytic : IsJointlyAnalytic δ F := by
    simpa using hnormalized 0
  by_cases hvertical : z.2 1 ≠ 0
  · exact (not_linearIndependent_of_iterated_normalizations_of_vertical_ne_zero
      hδ hnormalized henergy hcancel hz.1 hvertical) hindependent
  · push Not at hvertical
    have hphaseEmbedding : AnalyticAt ℝ
        (fun state : PhaseSpace ↦ (z.1, state)) z.2 :=
      analyticAt_const.prod analyticAt_id
    have hcandidateSlice : AnalyticAt ℝ (F z.1) z.2 :=
      (hanalytic z hz).comp
        (f := fun state : PhaseSpace ↦ (z.1, state)) hphaseEmbedding
    have hhamiltonianSlice : AnalyticAt ℝ (hamiltonian z.1) z.2 :=
      (hamiltonian_analyticAt hz.2).comp
        (f := fun state : PhaseSpace ↦ (z.1, state)) hphaseEmbedding
    have hcandidateDerivative : ContinuousAt
        (fun state ↦ fderiv ℝ (F z.1) state) z.2 := by
      have hsmooth : ContDiffAt ℝ 1 (F z.1) z.2 :=
        hcandidateSlice.contDiffAt
      exact hsmooth.continuousAt_fderiv (by norm_num)
    have hhamiltonianDerivative : ContinuousAt
        (fun state ↦ fderiv ℝ (hamiltonian z.1) state) z.2 := by
      have hsmooth : ContDiffAt ℝ 1 (hamiltonian z.1) z.2 :=
        hhamiltonianSlice.contDiffAt
      exact hsmooth.continuousAt_fderiv (by norm_num)
    let differentialPair : PhaseSpace → Fin 2 → (PhaseSpace →L[ℝ] ℝ) :=
      fun state ↦ ![fderiv ℝ (hamiltonian z.1) state,
        fderiv ℝ (F z.1) state]
    have hdifferentialPair : ContinuousAt differentialPair z.2 := by
      rw [continuousAt_pi]
      intro index
      fin_cases index
      · exact hhamiltonianDerivative
      · exact hcandidateDerivative
    have hcurve : ContinuousAt (verticalPerturbation z.2) 0 := by
      unfold verticalPerturbation
      fun_prop
    have hindependentEventually : ∀ᶠ offset in nhds (0 : ℝ),
        LinearIndependent ℝ (differentialPair (verticalPerturbation z.2 offset)) := by
      have hpairCurve : ContinuousAt
          (differentialPair ∘ verticalPerturbation z.2) 0 :=
        hdifferentialPair.comp_of_eq hcurve (by
          simp [verticalPerturbation])
      have hindependentBase : LinearIndependent ℝ
          ((differentialPair ∘ verticalPerturbation z.2) 0) := by
        simpa [differentialPair, verticalPerturbation] using hindependent
      simpa only [Function.comp_apply] using
        hpairCurve.eventually hindependentBase.eventually
    have hfirstCollision : ∀ᶠ offset in nhds (0 : ℝ),
        firstPrimaryDistanceSq z.1 (verticalPerturbation z.2 offset) ≠ 0 := by
      have hcontinuous : ContinuousAt
          (fun offset ↦ firstPrimaryDistanceSq z.1
            (verticalPerturbation z.2 offset)) 0 := by
        unfold firstPrimaryDistanceSq verticalPerturbation
        fun_prop
      exact hcontinuous.eventually_ne (by
        simpa [verticalPerturbation] using hz.2.1)
    have hsecondCollision : ∀ᶠ offset in nhds (0 : ℝ),
        secondPrimaryDistanceSq z.1 (verticalPerturbation z.2 offset) ≠ 0 := by
      have hcontinuous : ContinuousAt
          (fun offset ↦ secondPrimaryDistanceSq z.1
            (verticalPerturbation z.2 offset)) 0 := by
        unfold secondPrimaryDistanceSq verticalPerturbation
        fun_prop
      exact hcontinuous.eventually_ne (by
        simpa [verticalPerturbation] using hz.2.2)
    have hgood : ∀ᶠ offset in nhds (0 : ℝ),
        LinearIndependent ℝ
            (differentialPair (verticalPerturbation z.2 offset)) ∧
          firstPrimaryDistanceSq z.1 (verticalPerturbation z.2 offset) ≠ 0 ∧
          secondPrimaryDistanceSq z.1 (verticalPerturbation z.2 offset) ≠ 0 :=
      hindependentEventually.and (hfirstCollision.and hsecondCollision)
    rcases Metric.mem_nhds_iff.mp hgood with ⟨radius, hradius, hball⟩
    let offset := radius / 2
    have hoffsetBall : offset ∈ Metric.ball (0 : ℝ) radius := by
      rw [Metric.mem_ball]
      simp only [Real.dist_eq, sub_zero]
      dsimp only [offset]
      rw [abs_of_pos (by positivity)]
      linarith
    have hoffset : offset ≠ 0 := by
      dsimp only [offset]
      positivity
    have hperturbed := hball hoffsetBall
    have hperturbedVertical : verticalPerturbation z.2 offset 1 ≠ 0 := by
      rw [verticalPerturbation_vertical, hvertical, zero_add]
      exact hoffset
    have hdependent :=
      not_linearIndependent_of_iterated_normalizations_of_vertical_ne_zero
        hδ hnormalized henergy hcancel hz.1 hperturbedVertical
    exact hdependent hperturbed.1

/-- The remaining classical input, isolated as an induction principle: every analytic first
integral admits energy functions which cancel all successive Kepler-limit coefficients while the
normalized remainders remain jointly analytic. -/
def ClassicalNormalizationPrinciple : Prop :=
  ∀ {δ : ℝ} {F : ℝ → PhaseSpace → ℝ},
    0 < δ → IsJointlyAnalytic δ F → IsFirstIntegralFamily δ F →
      ∃ energyFunction : ℕ → ℝ → ℝ,
        (∀ n, IsJointlyAnalytic δ
          (iteratedMassNormalization F energyFunction n)) ∧
        (∀ n energy, AnalyticAt ℝ (energyFunction n) energy) ∧
        (∀ n state,
          iteratedMassNormalization F energyFunction n 0 state =
            energyFunction n (hamiltonian 0 state))

/-- Poincaré nonintegrability follows from the classical all-orders normalization principle. -/
theorem nonintegrability_of_classicalNormalizationPrinciple
    (hprinciple : ClassicalNormalizationPrinciple) :
    ¬∃ δ : ℝ, 0 < δ ∧ ∃ F : ℝ → PhaseSpace → ℝ,
      IsJointlyAnalytic δ F ∧ IsFirstIntegralFamily δ F ∧
        IsIndependentSomewhere δ F := by
  rintro ⟨δ, hδ, F, hanalytic, hfirstIntegral, hindependent⟩
  obtain ⟨energyFunction, hnormalized, henergy, hcancel⟩ :=
    hprinciple hδ hanalytic hfirstIntegral
  exact (not_isIndependentSomewhere_of_iterated_normalizations
    hδ hnormalized henergy hcancel) hindependent

end LeanPool.PoincareThreeBody
