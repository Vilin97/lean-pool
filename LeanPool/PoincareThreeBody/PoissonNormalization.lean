/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.AnalyticNormalization

/-!
# Poisson algebra for coefficient normalization

Subtracting a differentiable function of the Hamiltonian preserves the first-integral equation,
as does multiplication by a scalar.  Combined with the exact off-zero formula for `dslope`, this
shows that the mass-normalized candidate remains a first integral for nonzero mass wherever the
zeroth coefficient cancellation holds locally in phase space.
-/

namespace LeanPool.PoincareThreeBody


/-- A differentiable scalar function of an observable Poisson-commutes with that observable. -/
theorem poissonBracket_comp_self_eq_zero
    {observable : PhaseSpace → ℝ} {scalarFunction : ℝ → ℝ} {state : PhaseSpace}
    (hobservable : DifferentiableAt ℝ observable state)
    (hscalar : DifferentiableAt ℝ scalarFunction (observable state)) :
    poissonBracket (fun candidate ↦ scalarFunction (observable candidate))
      observable state = 0 := by
  have hchain := fderiv_comp state hscalar hobservable
  let coefficient := fderiv ℝ scalarFunction (observable state) 1
  have hscalarDerivative (value : ℝ) :
      fderiv ℝ scalarFunction (observable state) value =
        value * coefficient := by
    calc
      fderiv ℝ scalarFunction (observable state) value =
          fderiv ℝ scalarFunction (observable state) (value • (1 : ℝ)) := by simp
      _ = value • fderiv ℝ scalarFunction (observable state) 1 := by rw [map_smul]
      _ = value * coefficient := by rfl
  unfold poissonBracket
  rw [show fderiv ℝ (fun candidate ↦ scalarFunction (observable candidate)) state =
      (fderiv ℝ scalarFunction (observable state)).comp
        (fderiv ℝ observable state) by
    simpa only [Function.comp_def] using hchain]
  simp only [ContinuousLinearMap.comp_apply]
  simp_rw [hscalarDerivative]
  ring

/-- The Poisson bracket is additive in its first argument at differentiability points. -/
theorem poissonBracket_sub_left
    {first second observable : PhaseSpace → ℝ} {state : PhaseSpace}
    (hfirst : DifferentiableAt ℝ first state)
    (hsecond : DifferentiableAt ℝ second state) :
    poissonBracket (fun candidate ↦ first candidate - second candidate)
        observable state =
      poissonBracket first observable state -
        poissonBracket second observable state := by
  have hderivative := fderiv_sub hfirst hsecond
  change poissonBracket (first - second) observable state = _
  unfold poissonBracket
  rw [hderivative]
  simp only [sub_apply]
  ring

/-- Multiplying the first argument by a constant multiplies its Poisson bracket by that
constant. -/
theorem poissonBracket_const_mul_left
    {first observable : PhaseSpace → ℝ} {state : PhaseSpace}
    (hfirst : DifferentiableAt ℝ first state) (scalar : ℝ) :
    poissonBracket (fun candidate ↦ scalar * first candidate) observable state =
      scalar * poissonBracket first observable state := by
  have hderivative := fderiv_const_mul hfirst scalar
  unfold poissonBracket
  rw [hderivative]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- Subtracting a differentiable function of the Hamiltonian preserves Poisson commutation. -/
theorem poissonBracket_normalizationResidual_eq_zero
    {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    {mass : ℝ} {state : PhaseSpace}
    (hcandidate : DifferentiableAt ℝ (F mass) state)
    (hhamiltonian : DifferentiableAt ℝ (hamiltonian mass) state)
    (henergyFunction : DifferentiableAt ℝ energyFunction (hamiltonian mass state))
    (hcommutes : poissonBracket (F mass) (hamiltonian mass) state = 0) :
    poissonBracket (normalizationResidual F energyFunction mass)
      (hamiltonian mass) state = 0 := by
  have hcomposition : DifferentiableAt ℝ
      (fun candidate ↦ energyFunction (hamiltonian mass candidate)) state := by
    simpa only [Function.comp_def] using
      (henergyFunction.comp state hhamiltonian)
  change poissonBracket
    (fun candidate ↦ F mass candidate - energyFunction (hamiltonian mass candidate))
      (hamiltonian mass) state = 0
  rw [poissonBracket_sub_left hcandidate hcomposition,
    hcommutes,
    poissonBracket_comp_self_eq_zero hhamiltonian henergyFunction,
    sub_self]

/-- Under the challenge hypotheses, the normalization residual is a first integral at every
domain point where the chosen energy function is analytic. -/
theorem IsFirstIntegralFamily.normalizationResidual_poissonBracket_eq_zero
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    {z : ℝ × PhaseSpace} (hz : z ∈ parameterDomain δ)
    (henergyFunction : AnalyticAt ℝ energyFunction (hamiltonian z.1 z.2)) :
    poissonBracket (normalizationResidual F energyFunction z.1)
      (hamiltonian z.1) z.2 = 0 := by
  have hphaseEmbedding : AnalyticAt ℝ
      (fun state : PhaseSpace ↦ (z.1, state)) z.2 :=
    analyticAt_const.prod analyticAt_id
  have hcandidate : DifferentiableAt ℝ (F z.1) z.2 :=
    ((hanalytic z hz).comp
      (f := fun state : PhaseSpace ↦ (z.1, state)) hphaseEmbedding).differentiableAt
  have hhamiltonian : DifferentiableAt ℝ (hamiltonian z.1) z.2 :=
    ((hamiltonian_analyticAt hz.2).comp
      (f := fun state : PhaseSpace ↦ (z.1, state)) hphaseEmbedding).differentiableAt
  exact poissonBracket_normalizationResidual_eq_zero
    hcandidate hhamiltonian henergyFunction.differentiableAt
    (hfirstIntegral z hz)

/-- At nonzero mass, division of the normalization residual by mass preserves its
first-integral equation. -/
theorem IsFirstIntegralFamily.normalizationResidual_div_mass_poissonBracket_eq_zero
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    {mass : ℝ} (_hmass : mass ≠ 0) {state : PhaseSpace}
    (hdomain : (mass, state) ∈ parameterDomain δ)
    (henergyFunction : AnalyticAt ℝ energyFunction (hamiltonian mass state)) :
    poissonBracket
        (fun candidate ↦
          normalizationResidual F energyFunction mass candidate / mass)
        (hamiltonian mass) state = 0 := by
  have hresidual : DifferentiableAt ℝ
      (normalizationResidual F energyFunction mass) state := by
    have hphaseEmbedding : AnalyticAt ℝ
        (fun candidate : PhaseSpace ↦ (mass, candidate)) state :=
      analyticAt_const.prod analyticAt_id
    have hcandidate : DifferentiableAt ℝ (F mass) state :=
      ((hanalytic (mass, state) hdomain).comp
        (f := fun candidate : PhaseSpace ↦ (mass, candidate))
        hphaseEmbedding).differentiableAt
    have hhamiltonian : DifferentiableAt ℝ (hamiltonian mass) state :=
      ((hamiltonian_analyticAt hdomain.2).comp
        (f := fun candidate : PhaseSpace ↦ (mass, candidate))
        hphaseEmbedding).differentiableAt
    exact hcandidate.sub (henergyFunction.differentiableAt.comp state hhamiltonian)
  rw [show (fun candidate ↦
      normalizationResidual F energyFunction mass candidate / mass) =
      fun candidate ↦ mass⁻¹ *
        normalizationResidual F energyFunction mass candidate by
    funext candidate
    simp [div_eq_mul_inv, mul_comm]]
  rw [poissonBracket_const_mul_left hresidual,
    IsFirstIntegralFamily.normalizationResidual_poissonBracket_eq_zero
      hanalytic hfirstIntegral hdomain henergyFunction,
    mul_zero]

/-- If the zeroth residual vanishes on a phase neighborhood, then the `dslope`-normalized
candidate Poisson-commutes with the Hamiltonian at every nonzero mass in the domain. -/
theorem IsFirstIntegralFamily.massNormalizedCandidate_poissonBracket_eq_zero_of_ne
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    {mass : ℝ} (hmass : mass ≠ 0) {state : PhaseSpace}
    (hdomain : (mass, state) ∈ parameterDomain δ)
    (henergyFunction : AnalyticAt ℝ energyFunction (hamiltonian mass state))
    (hcancel : ∀ᶠ candidate in nhds state,
      F 0 candidate = energyFunction (hamiltonian 0 candidate)) :
    poissonBracket (massNormalizedCandidate F energyFunction mass)
      (hamiltonian mass) state = 0 := by
  have heventual : massNormalizedCandidate F energyFunction mass =ᶠ[nhds state]
      fun candidate ↦ normalizationResidual F energyFunction mass candidate / mass := by
    filter_upwards [hcancel] with candidate hcandidate
    exact massNormalizedCandidate_eq_div hmass hcandidate
  rw [poissonBracket]
  rw [heventual.fderiv_eq]
  exact IsFirstIntegralFamily.normalizationResidual_div_mass_poissonBracket_eq_zero
    hanalytic hfirstIntegral hmass hdomain henergyFunction

/-- A Poisson bracket formed from two jointly `C¹` mass/phase families varies continuously with
mass at a fixed phase point. -/
theorem continuousAt_poissonBracket_curry
    {first second : ℝ × PhaseSpace → ℝ} {mass : ℝ} {state : PhaseSpace}
    (hfirst : ContDiffAt ℝ 1 first (mass, state))
    (hsecond : ContDiffAt ℝ 1 second (mass, state)) :
    ContinuousAt
      (fun candidateMass ↦
        poissonBracket (fun candidate ↦ first (candidateMass, candidate))
          (fun candidate ↦ second (candidateMass, candidate)) state)
      mass := by
  let parameterCurve : ℝ → ℝ × PhaseSpace := fun candidateMass ↦
    (candidateMass, state)
  let firstPartial (coordinate : Fin 4) (candidateMass : ℝ) : ℝ :=
    fderiv ℝ first (candidateMass, state) (0, coordinateVector coordinate)
  let secondPartial (coordinate : Fin 4) (candidateMass : ℝ) : ℝ :=
    fderiv ℝ second (candidateMass, state) (0, coordinateVector coordinate)
  let representedBracket : ℝ → ℝ := fun candidateMass ↦
    firstPartial 0 candidateMass * secondPartial 2 candidateMass -
        firstPartial 2 candidateMass * secondPartial 0 candidateMass +
      (firstPartial 1 candidateMass * secondPartial 3 candidateMass -
        firstPartial 3 candidateMass * secondPartial 1 candidateMass)
  have hcurve : ContinuousAt parameterCurve mass := by
    exact continuousAt_id.prodMk continuousAt_const
  have hfirstDerivative : ContinuousAt
      (fun candidateMass ↦ fderiv ℝ first (candidateMass, state)) mass :=
    (hfirst.continuousAt_fderiv (by norm_num)).comp
      (f := parameterCurve) hcurve
  have hsecondDerivative : ContinuousAt
      (fun candidateMass ↦ fderiv ℝ second (candidateMass, state)) mass :=
    (hsecond.continuousAt_fderiv (by norm_num)).comp
      (f := parameterCurve) hcurve
  have hfirstPartial (coordinate : Fin 4) :
      ContinuousAt (firstPartial coordinate) mass :=
    continuousAt_clm_apply.mp hfirstDerivative (0, coordinateVector coordinate)
  have hsecondPartial (coordinate : Fin 4) :
      ContinuousAt (secondPartial coordinate) mass :=
    continuousAt_clm_apply.mp hsecondDerivative (0, coordinateVector coordinate)
  have hrepresented : ContinuousAt representedBracket mass := by
    dsimp only [representedBracket]
    fun_prop
  have hfirstEventually : ∀ᶠ candidateMass in nhds mass,
      DifferentiableAt ℝ first (candidateMass, state) := by
    exact hcurve.eventually
      ((hfirst.eventually (by norm_num)).mono fun _ h ↦ h.differentiableAt (by norm_num))
  have hsecondEventually : ∀ᶠ candidateMass in nhds mass,
      DifferentiableAt ℝ second (candidateMass, state) := by
    exact hcurve.eventually
      ((hsecond.eventually (by norm_num)).mono fun _ h ↦ h.differentiableAt (by norm_num))
  have heventual :
      (fun candidateMass ↦
        poissonBracket (fun candidate ↦ first (candidateMass, candidate))
          (fun candidate ↦ second (candidateMass, candidate)) state) =ᶠ[nhds mass]
        representedBracket := by
    filter_upwards [hfirstEventually, hsecondEventually]
      with candidateMass hfirstMass hsecondMass
    have hfirstSlice (direction : PhaseSpace) :
        fderiv ℝ (fun candidate ↦ first (candidateMass, candidate)) state direction =
          fderiv ℝ first (candidateMass, state) (0, direction) :=
      fderiv_curry_right_apply hfirstMass
    have hsecondSlice (direction : PhaseSpace) :
        fderiv ℝ (fun candidate ↦ second (candidateMass, candidate)) state direction =
          fderiv ℝ second (candidateMass, state) (0, direction) :=
      fderiv_curry_right_apply hsecondMass
    simp only [poissonBracket]
    unfold representedBracket firstPartial secondPartial
    rw [hfirstSlice (coordinateVector 0), hfirstSlice (coordinateVector 2),
      hfirstSlice (coordinateVector 1), hfirstSlice (coordinateVector 3),
      hsecondSlice (coordinateVector 0), hsecondSlice (coordinateVector 2),
      hsecondSlice (coordinateVector 1), hsecondSlice (coordinateVector 3)]
  exact hrepresented.congr_of_eventuallyEq heventual

/-- Once joint `C¹` regularity of the removable quotient is available, its off-zero
first-integral equation extends continuously to mass zero.  This isolates the joint analytic
Hadamard-division lemma needed to iterate Poincaré's normalization. -/
theorem IsFirstIntegralFamily.massNormalizedCandidate_poissonBracket_eq_zero_at_mass_zero
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    {state : PhaseSpace} (hcollision : (0, state) ∈ collisionFree)
    (henergyFunction : AnalyticAt ℝ energyFunction (hamiltonian 0 state))
    (hcancel : ∀ᶠ candidate in nhds state,
      F 0 candidate = energyFunction (hamiltonian 0 candidate))
    (hnormalized : ContDiffAt ℝ 1
      (Function.uncurry (massNormalizedCandidate F energyFunction)) (0, state)) :
    poissonBracket (massNormalizedCandidate F energyFunction 0)
      (hamiltonian 0) state = 0 := by
  let bracketAtMass : ℝ → ℝ := fun mass ↦
    poissonBracket (massNormalizedCandidate F energyFunction mass)
      (hamiltonian mass) state
  have hhamiltonianJoint : ContDiffAt ℝ 1
      (Function.uncurry hamiltonian) (0, state) :=
    (hamiltonian_analyticAt hcollision).contDiffAt
  have hbracketContinuous : ContinuousAt bracketAtMass 0 := by
    have hcontinuous := continuousAt_poissonBracket_curry
      (first := Function.uncurry (massNormalizedCandidate F energyFunction))
      (second := Function.uncurry hamiltonian)
      hnormalized hhamiltonianJoint
    simpa only [bracketAtMass, Function.uncurry_apply_pair] using hcontinuous
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
  have hhamiltonianSlice : ContinuousAt
      (fun mass ↦ hamiltonian mass state) 0 :=
    (hamiltonian_analyticAt_mass_zero hcollision).continuousAt
  have henergyEventually : ∀ᶠ mass in nhds (0 : ℝ),
      AnalyticAt ℝ energyFunction (hamiltonian mass state) :=
    hhamiltonianSlice.eventually henergyFunction.eventually_analyticAt
  have hne : ∀ᶠ mass in nhdsWithin (0 : ℝ) {0}ᶜ, mass ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with mass hmass
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hmass
  have hdomainWithin : ∀ᶠ mass in nhdsWithin (0 : ℝ) {0}ᶜ,
      (mass, state) ∈ parameterDomain δ :=
    hdomain.filter_mono inf_le_left
  have henergyWithin : ∀ᶠ mass in nhdsWithin (0 : ℝ) {0}ᶜ,
      AnalyticAt ℝ energyFunction (hamiltonian mass state) :=
    henergyEventually.filter_mono inf_le_left
  have hzero : bracketAtMass =ᶠ[nhdsWithin (0 : ℝ) {0}ᶜ] fun _ ↦ 0 := by
    filter_upwards [hne, hdomainWithin, henergyWithin]
      with mass hmass hmassDomain henergyMass
    exact IsFirstIntegralFamily.massNormalizedCandidate_poissonBracket_eq_zero_of_ne
      hanalytic hfirstIntegral hmass hmassDomain henergyMass hcancel
  have hlimit : Filter.Tendsto bracketAtMass (nhdsWithin (0 : ℝ) {0}ᶜ)
      (nhds (bracketAtMass 0)) :=
    hbracketContinuous.tendsto.mono_left inf_le_left
  have hzeroLimit : Filter.Tendsto (fun _ : ℝ ↦ (0 : ℝ))
      (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 0) :=
    tendsto_const_nhds
  exact tendsto_nhds_unique_of_eventuallyEq hlimit hzeroLimit hzero

/-- Joint analyticity of the domain-correct removable quotient upgrades the pointwise
normalization algebra to a first-integral family on the whole parameter domain. -/
theorem IsFirstIntegralFamily.domainMassNormalizedCandidate_isFirstIntegralFamily
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    (henergy : ∀ energy, AnalyticAt ℝ energyFunction energy)
    (hcancel : ∀ state, (0, state) ∈ collisionFree →
      F 0 state = energyFunction (hamiltonian 0 state))
    (hnormalized : IsJointlyAnalytic δ
      (domainMassNormalizedCandidate F energyFunction)) :
    IsFirstIntegralFamily δ (domainMassNormalizedCandidate F energyFunction) := by
  intro z hz
  by_cases hmass : z.1 = 0
  · rw [hmass]
    have hz0 : (0, z.2) ∈ parameterDomain δ := by
      refine ⟨by simpa using hδ, ?_⟩
      have hcollision := hz.2
      change firstPrimaryDistanceSq z.1 z.2 ≠ 0 ∧
        secondPrimaryDistanceSq z.1 z.2 ≠ 0 at hcollision
      rw [hmass] at hcollision
      exact hcollision
    have hfirstCollision : ∀ᶠ state in nhds z.2,
        firstPrimaryDistanceSq 0 state ≠ 0 := by
      have hcontinuous : Continuous (firstPrimaryDistanceSq 0) := by
        unfold firstPrimaryDistanceSq
        fun_prop
      exact hcontinuous.continuousAt.eventually_ne hz0.2.1
    have hsecondCollision : ∀ᶠ state in nhds z.2,
        secondPrimaryDistanceSq 0 state ≠ 0 := by
      have hcontinuous : Continuous (secondPrimaryDistanceSq 0) := by
        unfold secondPrimaryDistanceSq
        fun_prop
      exact hcontinuous.continuousAt.eventually_ne hz0.2.2
    have hcancelEventually : ∀ᶠ state in nhds z.2,
        F 0 state = energyFunction (hamiltonian 0 state) := by
      filter_upwards [hfirstCollision, hsecondCollision] with state hfirst hsecond
      exact hcancel state ⟨hfirst, hsecond⟩
    have hstateProjection : ContinuousAt
        (fun w : ℝ × PhaseSpace ↦ w.2) (0, z.2) := continuousAt_snd
    have hfirstJoint : ∀ᶠ w in nhds ((0 : ℝ), z.2),
        firstPrimaryDistanceSq 0 w.2 ≠ 0 :=
      hstateProjection.eventually hfirstCollision
    have hsecondJoint : ∀ᶠ w in nhds ((0 : ℝ), z.2),
        secondPrimaryDistanceSq 0 w.2 ≠ 0 :=
      hstateProjection.eventually hsecondCollision
    have hlocalEquality :
        Function.uncurry (massNormalizedCandidate F energyFunction) =ᶠ[nhds (0, z.2)]
          Function.uncurry (domainMassNormalizedCandidate F energyFunction) := by
      filter_upwards [hfirstJoint, hsecondJoint] with w hfirst hsecond
      exact (domainMassNormalizedCandidate_eq_massNormalizedCandidate
        (hcancel w.2 ⟨hfirst, hsecond⟩)).symm
    have hdomainNormalizedSmooth : ContDiffAt ℝ 1
        (Function.uncurry (domainMassNormalizedCandidate F energyFunction)) (0, z.2) :=
      (hnormalized (0, z.2) hz0).contDiffAt
    have hnormalizedSmooth : ContDiffAt ℝ 1
        (Function.uncurry (massNormalizedCandidate F energyFunction)) (0, z.2) :=
      hdomainNormalizedSmooth.congr_of_eventuallyEq hlocalEquality
    rw [show domainMassNormalizedCandidate F energyFunction 0 =
        massNormalizedCandidate F energyFunction 0 by
      funext state
      simp]
    exact IsFirstIntegralFamily.massNormalizedCandidate_poissonBracket_eq_zero_at_mass_zero
      hδ hanalytic hfirstIntegral hz0.2 (henergy _) hcancelEventually
      hnormalizedSmooth
  · rw [show domainMassNormalizedCandidate F energyFunction z.1 =
        fun state ↦ normalizationResidual F energyFunction z.1 state / z.1 by
      funext state
      exact domainMassNormalizedCandidate_eq_div hmass state]
    exact IsFirstIntegralFamily.normalizationResidual_div_mass_poissonBracket_eq_zero
      hanalytic hfirstIntegral hmass hz (henergy _)

end LeanPool.PoincareThreeBody
