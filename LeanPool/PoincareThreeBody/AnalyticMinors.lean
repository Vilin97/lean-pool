/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DifferentialDependence
import LeanPool.PoincareThreeBody.ParameterDomainTopology
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Analyticity and flatness of differential minors

The final output of Poincaré's coefficient induction is that every mass derivative of each
coordinate minor vanishes at zero.  This file proves the analytic consequences: the minors are
analytic mass germs, infinite-order vanishing makes them locally zero, and the identity principle
propagates that equality along any connected collision-free mass fiber.
-/

namespace LeanPool.PoincareThreeBody


/-- A coordinate minor of the Hamiltonian and candidate phase differentials at fixed mass and
phase. -/
noncomputable def massDifferentialMinor
    (F : ℝ → PhaseSpace → ℝ) (i j : Fin 4)
    (mass : ℝ) (state : PhaseSpace) : ℝ :=
  phaseCovectorMinor (fderiv ℝ (hamiltonian mass) state)
    (fderiv ℝ (F mass) state) i j

/-- Coordinate-minor form of the physical leading obstruction, suitable for analytic
continuation. -/
theorem IsFirstIntegralFamily.mass_zero_differentialMinor_eq_zero_on_liftedEllipse
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    (hdense : HasDenseClassicalPoincareSet)
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1)
    (i j : Fin 4) :
    massDifferentialMinor F i j 0
      (liftedDelaunayPhasePoint
        firstAction eccentricity meanAnomaly periapsisAngle) = 0 := by
  unfold massDifferentialMinor
  apply phaseCovectorMinor_eq_zero_of_not_linearIndependent
    (IsFirstIntegralFamily.mass_zero_differentials_dependent_on_liftedEllipse
      hδ hanalytic hfirstIntegral hdense hfirstAction heccentricity
      heccentricityOne hapoapsis)

/-- The same phase-coordinate minor, expressed using the joint mass/phase differentials.  This
form is analytic on the full parameter domain, so the several-variable identity principle can
propagate a local Poincaré obstruction between different phase points as well as different
masses. -/
noncomputable def jointDifferentialMinor
    (F : ℝ → PhaseSpace → ℝ) (i j : Fin 4)
    (z : ℝ × PhaseSpace) : ℝ :=
  fderiv ℝ (Function.uncurry hamiltonian) z (0, coordinateVector i) *
      fderiv ℝ (Function.uncurry F) z (0, coordinateVector j) -
    fderiv ℝ (Function.uncurry hamiltonian) z (0, coordinateVector j) *
      fderiv ℝ (Function.uncurry F) z (0, coordinateVector i)

/-- On the analytic domain, the joint and curried formulations of a phase minor agree. -/
theorem jointDifferentialMinor_eq_massDifferentialMinor
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hanalytic : IsJointlyAnalytic δ F) {z : ℝ × PhaseSpace}
    (hz : z ∈ parameterDomain δ) (i j : Fin 4) :
    jointDifferentialMinor F i j z = massDifferentialMinor F i j z.1 z.2 := by
  have hcandidate : DifferentiableAt ℝ (Function.uncurry F) z :=
    (hanalytic z hz).differentiableAt
  have hhamiltonian : DifferentiableAt ℝ (Function.uncurry hamiltonian) z :=
    (hamiltonian_analyticAt hz.2).differentiableAt
  have hcandidatePartial (coordinate : Fin 4) :
      fderiv ℝ (F z.1) z.2 (coordinateVector coordinate) =
        fderiv ℝ (Function.uncurry F) z (0, coordinateVector coordinate) := by
    simpa only [Function.uncurry_apply_pair] using
      (fderiv_curry_right_apply (v := coordinateVector coordinate) hcandidate)
  have hhamiltonianPartial (coordinate : Fin 4) :
      fderiv ℝ (hamiltonian z.1) z.2 (coordinateVector coordinate) =
        fderiv ℝ (Function.uncurry hamiltonian) z
          (0, coordinateVector coordinate) := by
    simpa only [Function.uncurry_apply_pair] using
      (fderiv_curry_right_apply (v := coordinateVector coordinate) hhamiltonian)
  unfold jointDifferentialMinor massDifferentialMinor phaseCovectorMinor
  rw [← hhamiltonianPartial i, ← hcandidatePartial j,
    ← hhamiltonianPartial j, ← hcandidatePartial i]

/-- Joint coordinate minors are analytic on the complete collision-free parameter domain. -/
theorem IsJointlyAnalytic.analyticOnNhd_jointDifferentialMinor
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hanalytic : IsJointlyAnalytic δ F) (i j : Fin 4) :
    AnalyticOnNhd ℝ (jointDifferentialMinor F i j) (parameterDomain δ) := by
  intro z hz
  have hcandidateDerivative : AnalyticAt ℝ
      (fun w ↦ fderiv ℝ (Function.uncurry F) w) z :=
    (hanalytic z hz).fderiv
  have hhamiltonianDerivative : AnalyticAt ℝ
      (fun w ↦ fderiv ℝ (Function.uncurry hamiltonian) w) z :=
    (hamiltonian_analyticAt hz.2).fderiv
  have hcandidate (coordinate : Fin 4) : AnalyticAt ℝ
      (fun w ↦ fderiv ℝ (Function.uncurry F) w
        (0, coordinateVector coordinate)) z :=
    ((ContinuousLinearMap.apply ℝ ℝ
      ((0 : ℝ), coordinateVector coordinate)).analyticAt _).comp
        hcandidateDerivative
  have hhamiltonian (coordinate : Fin 4) : AnalyticAt ℝ
      (fun w ↦ fderiv ℝ (Function.uncurry hamiltonian) w
        (0, coordinateVector coordinate)) z :=
    ((ContinuousLinearMap.apply ℝ ℝ
      ((0 : ℝ), coordinateVector coordinate)).analyticAt _).comp
        hhamiltonianDerivative
  exact ((hhamiltonian i).mul (hcandidate j)).sub
    ((hhamiltonian j).mul (hcandidate i))

/-- At mass zero, every phase differential minor is analytic on the full collision-free phase
domain. -/
theorem IsJointlyAnalytic.analyticOnNhd_massZeroDifferentialMinor
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F) (i j : Fin 4) :
    AnalyticOnNhd ℝ (fun state ↦ massDifferentialMinor F i j 0 state)
      massZeroCollisionFree := by
  intro state hcollision
  have hdomain : (0, state) ∈ parameterDomain δ :=
    ⟨by simpa using hδ, hcollision⟩
  have hembedding : AnalyticAt ℝ
      (fun candidate : PhaseSpace ↦ ((0 : ℝ), candidate)) state :=
    analyticAt_const.prod analyticAt_id
  have hjoint : AnalyticAt ℝ
      (fun candidate ↦ jointDifferentialMinor F i j ((0 : ℝ), candidate)) state :=
    ((IsJointlyAnalytic.analyticOnNhd_jointDifferentialMinor hanalytic i j)
      (0, state) hdomain).comp
      (f := fun candidate : PhaseSpace ↦ ((0 : ℝ), candidate)) hembedding
  have hfirstCollision : ∀ᶠ candidate in nhds state,
      firstPrimaryDistanceSq 0 candidate ≠ 0 := by
    have hcontinuous : Continuous (firstPrimaryDistanceSq 0) := by
      unfold firstPrimaryDistanceSq
      fun_prop
    exact hcontinuous.continuousAt.eventually_ne hcollision.1
  have hsecondCollision : ∀ᶠ candidate in nhds state,
      secondPrimaryDistanceSq 0 candidate ≠ 0 := by
    have hcontinuous : Continuous (secondPrimaryDistanceSq 0) := by
      unfold secondPrimaryDistanceSq
      fun_prop
    exact hcontinuous.continuousAt.eventually_ne hcollision.2
  have heq :
      (fun candidate ↦ jointDifferentialMinor F i j ((0 : ℝ), candidate)) =ᶠ[nhds state]
        fun candidate ↦ massDifferentialMinor F i j 0 candidate := by
    filter_upwards [hfirstCollision, hsecondCollision] with candidate hfirst hsecond
    exact jointDifferentialMinor_eq_massDifferentialMinor hanalytic
      ⟨by simpa using hδ, hfirst, hsecond⟩ i j
  exact hjoint.congr heq

/-- A mass-zero minor that vanishes near one collision-free phase point vanishes on the entire
connected mass-zero phase domain. -/
theorem IsJointlyAnalytic.massZeroDifferentialMinor_eq_zero
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    {base : PhaseSpace} (hbase : base ∈ massZeroCollisionFree)
    (i j : Fin 4)
    (hlocal : ∀ᶠ state in nhds base,
      massDifferentialMinor F i j 0 state = 0) :
    Set.EqOn (fun state ↦ massDifferentialMinor F i j 0 state) 0
      massZeroCollisionFree := by
  have hminorAnalytic :=
    IsJointlyAnalytic.analyticOnNhd_massZeroDifferentialMinor hδ hanalytic i j
  exact hminorAnalytic.eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const isPreconnected_massZeroCollisionFree hbase hlocal

/-- A joint minor which vanishes near one point vanishes throughout a connected parameter
domain.  Unlike continuation along a fixed-state mass fiber, this permits paths which move around
the collision cylinders. -/
theorem IsJointlyAnalytic.jointDifferentialMinor_eq_zero_on_preconnected
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hanalytic : IsJointlyAnalytic δ F)
    (hpreconnected : IsPreconnected (parameterDomain δ))
    {base : ℝ × PhaseSpace} (hbase : base ∈ parameterDomain δ)
    (i j : Fin 4)
    (hlocal : ∀ᶠ z in nhds base, jointDifferentialMinor F i j z = 0) :
    Set.EqOn (jointDifferentialMinor F i j) 0 (parameterDomain δ) := by
  have hminorAnalytic :=
    IsJointlyAnalytic.analyticOnNhd_jointDifferentialMinor hanalytic i j
  exact hminorAnalytic.eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const hpreconnected hbase hlocal

/-- The analytic-continuation endpoint of Poincaré's coefficient argument: local vanishing of all
phase-differential minors at one point contradicts functional independence anywhere in the
connected collision-free parameter domain. -/
theorem IsJointlyAnalytic.not_isIndependentSomewhere_of_local_minors_eq_zero
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hanalytic : IsJointlyAnalytic δ F)
    (hpreconnected : IsPreconnected (parameterDomain δ))
    {base : ℝ × PhaseSpace} (hbase : base ∈ parameterDomain δ)
    (hlocal : ∀ i j : Fin 4,
      ∀ᶠ z in nhds base, jointDifferentialMinor F i j z = 0) :
    ¬IsIndependentSomewhere δ F := by
  rintro ⟨z, hz, hindependent⟩
  have hdependent : ¬LinearIndependent ℝ
      ![fderiv ℝ (hamiltonian z.1) z.2, fderiv ℝ (F z.1) z.2] := by
    apply not_linearIndependent_fderiv_of_minors_eq_zero
    intro i j
    have hglobal := IsJointlyAnalytic.jointDifferentialMinor_eq_zero_on_preconnected
      hanalytic hpreconnected hbase i j (hlocal i j)
    change massDifferentialMinor F i j z.1 z.2 = 0
    rw [← jointDifferentialMinor_eq_massDifferentialMinor hanalytic hz]
    exact hglobal hz
  exact hdependent hindependent

/-- The connectedness-specialized form used by the final nonintegrability proof. -/
theorem IsJointlyAnalytic.not_isIndependentSomewhere_of_local_minors_eq_zero'
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    {base : ℝ × PhaseSpace} (hbase : base ∈ parameterDomain δ)
    (hlocal : ∀ i j : Fin 4,
      ∀ᶠ z in nhds base, jointDifferentialMinor F i j z = 0) :
    ¬IsIndependentSomewhere δ F :=
  IsJointlyAnalytic.not_isIndependentSomewhere_of_local_minors_eq_zero
    hanalytic (isPreconnected_parameterDomain hδ) hbase hlocal

/-- A pure phase partial derivative of a jointly analytic family is analytic as the mass varies
with phase held fixed. -/
theorem analyticAt_phaseFDeriv_massSlice
    {G : ℝ × PhaseSpace → ℝ} {mass : ℝ} {state direction : PhaseSpace}
    (hG : AnalyticAt ℝ G (mass, state)) :
    AnalyticAt ℝ
      (fun candidateMass ↦
        fderiv ℝ (fun candidate ↦ G (candidateMass, candidate)) state direction)
      mass := by
  let parameterCurve : ℝ → ℝ × PhaseSpace := fun candidateMass ↦
    (candidateMass, state)
  have hcurve : AnalyticAt ℝ parameterCurve mass :=
    analyticAt_id.prod analyticAt_const
  have hderivative : AnalyticAt ℝ
      (fun candidateMass ↦ fderiv ℝ G (candidateMass, state)) mass :=
    hG.fderiv.comp (f := parameterCurve) hcurve
  have hevaluation : AnalyticAt ℝ
      (fun derivative : (ℝ × PhaseSpace →L[ℝ] ℝ) ↦ derivative (0, direction))
      (fderiv ℝ G (mass, state)) :=
    (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), direction)).analyticAt _
  have hjointPartial : AnalyticAt ℝ
      (fun candidateMass ↦
        fderiv ℝ G (candidateMass, state) (0, direction)) mass :=
    hevaluation.comp
      (f := fun candidateMass ↦ fderiv ℝ G (candidateMass, state)) hderivative
  have hdifferentiable : ∀ᶠ candidateMass in nhds mass,
      DifferentiableAt ℝ G (candidateMass, state) := by
    exact hcurve.continuousAt.eventually
      (hG.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt)
  have heventual :
      (fun candidateMass ↦ fderiv ℝ G (candidateMass, state) (0, direction))
        =ᶠ[nhds mass]
      fun candidateMass ↦
        fderiv ℝ (fun candidate ↦ G (candidateMass, candidate)) state direction := by
    filter_upwards [hdifferentiable] with candidateMass hmass
    exact (fderiv_curry_right_apply hmass).symm
  exact hjointPartial.congr heventual

/-- Every Hamiltonian/candidate coordinate minor is analytic along a collision-free mass fiber. -/
theorem IsJointlyAnalytic.analyticAt_massDifferentialMinor_massSlice
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hanalytic : IsJointlyAnalytic δ F)
    {mass : ℝ} {state : PhaseSpace}
    (hdomain : (mass, state) ∈ parameterDomain δ) (i j : Fin 4) :
    AnalyticAt ℝ (fun candidateMass ↦
      massDifferentialMinor F i j candidateMass state) mass := by
  have hcandidateJoint : AnalyticAt ℝ (Function.uncurry F) (mass, state) :=
    hanalytic (mass, state) hdomain
  have hhamiltonianJoint : AnalyticAt ℝ
      (Function.uncurry hamiltonian) (mass, state) :=
    hamiltonian_analyticAt hdomain.2
  have hcandidate (coordinate : Fin 4) : AnalyticAt ℝ
      (fun candidateMass ↦
        fderiv ℝ (F candidateMass) state (coordinateVector coordinate)) mass := by
    simpa only [Function.uncurry_apply_pair] using
      (analyticAt_phaseFDeriv_massSlice
        (G := Function.uncurry F) (direction := coordinateVector coordinate)
        hcandidateJoint)
  have hhamiltonian (coordinate : Fin 4) : AnalyticAt ℝ
      (fun candidateMass ↦
        fderiv ℝ (hamiltonian candidateMass) state
          (coordinateVector coordinate)) mass := by
    simpa only [Function.uncurry_apply_pair] using
      (analyticAt_phaseFDeriv_massSlice
        (G := Function.uncurry hamiltonian)
        (direction := coordinateVector coordinate) hhamiltonianJoint)
  unfold massDifferentialMinor phaseCovectorMinor
  exact ((hhamiltonian i).mul (hcandidate j)).sub
    ((hhamiltonian j).mul (hcandidate i))

/-- Analyticity throughout a collision-free mass subset. -/
theorem IsJointlyAnalytic.analyticOnNhd_massDifferentialMinor_massSlice
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hanalytic : IsJointlyAnalytic δ F)
    {state : PhaseSpace} {massSet : Set ℝ}
    (hdomain : ∀ mass ∈ massSet, (mass, state) ∈ parameterDomain δ)
    (i j : Fin 4) :
    AnalyticOnNhd ℝ (fun mass ↦ massDifferentialMinor F i j mass state)
      massSet := by
  intro mass hmass
  exact IsJointlyAnalytic.analyticAt_massDifferentialMinor_massSlice
    hanalytic (hdomain mass hmass) i j

/-- Infinite-order vanishing of an analytic real germ makes it identically zero on a
neighborhood. -/
theorem AnalyticAt.eventually_eq_zero_of_iteratedDeriv_eq_zero
    {f : ℝ → ℝ} {base : ℝ} (hf : AnalyticAt ℝ f base)
    (hflat : ∀ n : ℕ, iteratedDeriv n f base = 0) :
    ∀ᶠ argument in nhds base, f argument = 0 := by
  have horder : analyticOrderAt f base = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
    exact fun i _ ↦ hflat i
  exact analyticOrderAt_eq_top.mp horder

/-- Taylor-flat differential minors vanish on every connected collision-free mass set containing
zero. -/
theorem IsJointlyAnalytic.massDifferentialMinor_eq_zero_on_preconnected
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hanalytic : IsJointlyAnalytic δ F)
    {state : PhaseSpace} {massSet : Set ℝ}
    (hpreconnected : IsPreconnected massSet) (hzero : 0 ∈ massSet)
    (hdomain : ∀ mass ∈ massSet, (mass, state) ∈ parameterDomain δ)
    (i j : Fin 4)
    (hflat : ∀ n : ℕ,
      iteratedDeriv n (fun mass ↦ massDifferentialMinor F i j mass state) 0 = 0) :
    Set.EqOn (fun mass ↦ massDifferentialMinor F i j mass state) 0 massSet := by
  have hminorAnalytic :=
    IsJointlyAnalytic.analyticOnNhd_massDifferentialMinor_massSlice
      hanalytic hdomain i j
  have hminorAtZero := hminorAnalytic 0 hzero
  have heventual :=
    AnalyticAt.eventually_eq_zero_of_iteratedDeriv_eq_zero hminorAtZero hflat
  exact hminorAnalytic.eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const hpreconnected hzero heventual

/-- Flatness of every minor at zero rules out functional independence at every mass in the same
connected collision-free fiber. -/
theorem IsJointlyAnalytic.not_independent_on_preconnected_massFiber_of_minors_flat
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hanalytic : IsJointlyAnalytic δ F)
    {state : PhaseSpace} {massSet : Set ℝ}
    (hpreconnected : IsPreconnected massSet) (hzero : 0 ∈ massSet)
    (hdomain : ∀ mass ∈ massSet, (mass, state) ∈ parameterDomain δ)
    (hflat : ∀ i j : Fin 4, ∀ n : ℕ,
      iteratedDeriv n (fun mass ↦ massDifferentialMinor F i j mass state) 0 = 0)
    {mass : ℝ} (hmass : mass ∈ massSet) :
    ¬LinearIndependent ℝ
      ![fderiv ℝ (hamiltonian mass) state, fderiv ℝ (F mass) state] := by
  apply not_linearIndependent_fderiv_of_minors_eq_zero
  intro i j
  have hminor :=
    IsJointlyAnalytic.massDifferentialMinor_eq_zero_on_preconnected
      hanalytic hpreconnected hzero hdomain i j (hflat i j)
  exact hminor hmass

end LeanPool.PoincareThreeBody
