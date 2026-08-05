/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.NormalizationInduction

/-!
# Closing the normalization induction from one step

This file reduces the all-orders classical normalization principle to a single reusable closure
theorem.  Once every jointly analytic first integral can be normalized once—preserving joint
analyticity and the first-integral equation—classical choice and primitive recursion construct all
orders automatically.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

/-- The one-step statement needed from the Poincaré-set obstruction and analytic Hadamard
division. -/
def ClassicalNormalizationStep : Prop :=
  ∀ {δ : ℝ} {F : ℝ → PhaseSpace → ℝ},
    0 < δ → IsJointlyAnalytic δ F → IsFirstIntegralFamily δ F →
      ∃ energyFunction : ℝ → ℝ,
        (∀ energy, AnalyticAt ℝ energyFunction energy) ∧
        (∀ state, (0, state) ∈ collisionFree →
          F 0 state = energyFunction (hamiltonian 0 state)) ∧
        IsJointlyAnalytic δ (domainMassNormalizedCandidate F energyFunction) ∧
        IsFirstIntegralFamily δ (domainMassNormalizedCandidate F energyFunction)

/-- Celestial-mechanics half of one normalization step: the mass-zero coefficient of every
analytic first integral is a globally analytic function of the Kepler Hamiltonian. -/
def ClassicalZerothCoefficientPrinciple : Prop :=
  ∀ {δ : ℝ} {F : ℝ → PhaseSpace → ℝ},
    0 < δ → IsJointlyAnalytic δ F → IsFirstIntegralFamily δ F →
      ∃ energyFunction : ℝ → ℝ,
        (∀ energy, AnalyticAt ℝ energyFunction energy) ∧
        (∀ state, (0, state) ∈ collisionFree →
          F 0 state = energyFunction (hamiltonian 0 state))

/-- Analytic half of one normalization step: division by the mass coordinate preserves joint
analyticity after the zeroth coefficient has been cancelled on the actual mass-zero domain. -/
def JointAnalyticMassDivisionPrinciple : Prop :=
  ∀ {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ},
    0 < δ → IsJointlyAnalytic δ F →
      (∀ energy, AnalyticAt ℝ energyFunction energy) →
      (∀ state, (0, state) ∈ collisionFree →
        F 0 state = energyFunction (hamiltonian 0 state)) →
      IsJointlyAnalytic δ (domainMassNormalizedCandidate F energyFunction)

/-- Pointwise form of analytic Hadamard division on the only nontrivial slice.  Ordinary
division already handles every point with nonzero mass, so this is equivalent to the global
joint-analytic division principle above. -/
def MassZeroAnalyticDivisionPrinciple : Prop :=
  ∀ {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} {energyFunction : ℝ → ℝ},
    0 < δ → IsJointlyAnalytic δ F →
      (∀ energy, AnalyticAt ℝ energyFunction energy) →
      (∀ state, (0, state) ∈ collisionFree →
        F 0 state = energyFunction (hamiltonian 0 state)) →
      ∀ state, (0, state) ∈ collisionFree →
        AnalyticAt ℝ
          (Function.uncurry (domainMassNormalizedCandidate F energyFunction)) (0, state)

/-- Parameterized analytic division is reduced exactly to the removable mass-zero slice. -/
theorem jointAnalyticMassDivisionPrinciple_iff_massZero :
    JointAnalyticMassDivisionPrinciple ↔ MassZeroAnalyticDivisionPrinciple := by
  constructor
  · intro hdivision δ F energyFunction hδ hanalytic henergy hcancel state hcollision
    exact hdivision hδ hanalytic henergy hcancel (0, state)
      ⟨by simpa using hδ, hcollision⟩
  · intro hdivision δ F energyFunction _hδ hanalytic henergy hcancel
    exact isJointlyAnalytic_domainMassNormalizedCandidate_of_mass_zero
      hanalytic henergy (hdivision _hδ hanalytic henergy hcancel)

/-- The functional-dependence and analytic-division halves together give the reusable one-step
closure theorem; preservation of the first-integral equation is already formal. -/
theorem classicalNormalizationStep_of_zerothCoefficient_of_massDivision
    (hcoefficient : ClassicalZerothCoefficientPrinciple)
    (hdivision : JointAnalyticMassDivisionPrinciple) :
    ClassicalNormalizationStep := by
  intro δ F hδ hanalytic hfirstIntegral
  obtain ⟨energyFunction, henergy, hcancel⟩ :=
    hcoefficient hδ hanalytic hfirstIntegral
  have hnormalized := hdivision hδ hanalytic henergy hcancel
  refine ⟨energyFunction, henergy, hcancel, hnormalized, ?_⟩
  exact IsFirstIntegralFamily.domainMassNormalizedCandidate_isFirstIntegralFamily
    hδ hanalytic hfirstIntegral henergy hcancel hnormalized

/-- A jointly analytic first integral, bundled so a normalization step can be iterated. -/
structure NormalizationState (δ : ℝ) where
  family : ℝ → PhaseSpace → ℝ
  analytic : IsJointlyAnalytic δ family
  firstIntegral : IsFirstIntegralFamily δ family

/-- The energy function selected for one normalization state. -/
noncomputable def selectedEnergy
    (hstep : ClassicalNormalizationStep) {δ : ℝ} (hδ : 0 < δ)
    (current : NormalizationState δ) : ℝ → ℝ :=
  Classical.choose (hstep hδ current.analytic current.firstIntegral)

theorem selectedEnergy_spec
    (hstep : ClassicalNormalizationStep) {δ : ℝ} (hδ : 0 < δ)
    (current : NormalizationState δ) :
    (∀ energy, AnalyticAt ℝ (selectedEnergy hstep hδ current) energy) ∧
      (∀ state, (0, state) ∈ collisionFree → current.family 0 state =
        selectedEnergy hstep hδ current (hamiltonian 0 state)) ∧
      IsJointlyAnalytic δ
        (domainMassNormalizedCandidate current.family (selectedEnergy hstep hδ current)) ∧
      IsFirstIntegralFamily δ
        (domainMassNormalizedCandidate current.family (selectedEnergy hstep hδ current)) :=
  Classical.choose_spec (hstep hδ current.analytic current.firstIntegral)

/-- Apply one selected normalization step to a bundled state. -/
noncomputable def nextNormalizationState
    (hstep : ClassicalNormalizationStep) {δ : ℝ} (hδ : 0 < δ)
    (current : NormalizationState δ) : NormalizationState δ where
  family := domainMassNormalizedCandidate current.family (selectedEnergy hstep hδ current)
  analytic := (selectedEnergy_spec hstep hδ current).2.2.1
  firstIntegral := (selectedEnergy_spec hstep hδ current).2.2.2

/-- The recursively selected sequence of analytic first integrals. -/
noncomputable def normalizationStateSequence
    (hstep : ClassicalNormalizationStep) {δ : ℝ} (hδ : 0 < δ)
    (initial : NormalizationState δ) : ℕ → NormalizationState δ
  | 0 => initial
  | n + 1 => nextNormalizationState hstep hδ
      (normalizationStateSequence hstep hδ initial n)

/-- The energy function selected at each recursive stage. -/
noncomputable def normalizationEnergySequence
    (hstep : ClassicalNormalizationStep) {δ : ℝ} (hδ : 0 < δ)
    (initial : NormalizationState δ) (n : ℕ) : ℝ → ℝ :=
  selectedEnergy hstep hδ (normalizationStateSequence hstep hδ initial n)

/-- The recursively bundled family agrees with the explicit iteration used by the all-orders
endpoint. -/
theorem normalizationStateSequence_family_eq_iterated
    (hstep : ClassicalNormalizationStep) {δ : ℝ} (hδ : 0 < δ)
    (initial : NormalizationState δ) (n : ℕ) :
    (normalizationStateSequence hstep hδ initial n).family =
      iteratedMassNormalization initial.family
        (normalizationEnergySequence hstep hδ initial) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [normalizationStateSequence, nextNormalizationState,
        iteratedMassNormalization_succ, normalizationEnergySequence]
      rw [ih]

/-- A one-step normalization closure theorem supplies the complete all-orders principle. -/
theorem classicalNormalizationPrinciple_of_step
    (hstep : ClassicalNormalizationStep) : ClassicalNormalizationPrinciple := by
  intro δ F hδ hanalytic hfirstIntegral
  let initial : NormalizationState δ := ⟨F, hanalytic, hfirstIntegral⟩
  let energyFunction := normalizationEnergySequence hstep hδ initial
  refine ⟨energyFunction, ?_, ?_, ?_⟩
  · intro n
    rw [← normalizationStateSequence_family_eq_iterated hstep hδ initial n]
    exact (normalizationStateSequence hstep hδ initial n).analytic
  · intro n energy
    exact (selectedEnergy_spec hstep hδ
      (normalizationStateSequence hstep hδ initial n)).1 energy
  · intro n state hcollision
    rw [← normalizationStateSequence_family_eq_iterated hstep hδ initial n]
    exact (selectedEnergy_spec hstep hδ
      (normalizationStateSequence hstep hδ initial n)).2.1 state hcollision

/-- Thus the exact challenge theorem follows from the one-step closure theorem. -/
theorem nonintegrability_of_classicalNormalizationStep
    (hstep : ClassicalNormalizationStep) :
    ¬∃ δ : ℝ, 0 < δ ∧ ∃ F : ℝ → PhaseSpace → ℝ,
      IsJointlyAnalytic δ F ∧ IsFirstIntegralFamily δ F ∧
        IsIndependentSomewhere δ F :=
  nonintegrability_of_classicalNormalizationPrinciple
    (classicalNormalizationPrinciple_of_step hstep)

/-- Final decomposition of the exact theorem into its two remaining reusable inputs. -/
theorem nonintegrability_of_zerothCoefficient_of_massDivision
    (hcoefficient : ClassicalZerothCoefficientPrinciple)
    (hdivision : JointAnalyticMassDivisionPrinciple) :
    ¬∃ δ : ℝ, 0 < δ ∧ ∃ F : ℝ → PhaseSpace → ℝ,
      IsJointlyAnalytic δ F ∧ IsFirstIntegralFamily δ F ∧
        IsIndependentSomewhere δ F :=
  nonintegrability_of_classicalNormalizationStep
    (classicalNormalizationStep_of_zerothCoefficient_of_massDivision
      hcoefficient hdivision)

end LeanPool.PoincareThreeBody
