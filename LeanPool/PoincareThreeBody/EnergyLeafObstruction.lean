/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.LeadingObstruction
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Constancy of the leading coefficient on Kepler energy leaves

The coordinate change `(L,E) ↦ (L,-1/(2L²)-E)` straightens the level sets of the rotating
Kepler Hamiltonian.  The dense-resonance obstruction says exactly that the derivative of the
leading coefficient in the `L` direction at fixed `E` vanishes.  The mean-value inequality then
makes that coefficient constant on every connected energy-leaf segment contained in the
interior elliptic region.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

/-- The Delaunay action on the Kepler energy leaf `E` with first action `L`. -/
noncomputable def energyLeafAction (energy firstAction : ℝ) : ActionSpace :=
  ![firstAction, -1 / (2 * firstAction ^ 2) - energy]

@[simp] theorem energyLeafAction_zero (energy firstAction : ℝ) :
    energyLeafAction energy firstAction 0 = firstAction :=
  rfl

@[simp] theorem energyLeafAction_one (energy firstAction : ℝ) :
    energyLeafAction energy firstAction 1 = -1 / (2 * firstAction ^ 2) - energy :=
  rfl

/-- The straightened leaf really has the prescribed Delaunay energy. -/
theorem delaunayHamiltonian_energyLeafAction
    {energy firstAction : ℝ} (_hfirstAction : firstAction ≠ 0) :
    delaunayHamiltonian (energyLeafAction energy firstAction) = energy := by
  unfold delaunayHamiltonian energyLeafAction
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Tangent vector to a straightened Kepler energy leaf. -/
theorem hasDerivAt_energyLeafAction
    (energy : ℝ) {firstAction : ℝ} (hfirstAction : firstAction ≠ 0) :
    HasDerivAt (energyLeafAction energy)
      ![1, 1 / firstAction ^ 3] firstAction := by
  rw [hasDerivAt_pi]
  intro coordinate
  fin_cases coordinate
  · simpa [energyLeafAction] using hasDerivAt_id' firstAction
  · simpa [energyLeafAction] using
      hasDerivAt_delaunayHamiltonian_firstAction hfirstAction energy

/-- The wedge obstruction is precisely vanishing of the candidate differential along a
fixed-energy tangent. -/
theorem dot_energyLeafTangent_eq_zero_of_wedge_frequency_eq_zero
    {firstAction : ℝ} {differential : ActionSpace}
    (hwedge : wedge (delaunayFrequency firstAction) differential = 0) :
    dot differential ![1, 1 / firstAction ^ 3] = 0 := by
  rw [dot_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold wedge delaunayFrequency at hwedge
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hwedge
  linarith

/-- Under the classical disturbing-function nondegeneracy input, the leading coefficient has
zero derivative in the `L` direction while its Kepler energy is held fixed. -/
theorem IsFirstIntegralFamily.hasDerivAt_leadingActionCoefficient_energyLeaf_zero
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    (hnondegenerate : ClassicalDisturbingNondegeneracy)
    {energy firstAction : ℝ}
    (haction : energyLeafAction energy firstAction ∈ ProgradeEllipticActions)
    (hapoapsis :
      firstAction ^ 2 *
          (1 + eccentricityFromActions (energyLeafAction energy firstAction)) < 1) :
    HasDerivAt
      (fun candidate ↦ leadingActionCoefficient F (energyLeafAction energy candidate))
      0 firstAction := by
  let action := energyLeafAction energy firstAction
  have hfirstAction : firstAction ≠ 0 := (haction.1.trans haction.2).ne'
  have hcoefficient : DifferentiableAt ℝ (leadingActionCoefficient F) action :=
    (IsJointlyAnalytic.analyticAt_leadingActionCoefficient
      hδ hanalytic haction hapoapsis).differentiableAt
  have hcurve := hasDerivAt_energyLeafAction energy hfirstAction
  have hcomposition := hcoefficient.hasFDerivAt.comp_hasDerivAt firstAction hcurve
  apply hcomposition.congr_deriv
  rw [fderiv_leadingActionCoefficient_eq_actionCovector]
  rw [actionCovector_apply]
  apply dot_energyLeafTangent_eq_zero_of_wedge_frequency_eq_zero
  change wedge (delaunayFrequency (action 0))
    (leadingActionDifferential F action) = 0
  exact IsFirstIntegralFamily.wedge_leadingActionDifferential_eq_zero
    hδ hanalytic hfirstIntegral hnondegenerate haction hapoapsis

/-- The leading coefficient is constant between two actions on the same Kepler energy leaf,
provided the whole intervening leaf segment stays in the interior collision-free elliptic chart. -/
theorem IsFirstIntegralFamily.leadingActionCoefficient_eq_of_same_energyLeaf
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    (hnondegenerate : ClassicalDisturbingNondegeneracy)
    {energy firstAction₁ firstAction₂ : ℝ}
    (haction : ∀ firstAction ∈ Set.uIcc firstAction₁ firstAction₂,
      energyLeafAction energy firstAction ∈ ProgradeEllipticActions)
    (hapoapsis : ∀ firstAction ∈ Set.uIcc firstAction₁ firstAction₂,
      firstAction ^ 2 *
          (1 + eccentricityFromActions (energyLeafAction energy firstAction)) < 1) :
    leadingActionCoefficient F (energyLeafAction energy firstAction₁) =
      leadingActionCoefficient F (energyLeafAction energy firstAction₂) := by
  let observable : ℝ → ℝ := fun firstAction ↦
    leadingActionCoefficient F (energyLeafAction energy firstAction)
  have hdifferentiable : ∀ firstAction ∈ Set.uIcc firstAction₁ firstAction₂,
      DifferentiableAt ℝ observable firstAction := by
    intro firstAction hfirstAction
    exact (IsFirstIntegralFamily.hasDerivAt_leadingActionCoefficient_energyLeaf_zero
      hδ hanalytic hfirstIntegral hnondegenerate
      (haction firstAction hfirstAction) (hapoapsis firstAction hfirstAction)).differentiableAt
  have hfderivZero : ∀ firstAction ∈ Set.uIcc firstAction₁ firstAction₂,
      fderiv ℝ observable firstAction = 0 := by
    intro firstAction hfirstAction
    have hderivative :=
      (IsFirstIntegralFamily.hasDerivAt_leadingActionCoefficient_energyLeaf_zero
      hδ hanalytic hfirstIntegral hnondegenerate
      (haction firstAction hfirstAction)
      (hapoapsis firstAction hfirstAction)).hasFDerivAt.fderiv
    change fderiv ℝ
      (fun candidate ↦ leadingActionCoefficient F (energyLeafAction energy candidate))
        firstAction = 0
    rw [hderivative]
    apply ContinuousLinearMap.ext
    intro direction
    simp
  have hbound := Convex.norm_image_sub_le_of_norm_fderiv_le
    hdifferentiable
    (fun firstAction hfirstAction ↦ by rw [hfderivZero firstAction hfirstAction, norm_zero])
    (convex_uIcc firstAction₁ firstAction₂)
    (Set.left_mem_uIcc) (Set.right_mem_uIcc) (C := 0)
  have hnorm : ‖observable firstAction₂ - observable firstAction₁‖ = 0 := by
    apply le_antisymm
    · simpa using hbound
    · exact norm_nonneg _
  have hequal : observable firstAction₂ = observable firstAction₁ :=
    sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  exact hequal.symm

/-- The explicit inverse relation between the original action coordinates and the straightened
`(L,E)` coordinates. -/
theorem energyLeafAction_delaunayHamiltonian (action : ActionSpace) :
    energyLeafAction (delaunayHamiltonian action) (action 0) = action := by
  funext coordinate
  fin_cases coordinate
  · rfl
  · simp [energyLeafAction, delaunayHamiltonian]

/-- A one-variable representative of the leading coefficient, obtained by meeting each nearby
energy leaf at one fixed reference value of the first action. -/
noncomputable def leadingEnergyCoefficient
    (F : ℝ → PhaseSpace → ℝ) (referenceFirstAction energy : ℝ) : ℝ :=
  leadingActionCoefficient F (energyLeafAction energy referenceFirstAction)

/-- The explicit fixed-`L` energy section is analytic. -/
theorem analyticAt_energyLeafAction
    (referenceFirstAction energy : ℝ) :
    AnalyticAt ℝ (fun candidateEnergy ↦
      energyLeafAction candidateEnergy referenceFirstAction) energy := by
  apply AnalyticAt.pi
  intro coordinate
  fin_cases coordinate
  · exact analyticAt_const
  · exact analyticAt_const.sub analyticAt_id

/-- The energy representative is analytic wherever its reference section remains in the
interior elliptic chart. -/
theorem IsJointlyAnalytic.analyticAt_leadingEnergyCoefficient
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    {referenceFirstAction energy : ℝ}
    (haction : energyLeafAction energy referenceFirstAction ∈ ProgradeEllipticActions)
    (hapoapsis : referenceFirstAction ^ 2 *
        (1 + eccentricityFromActions
          (energyLeafAction energy referenceFirstAction)) < 1) :
    AnalyticAt ℝ (leadingEnergyCoefficient F referenceFirstAction) energy := by
  change AnalyticAt ℝ
    (fun candidateEnergy ↦ leadingActionCoefficient F
      (energyLeafAction candidateEnergy referenceFirstAction)) energy
  exact (IsJointlyAnalytic.analyticAt_leadingActionCoefficient
    hδ hanalytic haction hapoapsis).comp
      (f := fun candidateEnergy ↦
        energyLeafAction candidateEnergy referenceFirstAction)
      (analyticAt_energyLeafAction referenceFirstAction energy)

/-- On any connected energy-leaf segment inside the chart, the leading action coefficient is
the analytic one-variable energy representative based at the other endpoint.  This is the local
functional-dependence statement used in Poincaré's coefficient normalization. -/
theorem IsFirstIntegralFamily.leadingActionCoefficient_eq_leadingEnergyCoefficient
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    (hnondegenerate : ClassicalDisturbingNondegeneracy)
    {action : ActionSpace} {referenceFirstAction : ℝ}
    (haction : ∀ firstAction ∈ Set.uIcc (action 0) referenceFirstAction,
      energyLeafAction (delaunayHamiltonian action) firstAction ∈
        ProgradeEllipticActions)
    (hapoapsis : ∀ firstAction ∈ Set.uIcc (action 0) referenceFirstAction,
      firstAction ^ 2 *
          (1 + eccentricityFromActions
            (energyLeafAction (delaunayHamiltonian action) firstAction)) < 1) :
    leadingActionCoefficient F action =
      leadingEnergyCoefficient F referenceFirstAction
        (delaunayHamiltonian action) := by
  have hconstant :=
    IsFirstIntegralFamily.leadingActionCoefficient_eq_of_same_energyLeaf
      hδ hanalytic hfirstIntegral hnondegenerate haction hapoapsis
  rw [energyLeafAction_delaunayHamiltonian] at hconstant
  exact hconstant

end LeanPool.PoincareThreeBody
