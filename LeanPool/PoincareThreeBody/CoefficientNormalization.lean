/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.AnalyticNormalization

/-!
# The first Poincaré coefficient-normalization cycle

The dense Poincaré-set obstruction makes the zeroth mass coefficient a local analytic function
of the Kepler Hamiltonian.  This file transfers that action-space statement to a physical lifted
ellipse and instantiates the removable mass quotient.  It is the complete local setup for one
iteration of Poincaré's subtract-and-divide argument.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

/-- On a connected local Kepler energy leaf, the mass-zero candidate is the analytic energy
function constructed from any reference first action on that leaf. -/
theorem IsFirstIntegralFamily.mass_zero_eq_leadingEnergyCoefficient_hamiltonian
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    (hdense : HasDenseClassicalPoincareSet)
    {firstAction eccentricity meanAnomaly periapsisAngle referenceFirstAction : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1)
    (hactionLeaf : ∀ candidateFirstAction ∈ Set.uIcc firstAction referenceFirstAction,
      energyLeafAction
          (delaunayHamiltonian
            ![firstAction,
              angularActionFromEccentricity firstAction eccentricity])
          candidateFirstAction ∈ ProgradeEllipticActions)
    (hapoapsisLeaf : ∀ candidateFirstAction ∈ Set.uIcc firstAction referenceFirstAction,
      candidateFirstAction ^ 2 *
          (1 + eccentricityFromActions
            (energyLeafAction
              (delaunayHamiltonian
                ![firstAction,
                  angularActionFromEccentricity firstAction eccentricity])
              candidateFirstAction)) < 1) :
    let state := liftedDelaunayPhasePoint
      firstAction eccentricity meanAnomaly periapsisAngle
    F 0 state =
      leadingEnergyCoefficient F referenceFirstAction (hamiltonian 0 state) := by
  let state := liftedDelaunayPhasePoint
    firstAction eccentricity meanAnomaly periapsisAngle
  let action : ActionSpace :=
    ![firstAction, angularActionFromEccentricity firstAction eccentricity]
  have hactionCoefficient :=
    IsFirstIntegralFamily.leadingActionCoefficient_eq_leadingEnergyCoefficient
      hδ hanalytic hfirstIntegral hdense
      (action := action) (referenceFirstAction := referenceFirstAction)
      hactionLeaf hapoapsisLeaf
  have hsectionValue :=
    IsFirstIntegralFamily.leadingActionCoefficient_eq_liftedDelaunayPhasePoint
      (angles := (meanAnomaly, periapsisAngle))
      hδ hanalytic hfirstIntegral hfirstAction heccentricity
      heccentricityOne hapoapsis
  have hhamiltonian : hamiltonian 0 state = delaunayHamiltonian action :=
    hamiltonian_zero_liftedDelaunayPhasePoint hfirstAction.ne'
      heccentricity.le heccentricityOne
  dsimp only [state, action] at hsectionValue hhamiltonian ⊢
  calc
    F 0 (liftedDelaunayPhasePoint
        firstAction eccentricity meanAnomaly periapsisAngle) =
        leadingActionCoefficient F
          ![firstAction,
            angularActionFromEccentricity firstAction eccentricity] :=
      hsectionValue.symm
    _ = leadingEnergyCoefficient F referenceFirstAction
          (delaunayHamiltonian
            ![firstAction,
              angularActionFromEccentricity firstAction eccentricity]) :=
      hactionCoefficient
    _ = leadingEnergyCoefficient F referenceFirstAction
          (hamiltonian 0
            (liftedDelaunayPhasePoint
              firstAction eccentricity meanAnomaly periapsisAngle)) := by
      rw [hhamiltonian]

/-- The local energy function used to cancel the zeroth coefficient is analytic at the physical
Kepler energy of the lifted ellipse. -/
theorem IsJointlyAnalytic.analyticAt_localLeadingEnergyCoefficient
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    {firstAction eccentricity meanAnomaly periapsisAngle referenceFirstAction : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hactionReference :
      energyLeafAction
          (delaunayHamiltonian
            ![firstAction,
              angularActionFromEccentricity firstAction eccentricity])
          referenceFirstAction ∈ ProgradeEllipticActions)
    (hapoapsisReference : referenceFirstAction ^ 2 *
        (1 + eccentricityFromActions
          (energyLeafAction
            (delaunayHamiltonian
              ![firstAction,
                angularActionFromEccentricity firstAction eccentricity])
            referenceFirstAction)) < 1) :
    let state := liftedDelaunayPhasePoint
      firstAction eccentricity meanAnomaly periapsisAngle
    AnalyticAt ℝ (leadingEnergyCoefficient F referenceFirstAction)
      (hamiltonian 0 state) := by
  let state := liftedDelaunayPhasePoint
    firstAction eccentricity meanAnomaly periapsisAngle
  let action : ActionSpace :=
    ![firstAction, angularActionFromEccentricity firstAction eccentricity]
  have henergy : hamiltonian 0 state = delaunayHamiltonian action :=
    hamiltonian_zero_liftedDelaunayPhasePoint hfirstAction.ne'
      heccentricity.le heccentricityOne
  dsimp only [state, action] at henergy ⊢
  rw [henergy]
  exact IsJointlyAnalytic.analyticAt_leadingEnergyCoefficient
    hδ hanalytic hactionReference hapoapsisReference

/-- After cancelling the zeroth coefficient by the local analytic energy function, the
mass-normalized candidate is analytic in mass at zero on the selected physical phase slice. -/
theorem IsFirstIntegralFamily.analyticAt_massNormalizedCandidate_localEnergy_massSlice
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (_hfirstIntegral : IsFirstIntegralFamily δ F)
    (_hdense : HasDenseClassicalPoincareSet)
    {firstAction eccentricity meanAnomaly periapsisAngle referenceFirstAction : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1)
    (hactionLeaf : ∀ candidateFirstAction ∈ Set.uIcc firstAction referenceFirstAction,
      energyLeafAction
          (delaunayHamiltonian
            ![firstAction,
              angularActionFromEccentricity firstAction eccentricity])
          candidateFirstAction ∈ ProgradeEllipticActions)
    (hapoapsisLeaf : ∀ candidateFirstAction ∈ Set.uIcc firstAction referenceFirstAction,
      candidateFirstAction ^ 2 *
          (1 + eccentricityFromActions
            (energyLeafAction
              (delaunayHamiltonian
                ![firstAction,
                  angularActionFromEccentricity firstAction eccentricity])
              candidateFirstAction)) < 1) :
    let state := liftedDelaunayPhasePoint
      firstAction eccentricity meanAnomaly periapsisAngle
    AnalyticAt ℝ (fun mass ↦
      massNormalizedCandidate F
        (leadingEnergyCoefficient F referenceFirstAction) mass state) 0 := by
  let state := liftedDelaunayPhasePoint
    firstAction eccentricity meanAnomaly periapsisAngle
  have hcollision : (0, state) ∈ collisionFree :=
    liftedDelaunayPhasePoint_collisionFree_mass_zero hfirstAction.ne'
      heccentricity.le heccentricityOne hapoapsis
  have hdomain : (0, state) ∈ parameterDomain δ :=
    ⟨by simpa using hδ, hcollision⟩
  have hreferenceAction := hactionLeaf referenceFirstAction Set.right_mem_uIcc
  have hreferenceApoapsis :=
    hapoapsisLeaf referenceFirstAction Set.right_mem_uIcc
  have henergyAnalytic :=
    IsJointlyAnalytic.analyticAt_localLeadingEnergyCoefficient
      (meanAnomaly := meanAnomaly) (periapsisAngle := periapsisAngle)
      hδ hanalytic hfirstAction heccentricity heccentricityOne
      hreferenceAction hreferenceApoapsis
  exact analyticAt_massNormalizedCandidate_massSlice
    hanalytic hdomain henergyAnalytic

/-- The same local normalization satisfies the exact subtract-and-divide identity at every mass
on the chosen phase slice. -/
theorem IsFirstIntegralFamily.mass_mul_massNormalizedCandidate_localEnergy
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    (hdense : HasDenseClassicalPoincareSet)
    {firstAction eccentricity meanAnomaly periapsisAngle referenceFirstAction mass : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1)
    (hactionLeaf : ∀ candidateFirstAction ∈ Set.uIcc firstAction referenceFirstAction,
      energyLeafAction
          (delaunayHamiltonian
            ![firstAction,
              angularActionFromEccentricity firstAction eccentricity])
          candidateFirstAction ∈ ProgradeEllipticActions)
    (hapoapsisLeaf : ∀ candidateFirstAction ∈ Set.uIcc firstAction referenceFirstAction,
      candidateFirstAction ^ 2 *
          (1 + eccentricityFromActions
            (energyLeafAction
              (delaunayHamiltonian
                ![firstAction,
                  angularActionFromEccentricity firstAction eccentricity])
              candidateFirstAction)) < 1) :
    let state := liftedDelaunayPhasePoint
      firstAction eccentricity meanAnomaly periapsisAngle
    mass * massNormalizedCandidate F
        (leadingEnergyCoefficient F referenceFirstAction) mass state =
      normalizationResidual F
        (leadingEnergyCoefficient F referenceFirstAction) mass state := by
  let state := liftedDelaunayPhasePoint
    firstAction eccentricity meanAnomaly periapsisAngle
  apply mass_mul_massNormalizedCandidate
  exact IsFirstIntegralFamily.mass_zero_eq_leadingEnergyCoefficient_hamiltonian
    (meanAnomaly := meanAnomaly) (periapsisAngle := periapsisAngle)
    hδ hanalytic hfirstIntegral hdense hfirstAction heccentricity
    heccentricityOne hapoapsis hactionLeaf hapoapsisLeaf

end LeanPool.PoincareThreeBody
