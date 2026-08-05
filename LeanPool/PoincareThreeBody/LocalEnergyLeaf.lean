/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DelaunayAnchorChart
import LeanPool.PoincareThreeBody.EnergyLeafObstruction

/-!
# Local energy leaves at the rational anchor

The interior elliptic action region contains a product box around the rational anchor in
energy/first-action coordinates.  Shrinking the first-action side to an interval ensures that
the whole straight energy-leaf segment back to the anchor remains in the region.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody Set

/-- The first action used at the rational anchor. -/
noncomputable def delaunayAnchorFirstAction : ℝ :=
  1 / Real.sqrt 3

theorem energyLeafAction_anchor :
    energyLeafAction (-2) delaunayAnchorFirstAction = delaunayAnchorAction := by
  funext coordinate
  fin_cases coordinate
  · rfl
  · have hsqrtPos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have hsqrtSq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    change -1 / (2 * (1 / Real.sqrt 3) ^ 2) - (-2) = (1 / 2 : ℝ)
    have hsquare : (1 / Real.sqrt 3 : ℝ) ^ 2 = 1 / 3 := by
      field_simp [hsqrtPos.ne']
      exact hsqrtSq.symm
    rw [hsquare]
    norm_num

/-- The straight energy-leaf action is jointly analytic in energy and first action away from
`L = 0`. -/
theorem analyticAt_energyLeafAction_parameters
    {energy firstAction : ℝ} (hfirstAction : firstAction ≠ 0) :
    AnalyticAt ℝ
      (fun parameters : ℝ × ℝ ↦ energyLeafAction parameters.1 parameters.2)
      (energy, firstAction) := by
  rw [analyticAt_pi_iff]
  intro coordinate
  fin_cases coordinate
  · exact analyticAt_snd
  · change AnalyticAt ℝ
      (fun parameters : ℝ × ℝ ↦
        -1 / (2 * parameters.2 ^ 2) - parameters.1) (energy, firstAction)
    have hdenominator : AnalyticAt ℝ
        (fun parameters : ℝ × ℝ ↦ 2 * parameters.2 ^ 2)
        (energy, firstAction) :=
      analyticAt_const.mul (analyticAt_snd.pow 2)
    have hdenominatorNe : 2 * firstAction ^ 2 ≠ 0 := by
      positivity
    exact analyticAt_const.div hdenominator hdenominatorNe |>.sub analyticAt_fst

/-- Interior ellipticity holds throughout a whole short energy-leaf segment for every nearby
energy/action pair. -/
theorem eventually_energyLeaf_segment_interior :
    ∀ᶠ parameters in nhds ((-2 : ℝ), delaunayAnchorFirstAction),
      ∀ firstAction ∈ Set.uIcc parameters.2 delaunayAnchorFirstAction,
        energyLeafAction parameters.1 firstAction ∈ ProgradeEllipticActions ∧
          firstAction ^ 2 *
            (1 + eccentricityFromActions
              (energyLeafAction parameters.1 firstAction)) < 1 := by
  let actionMap : ℝ × ℝ → ActionSpace := fun parameters ↦
    energyLeafAction parameters.1 parameters.2
  let interiorCondition : Set (ℝ × ℝ) :=
    {parameters | actionMap parameters ∈ ProgradeEllipticActions ∧
      parameters.2 ^ 2 *
        (1 + eccentricityFromActions (actionMap parameters)) < 1}
  have hanchorFirst : delaunayAnchorFirstAction ≠ 0 := by
    exact one_div_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hactionAnalytic : AnalyticAt ℝ actionMap
      ((-2 : ℝ), delaunayAnchorFirstAction) :=
    analyticAt_energyLeafAction_parameters hanchorFirst
  have hanchorAction : actionMap ((-2 : ℝ), delaunayAnchorFirstAction) =
      delaunayAnchorAction := energyLeafAction_anchor
  have hprograde : ∀ᶠ parameters in
      nhds ((-2 : ℝ), delaunayAnchorFirstAction),
      actionMap parameters ∈ ProgradeEllipticActions :=
    hactionAnalytic.continuousAt.eventually
      (isOpen_progradeEllipticActions.mem_nhds
        (hanchorAction.symm ▸ delaunayAnchorAction_prograde))
  have heccentricity : AnalyticAt ℝ
      (fun parameters ↦ eccentricityFromActions (actionMap parameters))
      ((-2 : ℝ), delaunayAnchorFirstAction) := by
    exact (analyticAt_eccentricityFromActions
      (hanchorAction.symm ▸ delaunayAnchorAction_prograde)).comp
        (f := actionMap) hactionAnalytic
  have hfirst : AnalyticAt ℝ (fun parameters : ℝ × ℝ ↦ parameters.2)
      ((-2 : ℝ), delaunayAnchorFirstAction) := analyticAt_snd
  have hapoapsis : ∀ᶠ parameters in
      nhds ((-2 : ℝ), delaunayAnchorFirstAction),
      parameters.2 ^ 2 *
          (1 + eccentricityFromActions (actionMap parameters)) < 1 := by
    have honePlus : AnalyticAt ℝ
        (fun parameters : ℝ × ℝ ↦
          1 + eccentricityFromActions (actionMap parameters))
        ((-2 : ℝ), delaunayAnchorFirstAction) :=
      analyticAt_const.add heccentricity
    have hcontinuous : ContinuousAt
        (fun parameters : ℝ × ℝ ↦ parameters.2 ^ 2 *
          (1 + eccentricityFromActions (actionMap parameters)))
        ((-2 : ℝ), delaunayAnchorFirstAction) :=
      ((hfirst.pow 2).mul honePlus).continuousAt
    apply hcontinuous.eventually_lt continuousAt_const
    rw [hanchorAction]
    change delaunayAnchorAction 0 ^ 2 *
      (1 + eccentricityFromActions delaunayAnchorAction) < 1
    rw [delaunayAnchorAction,
      ← cartesianDelaunayActions_globalEnergySection_neg_two]
    exact globalEnergySection_neg_two_action_apoapsis
  have hinterior : interiorCondition ∈
      nhds ((-2 : ℝ), delaunayAnchorFirstAction) := by
    filter_upwards [hprograde, hapoapsis] with parameters hp ha
    exact ⟨hp, ha⟩
  obtain ⟨energySet, henergySet, firstActionSet, hfirstActionSet, hproduct⟩ :=
    mem_nhds_prod_iff.mp hinterior
  obtain ⟨lower, upper, hanchorInterval, hinterval⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hfirstActionSet
  have heventual : energySet ×ˢ Ioo lower upper ∈
      nhds ((-2 : ℝ), delaunayAnchorFirstAction) := by
    exact prod_mem_nhds henergySet
      (Ioo_mem_nhds hanchorInterval.1 hanchorInterval.2)
  filter_upwards [heventual] with parameters hparameters
  intro firstAction hfirstAction
  have hfirstActionInterval : firstAction ∈ Ioo lower upper := by
    rw [Set.mem_uIcc] at hfirstAction
    rcases hfirstAction with hbetween | hbetween
    · exact ⟨lt_of_lt_of_le hparameters.2.1 hbetween.1,
        lt_of_le_of_lt hbetween.2 hanchorInterval.2⟩
    · exact ⟨lt_of_lt_of_le hanchorInterval.1 hbetween.1,
        lt_of_le_of_lt hbetween.2 hparameters.2.2⟩
  have hpair : (parameters.1, firstAction) ∈
      energySet ×ˢ firstActionSet :=
    ⟨hparameters.1, hinterval hfirstActionInterval⟩
  exact hproduct hpair

/-- On the interior part of the anchor chart, angle independence identifies the phase value with
the action-section representative. -/
theorem IsFirstIntegralFamily.delaunayAnchorChart_eq_leadingActionCoefficient
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    {parameters : DelaunayAnchorParameters}
    (haction : parameters.1 ∈ ProgradeEllipticActions)
    (hapoapsis : parameters.1 0 ^ 2 *
      (1 + eccentricityFromActions parameters.1) < 1) :
    F 0 (delaunayAnchorChart parameters) =
      leadingActionCoefficient F parameters.1 := by
  have hfirstAction : 0 < parameters.1 0 :=
    haction.1.trans haction.2
  have heccentricity : 0 < eccentricityFromActions parameters.1 :=
    eccentricityFromActions_pos haction
  have heccentricityOne : eccentricityFromActions parameters.1 < 1 :=
    eccentricityFromActions_lt_one haction
  have hvalue :=
    IsFirstIntegralFamily.leadingActionCoefficient_eq_liftedDelaunayPhasePoint
      hδ hanalytic hfirstIntegral hfirstAction heccentricity
      heccentricityOne hapoapsis
      (eccentricMeanAnomaly (eccentricityFromActions parameters.1) parameters.2.1,
        parameters.2.2)
  rw [actions_from_eccentricityFromActions haction] at hvalue
  unfold delaunayAnchorChart
  rw [delaunayActionSectionAtAnomaly_eq_liftedDelaunayPhasePoint haction]
  exact hvalue.symm

/-- The mass-zero Hamiltonian in the anchor chart is the Delaunay Hamiltonian of its action
parameters. -/
theorem hamiltonian_zero_delaunayAnchorChart
    {parameters : DelaunayAnchorParameters}
    (haction : parameters.1 ∈ ProgradeEllipticActions) :
    hamiltonian 0 (delaunayAnchorChart parameters) =
      delaunayHamiltonian parameters.1 := by
  have hfirstAction : parameters.1 0 ≠ 0 :=
    (haction.1.trans haction.2).ne'
  have heccentricity : 0 ≤ eccentricityFromActions parameters.1 :=
    eccentricityFromActions_nonneg parameters.1
  have heccentricityOne : eccentricityFromActions parameters.1 < 1 :=
    eccentricityFromActions_lt_one haction
  unfold delaunayAnchorChart
  rw [delaunayActionSectionAtAnomaly_eq_liftedDelaunayPhasePoint haction,
    hamiltonian_zero_liftedDelaunayPhasePoint hfirstAction heccentricity
      heccentricityOne]
  rw [actions_from_eccentricityFromActions haction]

/-- Dense Poincaré resonances make every nearby leading action coefficient equal to the fixed
anchor-section representative on the same energy leaf. -/
theorem IsFirstIntegralFamily.eventually_leadingActionCoefficient_eq_anchorEnergyCoefficient
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    (hdense : HasDenseClassicalPoincareSet) :
    ∀ᶠ action in nhds delaunayAnchorAction,
      leadingActionCoefficient F action =
        leadingEnergyCoefficient F delaunayAnchorFirstAction
          (delaunayHamiltonian action) := by
  let leafParameters : ActionSpace → ℝ × ℝ := fun action ↦
    (delaunayHamiltonian action, action 0)
  have hanchorFirst : delaunayAnchorFirstAction ≠ 0 := by
    exact one_div_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hanchorEnergy : delaunayHamiltonian delaunayAnchorAction = (-2 : ℝ) := by
    rw [← energyLeafAction_anchor]
    exact delaunayHamiltonian_energyLeafAction hanchorFirst
  have hleafAnalytic : AnalyticAt ℝ leafParameters delaunayAnchorAction := by
    have henergy : AnalyticAt ℝ delaunayHamiltonian delaunayAnchorAction := by
      apply analyticAt_delaunayHamiltonian
      simpa only [delaunayAnchorFirstAction, delaunayAnchorAction,
        Matrix.cons_val_zero] using hanchorFirst
    have hfirst : AnalyticAt ℝ (fun action : ActionSpace ↦ action 0)
        delaunayAnchorAction :=
      (ContinuousLinearMap.proj 0 : ActionSpace →L[ℝ] ℝ).analyticAt _
    exact henergy.prod hfirst
  have hleafBase : leafParameters delaunayAnchorAction =
      ((-2 : ℝ), delaunayAnchorFirstAction) := by
    apply Prod.ext
    · exact hanchorEnergy
    · rfl
  have heventual : ∀ᶠ action in nhds delaunayAnchorAction,
      ∀ firstAction ∈ Set.uIcc (leafParameters action).2
          delaunayAnchorFirstAction,
        energyLeafAction (leafParameters action).1 firstAction ∈
            ProgradeEllipticActions ∧
          firstAction ^ 2 *
            (1 + eccentricityFromActions
              (energyLeafAction (leafParameters action).1 firstAction)) < 1 := by
    have htarget := eventually_energyLeaf_segment_interior
    rw [← hleafBase] at htarget
    exact hleafAnalytic.continuousAt.eventually htarget
  filter_upwards [heventual] with action hsegment
  apply IsFirstIntegralFamily.leadingActionCoefficient_eq_leadingEnergyCoefficient
    hδ hanalytic hfirstIntegral hdense
  · intro firstAction hfirstAction
    exact (hsegment firstAction hfirstAction).1
  · intro firstAction hfirstAction
    exact (hsegment firstAction hfirstAction).2

/-- The canonical global energy section agrees locally with the fixed-anchor energy
representative.  Local openness supplies a nearby Delaunay preimage of every section point. -/
theorem IsFirstIntegralFamily.eventually_globalEnergyCoefficient_eq_anchorEnergyCoefficient
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    (hdense : HasDenseClassicalPoincareSet) :
    ∀ᶠ energy in nhds (-2 : ℝ),
      globalEnergyCoefficient F energy =
        leadingEnergyCoefficient F delaunayAnchorFirstAction energy := by
  have hleading :=
    IsFirstIntegralFamily.eventually_leadingActionCoefficient_eq_anchorEnergyCoefficient
      hδ hanalytic hfirstIntegral hdense
  have hactionMap : AnalyticAt ℝ
      (fun parameters : DelaunayAnchorParameters ↦ parameters.1)
      delaunayAnchorParameters :=
    (ContinuousLinearMap.fst ℝ ActionSpace (ℝ × ℝ)).analyticAt _
  have hleadingParameters : ∀ᶠ parameters in nhds delaunayAnchorParameters,
      leadingActionCoefficient F parameters.1 =
        leadingEnergyCoefficient F delaunayAnchorFirstAction
          (delaunayHamiltonian parameters.1) :=
    hactionMap.continuousAt.eventually hleading
  have hprograde : ∀ᶠ parameters in nhds delaunayAnchorParameters,
      parameters.1 ∈ ProgradeEllipticActions :=
    hactionMap.continuousAt.eventually
      (isOpen_progradeEllipticActions.mem_nhds delaunayAnchorAction_prograde)
  have heccentricity : AnalyticAt ℝ
      (fun parameters : DelaunayAnchorParameters ↦
        eccentricityFromActions parameters.1) delaunayAnchorParameters := by
    exact (analyticAt_eccentricityFromActions delaunayAnchorAction_prograde).comp
      (f := fun parameters : DelaunayAnchorParameters ↦ parameters.1) hactionMap
  have hfirst : AnalyticAt ℝ
      (fun parameters : DelaunayAnchorParameters ↦ parameters.1 0)
      delaunayAnchorParameters :=
    ((ContinuousLinearMap.proj 0 : ActionSpace →L[ℝ] ℝ).analyticAt _).comp
      (f := fun parameters : DelaunayAnchorParameters ↦ parameters.1) hactionMap
  have hapoapsis : ∀ᶠ parameters in nhds delaunayAnchorParameters,
      parameters.1 0 ^ 2 *
        (1 + eccentricityFromActions parameters.1) < 1 := by
    have honePlus : AnalyticAt ℝ
        (fun parameters : DelaunayAnchorParameters ↦
          1 + eccentricityFromActions parameters.1) delaunayAnchorParameters :=
      analyticAt_const.add heccentricity
    have hcontinuous := ((hfirst.pow 2).mul honePlus).continuousAt
    apply hcontinuous.eventually_lt continuousAt_const
    change delaunayAnchorAction 0 ^ 2 *
      (1 + eccentricityFromActions delaunayAnchorAction) < 1
    rw [delaunayAnchorAction,
      ← cartesianDelaunayActions_globalEnergySection_neg_two]
    exact globalEnergySection_neg_two_action_apoapsis
  let goodParameters : Set DelaunayAnchorParameters :=
    {parameters | parameters.1 ∈ ProgradeEllipticActions ∧
      parameters.1 0 ^ 2 * (1 + eccentricityFromActions parameters.1) < 1 ∧
      leadingActionCoefficient F parameters.1 =
        leadingEnergyCoefficient F delaunayAnchorFirstAction
          (delaunayHamiltonian parameters.1)}
  have hgood : goodParameters ∈ nhds delaunayAnchorParameters := by
    filter_upwards [hprograde, hapoapsis, hleadingParameters] with parameters hp ha hl
    exact ⟨hp, ha, hl⟩
  have hstatePreimage :=
    eventually_exists_delaunayAnchorChart_preimage hgood
  have henergyPreimage : ∀ᶠ energy in nhds (-2 : ℝ),
      ∃ parameters ∈ goodParameters,
        delaunayAnchorChart parameters = globalEnergySection energy :=
    (analyticAt_globalEnergySection (-2)).continuousAt.eventually hstatePreimage
  filter_upwards [henergyPreimage] with energy hpreimage
  rcases hpreimage with ⟨parameters, hparameters, hchart⟩
  rcases hparameters with ⟨haction, hapo, hleadingEqual⟩
  unfold globalEnergyCoefficient
  rw [← hchart,
    IsFirstIntegralFamily.delaunayAnchorChart_eq_leadingActionCoefficient
      hδ hanalytic hfirstIntegral haction hapo,
    hleadingEqual]
  congr 1
  rw [← hamiltonian_zero_delaunayAnchorChart haction, hchart,
    hamiltonian_zero_globalEnergySection]

/-- Density of the classical Poincaré set proves factorization on a genuine phase-space
neighborhood of the rational anchor. -/
theorem localZerothCoefficientFactorizationAtAnchor_of_densePoincareSet
    (hdense : HasDenseClassicalPoincareSet) :
    LocalZerothCoefficientFactorizationAtAnchor := by
  intro δ F hδ hanalytic hfirstIntegral
  have hleading :=
    IsFirstIntegralFamily.eventually_leadingActionCoefficient_eq_anchorEnergyCoefficient
      hδ hanalytic hfirstIntegral hdense
  have hglobal :=
    IsFirstIntegralFamily.eventually_globalEnergyCoefficient_eq_anchorEnergyCoefficient
      hδ hanalytic hfirstIntegral hdense
  have hactionMap : AnalyticAt ℝ
      (fun parameters : DelaunayAnchorParameters ↦ parameters.1)
      delaunayAnchorParameters :=
    (ContinuousLinearMap.fst ℝ ActionSpace (ℝ × ℝ)).analyticAt _
  have hleadingParameters := hactionMap.continuousAt.eventually hleading
  have hprograde : ∀ᶠ parameters in nhds delaunayAnchorParameters,
      parameters.1 ∈ ProgradeEllipticActions :=
    hactionMap.continuousAt.eventually
      (isOpen_progradeEllipticActions.mem_nhds delaunayAnchorAction_prograde)
  have heccentricity : AnalyticAt ℝ
      (fun parameters : DelaunayAnchorParameters ↦
        eccentricityFromActions parameters.1) delaunayAnchorParameters := by
    exact (analyticAt_eccentricityFromActions delaunayAnchorAction_prograde).comp
      (f := fun parameters : DelaunayAnchorParameters ↦ parameters.1) hactionMap
  have hfirst : AnalyticAt ℝ
      (fun parameters : DelaunayAnchorParameters ↦ parameters.1 0)
      delaunayAnchorParameters :=
    ((ContinuousLinearMap.proj 0 : ActionSpace →L[ℝ] ℝ).analyticAt _).comp
      (f := fun parameters : DelaunayAnchorParameters ↦ parameters.1) hactionMap
  have hapoapsis : ∀ᶠ parameters in nhds delaunayAnchorParameters,
      parameters.1 0 ^ 2 *
        (1 + eccentricityFromActions parameters.1) < 1 := by
    have honePlus : AnalyticAt ℝ
        (fun parameters : DelaunayAnchorParameters ↦
          1 + eccentricityFromActions parameters.1) delaunayAnchorParameters :=
      analyticAt_const.add heccentricity
    have hcontinuous := ((hfirst.pow 2).mul honePlus).continuousAt
    apply hcontinuous.eventually_lt continuousAt_const
    change delaunayAnchorAction 0 ^ 2 *
      (1 + eccentricityFromActions delaunayAnchorAction) < 1
    rw [delaunayAnchorAction,
      ← cartesianDelaunayActions_globalEnergySection_neg_two]
    exact globalEnergySection_neg_two_action_apoapsis
  have henergyAnalytic : AnalyticAt ℝ
      (fun parameters : DelaunayAnchorParameters ↦
        delaunayHamiltonian parameters.1) delaunayAnchorParameters := by
    have hanchorFirst : delaunayAnchorAction 0 ≠ 0 :=
      (delaunayAnchorAction_prograde.1.trans
        delaunayAnchorAction_prograde.2).ne'
    exact (analyticAt_delaunayHamiltonian hanchorFirst).comp
      (f := fun parameters : DelaunayAnchorParameters ↦ parameters.1) hactionMap
  have henergyBase : delaunayHamiltonian delaunayAnchorAction = (-2 : ℝ) := by
    rw [← energyLeafAction_anchor]
    apply delaunayHamiltonian_energyLeafAction
    exact one_div_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hglobalParameters : ∀ᶠ parameters in nhds delaunayAnchorParameters,
      globalEnergyCoefficient F (delaunayHamiltonian parameters.1) =
        leadingEnergyCoefficient F delaunayAnchorFirstAction
          (delaunayHamiltonian parameters.1) := by
    have htarget := hglobal
    rw [← henergyBase] at htarget
    exact henergyAnalytic.continuousAt.eventually htarget
  have hparameterEquality : ∀ᶠ parameters in nhds delaunayAnchorParameters,
      F 0 (delaunayAnchorChart parameters) =
        globalEnergyCoefficient F
          (hamiltonian 0 (delaunayAnchorChart parameters)) := by
    filter_upwards [hprograde, hapoapsis, hleadingParameters,
      hglobalParameters] with parameters hp ha hl hg
    rw [IsFirstIntegralFamily.delaunayAnchorChart_eq_leadingActionCoefficient
      hδ hanalytic hfirstIntegral hp ha,
      hamiltonian_zero_delaunayAnchorChart hp, hl, ← hg]
  rw [← map_delaunayAnchorChart_nhds]
  exact hparameterEquality

/-- The classical dense resonant set now supplies the complete global zeroth-coefficient
factorization. -/
theorem globalZerothCoefficientFactorization_of_densePoincareSet
    (hdense : HasDenseClassicalPoincareSet) :
    GlobalZerothCoefficientFactorization :=
  localZerothCoefficientFactorizationAtAnchor_iff_global.mp
    (localZerothCoefficientFactorizationAtAnchor_of_densePoincareSet hdense)

/-- Conditional final form: the exact challenge follows from the sole remaining classical
celestial-mechanics input, density of the Poincaré set. -/
theorem nonintegrability_of_denseClassicalPoincareSet
    (hdense : HasDenseClassicalPoincareSet) :
    ¬∃ δ : ℝ, 0 < δ ∧ ∃ F : ℝ → PhaseSpace → ℝ,
      IsJointlyAnalytic δ F ∧ IsFirstIntegralFamily δ F ∧
        IsIndependentSomewhere δ F :=
  nonintegrability_of_globalZerothCoefficientFactorization
    (globalZerothCoefficientFactorization_of_densePoincareSet hdense)

/-- The exact challenge follows from the reduced analytic nonidentity form of Poincaré's
disturbing-function calculation. -/
theorem nonintegrability_of_analytic_separation
    (hseparation : HasAnalyticSeparatingResonantAverages) :
    ¬∃ δ : ℝ, 0 < δ ∧ ∃ F : ℝ → PhaseSpace → ℝ,
      IsJointlyAnalytic δ F ∧ IsFirstIntegralFamily δ F ∧
        IsIndependentSomewhere δ F :=
  nonintegrability_of_denseClassicalPoincareSet
    (hasDenseClassicalPoincareSet_of_analytic_separation hseparation)

end LeanPool.PoincareThreeBody
