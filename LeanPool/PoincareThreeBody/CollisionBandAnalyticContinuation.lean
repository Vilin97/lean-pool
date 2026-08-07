/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.CollisionBandObstruction
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Analytic continuation from the collision band

For each fixed eccentricity, the leading wedge is analytic in the first action.  Its vanishing on
the nonempty collision band therefore extends to the entire connected interior first-action
interval.
-/

namespace LeanPool.PoincareThreeBody

open Filter Set Topology

/-- The raw open interval of positive first actions whose apoapsis remains inside the unit orbit. -/
def interiorFirstActionSet (eccentricity : ℝ) : Set ℝ :=
  {firstAction | 0 < firstAction ∧ firstAction ^ 2 * (1 + eccentricity) < 1}

theorem isOpen_interiorFirstActionSet (eccentricity : ℝ) :
    IsOpen (interiorFirstActionSet eccentricity) := by
  exact (isOpen_lt continuous_const continuous_id).and
    (isOpen_lt ((continuous_id.pow 2).mul continuous_const) continuous_const)

theorem isConnected_interiorFirstActionSet
    {eccentricity : ℝ} (heccentricity : 0 < eccentricity)
    (heccentricityOne : eccentricity < 1) :
    IsConnected (interiorFirstActionSet eccentricity) := by
  have hhalf : (0 : ℝ) < 1 / 2 ∧
      (1 / 2 : ℝ) ^ 2 * (1 + eccentricity) < 1 := by
    constructor
    · norm_num
    · nlinarith
  refine ⟨⟨1 / 2, hhalf⟩, Set.OrdConnected.isPreconnected ?_⟩
  rw [Set.ordConnected_iff]
  intro x hx z hz hxz y hy
  have hyPositive : 0 < y := hx.1.trans_le hy.1
  have hzNonnegative : 0 ≤ z := hz.1.le
  have hySquare : y ^ 2 ≤ z ^ 2 := (sq_le_sq₀ hyPositive.le hzNonnegative).mpr hy.2
  have hfactor : 0 ≤ 1 + eccentricity := by linarith
  exact ⟨hyPositive,
    (mul_le_mul_of_nonneg_right hySquare hfactor).trans_lt hz.2⟩

/-- The leading-order wedge obstruction along the action line of fixed eccentricity. -/
noncomputable def fixedEccentricityWedge
    (F : ℝ → PhaseSpace → ℝ) (eccentricity firstAction : ℝ) : ℝ :=
  wedge (delaunayFrequency firstAction)
    (leadingActionDifferential F
      (fixedEccentricityAction eccentricity firstAction))

theorem analyticAt_fixedEccentricityAction
    (eccentricity firstAction : ℝ) :
    AnalyticAt ℝ (fixedEccentricityAction eccentricity) firstAction := by
  rw [analyticAt_pi_iff]
  intro coordinate
  fin_cases coordinate
  · exact analyticAt_id
  · change AnalyticAt ℝ
      (fun candidate ↦ candidate * Real.sqrt (1 - eccentricity ^ 2)) firstAction
    exact analyticAt_id.mul analyticAt_const

theorem analyticAt_delaunayFrequency
    {firstAction : ℝ} (hfirstAction : firstAction ≠ 0) :
    AnalyticAt ℝ delaunayFrequency firstAction := by
  rw [analyticAt_pi_iff]
  intro coordinate
  fin_cases coordinate
  · change AnalyticAt ℝ (fun candidate : ℝ ↦ 1 / candidate ^ 3) firstAction
    exact analyticAt_const.div (analyticAt_id.pow 3) (pow_ne_zero 3 hfirstAction)
  · exact analyticAt_const

theorem IsJointlyAnalytic.analyticAt_fixedEccentricityWedge
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    {eccentricity firstAction : ℝ}
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hfirstAction : firstAction ∈ interiorFirstActionSet eccentricity) :
    AnalyticAt ℝ (fixedEccentricityWedge F eccentricity) firstAction := by
  let action := fixedEccentricityAction eccentricity firstAction
  have haction : action ∈ ProgradeEllipticActions := by
    exact ⟨angularActionFromEccentricity_pos hfirstAction.1 heccentricity
        heccentricityOne,
      angularActionFromEccentricity_lt_firstAction hfirstAction.1 heccentricity⟩
  have heRecover : eccentricityFromActions action = eccentricity :=
    eccentricityFromActions_angularActionFromEccentricity hfirstAction.1
      heccentricity.le heccentricityOne
  have hapoapsis : action 0 ^ 2 * (1 + eccentricityFromActions action) < 1 := by
    rw [heRecover]
    exact hfirstAction.2
  have hactionAnalytic := analyticAt_fixedEccentricityAction eccentricity firstAction
  have hdifferential := (IsJointlyAnalytic.analyticAt_leadingActionDifferential
    hδ hanalytic haction hapoapsis).comp hactionAnalytic
  have hfrequency := analyticAt_delaunayFrequency hfirstAction.1.ne'
  have hfrequencyZero : AnalyticAt ℝ (fun candidate ↦ delaunayFrequency candidate 0)
      firstAction := analyticAt_pi_iff.mp hfrequency 0
  have hfrequencyOne : AnalyticAt ℝ (fun candidate ↦ delaunayFrequency candidate 1)
      firstAction := analyticAt_pi_iff.mp hfrequency 1
  have hdifferentialZero : AnalyticAt ℝ (fun candidate ↦
      leadingActionDifferential F (fixedEccentricityAction eccentricity candidate) 0)
      firstAction := analyticAt_pi_iff.mp hdifferential 0
  have hdifferentialOne : AnalyticAt ℝ (fun candidate ↦
      leadingActionDifferential F (fixedEccentricityAction eccentricity candidate) 1)
      firstAction := analyticAt_pi_iff.mp hdifferential 1
  unfold fixedEccentricityWedge wedge
  exact (hfrequencyZero.mul hdifferentialOne).sub
    (hfrequencyOne.mul hdifferentialZero)

theorem collisionBandInteriorPositiveAction_nonempty
    {eccentricity : ℝ} (heccentricity : 0 < eccentricity)
    (heccentricityOne : eccentricity < 1) :
    Nonempty (CollisionBandInteriorPositiveAction eccentricity) := by
  let upperSquare := 1 / (1 + eccentricity)
  have hfactor : 0 < 1 + eccentricity := by linarith
  have hupperHalf : (1 / 2 : ℝ) < upperSquare := by
    dsimp [upperSquare]
    rw [lt_div_iff₀ hfactor]
    nlinarith
  let square := ((1 / 2 : ℝ) + upperSquare) / 2
  have hsquareHalf : (1 / 2 : ℝ) < square := by
    dsimp [square]
    linarith
  have hsquareUpper : square < upperSquare := by
    dsimp [square]
    linarith
  have hsquarePositive : 0 < square := (by linarith : 0 < square)
  let firstAction := Real.sqrt square
  have hfirstAction : 0 < firstAction := Real.sqrt_pos.mpr hsquarePositive
  have hfirstActionSq : firstAction ^ 2 = square := Real.sq_sqrt hsquarePositive.le
  have hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1 := by
    rw [hfirstActionSq]
    exact (lt_div_iff₀ hfactor).mp hsquareUpper
  exact ⟨⟨⟨⟨firstAction, hfirstAction⟩, hapoapsis⟩, by
    rw [hfirstActionSq]
    exact hsquareHalf⟩⟩

/-- The collision-band obstruction analytically continues to every interior first action. -/
theorem IsFirstIntegralFamily.wedge_leadingActionDifferential_eq_zero_of_collisionBand
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    {eccentricity firstAction : ℝ}
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hfirstAction : firstAction ∈ interiorFirstActionSet eccentricity) :
    fixedEccentricityWedge F eccentricity firstAction = 0 := by
  let obstruction := fixedEccentricityWedge F eccentricity
  let domain := interiorFirstActionSet eccentricity
  have hanalyticOn : AnalyticOnNhd ℝ obstruction domain := by
    intro candidate hcandidate
    exact IsJointlyAnalytic.analyticAt_fixedEccentricityWedge
      hδ hanalytic heccentricity heccentricityOne hcandidate
  let bandAction := Classical.choice
    (collisionBandInteriorPositiveAction_nonempty heccentricity heccentricityOne)
  let center := bandAction.1.1.1
  have hcenterDomain : center ∈ domain := by
    exact ⟨bandAction.1.1.2, bandAction.1.2⟩
  have hcenterBand : (1 / 2 : ℝ) < center ^ 2 := bandAction.2
  have heventuallyZero : obstruction =ᶠ[𝓝 center] 0 := by
    have hopen : IsOpen (domain ∩ {candidate : ℝ | 1 / 2 < candidate ^ 2}) :=
      (isOpen_interiorFirstActionSet eccentricity).inter
        (isOpen_lt continuous_const (continuous_id.pow 2))
    filter_upwards [hopen.mem_nhds ⟨hcenterDomain, hcenterBand⟩]
      with candidate hcandidate
    let candidateAction : CollisionBandInteriorPositiveAction eccentricity :=
      ⟨⟨⟨candidate, hcandidate.1.1⟩, hcandidate.1.2⟩, hcandidate.2⟩
    exact IsFirstIntegralFamily.wedge_leadingActionDifferential_eq_zero_on_collisionBand
      hδ hanalytic hfirstIntegral heccentricity heccentricityOne candidateAction
  exact hanalyticOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isConnected_interiorFirstActionSet heccentricity heccentricityOne).isPreconnected
      hcenterDomain heventuallyZero hfirstAction

/-- Global action-space form of the collision-band obstruction. -/
theorem IsFirstIntegralFamily.wedge_leadingActionDifferential_eq_zero_of_collisionBand_global
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions)
    (hapoapsis : action 0 ^ 2 * (1 + eccentricityFromActions action) < 1) :
    wedge (delaunayFrequency (action 0))
      (leadingActionDifferential F action) = 0 := by
  let eccentricity := eccentricityFromActions action
  have heccentricity : 0 < eccentricity := eccentricityFromActions_pos haction
  have heccentricityOne : eccentricity < 1 := eccentricityFromActions_lt_one haction
  have hfirstAction : action 0 ∈ interiorFirstActionSet eccentricity :=
    ⟨haction.1.trans haction.2, hapoapsis⟩
  have hobstruction :=
    IsFirstIntegralFamily.wedge_leadingActionDifferential_eq_zero_of_collisionBand
      hδ hanalytic hfirstIntegral heccentricity heccentricityOne hfirstAction
  have hrecover : fixedEccentricityAction eccentricity (action 0) = action :=
    actions_from_eccentricityFromActions haction
  unfold fixedEccentricityWedge at hobstruction
  rwa [hrecover] at hobstruction

end LeanPool.PoincareThreeBody
