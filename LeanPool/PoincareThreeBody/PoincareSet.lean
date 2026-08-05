/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DenseResonantObstruction

/-!
# The classical Poincaré set

The classical proof does not require nonvanishing at every resonant action.  It requires the set
of resonant actions carrying a nonzero disturbing coefficient to be a uniqueness set; density is
a convenient sufficient formulation in the real-analytic setting developed here.  This file
defines that set intrinsically in the full two-dimensional action region and proves the resulting
leading-coefficient obstruction.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

/-- Prograde, noncircular elliptic actions whose entire ellipse stays inside the unit primary
orbit. -/
def InteriorProgradeEllipticActions : Set ActionSpace :=
  {action | action ∈ ProgradeEllipticActions ∧
    action 0 ^ 2 * (1 + eccentricityFromActions action) < 1}

/-- An interior prograde elliptic action, as a topological subtype. -/
abbrev InteriorProgradeEllipticAction :=
  {action : ActionSpace // action ∈ InteriorProgradeEllipticActions}

/-- The classical Poincaré set: rational Kepler resonances at which the disturbing average has a
nonzero orientation derivative. -/
def classicalPoincareSet : Set InteriorProgradeEllipticAction :=
  {action | ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
    action.1 0 = resonantFirstAction p q ∧
    ∃ orientation,
      deriv
        (resonantDisturbingAverage p q
          (eccentricityFromActions action.1)) orientation ≠ 0}

/-- The exact classical celestial-mechanics input used by the density argument. -/
def HasDenseClassicalPoincareSet : Prop :=
  Dense classicalPoincareSet

/-- A stronger sufficient condition: every interior positive rational resonance has a
nonconstant disturbing average as the relative apsidal orientation varies. -/
def ClassicalDisturbingNondegeneracy : Prop :=
  ∀ {eccentricity : ℝ}, 0 < eccentricity → eccentricity < 1 →
    ∀ {p q : ℕ}, 0 < p → 0 < q →
      resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1 →
      ∃ orientation,
        deriv (resonantDisturbingAverage p q eccentricity) orientation ≠ 0

/-- The Kepler frequency varies continuously on the full interior action subtype. -/
theorem continuous_interiorDelaunayFrequency :
    Continuous (fun action : InteriorProgradeEllipticAction ↦
      delaunayFrequency (action.1 0)) := by
  rw [continuous_iff_continuousAt]
  intro action
  have hcoordinate : ContinuousAt
      (fun candidate : InteriorProgradeEllipticAction ↦ candidate.1 0) action :=
    (continuous_apply 0).continuousAt.comp continuousAt_subtype_val
  have hfirstAction : action.1 0 ≠ 0 :=
    (action.2.1.1.trans action.2.1.2).ne'
  unfold delaunayFrequency
  rw [continuousAt_pi]
  intro coordinate
  fin_cases coordinate
  · exact continuousAt_const.div (hcoordinate.pow 3)
      (pow_ne_zero 3 hfirstAction)
  · exact continuousAt_const

/-- The represented leading differential varies continuously on the full interior action
subtype. -/
theorem IsJointlyAnalytic.continuous_interiorLeadingActionDifferential
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ)
    (hanalytic : IsJointlyAnalytic δ F) :
    Continuous (fun action : InteriorProgradeEllipticAction ↦
      leadingActionDifferential F action.1) := by
  rw [continuous_iff_continuousAt]
  intro action
  exact (IsJointlyAnalytic.continuousAt_leadingActionDifferential
    hδ hanalytic action.2.1 action.2.2).comp continuousAt_subtype_val

/-- Every member of the classical Poincaré set forces the leading differential and Kepler
frequency to have zero wedge. -/
theorem IsFirstIntegralFamily.wedge_leadingActionDifferential_eq_zero_of_mem_poincareSet
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    (action : InteriorProgradeEllipticAction)
    (haction : action ∈ classicalPoincareSet) :
    wedge (delaunayFrequency (action.1 0))
      (leadingActionDifferential F action.1) = 0 := by
  rcases haction with ⟨p, q, hp, hq, hfirst, orientation, haverage⟩
  let eccentricity := eccentricityFromActions action.1
  have heccentricity : 0 < eccentricity :=
    eccentricityFromActions_pos action.2.1
  have heccentricityOne : eccentricity < 1 :=
    eccentricityFromActions_lt_one action.2.1
  have hapoapsis :
      resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1 := by
    rw [← hfirst]
    exact action.2.2
  have horthogonal :=
    IsFirstIntegralFamily.resonantLeadingDifferential_orthogonal
      hδ hanalytic hfirstIntegral hp hq heccentricity heccentricityOne
      hapoapsis haverage
  have hrecover :
      ![action.1 0,
        angularActionFromEccentricity (action.1 0) eccentricity] = action.1 :=
    actions_from_eccentricityFromActions action.2.1
  have hresonantAction :
      ![resonantFirstAction p q,
        angularActionFromEccentricity (resonantFirstAction p q) eccentricity] =
        action.1 := by
    rw [← hfirst]
    exact hrecover
  rw [hfirst]
  apply wedge_eq_zero_of_resonance (resonanceVector_ne_zero hp)
    (resonantFirstAction_is_resonant hp hq)
  simpa only [resonantLeadingActionDifferential, hresonantAction] using horthogonal

/-- Density of the classical Poincaré set propagates its resonant obstruction to every interior
prograde elliptic action. -/
theorem IsFirstIntegralFamily.wedge_leadingActionDifferential_eq_zero_of_densePoincareSet
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    (hdense : HasDenseClassicalPoincareSet)
    (action : InteriorProgradeEllipticAction) :
    wedge (delaunayFrequency (action.1 0))
      (leadingActionDifferential F action.1) = 0 := by
  exact wedge_eq_zero_of_dense_resonances hdense
    continuous_interiorDelaunayFrequency
    (IsJointlyAnalytic.continuous_interiorLeadingActionDifferential hδ hanalytic)
    (fun resonant hresonant ↦
      IsFirstIntegralFamily.wedge_leadingActionDifferential_eq_zero_of_mem_poincareSet
        hδ hanalytic hfirstIntegral resonant hresonant)
    action

/-- Nonvanishing at every interior rational resonance implies density of the classical Poincaré
set.  The proof uses density of rational Kepler frequencies along the fixed-eccentricity curve
through each action. -/
theorem hasDenseClassicalPoincareSet_of_nondegeneracy
    (hnondegenerate : ClassicalDisturbingNondegeneracy) :
    HasDenseClassicalPoincareSet := by
  apply Subtype.dense_iff.mpr
  intro action haction
  let eccentricity := eccentricityFromActions action
  have heccentricity : 0 < eccentricity :=
    eccentricityFromActions_pos haction.1
  have heccentricityOne : eccentricity < 1 :=
    eccentricityFromActions_lt_one haction.1
  let source : InteriorPositiveAction eccentricity :=
    ⟨⟨action 0, haction.1.1.trans haction.1.2⟩, haction.2⟩
  let curve : InteriorPositiveAction eccentricity → ActionSpace :=
    fun firstAction ↦
      fixedEccentricityAction eccentricity firstAction.1.1
  have hcurve : Continuous curve := by
    unfold curve fixedEccentricityAction angularActionFromEccentricity
    fun_prop
  have hsourceClosure :
      source ∈ closure (resonantInteriorPositiveActions eccentricity) := by
    rw [(resonantInteriorPositiveActions_dense eccentricity).closure_eq]
    exact Set.mem_univ source
  have hmaps : Set.MapsTo curve
      (resonantInteriorPositiveActions eccentricity)
      ((↑) '' classicalPoincareSet) := by
    intro resonant hresonant
    rcases hresonant with ⟨p, q, hp, hq, hfirst⟩
    have hcurveAction : curve resonant ∈ InteriorProgradeEllipticActions := by
      have hprograde : curve resonant ∈ ProgradeEllipticActions := by
        exact ⟨angularActionFromEccentricity_pos resonant.1.2
            heccentricity heccentricityOne,
          angularActionFromEccentricity_lt_firstAction resonant.1.2
            heccentricity⟩
      have heRecover : eccentricityFromActions (curve resonant) = eccentricity := by
        exact eccentricityFromActions_angularActionFromEccentricity
          resonant.1.2 heccentricity.le heccentricityOne
      refine ⟨hprograde, ?_⟩
      change resonant.1.1 ^ 2 *
        (1 + eccentricityFromActions (curve resonant)) < 1
      rw [heRecover]
      exact resonant.2
    let certifiedAction : InteriorProgradeEllipticAction :=
      ⟨curve resonant, hcurveAction⟩
    have heRecover :
        eccentricityFromActions certifiedAction.1 = eccentricity := by
      exact eccentricityFromActions_angularActionFromEccentricity
        resonant.1.2 heccentricity.le heccentricityOne
    have hapoapsis :
        resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1 := by
      rw [← hfirst]
      exact resonant.2
    have hderivative := hnondegenerate heccentricity heccentricityOne
      hp hq hapoapsis
    refine ⟨certifiedAction, ?_, rfl⟩
    exact ⟨p, q, hp, hq, by
      simpa only [certifiedAction, curve, fixedEccentricityAction,
        Matrix.cons_val_zero] using hfirst,
      by simpa only [heRecover] using hderivative⟩
  have himage := map_mem_closure hcurve hsourceClosure hmaps
  have hrecover : curve source = action := by
    exact actions_from_eccentricityFromActions haction.1
  rwa [hrecover] at himage

end LeanPool.PoincareThreeBody
