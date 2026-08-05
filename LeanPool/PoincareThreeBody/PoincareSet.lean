/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DenseResonantObstruction
import LeanPool.PoincareThreeBody.AnalyticDensity
import LeanPool.PoincareThreeBody.DisturbingAverageAnalytic

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

/-- The open interval of admissible noncircular eccentricities for one fixed positive rational
resonance. -/
def admissibleResonantEccentricitySet (p q : ℕ) : Set ℝ :=
  {eccentricity | 0 < eccentricity ∧ eccentricity < 1 ∧
    resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1}

/-- An admissible noncircular eccentricity for one fixed positive rational resonance. -/
abbrev AdmissibleResonantEccentricity (p q : ℕ) :=
  {eccentricity : ℝ // eccentricity ∈ admissibleResonantEccentricitySet p q}

/-- Eccentricities at a fixed resonance where the resonant disturbing average is nonconstant. -/
def nondegenerateResonantEccentricities (p q : ℕ) :
    Set (AdmissibleResonantEccentricity p q) :=
  {eccentricity | ∃ orientation,
    deriv (resonantDisturbingAverage p q eccentricity.1) orientation ≠ 0}

/-- A one-dimensional sufficient form of the classical perturbing-function calculation: at
every rational resonance, nondegenerate eccentricities are dense in their admissible interval.
Unlike `ClassicalDisturbingNondegeneracy`, this permits isolated zeros of individual Fourier
coefficients. -/
def HasDenseNondegenerateResonantEccentricities : Prop :=
  ∀ p q : ℕ, 0 < p → 0 < q →
    Dense (nondegenerateResonantEccentricities p q)

/-- A sharply localized analytic form of the classical disturbing-function input.  For every
positive rational resonance, two fixed orientations separate at one admissible eccentricity and
their averaged-value difference is analytic throughout the admissible eccentricity interval.

The classical high-rank Fourier-coefficient calculation is precisely what supplies the two
orientations and the nonzero witness. -/
def HasAnalyticSeparatingResonantAverages : Prop :=
  ∀ p q : ℕ, 0 < p → 0 < q →
    ∃ phaseA phaseB : ℝ,
      AnalyticOnNhd ℝ
        (fun eccentricity ↦
          resonantDisturbingAverage p q eccentricity phaseA -
            resonantDisturbingAverage p q eccentricity phaseB)
        (admissibleResonantEccentricitySet p q) ∧
      ∃ witness ∈ admissibleResonantEccentricitySet p q,
        resonantDisturbingAverage p q witness phaseA -
          resonantDisturbingAverage p q witness phaseB ≠ 0

/-- The remaining classical disturbing-function calculation, stripped of analyticity: at every
positive rational resonance, two orientations give different averaged perturbations at one
admissible eccentricity. -/
def HasSeparatingResonantAverages : Prop :=
  ∀ p q : ℕ, 0 < p → 0 < q →
    ∃ phaseA phaseB : ℝ, ∃ witness ∈ admissibleResonantEccentricitySet p q,
      resonantDisturbingAverage p q witness phaseA -
        resonantDisturbingAverage p q witness phaseB ≠ 0

/-- Compact parameter integration supplies the analytic clause automatically, so the classical
Fourier calculation only has to provide a separating value at each resonance. -/
theorem hasAnalyticSeparatingResonantAverages_of_separation
    (hseparation : HasSeparatingResonantAverages) :
    HasAnalyticSeparatingResonantAverages := by
  intro p q hp hq
  rcases hseparation p q hp hq with
    ⟨phaseA, phaseB, witness, hwitness, hvalues⟩
  refine ⟨phaseA, phaseB, ?_, witness, hwitness, hvalues⟩
  exact (analyticOnNhd_resonantDisturbingAverage_eccentricity hp hq phaseA).sub
    (analyticOnNhd_resonantDisturbingAverage_eccentricity hp hq phaseB)

/-- The admissible eccentricity domain is open. -/
theorem isOpen_admissibleResonantEccentricitySet (p q : ℕ) :
    IsOpen (admissibleResonantEccentricitySet p q) := by
  unfold admissibleResonantEccentricitySet
  exact (isOpen_lt continuous_const continuous_id).and
    ((isOpen_lt continuous_id continuous_const).and
      (isOpen_lt (by fun_prop) continuous_const))

/-- A nonempty admissible eccentricity domain is connected. -/
theorem isConnected_admissibleResonantEccentricitySet
    {p q : ℕ} (hnonempty : (admissibleResonantEccentricitySet p q).Nonempty) :
    IsConnected (admissibleResonantEccentricitySet p q) := by
  refine ⟨hnonempty, Set.OrdConnected.isPreconnected ?_⟩
  rw [Set.ordConnected_iff]
  intro x hx z hz hxz y hy
  change 0 < x ∧ x < 1 ∧ resonantFirstAction p q ^ 2 * (1 + x) < 1 at hx
  change 0 < z ∧ z < 1 ∧ resonantFirstAction p q ^ 2 * (1 + z) < 1 at hz
  change 0 < y ∧ y < 1 ∧ resonantFirstAction p q ^ 2 * (1 + y) < 1
  have hscale : 0 ≤ resonantFirstAction p q ^ 2 := sq_nonneg _
  have hapoapsisMono :=
    mul_le_mul_of_nonneg_left (add_le_add_left hy.2 1) hscale
  constructor
  · exact hx.1.trans_le hy.1
  constructor
  · exact hy.2.trans_lt hz.2.1
  · simpa [add_comm] using
      hapoapsisMono.trans_lt (by simpa [add_comm] using hz.2.2)

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

/-- Density in eccentricity on each rational resonance is enough to make the full classical
Poincaré set dense in the two-dimensional interior action region. -/
theorem hasDenseClassicalPoincareSet_of_dense_resonant_eccentricities
    (hdense : HasDenseNondegenerateResonantEccentricities) :
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
  let actionCurve : InteriorPositiveAction eccentricity → ActionSpace :=
    fun firstAction ↦ fixedEccentricityAction eccentricity firstAction.1.1
  have hactionCurve : Continuous actionCurve := by
    unfold actionCurve fixedEccentricityAction angularActionFromEccentricity
    fun_prop
  have hsourceClosure :
      source ∈ closure (resonantInteriorPositiveActions eccentricity) := by
    rw [(resonantInteriorPositiveActions_dense eccentricity).closure_eq]
    exact Set.mem_univ source
  have hresonantMaps : Set.MapsTo actionCurve
      (resonantInteriorPositiveActions eccentricity)
      (closure ((↑) '' classicalPoincareSet)) := by
    intro resonant hresonant
    rcases hresonant with ⟨p, q, hp, hq, hfirst⟩
    have hapoapsis :
        resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1 := by
      rw [← hfirst]
      exact resonant.2
    let sourceEccentricity : AdmissibleResonantEccentricity p q :=
      ⟨eccentricity, heccentricity, heccentricityOne, hapoapsis⟩
    let eccentricityCurve : AdmissibleResonantEccentricity p q → ActionSpace :=
      fun candidate ↦ fixedEccentricityAction
        candidate.1 (resonantFirstAction p q)
    have heccentricityCurve : Continuous eccentricityCurve := by
      unfold eccentricityCurve fixedEccentricityAction
        angularActionFromEccentricity
      fun_prop
    have hsourceEccentricityClosure : sourceEccentricity ∈
        closure (nondegenerateResonantEccentricities p q) := by
      rw [(hdense p q hp hq).closure_eq]
      exact Set.mem_univ sourceEccentricity
    have heccentricityMaps : Set.MapsTo eccentricityCurve
        (nondegenerateResonantEccentricities p q)
        ((↑) '' classicalPoincareSet) := by
      intro candidate hcandidate
      have hprograde : eccentricityCurve candidate ∈
          ProgradeEllipticActions := by
        exact ⟨angularActionFromEccentricity_pos
            (resonantFirstAction_pos hp hq) candidate.2.1 candidate.2.2.1,
          angularActionFromEccentricity_lt_firstAction
            (resonantFirstAction_pos hp hq) candidate.2.1⟩
      have heRecover : eccentricityFromActions (eccentricityCurve candidate) =
          candidate.1 := by
        exact eccentricityFromActions_angularActionFromEccentricity
          (resonantFirstAction_pos hp hq) candidate.2.1.le candidate.2.2.1
      have hinside : eccentricityCurve candidate ∈
          InteriorProgradeEllipticActions := by
        refine ⟨hprograde, ?_⟩
        change resonantFirstAction p q ^ 2 *
          (1 + eccentricityFromActions (eccentricityCurve candidate)) < 1
        rw [heRecover]
        exact candidate.2.2.2
      let poincareAction : InteriorProgradeEllipticAction :=
        ⟨eccentricityCurve candidate, hinside⟩
      refine ⟨poincareAction, ?_, rfl⟩
      rcases hcandidate with ⟨orientation, horientation⟩
      refine ⟨p, q, hp, hq, ?_, orientation, ?_⟩
      · rfl
      · simpa only [poincareAction, heRecover] using horientation
    have himage := map_mem_closure heccentricityCurve
      hsourceEccentricityClosure heccentricityMaps
    have hcurvesAgree : eccentricityCurve sourceEccentricity =
        actionCurve resonant := by
      unfold eccentricityCurve actionCurve sourceEccentricity
      rw [hfirst]
    rwa [hcurvesAgree] at himage
  have himage := map_mem_closure hactionCurve hsourceClosure hresonantMaps
  rw [closure_closure] at himage
  have hrecover : actionCurve source = action := by
    exact actions_from_eccentricityFromActions haction.1
  rwa [hrecover] at himage

/-- Analyticity plus one separating value at each resonance makes the nondegenerate
eccentricities dense.  Thus the classical calculation need only prove a nonidentity statement,
not pointwise nonvanishing at every eccentricity. -/
theorem hasDenseNondegenerateResonantEccentricities_of_analytic_separation
    (hseparation : HasAnalyticSeparatingResonantAverages) :
    HasDenseNondegenerateResonantEccentricities := by
  intro p q hp hq
  rcases hseparation p q hp hq with
    ⟨phaseA, phaseB, hanalytic, witness, hwitness, hvalues⟩
  let difference : ℝ → ℝ := fun eccentricity ↦
    resonantDisturbingAverage p q eccentricity phaseA -
      resonantDisturbingAverage p q eccentricity phaseB
  have hdense : Dense
      {eccentricity : AdmissibleResonantEccentricity p q |
        difference eccentricity.1 ≠ 0} := by
    apply dense_nonzero_of_analyticOnNhd
      (isOpen_admissibleResonantEccentricitySet p q)
      (isConnected_admissibleResonantEccentricitySet ⟨witness, hwitness⟩)
      (f := difference) (witness := witness)
    · exact hanalytic
    · exact hwitness
    · exact hvalues
  apply hdense.mono
  intro eccentricity heccentricity
  apply exists_deriv_resonantDisturbingAverage_ne_zero_of_values_ne
    hp hq eccentricity.2.1.le eccentricity.2.2.1 eccentricity.2.2.2
  exact sub_ne_zero.mp heccentricity

/-- The analytic nonidentity statement at each rational resonance supplies the full dense
classical Poincaré set. -/
theorem hasDenseClassicalPoincareSet_of_analytic_separation
    (hseparation : HasAnalyticSeparatingResonantAverages) :
    HasDenseClassicalPoincareSet :=
  hasDenseClassicalPoincareSet_of_dense_resonant_eccentricities
    (hasDenseNondegenerateResonantEccentricities_of_analytic_separation hseparation)

/-- The original pointwise nondegeneracy condition implies the more flexible fiberwise density
condition. -/
theorem hasDenseNondegenerateResonantEccentricities_of_nondegeneracy
    (hnondegenerate : ClassicalDisturbingNondegeneracy) :
    HasDenseNondegenerateResonantEccentricities := by
  intro p q hp hq
  apply dense_iff_closure_eq.mpr
  apply Set.Subset.antisymm (closure_minimal (by
    intro eccentricity _
    exact Set.mem_univ eccentricity) isClosed_univ)
  intro eccentricity _
  apply subset_closure
  exact hnondegenerate eccentricity.2.1 eccentricity.2.2.1 hp hq
    eccentricity.2.2.2

end LeanPool.PoincareThreeBody
