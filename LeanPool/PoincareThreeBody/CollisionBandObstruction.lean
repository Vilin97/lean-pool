/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.ResonantAverageSeparation

/-!
# The leading obstruction on collision-band resonances

Fiberwise density in eccentricity propagates each collision-band resonant obstruction from the
nondegenerate eccentricities to every admissible eccentricity at that resonance.
-/

namespace LeanPool.PoincareThreeBody


/-- Interior first actions whose semimajor axis lies in the collision band. -/
abbrev CollisionBandInteriorPositiveAction (eccentricity : ℝ) :=
  {action : InteriorPositiveAction eccentricity // 1 / 2 < action.1.1 ^ 2}

/-- Positive rational resonances restricted to the collision band. -/
def resonantCollisionBandActions (eccentricity : ℝ) :
    Set (CollisionBandInteriorPositiveAction eccentricity) :=
  {action | ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
    action.1.1.1 = resonantFirstAction p q}

theorem resonantCollisionBandActions_dense (eccentricity : ℝ) :
    Dense (resonantCollisionBandActions eccentricity) := by
  apply Subtype.dense_iff.mpr
  intro action haction
  have hopen : IsOpen
      {candidate : InteriorPositiveAction eccentricity | 1 / 2 < candidate.1.1 ^ 2} :=
    isOpen_lt continuous_const ((continuous_subtype_val.comp continuous_subtype_val).pow 2)
  have hclosure := (resonantInteriorPositiveActions_dense eccentricity).open_subset_closure_inter
    hopen haction
  have himage :
      ((↑) : CollisionBandInteriorPositiveAction eccentricity →
          InteriorPositiveAction eccentricity) '' resonantCollisionBandActions eccentricity =
        {candidate : InteriorPositiveAction eccentricity | 1 / 2 < candidate.1.1 ^ 2} ∩
          resonantInteriorPositiveActions eccentricity := by
    ext candidate
    constructor
    · rintro ⟨bandAction, hresonant, rfl⟩
      exact ⟨bandAction.2, hresonant⟩
    · rintro ⟨hband, hresonant⟩
      exact ⟨⟨candidate, hband⟩, hresonant, rfl⟩
  have hclosures := congrArg closure himage
  exact hclosures.symm ▸ hclosure

theorem IsFirstIntegralFamily.wedge_leadingActionDifferential_eq_zero_at_collisionBandResonance
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (haxisHalf : 1 / 2 < resonantSemimajorAxis p q)
    (haxisOne : resonantSemimajorAxis p q < 1)
    (eccentricity : AdmissibleResonantEccentricity p q) :
    wedge (delaunayFrequency (resonantFirstAction p q))
      (leadingActionDifferential F
        (fixedEccentricityAction eccentricity.1 (resonantFirstAction p q))) = 0 := by
  let actionCurve : AdmissibleResonantEccentricity p q → ActionSpace :=
    fun candidate ↦ fixedEccentricityAction candidate.1 (resonantFirstAction p q)
  let differential : AdmissibleResonantEccentricity p q → ActionSpace :=
    fun candidate ↦ leadingActionDifferential F (actionCurve candidate)
  have hactionCurve : Continuous actionCurve := by
    unfold actionCurve fixedEccentricityAction angularActionFromEccentricity
    fun_prop
  have hdifferential : Continuous differential := by
    rw [continuous_iff_continuousAt]
    intro candidate
    have hfirstAction := resonantFirstAction_pos hp hq
    have haction : actionCurve candidate ∈ ProgradeEllipticActions := by
      exact ⟨angularActionFromEccentricity_pos hfirstAction candidate.2.1
          candidate.2.2.1,
        angularActionFromEccentricity_lt_firstAction hfirstAction candidate.2.1⟩
    have heRecover : eccentricityFromActions (actionCurve candidate) = candidate.1 :=
      eccentricityFromActions_angularActionFromEccentricity hfirstAction
        candidate.2.1.le candidate.2.2.1
    have hapoapsis : (actionCurve candidate) 0 ^ 2 *
        (1 + eccentricityFromActions (actionCurve candidate)) < 1 := by
      rw [heRecover]
      exact candidate.2.2.2
    exact (IsJointlyAnalytic.continuousAt_leadingActionDifferential
      hδ hanalytic haction hapoapsis).comp hactionCurve.continuousAt
  apply wedge_eq_zero_of_dense_resonances
    (dense_nondegenerateResonantEccentricities_of_collision_band
      hp hq haxisHalf haxisOne)
    continuous_const hdifferential
  · intro candidate hcandidate
    rcases hcandidate with ⟨orientation, haverage⟩
    have horthogonal :=
      IsFirstIntegralFamily.resonantLeadingDifferential_orthogonal
        hδ hanalytic hfirstIntegral hp hq candidate.2.1 candidate.2.2.1
          candidate.2.2.2 haverage
    apply wedge_eq_zero_of_resonance (resonanceVector_ne_zero hp)
      (resonantFirstAction_is_resonant hp hq)
    simpa [differential, actionCurve, fixedEccentricityAction,
      resonantLeadingActionDifferential] using horthogonal

/-- Collision-band resonances are dense, so the leading wedge vanishes throughout the band at
every fixed admissible eccentricity. -/
theorem IsFirstIntegralFamily.wedge_leadingActionDifferential_eq_zero_on_collisionBand
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    {eccentricity : ℝ} (heccentricity : 0 < eccentricity)
    (heccentricityOne : eccentricity < 1)
    (action : CollisionBandInteriorPositiveAction eccentricity) :
    wedge (delaunayFrequency action.1.1.1)
      (leadingActionDifferential F
        (fixedEccentricityAction eccentricity action.1.1.1)) = 0 := by
  let frequency : CollisionBandInteriorPositiveAction eccentricity → ActionSpace :=
    fun candidate ↦ delaunayFrequency candidate.1.1.1
  let differential : CollisionBandInteriorPositiveAction eccentricity → ActionSpace :=
    fun candidate ↦ leadingActionDifferential F
      (fixedEccentricityAction eccentricity candidate.1.1.1)
  have hfrequency : Continuous frequency :=
    (continuous_delaunayFrequencyOnPositive.comp continuous_subtype_val).comp
      continuous_subtype_val
  have hdifferential : Continuous differential := by
    rw [continuous_iff_continuousAt]
    intro candidate
    let interiorCandidate : InteriorPositiveAction eccentricity := candidate.1
    have hbase := IsJointlyAnalytic.continuous_leadingActionDifferentialAtEccentricity
      hδ hanalytic heccentricity heccentricityOne
    exact hbase.continuousAt.comp continuousAt_subtype_val
  apply wedge_eq_zero_of_dense_resonances
    (resonantCollisionBandActions_dense eccentricity) hfrequency hdifferential
  intro resonant hresonant
  rcases hresonant with ⟨p, q, hp, hq, hfirst⟩
  have haxisHalf : 1 / 2 < resonantSemimajorAxis p q := by
    simpa [resonantSemimajorAxis, ← hfirst] using resonant.2
  have hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1 := by
    rw [← hfirst]
    exact resonant.1.2
  have haxisOne : resonantSemimajorAxis p q < 1 := by
    have hfactor : 1 < 1 + eccentricity := by linarith
    have hstrict : resonantFirstAction p q ^ 2 <
        resonantFirstAction p q ^ 2 * (1 + eccentricity) := by
      have hfirstPositive := resonantFirstAction_pos hp hq
      simpa only [mul_one] using
        (mul_lt_mul_of_pos_left hfactor (sq_pos_of_pos hfirstPositive))
    simpa [resonantSemimajorAxis] using hstrict.trans hapoapsis
  let resonantEccentricity : AdmissibleResonantEccentricity p q :=
    ⟨eccentricity, heccentricity, heccentricityOne, hapoapsis⟩
  have hobstruction :=
    IsFirstIntegralFamily.wedge_leadingActionDifferential_eq_zero_at_collisionBandResonance
      hδ hanalytic hfirstIntegral hp hq haxisHalf haxisOne resonantEccentricity
  simpa [frequency, differential, fixedEccentricityAction, hfirst] using hobstruction

end LeanPool.PoincareThreeBody
