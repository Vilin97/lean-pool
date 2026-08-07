/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.ResonantActionObstruction

/-!
# Propagating resonant obstructions by density

Positive rational Kepler resonances remain dense after restricting to ellipses inside the unit
primary orbit.  Consequently, nonconstancy of the disturbing average at every such resonance
forces the leading integral differential to be dependent on the Kepler frequency everywhere in
the corresponding fixed-eccentricity action interval.
-/

namespace LeanPool.PoincareThreeBody

/-- Interior first actions carrying a positive rational Kepler resonance. -/
def resonantInteriorPositiveActions (eccentricity : ℝ) :
    Set (InteriorPositiveAction eccentricity) :=
  {action | ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
    action.1.1 = resonantFirstAction p q}

/-- Rational Kepler resonances are dense even after imposing the open apoapsis constraint. -/
theorem resonantInteriorPositiveActions_dense (eccentricity : ℝ) :
    Dense (resonantInteriorPositiveActions eccentricity) := by
  apply Subtype.dense_iff.mpr
  intro action haction
  have hopen : IsOpen
      {candidate : PositiveAction |
        candidate.1 ^ 2 * (1 + eccentricity) < 1} := by
    exact isOpen_lt ((continuous_subtype_val.pow 2).mul continuous_const)
      continuous_const
  have hclosure :=
    resonantPositiveActions_dense.open_subset_closure_inter hopen haction
  have himage :
      ((↑) : InteriorPositiveAction eccentricity → PositiveAction) ''
          resonantInteriorPositiveActions eccentricity =
        {candidate : PositiveAction |
            candidate.1 ^ 2 * (1 + eccentricity) < 1} ∩
          resonantPositiveActions := by
    ext candidate
    constructor
    · rintro ⟨interiorAction, hresonant, rfl⟩
      exact ⟨interiorAction.2, hresonant⟩
    · rintro ⟨hinterior, hresonant⟩
      exact ⟨⟨candidate, hinterior⟩, hresonant, rfl⟩
  have hclosures := congrArg closure himage
  exact hclosures.symm ▸ hclosure

/-- Conditional classical density step: nonconstant resonant averages force the frequency and
leading differential to have zero wedge at every interior action of fixed eccentricity. -/
theorem IsFirstIntegralFamily.wedge_leadingActionDifferentialAtEccentricity_eq_zero
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    {eccentricity : ℝ} (heccentricity : 0 < eccentricity)
    (heccentricityOne : eccentricity < 1)
    (hnonconstant : ∀ {p q : ℕ} (_hp : 0 < p) (_hq : 0 < q),
      resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1 →
      ∃ orientation,
        deriv (resonantDisturbingAverage p q eccentricity) orientation ≠ 0)
    (action : InteriorPositiveAction eccentricity) :
    wedge (delaunayFrequency action.1.1)
      (leadingActionDifferentialAtEccentricity F eccentricity action) = 0 := by
  apply wedge_eq_zero_of_dense_resonances
    (resonantInteriorPositiveActions_dense eccentricity)
    (continuous_delaunayFrequencyOnPositive.comp continuous_subtype_val)
    (IsJointlyAnalytic.continuous_leadingActionDifferentialAtEccentricity
      hδ hanalytic heccentricity heccentricityOne)
  intro resonant hresonant
  rcases hresonant with ⟨p, q, hp, hq, heq⟩
  have hapoapsis : resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1 := by
    rw [← heq]
    exact resonant.2
  have hsubtype : resonant =
      ⟨⟨resonantFirstAction p q, resonantFirstAction_pos hp hq⟩, by
        simpa [heq] using resonant.2⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    exact heq
  rw [hsubtype]
  obtain ⟨orientation, haverage⟩ := hnonconstant hp hq hapoapsis
  have horthogonal :=
    IsFirstIntegralFamily.resonantLeadingDifferential_orthogonal
      hδ hanalytic hfirstIntegral hp hq heccentricity heccentricityOne
      hapoapsis haverage
  apply wedge_eq_zero_of_resonance (resonanceVector_ne_zero hp)
    (resonantFirstAction_is_resonant hp hq)
  simpa [leadingActionDifferentialAtEccentricity, fixedEccentricityAction,
    resonantLeadingActionDifferential] using horthogonal

/-- Under the same resonant nonconstancy input, the two differentials are dependent at every
interior fixed-eccentricity action. -/
theorem IsFirstIntegralFamily.leadingActionDifferentialAtEccentricity_obstruction
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    {eccentricity : ℝ} (heccentricity : 0 < eccentricity)
    (heccentricityOne : eccentricity < 1)
    (hnonconstant : ∀ {p q : ℕ} (_hp : 0 < p) (_hq : 0 < q),
      resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1 →
      ∃ orientation,
        deriv (resonantDisturbingAverage p q eccentricity) orientation ≠ 0)
    (action : InteriorPositiveAction eccentricity) :
    ¬LinearIndependent ℝ
      ![delaunayFrequency action.1.1,
        leadingActionDifferentialAtEccentricity F eccentricity action] := by
  apply not_linearIndependent_of_wedge_eq_zero
  exact IsFirstIntegralFamily.wedge_leadingActionDifferentialAtEccentricity_eq_zero
    hδ hanalytic hfirstIntegral heccentricity heccentricityOne
    hnonconstant action

end LeanPool.PoincareThreeBody
