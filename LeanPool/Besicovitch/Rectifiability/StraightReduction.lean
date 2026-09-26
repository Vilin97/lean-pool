/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Measure.DensityLocalization
public import LeanPool.Besicovitch.Rectifiability.Decomposition

/-!
# Reduction to a straight purely unrectifiable set

A hypothetical nonrectifiable finite set has a positive purely unrectifiable part.  A straight
piece of that part retains every strictly smaller lower-density threshold almost everywhere.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal MeasureTheory

namespace LeanPool.Besicovitch

/-- A nonrectifiable finite set with density at least `gamma` contains a positive straight,
purely unrectifiable subset with density strictly above every `beta < gamma`. -/
theorem exists_pure_straight_subset_of_not_rectifiable
    {e : Set (EuclideanSpace ℝ (Fin 2))} (he : MeasurableSet e) (he_fin : μH[1] e < ∞)
    (he_not_rectifiable : ¬IsCountablyOneRectifiable e)
    {beta gamma : ℝ} (hbeta : 0 ≤ beta) (hbeta_gamma : beta < gamma)
    (hdensity : ∀ᵐ x ∂μH[1].restrict e,
      ENNReal.ofReal gamma ≤ lowerOneDensity e x) :
    ∃ a : Set (EuclideanSpace ℝ (Fin 2)),
      MeasurableSet a ∧ a ⊆ e ∧ 0 < μH[1] a ∧ μH[1] a < ∞ ∧
        IsPurelyOneUnrectifiable a ∧ IsStraightMeasure (μH[1].restrict a) ∧
          ∀ᵐ x ∂μH[1].restrict a,
            ENNReal.ofReal beta < lowerOneDensity a x := by
  obtain ⟨r, p, hr_measurable, hp_measurable, hr_subset, hp_eq,
      hr_rectifiable, hp_pure⟩ :=
    exists_rectifiable_pure_decomposition he he_fin
  have hp_subset : p ⊆ e := by
    rw [hp_eq]
    exact sdiff_subset
  have hp_fin : μH[1] p < ∞ := (measure_mono hp_subset).trans_lt he_fin
  have hp_pos : 0 < μH[1] p := by
    apply pos_iff_ne_zero.mpr
    intro hp_zero
    have hp_rectifiable : IsCountablyOneRectifiable p :=
      isCountablyOneRectifiable_of_measure_zero hp_zero
    have he_union : e = r ∪ p := by
      rw [hp_eq]
      exact (union_sdiff_cancel hr_subset).symm
    exact he_not_rectifiable (he_union ▸ hr_rectifiable.union hp_rectifiable)
  obtain ⟨a, ha_measurable, ha_subset_p, ha_pos, ha_straight⟩ :=
    exists_straight_measure_restrict_subset hp_measurable hp_pos hp_fin
  have ha_subset_e : a ⊆ e := ha_subset_p.trans hp_subset
  have ha_fin : μH[1] a < ∞ := (measure_mono ha_subset_e).trans_lt he_fin
  have ha_pure : IsPurelyOneUnrectifiable a := hp_pure.mono ha_subset_p
  have hdensity_a : ∀ᵐ x ∂μH[1].restrict a,
      ENNReal.ofReal gamma ≤ lowerOneDensity e x :=
    ae_mono (Measure.restrict_mono ha_subset_e le_rfl) hdensity
  have ha_density := ae_lt_lowerOneDensity_of_subset_of_straight
    ha_measurable ha_subset_e he_fin ha_straight hbeta hbeta_gamma hdensity_a
  exact ⟨a, ha_measurable, ha_subset_e, ha_pos, ha_fin, ha_pure, ha_straight, ha_density⟩

end LeanPool.Besicovitch
