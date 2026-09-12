/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Rectifiability.BadConvexSets

/-!
# Packing bad convex sets

For a disjoint countable family of bad convex sets, the sum of their diameters is controlled by
the mass outside the compact core.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal MeasureTheory

namespace LeanPool.Besicovitch

/-- Disjoint bad convex sets contained in an ambient set charge only its mass outside the core. -/
theorem mul_tsum_ediam_badConvexSets_le_measure
    {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    {F ambient : Set (EuclideanSpace ℝ (Fin 2))}
    (hF : MeasurableSet F) {alpha : ℝ} {chosen : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hchosen : chosen ⊆ badConvexSets mu F alpha) (hcountable : chosen.Countable)
    (hdisjoint : chosen.PairwiseDisjoint id)
    (hcontained : ∀ V ∈ chosen, V ⊆ ambient) :
    ENNReal.ofReal alpha *
      ∑' V : chosen, Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2))) ≤
        mu (ambient \ F) := by
  letI : Countable chosen := hcountable.to_subtype
  have hpair : Pairwise fun V W : chosen ↦
      Disjoint ((V : Set (EuclideanSpace ℝ (Fin 2))) \ F)
        ((W : Set (EuclideanSpace ℝ (Fin 2))) \ F) := by
    intro V W hVW
    have hne : (V : Set (EuclideanSpace ℝ (Fin 2))) ≠
        (W : Set (EuclideanSpace ℝ (Fin 2))) :=
      fun h ↦ hVW (Subtype.ext h)
    exact (hdisjoint V.property W.property hne).mono sdiff_subset sdiff_subset
  have hmeasurable (V : chosen) : MeasurableSet ((V : Set (EuclideanSpace ℝ (Fin 2))) \ F) :=
    (hchosen V.property).1.measurableSet.diff hF
  rw [← ENNReal.tsum_mul_left]
  calc
    (∑' V : chosen,
      ENNReal.ofReal alpha * Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2)))) ≤
        ∑' V : chosen, mu ((V : Set (EuclideanSpace ℝ (Fin 2))) \ F) :=
      ENNReal.tsum_le_tsum fun V ↦ (hchosen V.property).2.2.2.le
    _ = mu (⋃ V : chosen, (V : Set (EuclideanSpace ℝ (Fin 2))) \ F) :=
      (measure_iUnion hpair hmeasurable).symm
    _ ≤ mu (ambient \ F) := measure_mono <| iUnion_subset fun V x hx ↦
      ⟨hcontained V V.property hx.1, hx.2⟩

/-- Disjoint bad convex sets have total extended diameter controlled by the mass outside the
compact core. -/
theorem mul_tsum_ediam_badConvexSets_le
    {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    {F : Set (EuclideanSpace ℝ (Fin 2))}
    (hF : MeasurableSet F) {alpha : ℝ} {chosen : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hchosen : chosen ⊆ badConvexSets mu F alpha) (hcountable : chosen.Countable)
    (hdisjoint : chosen.PairwiseDisjoint id) :
    ENNReal.ofReal alpha *
      ∑' V : chosen, Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2))) ≤ mu Fᶜ := by
  letI : Countable chosen := hcountable.to_subtype
  have hpair : Pairwise fun V W : chosen ↦
      Disjoint ((V : Set (EuclideanSpace ℝ (Fin 2))) \ F)
        ((W : Set (EuclideanSpace ℝ (Fin 2))) \ F) := by
    intro V W hVW
    have hne : (V : Set (EuclideanSpace ℝ (Fin 2))) ≠
        (W : Set (EuclideanSpace ℝ (Fin 2))) :=
      fun h ↦ hVW (Subtype.ext h)
    exact (hdisjoint V.property W.property hne).mono sdiff_subset sdiff_subset
  have hmeasurable (V : chosen) : MeasurableSet ((V : Set (EuclideanSpace ℝ (Fin 2))) \ F) :=
    (hchosen V.property).1.measurableSet.diff hF
  rw [← ENNReal.tsum_mul_left]
  calc
    (∑' V : chosen,
      ENNReal.ofReal alpha * Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2)))) ≤
        ∑' V : chosen, mu ((V : Set (EuclideanSpace ℝ (Fin 2))) \ F) :=
      ENNReal.tsum_le_tsum fun V ↦ (hchosen V.property).2.2.2.le
    _ = mu (⋃ V : chosen, (V : Set (EuclideanSpace ℝ (Fin 2))) \ F) :=
      (measure_iUnion hpair hmeasurable).symm
    _ ≤ mu Fᶜ := measure_mono <| iUnion_subset fun V _ hx ↦ hx.2

/-- If the outside mass is less than `alpha / enlargement` times the retained mass, then the
diameter sum is less than `1 / enlargement` times the retained mass. -/
theorem tsum_ediam_badConvexSets_lt
    {mu : Measure (EuclideanSpace ℝ (Fin 2))}
    {F : Set (EuclideanSpace ℝ (Fin 2))}
    (hF : MeasurableSet F) {alpha enlargement : ℝ} (halpha : 0 < alpha)
    (henlargement : 0 < enlargement) {chosen : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hchosen : chosen ⊆ badConvexSets mu F alpha) (hcountable : chosen.Countable)
    (hdisjoint : chosen.PairwiseDisjoint id)
    (houtside : mu Fᶜ < ENNReal.ofReal (alpha / enlargement) * mu F) :
    ∑' V : chosen, Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2))) <
      ENNReal.ofReal (1 / enlargement) * mu F := by
  have hpacking := mul_tsum_ediam_badConvexSets_le hF hchosen hcountable hdisjoint
  have hcombined := hpacking.trans_lt houtside
  have hfactor : ENNReal.ofReal (alpha / enlargement) =
      ENNReal.ofReal alpha * ENNReal.ofReal (1 / enlargement) := by
    rw [ENNReal.ofReal_div_of_pos henlargement, ENNReal.ofReal_div_of_pos henlargement]
    simp [div_eq_mul_inv]
  have hcombined' : ENNReal.ofReal alpha *
      (∑' V : chosen, Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2)))) <
      ENNReal.ofReal alpha * (ENNReal.ofReal (1 / enlargement) * mu F) := by
    rw [hfactor, mul_assoc] at hcombined
    exact hcombined
  exact lt_of_mul_lt_mul_left hcombined' (by positivity)

end LeanPool.Besicovitch
