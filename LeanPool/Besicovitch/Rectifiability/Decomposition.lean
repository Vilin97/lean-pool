/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Rectifiability.Basic
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Order.IsLUB

/-!
# Rectifiable and purely unrectifiable parts

A finite measurable set splits into a countably one-rectifiable part and a measurable purely
one-unrectifiable remainder.  The proof maximizes the measure captured by countably many
Lipschitz curves; it does not assume a decomposition theorem from outside Mathlib.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory NNReal Topology

namespace LeanPool.Besicovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A countable union of ranges of Lipschitz curves is measurable. -/
theorem measurableSet_iUnion_range_of_lipschitz {f : ℕ → ℝ → X}
    (hf : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (f i)) :
    MeasurableSet (⋃ i, range (f i)) := by
  apply MeasurableSet.iUnion
  intro i
  obtain ⟨K, hK⟩ := hf i
  have hcompact : IsSigmaCompact (range (f i)) := by
    rw [← image_univ]
    exact isSigmaCompact_univ.image hK.continuous
  obtain ⟨sets, sets_compact, hsets⟩ := hcompact
  rw [← hsets]
  exact MeasurableSet.iUnion fun n ↦ (sets_compact n).isClosed.measurableSet

/-- A rectifiable set is covered up to a null set by a measurable rectifiable set. -/
theorem IsCountablyOneRectifiable.exists_measurable_cover {s : Set X}
    (hs : IsCountablyOneRectifiable s) :
    ∃ t : Set X, MeasurableSet t ∧ IsCountablyOneRectifiable t ∧ μH[1] (s \ t) = 0 := by
  obtain ⟨f, hf, hnull⟩ := hs
  refine ⟨⋃ i, range (f i), measurableSet_iUnion_range_of_lipschitz hf, ?_, hnull⟩
  exact ⟨f, hf, by simp⟩

/-- Every finite measurable set is the disjoint union of a rectifiable part and a purely
unrectifiable part. -/
theorem exists_rectifiable_pure_decomposition [Nonempty X] {s : Set X}
    (hs : MeasurableSet s) (hfinite : μH[1] s < ∞) :
    ∃ r p : Set X,
      MeasurableSet r ∧ MeasurableSet p ∧ r ⊆ s ∧ p = s \ r ∧
        IsCountablyOneRectifiable r ∧ IsPurelyOneUnrectifiable p := by
  let candidates : Set (Set X) :=
    {t | MeasurableSet t ∧ t ⊆ s ∧ IsCountablyOneRectifiable t}
  let masses : Set ℝ := {a | ∃ t ∈ candidates, a = (μH[1] t).toReal}
  have candidates_empty : (∅ : Set X) ∈ candidates := by
    exact ⟨MeasurableSet.empty, empty_subset s, isCountablyOneRectifiable_empty⟩
  have masses_nonempty : masses.Nonempty := by
    exact ⟨0, ∅, candidates_empty, by simp⟩
  have masses_bddAbove : BddAbove masses := by
    refine ⟨(μH[1] s).toReal, ?_⟩
    rintro a ⟨t, ht, rfl⟩
    exact ENNReal.toReal_mono (ne_of_lt hfinite) (measure_mono ht.2.1)
  obtain ⟨u, -, hu_tendsto, hu_mem⟩ :=
    exists_seq_tendsto_sSup masses_nonempty masses_bddAbove
  choose pieces hpieces hu_eq using hu_mem
  have pieces_candidate (n : ℕ) : pieces n ∈ candidates := hpieces n
  let r : Set X := ⋃ n, pieces n
  have r_measurable : MeasurableSet r := by
    exact MeasurableSet.iUnion fun n ↦ (pieces_candidate n).1
  have r_subset : r ⊆ s := by
    exact iUnion_subset fun n ↦ (pieces_candidate n).2.1
  have r_rectifiable : IsCountablyOneRectifiable r := by
    exact isCountablyOneRectifiable_iUnion fun n ↦ (pieces_candidate n).2.2
  have r_finite : μH[1] r ≠ ∞ := by
    exact ne_of_lt ((measure_mono r_subset).trans_lt hfinite)
  have r_mass_mem : (μH[1] r).toReal ∈ masses := by
    exact ⟨r, ⟨r_measurable, r_subset, r_rectifiable⟩, rfl⟩
  have supremum_eq : sSup masses = (μH[1] r).toReal := by
    apply le_antisymm
    · apply le_of_tendsto hu_tendsto
      filter_upwards [] with n
      rw [hu_eq n]
      exact ENNReal.toReal_mono r_finite (measure_mono (subset_iUnion pieces n))
    · exact le_csSup masses_bddAbove r_mass_mem
  let p : Set X := s \ r
  have p_measurable : MeasurableSet p := hs.diff r_measurable
  have p_pure : IsPurelyOneUnrectifiable p := by
    intro t ht
    obtain ⟨cover, cover_measurable, cover_rectifiable, ht_null⟩ := ht.exists_measurable_cover
    have p_inter_cover_rectifiable : IsCountablyOneRectifiable (p ∩ cover) :=
      cover_rectifiable.mono inter_subset_right
    have p_inter_cover_subset : p ∩ cover ⊆ s := by
      intro x hx
      exact hx.1.1
    have union_candidate : r ∪ (p ∩ cover) ∈ candidates := by
      refine ⟨r_measurable.union (p_measurable.inter cover_measurable), ?_,
        r_rectifiable.union p_inter_cover_rectifiable⟩
      exact union_subset r_subset p_inter_cover_subset
    have union_mass_le : (μH[1] (r ∪ (p ∩ cover))).toReal ≤ (μH[1] r).toReal := by
      rw [← supremum_eq]
      exact le_csSup masses_bddAbove ⟨_, union_candidate, rfl⟩
    have p_inter_cover_finite : μH[1] (p ∩ cover) ≠ ∞ := by
      exact ne_of_lt ((measure_mono p_inter_cover_subset).trans_lt hfinite)
    have disjoint_parts : Disjoint r (p ∩ cover) := by
      rw [disjoint_left]
      intro x hxr hxp
      exact hxp.1.2 hxr
    have p_inter_cover_null : μH[1] (p ∩ cover) = 0 := by
      rw [measure_union disjoint_parts (p_measurable.inter cover_measurable),
        ENNReal.toReal_add r_finite p_inter_cover_finite] at union_mass_le
      have : (μH[1] (p ∩ cover)).toReal = 0 := by
        linarith [ENNReal.toReal_nonneg (a := μH[1] (p ∩ cover))]
      exact ((ENNReal.toReal_eq_zero_iff _).mp this).resolve_right p_inter_cover_finite
    apply measure_mono_null ?_ (measure_union_null p_inter_cover_null ht_null)
    intro x hx
    by_cases hxc : x ∈ cover
    · exact Or.inl ⟨hx.1, hxc⟩
    · exact Or.inr ⟨hx.2, hxc⟩
  exact ⟨r, p, r_measurable, p_measurable, r_subset, rfl, r_rectifiable, p_pure⟩

end LeanPool.Besicovitch
