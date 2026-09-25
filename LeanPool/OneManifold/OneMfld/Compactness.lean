/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Tactic
public import LeanPool.OneManifold.OneMfld.FiniteIntervalCharts
public import LeanPool.OneManifold.OneMfld.Noncompact


/-!
# Compactness

Supporting results for the classification of compact one-dimensional manifolds.
-/

@[expose] public section

variable
  {M : Type*}
  [TopologicalSpace M]

lemma clopen_in_r (s : Set NNReal) : (s ≠ ∅ ∧ s ≠ Set.univ) → ¬ IsClopen s := by
  intro h12
  by_contra h'
  have h1 := isClopen_iff.mp h'
  tauto

lemma noncompact_nnreal : NoncompactSpace NNReal := by
  have := not_compactSpace_NNReal
  exact not_compactSpace_iff.mp this

lemma noncompact_ioo' (x y : NNReal) (hxy : x < y) : NoncompactSpace (Set.Ioo x y) := by
  let s := Set.Ioo x y
  have h : ¬ CompactSpace s := by
    by_contra h'
    have hc : IsCompact s := by exact isCompact_iff_compactSpace.mpr h'
    have hs : IsClosed s := by exact IsCompact.isClosed hc
    have ho : IsOpen s := by exact isOpen_Ioo
    have hn : Nonempty s := by exact Set.nonempty_Ioo_subtype hxy
    have hc' := clopen_in_r s
    apply hc'
    constructor
    · exact Set.nonempty_iff_ne_empty'.mp hn
    · by_contra ha
      rw [ha] at h'
      have : ¬ IsCompact (Set.univ : Set NNReal) := by
        have ht : ¬ CompactSpace (NNReal) := by
          exact not_compactSpace_iff.mpr noncompact_nnreal
        by_contra ht'
        apply ht
        exact { isCompact_univ := ht' }
      apply this
      exact isCompact_iff_compactSpace.mpr h'
    exact ⟨ hs, ho ⟩
  exact not_compactSpace_iff.mp h

lemma noncompact_ioo (x y : NNReal) (hxy : x < y) : ¬ CompactSpace (Set.Ioo x y) := by
  have h := noncompact_ioo' x y hxy
  exact not_compactSpace_iff.mpr h

lemma noncompact_iio' (x : NNReal) (hx : 0 < x) : NoncompactSpace (Set.Iio x) := by
  let s := Set.Iio x
  have h : ¬ CompactSpace s := by
    by_contra h'
    have hc : IsCompact s := by exact isCompact_iff_compactSpace.mpr h'
    have hs : IsClosed s := by exact IsCompact.isClosed hc
    have ho : IsOpen s := by exact isOpen_Iio
    have hn : Nonempty s := by
      apply nonempty_subtype.mpr
      exact Exists.intro 0 hx
    have hc' := clopen_in_r s
    apply hc'
    constructor
    · exact Set.nonempty_iff_ne_empty'.mp hn
    · by_contra ha
      rw [ha] at h'
      have : ¬ IsCompact (Set.univ : Set NNReal) := by
        have ht : ¬ CompactSpace (NNReal) := by
          exact not_compactSpace_iff.mpr noncompact_nnreal
        by_contra ht'
        apply ht
        exact { isCompact_univ := ht' }
      apply this
      exact isCompact_iff_compactSpace.mpr h'
    exact ⟨ hs, ho ⟩
  exact not_compactSpace_iff.mp h

lemma noncompact_iio (x : NNReal) (hx : 0 < x) : ¬ CompactSpace (Set.Iio x) := by
  have h:= noncompact_iio' x hx
  exact not_compactSpace_iff.mpr h

lemma noncompact_target (ht : FinitelyIntervalChartedSpace M) (z : M) (a : OpenPartialHomeomorph
    M NNReal) (ha : a ∈ ht.atlas) (hz : z ∈ a.source) : ¬ CompactSpace (a.target) := by
    have := ht.is_interval a ha
    rcases this with (h|h)
    · rcases h with ⟨ x, y, h ⟩
      rw [←h]
      have hz' : a.toFun z ∈ a.target := by exact PartialEquiv.map_source a.toPartialEquiv hz
      rw [←h] at hz'
      simp only [Set.mem_Ioo] at hz'
      rcases hz' with ⟨ hxz, hzy ⟩
      have hxy : x < y := gt_trans hzy hxz
      apply noncompact_ioo x y hxy
    · rcases h with ⟨ x, h ⟩
      rw [←h]
      have hz' : a.toFun z ∈ a.target := by exact PartialEquiv.map_source a.toPartialEquiv hz
      rw [←h] at hz'
      simp only [Set.mem_Iio] at hz'
      have hx : 0 < x := by exact pos_of_gt hz'
      apply noncompact_iio x hx
