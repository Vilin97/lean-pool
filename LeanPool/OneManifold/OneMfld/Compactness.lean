/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import LeanPool.OneManifold.OneMfld.FiniteIntervalCharts
public import LeanPool.OneManifold.OneMfld.Noncompact

/-!
# Compactness

Supporting results for the classification of compact one-dimensional manifolds.
-/

public section

namespace OneMfld

variable
  {M : Type*}
  [TopologicalSpace M]

lemma clopen_in_r (s : Set NNReal) : (s ≠ ∅ ∧ s ≠ Set.univ) → ¬ IsClopen s := by
  intro h12 hs
  exact (isClopen_iff.mp hs).elim h12.1 h12.2

lemma noncompact_nnreal : NoncompactSpace NNReal := by
  have := not_compactSpace_NNReal
  exact not_compactSpace_iff.mp this

private lemma noncompact_open_nnreal (s : Set NNReal) (ho : IsOpen s) (hn : s.Nonempty) :
    NoncompactSpace s := by
  apply not_compactSpace_iff.mp
  intro h
  have hc := isCompact_iff_compactSpace.mpr h
  rcases isClopen_iff.mp ⟨hc.isClosed, ho⟩ with he | hu
  · exact hn.ne_empty he
  · rw [hu] at hc
    exact not_compactSpace_NNReal ⟨hc⟩

lemma noncompact_ioo' (x y : NNReal) (hxy : x < y) : NoncompactSpace (Set.Ioo x y) :=
  noncompact_open_nnreal _ isOpen_Ioo (Set.nonempty_Ioo.mpr hxy)

lemma noncompact_ioo (x y : NNReal) (hxy : x < y) : ¬ CompactSpace (Set.Ioo x y) := by
  have h := noncompact_ioo' x y hxy
  exact not_compactSpace_iff.mpr h

lemma noncompact_iio' (x : NNReal) (hx : 0 < x) : NoncompactSpace (Set.Iio x) :=
  noncompact_open_nnreal _ isOpen_Iio ⟨0, hx⟩

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

end OneMfld
