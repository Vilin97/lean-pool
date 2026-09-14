/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Example.LowerDensity
public import LeanPool.Besicovitch.Example.Reduction
public import LeanPool.Besicovitch.Example.Zero
public import LeanPool.Besicovitch.Main.RationalBound
public import LeanPool.Besicovitch.Sigma.Basic

/-!
# The planar threshold is at least `1/2`

Besicovitch's set `Π`, the graph of `g` over `[0, 1]`, is measurable and has positive finite
length.  It is purely unrectifiable: a Lipschitz curve meeting it in positive length would make
`g` Lipschitz on a set of positive Lebesgue measure (`LeanPool.Besicovitch.Example.Reduction`), which is
impossible (`LeanPool.Besicovitch.Example.Zero`).  On the other hand its lower one-density is at least
`1/2` at every interior point (`LeanPool.Besicovitch.Example.LowerDensity`), hence almost everywhere.
So no threshold below `1/2` forces one-rectifiability in the plane, and `sigmaOne ℝ² ≥ 1/2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace LeanPool.Besicovitch.Example

/-- Besicovitch's set has positive length. -/
theorem hausdorffMeasure_besicovitchSet_pos : 0 < μH[1] besicovitchSet := by
  have h := volume_le_hausdorffMeasure_graphMap_image (Icc (0:ℝ) 1)
  rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one] at h
  exact lt_of_lt_of_le zero_lt_one h

/-- Besicovitch's set has finite length. -/
theorem hausdorffMeasure_besicovitchSet_lt_top : μH[1] besicovitchSet < ∞ := by
  have h := hausdorffMeasure_graphMap_image_le (Icc (0:ℝ) 1)
  rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one] at h
  exact lt_of_le_of_lt h ENNReal.ofNat_lt_top

/-- A Lipschitz curve meets Besicovitch's set in a null set. -/
theorem hausdorffMeasure_range_inter_besicovitchSet {K : ℝ≥0} {f : ℝ → Plane}
    (hf : LipschitzWith K f) : μH[1] (range f ∩ besicovitchSet) = 0 := by
  by_contra hne
  obtain ⟨L, A, hA, hvol, hg⟩ :=
    exists_lipschitzOnWith_of_hausdorffMeasure_pos hf (pos_iff_ne_zero.mpr hne)
  exact hvol.ne' (volume_eq_zero_of_lipschitzOnWith hA hg)

/-- Besicovitch's set is not countably one-rectifiable. -/
theorem not_isCountablyOneRectifiable_besicovitchSet :
    ¬ IsCountablyOneRectifiable besicovitchSet := by
  rintro ⟨f, hf, hnull⟩
  have hcover : besicovitchSet ⊆
      (besicovitchSet \ ⋃ i, range (f i)) ∪ ⋃ i, (range (f i) ∩ besicovitchSet) := by
    intro p hp
    by_cases h : p ∈ ⋃ i, range (f i)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact Or.inr (mem_iUnion.mpr ⟨i, hi, hp⟩)
    · exact Or.inl ⟨hp, h⟩
  have hzero : μH[1] besicovitchSet = 0 := by
    refine measure_mono_null hcover (measure_union_null hnull (measure_iUnion_null fun i ↦ ?_))
    obtain ⟨K, hK⟩ := hf i
    exact hausdorffMeasure_range_inter_besicovitchSet hK
  exact hausdorffMeasure_besicovitchSet_pos.ne' hzero

/-- Almost every point of Besicovitch's set has lower density at least `1/2`. -/
theorem ae_one_half_le_lowerOneDensity :
    ∀ᵐ p ∂(μH[1].restrict besicovitchSet),
      ENNReal.ofReal (1 / 2) ≤ lowerOneDensity besicovitchSet p := by
  rw [ae_restrict_iff' measurableSet_besicovitchSet, ae_iff]
  refine measure_mono_null ?_
    (hausdorffMeasure_graphMap_image_eq_zero (A := {0, 1})
      (((Set.finite_singleton (1:ℝ)).insert 0).measure_zero volume))
  intro p hp
  simp only [mem_setOf_eq, Classical.not_imp] at hp
  obtain ⟨⟨x, hx, rfl⟩, hbad⟩ := hp
  refine ⟨x, ?_, rfl⟩
  by_contra hx01
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx01
  exact hbad (one_half_le_lowerOneDensity_graphMap
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hx01.1), lt_of_le_of_ne hx.2 hx01.2⟩)

/-- No threshold below `1/2` forces one-rectifiability in the plane. -/
theorem not_forcesOneRectifiability_of_lt_half {β : ℝ} (hβ : β < 1 / 2) :
    ¬ ForcesOneRectifiability (EuclideanSpace ℝ (Fin 2)) (ENNReal.ofReal β) := by
  intro h
  apply not_isCountablyOneRectifiable_besicovitchSet
  refine h besicovitchSet measurableSet_besicovitchSet
    hausdorffMeasure_besicovitchSet_lt_top ?_
  exact ae_one_half_le_lowerOneDensity.mono fun p hp ↦
    (ENNReal.ofReal_le_ofReal hβ.le).trans hp

/-- The planar threshold is at least `1/2`. -/
theorem one_half_le_sigmaOne_plane :
    (1 / 2 : ℝ) ≤ sigmaOne (EuclideanSpace ℝ (Fin 2)) := by
  unfold sigmaOne
  apply le_csInf
  · refine ⟨7 / 10, by norm_num, ?_⟩
    exact forcesOneRectifiability_plane_of_barS_lt (by rw [barS_eq]; norm_num)
  · rintro β ⟨_, hβ⟩
    by_contra hlt
    exact not_forcesOneRectifiability_of_lt_half (not_le.mp hlt) hβ

end LeanPool.Besicovitch.Example
