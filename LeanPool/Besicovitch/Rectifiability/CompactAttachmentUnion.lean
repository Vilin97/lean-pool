/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Rectifiability.ConvexAttachment
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The compact union of convex attachments

If the selected holes have finite total diameter, their compact attachments accumulate only on
the compact core.  Consequently the core together with all attachments is compact.
-/

@[expose] public section

noncomputable section

open Bornology Set
open scoped ENNReal Topology

namespace LeanPool.Besicovitch

/-- The compact core together with all convex pieces attached along selected holes. -/
def compactAttachmentUnion (F : Set (EuclideanSpace ℝ (Fin 2)))
    (chosen : Set (Set (EuclideanSpace ℝ (Fin 2)))) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  F ∪ ⋃ V : chosen, convexAttachment F (V : Set (EuclideanSpace ℝ (Fin 2)))

/-- Finite total hole diameter makes the full attachment union compact. -/
theorem isCompact_compactAttachmentUnion {mu : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2))}
    {F : Set (EuclideanSpace ℝ (Fin 2))} (hF : IsCompact F)
    {alpha : ℝ} (halpha : 0 < alpha) {chosen : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hchosen : chosen ⊆ badConvexSets mu F alpha)
    (hsum : ∑' V : chosen, Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2))) ≠ ∞) :
    IsCompact (compactAttachmentUnion F chosen) := by
  classical
  rw [isCompact_iff_finite_subcover]
  intro ι U hU_open hcover
  have hcoverF : F ⊆ ⋃ i, U i := fun x hx ↦ hcover (Or.inl hx)
  obtain ⟨coreCover, hcoreCover⟩ := hF.elim_finite_subcover U hU_open hcoverF
  let O := ⋃ i ∈ coreCover, U i
  have hO_open : IsOpen O := isOpen_biUnion fun i _ ↦ hU_open i
  obtain ⟨epsilon, hepsilon, hthickening⟩ :=
    hF.exists_thickening_subset_open hO_open hcoreCover
  let large : Set chosen :=
    {V | ENNReal.ofReal (epsilon / 5) ≤ Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2)))}
  have hlarge_finite : large.Finite := by
    exact ENNReal.finite_const_le_of_tsum_ne_top hsum
      (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
  letI : Fintype large := hlarge_finite.fintype
  have hattachment_compact (V : large) :
      IsCompact (convexAttachment F (V : Set (EuclideanSpace ℝ (Fin 2)))) :=
    isCompact_convexAttachment hF
  have hattachment_cover (V : large) :
      convexAttachment F (V : Set (EuclideanSpace ℝ (Fin 2))) ⊆ ⋃ i, U i := by
    intro x hx
    exact hcover (Or.inr (mem_iUnion_of_mem (V : chosen) hx))
  choose attachmentCover hattachmentCover using fun V : large ↦
    (hattachment_compact V).elim_finite_subcover U hU_open (hattachment_cover V)
  let cover := coreCover ∪ Finset.univ.biUnion attachmentCover
  refine ⟨cover, ?_⟩
  have hsmall {V : chosen} (hVsmall : V ∉ large) :
      convexAttachment F (V : Set (EuclideanSpace ℝ (Fin 2))) ⊆ O := by
    have hVbad := hchosen V.property
    have hVbounded := isBounded_of_mem_badConvexSets halpha hVbad
    have hVdiam := diam_pos_of_mem_badConvexSets halpha hVbad
    have hedV :
        Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2))) < ENNReal.ofReal (epsilon / 5) := by
      exact lt_of_not_ge hVsmall
    have hattachment_ediam :
        Metric.ediam (convexAttachment F (V : Set (EuclideanSpace ℝ (Fin 2)))) <
        ENNReal.ofReal epsilon := by
      calc
        Metric.ediam (convexAttachment F (V : Set (EuclideanSpace ℝ (Fin 2)))) ≤
            ENNReal.ofReal 5 * Metric.ediam (V : Set (EuclideanSpace ℝ (Fin 2))) :=
          ediam_convexAttachment_le hVbounded
        _ < ENNReal.ofReal 5 * ENNReal.ofReal (epsilon / 5) :=
          ENNReal.mul_lt_mul_right (by norm_num) ENNReal.ofReal_ne_top hedV
        _ = ENNReal.ofReal epsilon := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
          congr 1
          field_simp
    intro x hx
    apply hthickening
    obtain ⟨f, hfV, hfF⟩ := hVbad.2.2.1
    have hfattachment : f ∈ convexAttachment F (V : Set (EuclideanSpace ℝ (Fin 2))) :=
      inter_subset_convexAttachment hVdiam ⟨hfF, hfV⟩
    have hdist : dist x f < epsilon := by
      have hedist := (Metric.edist_le_ediam_of_mem hx hfattachment).trans_lt
        hattachment_ediam
      rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hepsilon] at hedist
      exact hedist
    rw [Metric.mem_thickening_iff]
    exact ⟨f, hfF, hdist⟩
  intro x hx
  rcases hx with hxF | hxattachment
  · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcoreCover hxF)
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_union_left _ hi, hxi⟩
  · obtain ⟨V, hxV⟩ := mem_iUnion.mp hxattachment
    by_cases hVlarge : V ∈ large
    · let W : large := ⟨V, hVlarge⟩
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hattachmentCover W hxV)
      apply mem_iUnion₂.mpr
      refine ⟨i, ?_, hxi⟩
      exact Finset.mem_union_right _ <| Finset.mem_biUnion.mpr ⟨W, Finset.mem_univ _, hi⟩
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hsmall hVlarge hxV)
      exact mem_iUnion₂.mpr ⟨i, Finset.mem_union_left _ hi, hxi⟩

end LeanPool.Besicovitch
