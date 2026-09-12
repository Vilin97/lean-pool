/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Rectifiability.BadConvexLocalization
public import LeanPool.Besicovitch.Rectifiability.ComponentDiameter

/-!
# Removing the local attachment holes

Every point of the compact attachment union outside the core lies in an attachment.  If that
point also lies in a local set `C`, the attachment's three-diameter enlargement is one of the
holes recorded as touching `C`.
-/

@[expose] public section

noncomputable section

open Set

namespace LeanPool.Besicovitch

/-- Removing every three-diameter enlargement which touches `C` leaves only points of the compact
core `F`. -/
theorem sdiff_iUnion_touchingBadConvexSets_subset_core
    {mu : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2))}
    {F C : Set (EuclideanSpace ℝ (Fin 2))} {alpha : ℝ} (halpha : 0 < alpha)
    {chosen : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hchosen : chosen ⊆ badConvexSets mu F alpha)
    (hC : C ⊆ compactAttachmentUnion F chosen) :
    C \ ⋃ V : touchingBadConvexSets 3 chosen C,
        diameterThickening 3 (V : Set (EuclideanSpace ℝ (Fin 2))) ⊆ F := by
  intro x hx
  rcases hC hx.1 with hxF | hxAttachment
  · exact hxF
  · obtain ⟨V, hxV⟩ := mem_iUnion.1 hxAttachment
    have hVbad := hchosen V.property
    have hxThickening : x ∈ diameterThickening 3 (V : Set (EuclideanSpace ℝ (Fin 2))) :=
      convexAttachment_subset_diameterThickening_three hVbad.2.1
        (diam_pos_of_mem_badConvexSets halpha hVbad) hxV
    let W : touchingBadConvexSets 3 chosen C :=
      ⟨V, V.property, ⟨x, hxThickening, hx.1⟩⟩
    exact (hx.2 (mem_iUnion_of_mem W hxThickening)).elim

end LeanPool.Besicovitch
