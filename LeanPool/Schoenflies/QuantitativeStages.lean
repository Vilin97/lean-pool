/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.FreshDenseSelection
public import LeanPool.Schoenflies.StageTransition

/-!
# Quantitative successor stages

The reverse half of the quantitative-refinement recursion is now a closed construction.  From
one generated pair over the closed Jordan domain and one requested positive bound, it selects an
exact finite target-segment cover, a sufficiently fine square-mesh overlay, finitely many clean
accessible boundary anchors, and the reverse finite transfer.  Its target stars are smaller than
the requested bound.

## Blueprint

* `Schoenflies.QuantitativeReverseStage` — all construction data for one reverse quantitative
  successor.
* `Schoenflies.exists_quantitativeReverseStage` — construction from separation
  and the persistent outer-cycle invariant.
* `Schoenflies.QuantitativeReverseStage.transition` — the output is a `StageTransition`.
* `Schoenflies.QuantitativeReverseStage.diam_targetStar_lt_bound` — the uniform half of
  `prop:shrinking-stars` at this successor.
* `Schoenflies.TargetFaceMesh.refine` — subsequent forward transfers preserve the target
  face-mesh estimate.
-/

public section

open Set

namespace Schoenflies

variable {γ : Type*} {S₀ : CellStructure γ} {C : Set Plane}
  {P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)}

/-- A uniform mesh bound on the closed target 2-cells of a generated pair. -/
def TargetFaceMesh
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (bound : ℝ) : Prop :=
  ∀ {F : γ}, F ∈ P.str.faces → Metric.diam (closure (P.tgt.cell F)) < bound

namespace TargetFaceMesh

variable {T : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)}
  {par : γ → γ} {bound : ℝ}

/-- A target face-mesh bound survives any compatible refinement. -/
theorem refine (hmesh : TargetFaceMesh P bound) (href : T.tgt.Refines P.tgt par) :
    TargetFaceMesh T bound := by
  intro F hF
  exact lt_of_le_of_lt
    (href.diam_cell_le P.tgt_isCellDecomposition
      (Plane.isBounded_closedSquare 0 1) (T.str.mem_cells_of_mem_faces hF))
    (hmesh (href.parent_mem_faces hF))

/-- In particular, direction (a) of finite transfer preserves the target mesh bound. -/
theorem forwardTransfer (hmesh : TargetFaceMesh P bound)
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (h : IsTransferOf T P H Hdraw par) : TargetFaceMesh T bound :=
  hmesh.refine h.refines_tgt

/-- A target face-mesh estimate gives the corresponding factor-two bound on every star. -/
theorem diam_star_lt (hmesh : TargetFaceMesh P bound)
    {σ : γ} (hσ : σ ∈ P.str.cells) :
    Metric.diam (P.tgt.star σ) < 2 * bound :=
  P.tgt_isCellDecomposition.diam_star_lt P.str_combInvariants
    (Plane.isBounded_closedSquare 0 1) hσ
    (fun _ hF _ => hmesh hF)

end TargetFaceMesh

/-- The complete output of one quantitatively bounded reverse-transfer successor. -/
structure QuantitativeReverseStage
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (anchors : List Plane) (bound : ℝ) where
  /-- A finite exact segment presentation of the old target skeleton. -/
  cover : TargetSegmentCover P
  /-- The chosen overlay and transferred generated pair. -/
  overlay : TargetSegmentCover.MeshOverlayTransferData cover anchors
  /-- Half the requested bound leaves room for the factor two in the star estimate. -/
  delta_lt_half_bound : overlay.delta < bound / 2

namespace QuantitativeReverseStage

variable {anchors : List Plane} {bound : ℝ}
  (w : QuantitativeReverseStage P anchors bound)

/-- The generated pair at the new successor stage. -/
abbrev pair : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1) :=
  w.overlay.pair

/-- The common abstract parent map from the successor to the old stage. -/
abbrev parent : γ → γ := w.overlay.parent

/-- Reverse finite transfer supplies exactly the common transition interface used by the tower. -/
theorem transition : StageTransition w.pair P w.parent :=
  w.overlay.transfer.stageTransition

/-- Every target star at the successor has diameter below the prescribed bound. -/
theorem diam_targetStar_lt_bound {σ : γ} (hσ : σ ∈ w.pair.str.cells) :
    Metric.diam (w.pair.tgt.star σ) < bound := by
  have hstar := w.overlay.diam_targetStar_lt hσ
  linarith [w.delta_lt_half_bound]

/-- The stronger face-level estimate retained by later forward refinements. -/
theorem targetFaceMesh : TargetFaceMesh w.pair w.overlay.delta := by
  intro F hF
  exact w.overlay.diam_closure_targetFace_lt hF

end QuantitativeReverseStage

/-- **Quantitative reverse successor.** Every generated stage over the closed
Jordan domain admits a reverse transferred refinement whose target stars are smaller than any
specified positive bound. -/
theorem exists_quantitativeReverseStage [Infinite γ]
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hsep : IsSeparating C) (hcycle : S₀.OuterEdgesFormCycle)
    (anchors : List Plane) {bound : ℝ} (hbound : 0 < bound) :
    Nonempty (QuantitativeReverseStage P anchors bound) := by
  obtain ⟨Q⟩ := P.exists_targetSegmentCover
  have hhalf : 0 < bound / 2 := by positivity
  obtain ⟨w, hw⟩ := Q.exists_meshOverlayTransferData_lt_inside
    hsep hcycle anchors hhalf
  exact ⟨{ cover := Q, overlay := w, delta_lt_half_bound := hw }⟩

end Schoenflies
