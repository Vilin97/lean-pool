/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.SourceJoining
import LeanPool.Schoenflies.QuantitativeStages
import LeanPool.Schoenflies.StageTower
import LeanPool.Schoenflies.Windows

/-!
# Quantitative forward local-grid stages

The local-grid attachment supplies a complete raw grid in the source skeleton.
This module turns that containment into the pointwise source-star estimate used by
`prop:shrinking-stars`, and records that the target face mesh from the preceding reverse stage
survives the forward refinement.
-/

open Metric Set

namespace Schoenflies

variable {γ : Type*} [Nonempty γ] {S₀ : CellStructure γ} {C : Set Plane}
  {P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)}

/-- The frame of a positive local-grid square is contained in its raw grid carrier. -/
theorem localGrid_frame_subset {p : Plane} {s : ℝ} {k : ℕ}
    (hs : 0 < s) (hk : 1 ≤ k) :
    Plane.closedSquare p s \ Plane.openSquare p s ⊆
      cover (localGridEdges p s k) := by
  intro z hz
  have hclosed := hz.1
  rw [Plane.closedSquare_eq_inter] at hclosed
  have hopen := hz.2
  rw [Plane.openSquare_eq_inter] at hopen
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hclosed
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, not_and_or, not_lt] at hopen
  rcases hopen with hX | hY
  · rcases hX with hleft | hright
    · exact mem_cover_of_coord_eq hs hk (Nat.zero_le k) hz.1 (by
        rw [localGridX_zero]
        linarith [hclosed.1.1])
    · exact mem_cover_of_coord_eq hs hk (le_refl k) hz.1 (by
        rw [localGridX_last hk]
        linarith [hclosed.1.2])
  · rcases hY with hbottom | htop
    · exact mem_cover_of_coord_eq' hs hk (Nat.zero_le k) hz.1 (by
        rw [localGridY_zero]
        linarith [hclosed.2.1])
    · exact mem_cover_of_coord_eq' hs hk (le_refl k) hz.1 (by
        rw [localGridY_last hk]
        linarith [hclosed.2.2])

namespace LocalGridForwardStageData

variable {p : Plane} {s epsilon : ℝ}
  (w : LocalGridForwardStageData P p s epsilon)

/-- Every new source face incident with a point in the open grid window stays inside that
window.  Its connected open cell cannot cross the grid's outer frame, which is now part of the
source skeleton. -/
theorem face_subset_openSquare (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ (C ∪ inside C) \ C)
    {x : Plane} (hx : x ∈ Plane.openSquare p s)
    {F : γ} (hF : F ∈ w.pair.str.faces)
    (hsub : w.pair.str.sub (w.pair.src.carrier x) F) :
    w.pair.src.cell F ⊆ Plane.openSquare p s := by
  have hxClosed : x ∈ Plane.closedSquare p s := by
    change Plane.supDist x p ≤ s
    exact hx.le
  have hxDom : x ∈ C ∪ inside C := (hwindow hxClosed).1
  have hxCell : x ∈ w.pair.src.cell (w.pair.src.carrier x) :=
    w.pair.src_isCellDecomposition.mem_cell_carrier hxDom
  have hxClosure : x ∈ closure (w.pair.src.cell F) :=
    w.pair.src_isCellDecomposition.mem_closure_face
      (w.pair.src_isCellDecomposition.mem_cells_carrier hxDom) hF hsub hxCell
  obtain ⟨ρ, hρ, hball⟩ :=
    Metric.isOpen_iff.1 (Plane.isOpen_openSquare p s) x hx
  obtain ⟨y, hyFace, hyDist⟩ := Metric.mem_closure_iff.1 hxClosure ρ hρ
  have hyOpen : y ∈ Plane.openSquare p s := hball (by
    rw [mem_ball, dist_comm]
    exact hyDist)
  have hfrontier : frontier (Plane.openSquare p s) ⊆ w.pair.src.skeletonSet := by
    intro z hz
    apply w.localGrid_subset
    rw [localGrid_eq, pieceListGraph_pointSet]
    exact localGrid_frame_subset hs (one_le_localGridCount s epsilon)
      (frontier_openSquare_subset p s hz)
  exact subset_of_isPreconnected_of_frontier_disjoint
    (Plane.isOpen_openSquare p s)
    (w.pair.src_isFaceJordan.isConnected hF).isPreconnected
    ((w.pair.src.disjoint_cell_skeletonSet
      w.pair.src_isCellDecomposition hF).mono_right hfrontier)
    ⟨y, hyFace, hyOpen⟩

/-- Every source face incident with a point in the open window has closed diameter at most the
chosen local-grid mesh bound. -/
theorem diam_closure_face_le (hs : 0 < s) (hepsilon : 0 < epsilon)
    (hwindow : Plane.closedSquare p s ⊆ (C ∪ inside C) \ C)
    {x : Plane} (hx : x ∈ Plane.openSquare p s)
    {F : γ} (hF : F ∈ w.pair.str.faces)
    (hsub : w.pair.str.sub (w.pair.src.carrier x) F) :
    diam (closure (w.pair.src.cell F)) ≤ epsilon := by
  rw [Metric.diam_closure]
  apply Metric.diam_le_of_forall_dist_le hepsilon.le
  intro y hy z hz
  apply le_of_lt
  refine lt_trans ?_ (localGridCount_spec (s := s) hepsilon)
  apply dist_lt_of_avoiding_localGrid (p := p) hs
    (one_le_localGridCount s epsilon)
    (w.pair.src_isFaceJordan.isConnected hF).isPreconnected
    ((w.face_subset_openSquare hs hwindow hx hF hsub).trans fun q hq => by
      change Plane.supDist q p ≤ s
      exact hq.le)
  · intro q hq hqGrid
    exact Set.disjoint_left.1
      (w.pair.src.disjoint_cell_skeletonSet
        w.pair.src_isCellDecomposition hF) hq
      (w.localGrid_subset (by
        rw [localGrid_eq, pieceListGraph_pointSet]
        exact hqGrid))
  · exact hy
  · exact hz

/-- **`lem:grid-star-estimate`.** At a point in the open grid window, the new source star has
diameter at most twice the selected mesh bound. -/
theorem diam_sourceStar_le (hC : IsSeparating C)
    (hs : 0 < s) (hepsilon : 0 < epsilon)
    (hwindow : Plane.closedSquare p s ⊆ (C ∪ inside C) \ C)
    {x : Plane} (hx : x ∈ Plane.openSquare p s) :
    diam (w.pair.src.star (w.pair.src.carrier x)) ≤ 2 * epsilon := by
  have hxClosed : x ∈ Plane.closedSquare p s := by
    change Plane.supDist x p ≤ s
    exact hx.le
  have hxDom : x ∈ C ∪ inside C := (hwindow hxClosed).1
  exact w.pair.src_isCellDecomposition.diam_star_le
    w.pair.str_combInvariants (isBounded_union_inside hC)
    (w.pair.src_isCellDecomposition.mem_cells_carrier hxDom)
    (fun F hF hsub => w.diam_closure_face_le hs hepsilon hwindow hx hF hsub)

omit [Nonempty γ] in
/-- A target face-mesh estimate survives the forward local-grid stage. -/
theorem targetFaceMesh {bound : ℝ} (hmesh : TargetFaceMesh P bound) :
    TargetFaceMesh w.pair bound :=
  hmesh.refine w.transition.refines_tgt

end LocalGridForwardStageData

omit [Nonempty γ] in
/-- The window used by quantitative refinement automatically satisfies every geometric
hypothesis of the local-grid forward constructor. -/
theorem GeneratedPair.exists_localGridForwardStageData_window [Infinite γ]
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hC : IsSeparating C) {p : Plane} (hp : p ∈ inside C)
    {windowEpsilon meshEpsilon : ℝ}
    (hwindowEpsilon : 0 < windowEpsilon) (_hmeshEpsilon : 0 < meshEpsilon)
    (hsource : IsConnected P.src.nonboundary) :
    Nonempty (LocalGridForwardStageData P p
      (windowRadius C windowEpsilon p) meshEpsilon) := by
  have hpC : p ∉ C := fun hpC => inside_subset_compl hp hpC
  have hs : 0 < windowRadius C windowEpsilon p :=
    windowRadius_pos hC.isJordanCurve.isCompact
      hC.isJordanCurve.nonempty hpC
  have hwindow : window C windowEpsilon p ⊆ (C ∪ inside C) \ C := by
    intro x hx
    have hxInside := window_subset_inside hC.isJordanCurve.isCompact
      hC.isJordanCurve.nonempty hC hp hwindowEpsilon hx
    exact ⟨Or.inr hxInside, inside_subset_compl hxInside⟩
  exact P.exists_localGridForwardStageData hC hs hwindow hsource

/-- One quantitative forward successor: the local-grid refinement together with
the target face-mesh estimate inherited from the preceding reverse stage. -/
structure QuantitativeForwardStage
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (p : Plane) (windowEpsilon meshEpsilon targetBound : ℝ) where
  forward : LocalGridForwardStageData P p
    (windowRadius C windowEpsilon p) meshEpsilon
  targetFaceMesh : TargetFaceMesh forward.pair targetBound

namespace QuantitativeForwardStage

variable {p : Plane} {windowEpsilon meshEpsilon targetBound : ℝ}
  (w : QuantitativeForwardStage P p windowEpsilon meshEpsilon targetBound)

/-- The generated pair at the forward successor. -/
abbrev pair : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1) :=
  w.forward.pair

/-- The shared parent map to the preceding stage. -/
abbrev parent : γ → γ := w.forward.parent

omit [Nonempty γ] in
/-- The forward successor exposes the common transition interface. -/
theorem transition : StageTransition w.pair P w.parent := w.forward.transition

/-- The local-grid estimate in the window form used by `prop:shrinking-stars`. -/
theorem diam_sourceStar_le (hC : IsSeparating C)
    (hp : p ∈ inside C)
    (hwindowEpsilon : 0 < windowEpsilon) (hmeshEpsilon : 0 < meshEpsilon)
    {x : Plane} (hx : x ∈ openWindow C windowEpsilon p) :
    diam (w.pair.src.star (w.pair.src.carrier x)) ≤ 2 * meshEpsilon := by
  have hwindow : window C windowEpsilon p ⊆ (C ∪ inside C) \ C := by
    intro z hz
    have hzInside := window_subset_inside hC.isJordanCurve.isCompact
      hC.isJordanCurve.nonempty hC hp hwindowEpsilon hz
    exact ⟨Or.inr hzInside, inside_subset_compl hzInside⟩
  exact w.forward.diam_sourceStar_le hC
    (windowRadius_pos hC.isJordanCurve.isCompact hC.isJordanCurve.nonempty
      (fun hpC => inside_subset_compl hp hpC))
    hmeshEpsilon hwindow hx

end QuantitativeForwardStage

omit [Nonempty γ] in
/-- Construct a quantitative forward successor from any target face-mesh estimate on the
preceding stage. -/
theorem GeneratedPair.exists_quantitativeForwardStage [Infinite γ]
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hC : IsSeparating C) {p : Plane} (hp : p ∈ inside C)
    {windowEpsilon meshEpsilon targetBound : ℝ}
    (hwindowEpsilon : 0 < windowEpsilon) (hmeshEpsilon : 0 < meshEpsilon)
    (hsource : IsConnected P.src.nonboundary)
    (hmesh : TargetFaceMesh P targetBound) :
    Nonempty (QuantitativeForwardStage P p windowEpsilon meshEpsilon targetBound) := by
  obtain ⟨w⟩ := P.exists_localGridForwardStageData_window hC hp
    hwindowEpsilon hmeshEpsilon hsource
  exact ⟨{ forward := w, targetFaceMesh := w.targetFaceMesh hmesh }⟩

/-- One complete quantitative successor consists of the uniform reverse target refinement and
the pointwise forward source-grid refinement. -/
structure QuantitativeSuccessor
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (anchors : List Plane) (p : Plane)
    (windowEpsilon sourceBound targetBound : ℝ) where
  reverse : QuantitativeReverseStage P anchors targetBound
  forward : QuantitativeForwardStage reverse.pair p windowEpsilon sourceBound
    reverse.overlay.delta

namespace QuantitativeSuccessor

variable {anchors : List Plane} {p : Plane}
  {windowEpsilon sourceBound targetBound : ℝ}
  (w : QuantitativeSuccessor P anchors p windowEpsilon sourceBound targetBound)

/-- The generated pair at the end of the two half-steps. -/
abbrev pair : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1) :=
  w.forward.pair

/-- The composite shared parent map to the preceding full stage. -/
abbrev parent : γ → γ := w.reverse.parent ∘ w.forward.parent

omit [Nonempty γ] in
/-- The reverse and forward transitions compose to one full-stage transition. -/
theorem transition : StageTransition w.pair P w.parent :=
  w.forward.transition.trans w.reverse.transition

omit [Nonempty γ] in
/-- The uniform target-star estimate survives the following forward refinement. -/
theorem diam_targetStar_lt {σ : γ} (hσ : σ ∈ w.pair.str.cells) :
    diam (w.pair.tgt.star σ) < targetBound := by
  have hstar := TargetFaceMesh.diam_star_lt w.forward.targetFaceMesh hσ
  linarith [w.reverse.delta_lt_half_bound]

/-- The pointwise source-star estimate at every point caught by this stage's window. -/
theorem diam_sourceStar_le (hC : IsSeparating C) (hp : p ∈ inside C)
    (hwindowEpsilon : 0 < windowEpsilon) (hsourceBound : 0 < sourceBound)
    {x : Plane} (hx : x ∈ openWindow C windowEpsilon p) :
    diam (w.pair.src.star (w.pair.src.carrier x)) ≤ 2 * sourceBound :=
  w.forward.diam_sourceStar_le hC hp hwindowEpsilon hsourceBound hx

end QuantitativeSuccessor

omit [Nonempty γ] in
/-- **Quantitative successor.** Starting from any generated stage, construct a
refinement with the requested target-star bound and a source-star bound throughout the selected
window. -/
theorem GeneratedPair.exists_quantitativeSuccessor [Infinite γ]
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hC : IsSeparating C) (hcycle : S₀.OuterEdgesFormCycle)
    (anchors : List Plane) {p : Plane} (hp : p ∈ inside C)
    {windowEpsilon sourceBound targetBound : ℝ}
    (hwindowEpsilon : 0 < windowEpsilon) (hsourceBound : 0 < sourceBound)
    (htargetBound : 0 < targetBound) :
    Nonempty (QuantitativeSuccessor P anchors p
      windowEpsilon sourceBound targetBound) := by
  obtain ⟨r⟩ := exists_quantitativeReverseStage P
    hC hcycle anchors htargetBound
  obtain ⟨f⟩ := r.pair.exists_quantitativeForwardStage hC hp
    hwindowEpsilon hsourceBound
    r.overlay.transfer.src_isAdmissible.isConnected_nonboundary r.targetFaceMesh
  exact ⟨{ reverse := r, forward := f }⟩

end Schoenflies
