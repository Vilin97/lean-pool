/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.RefinementStars
import LeanPool.Schoenflies.OverlayGraph
import LeanPool.Schoenflies.SkeletonAccess
import LeanPool.Schoenflies.Graph.RelativeEar
import LeanPool.Schoenflies.Graph.Relabel
import LeanPool.Schoenflies.Graph.CycleJordan
import LeanPool.Schoenflies.JordanClosed
import LeanPool.Schoenflies.BoundaryCyclesGenerated
import LeanPool.Schoenflies.MatchedSplit
import LeanPool.Schoenflies.MatchedArc

/-!
# Finite transfer, direction (a): toward the square

`thm:finite-transfer` is the largest single statement of the manuscript. This module states it —
in full, with every hypothesis — for **direction (a)** only, and proves as much of its four-step
proof as is within reach of what is on `main`.

Direction (b) is deliberately absent: its extra accessibility problem at the wild source
boundary needs `lem:tangent-cone`, `lem:compact-separation`(c) and the fresh-point bookkeeping
of the target mesh, none of which enters (a).

## The statement, and how it is read

The blueprint's (a) reads: *let `(Γ, Γ')` be a generated matched cellulation; suppose `H` is a
finite 2-connected plane graph containing a subdivision of `Γ`, with outer cycle `C`, with every
nonboundary edge polygonal, and with `|H| ∖ C` connected; then the common subdivision can be
made on `Γ'`, and `H` can be transferred to an admissible target realization `H'`; the resulting
generated matched cellulation refines the old one by explicit parent maps.*

Four objects carry that sentence.

* `Schoenflies.CellStructure.Realization.IsWeaklyAdmissible` and
  `Schoenflies.CellStructure.Realization.IsAdmissible` — `def:admissible-graph`. The weak form
  is exactly the strong one with connectedness of the open nonboundary part waived, which is
  what `def:generated-structure` requires of an intermediate stage and what
  `rem:intermediate-disconnection` insists on.
* `Schoenflies.GeneratedPair` — a generated matched cell structure *with its geometry*: the
  abstract structure, its two realizations, the skeleton homeomorphism, and the two cell
  decompositions. This is the Lean form of "`(Γ, Γ')` is a generated matched cellulation".
  It is a bundle of **data**, not an existential: every consumer reads `.src`, `.tgt`, `.homeo`
  by name.
* `Schoenflies.IsSourceExtension` — the hypotheses on `H`.
* `Schoenflies.IsTransferOf` — the conclusion, relating the new pair to the old one by an
  explicit parent map.

The one place where the Lean statement is *weaker in form* than the prose, and deliberately so:
"`H` can be transferred" is recorded as `T.src.skeletonSet = pointSet H Hdraw`, an equality of
point sets, rather than as a graph isomorphism onto `H`. The reason is step 1: the common
subdivision inserts a vertex at every intersection of a new edge with an old one, so the source
realization of the transferred structure realizes a *subdivision* of `H`, never `H` itself. What
survives verbatim is what the construction uses downstream — the occupied set, the
2-connectivity (which `lem:combinatorial-invariance` moves to the target) and the refinement.

## What is proved here

* **Step 1, the overlay** — `Schoenflies.exists_overlay_of_biUnion_finite`: the union of
  finitely many nondegenerate polygonal sets is the point set of a finite plane graph drawn by
  straight segments. That is `lem:polygonal-overlay` in the form step 1 needs, bridging
  `Schoenflies.polygonal_overlay`, which is stated for a list of segments, to the finite family
  of polygonal *arcs* a skeleton stage arrives as.
* **Step 4, target side** — `Schoenflies.exists_target_crosscut` and
  `Schoenflies.exists_target_crosscut_split`. In direction (a) the target face `F*` is a
  polygonal Jordan region in the square by `lem:cellulation-invariants`(vii); every point of its
  boundary is polygonally accessible from its interior by `lem:polygonal-side-accessibility`
  (target half); and `lem:accessible-endpoints` gives a polygonal crosscut `P* ⊆ closure F*`
  from `v*` to `w*`, which by `thm:general-crosscut` splits `F*` into exactly the two Jordan
  regions bounded by `P*` and the two boundary paths. These constructions supply the complete
  target-side argument.
* **The second sentence of step 2** — `…IsCellDecomposition.exists_unique_face_subset_cell` and
  `…IsCellDecomposition.exists_face_of_ear`: the interior of an ear lies in one current face,
  because it is connected and disjoint from the current skeleton, and its two endpoints then lie
  on that face's boundary cycle. `IsCellDecomposition.cellsAbsorb` derives the formerly named
  `CellsAbsorb` premise from the maintained cell-decomposition and Jordan-face invariants, so
  this requires no additional interface.
* **One ear insertion, step 3** — `exists_sourceEarStepData`,
  `EarCrosscut.exists_matched_target`, `earStepConstruction`, and `earStep`. The ambient source
  path is given fresh abstract cell names, its face split is realized on both sides, and a
  parameter-matching homeomorphism divides the target polygonal crosscut into exactly the same
  abstract edges. Matching source and target crosscuts then produce the next pair, compose both
  refinement maps, preserve every bundle invariant, and enlarge the occupied source graph by
  exactly the supplied ear, under the necessary `[Infinite γ]` name supply.
* **The last paragraph of the proof** — `Schoenflies.GeneratedPair.src_isAdmissible` and
  `Schoenflies.GeneratedPair.tgt_isAdmissible`. Admissibility of the *final* object is
  recovered from `lem:combinatorial-invariance`: the reproduced realization has the same
  2-connectivity and the same connectedness of the open nonboundary part as the given one.
  This uses only the hypotheses of the finite-transfer statement.
* **The induction scheme, steps 2 and 3** — `Schoenflies.transfer_of_ears`. With `earStep`
  supplying each insertion, `lem:relative-ear` in its iterated form
  (`Graph.IsTwoConnected.ear_decomposition`) transfers the whole extension. This is the backbone
  of the induction, and it honours `rem:intermediate-disconnection`: the invariant carried
  through the induction, `Schoenflies.IsPartialTransferOf`, asks only for *weak* admissibility,
  and connectedness of the open nonboundary part is restored only at the very end.

## Completion of step 1

This module keeps `Schoenflies.CommonSubdivision` as the compositional interface consumed by the
ear induction.  `Schoenflies/CommonSubdivision.lean` constructs it: it traces the part of `H`
supported on the old skeleton, proves that trace 2-connected, and carries all of its finitely many
vertices through matched source/target edge subdivisions.  Consequently direction (a) is exposed
there as `Schoenflies.finite_transfer_toward_square`.

## Blueprint

* `Schoenflies.CellStructure.Realization.IsWeaklyAdmissible`,
  `Schoenflies.CellStructure.Realization.IsAdmissible` — `def:admissible-graph`.
* `Schoenflies.GeneratedPair` — `def:generated-structure` with its two realizations,
  `def:matched-pair` and `def:matched-cellulation` folded in.
* `Schoenflies.IsSourceExtension` — the hypotheses of `thm:finite-transfer`(a) on `H`.
* `Schoenflies.IsPartialTransferOf`, `Schoenflies.IsTransferOf` — the conclusion of
  `thm:finite-transfer`, at an intermediate stage and at the end.
* `Schoenflies.exists_target_crosscut`, `Schoenflies.exists_target_crosscut_split` —
  the fourth paragraph of the proof of `thm:finite-transfer`, direction (a):
  `lem:cellulation-invariants`(vii) + `lem:polygonal-side-accessibility` +
  `lem:accessible-endpoints` + `thm:general-crosscut`.
* `Schoenflies.CellStructure.Realization.IsCellDecomposition.exists_unique_face_subset_cell`,
  `…IsCellDecomposition.exists_face_of_ear`,
  `…IsCellDecomposition.sub_of_pos_mem_closure_cell` — "the interior of each ear lies in one
  current face", with the two supporting facts
  `Schoenflies.CellStructure.Realization.cell_subset_skeletonSet` (hoisted to
  `Schoenflies/CombinatorialInvariance.lean`) and
  `Schoenflies.CellStructure.Realization.mem_faces_of_notMem_skeletonSet`.
* `Schoenflies.CellStructure.Realization.pos_mem_closure_cell_congr`,
  `Schoenflies.exists_target_ear` — "let `F*, v*, w*` be the corresponding face and endpoints in
  the other realization", and the whole fourth paragraph assembled from the source-side data.
* `Schoenflies.GeneratedPair.src_isAdmissible`, `Schoenflies.GeneratedPair.tgt_isAdmissible` —
  the last paragraph of the proof, via `lem:combinatorial-invariance`.
* `Schoenflies.exists_overlay_of_biUnion_finite` — `lem:polygonal-overlay` and
  `rem:polygonal-overlay-convention`, for a finite family of polygonal sets: the first half of
  step 1.
* `Schoenflies.earStep` — step 3; `Schoenflies.CommonSubdivision` — the step-1 interface,
  discharged by `Schoenflies.commonSubdivision` in `CommonSubdivision.lean`.
* `Schoenflies.transfer_of_ears_of_commonSubdivision_of_earStep`,
  `Schoenflies.finite_transfer_toward_square_of_commonSubdivision_of_earStep` — the
  finite-transfer induction parametrized by its two construction interfaces.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

open Graph

variable {γ : Type*}

/-! ### `def:admissible-graph`

An admissible graph in the closed Jordan domain is a finite 2-connected plane graph whose outer
cycle is `C`, whose edges not contained in `C` are polygonal arcs with interiors in `D`, and
whose open nonboundary part `|Γ| ∖ C` is connected. A *weakly* admissible graph satisfies
everything but the last clause.

`outer` is the realized outer cycle and `dom` the closed domain; the open domain is `dom ∖
outer`. On the source side that reads `C` and `C ∪ D`; on the target side `S` and `Q`. -/

namespace CellStructure

namespace Realization

variable {S : CellStructure γ}

/-- **A weakly admissible realization** — `def:admissible-graph` with connectedness of the open
nonboundary part waived, which is what `def:generated-structure` requires of every intermediate
stage (`rem:intermediate-disconnection`). -/
structure IsWeaklyAdmissible (R : S.Realization) (outer dom : Set Plane) : Prop where
  /-- The drawn skeleton is 2-connected. -/
  isTwoConnected : R.graph.IsTwoConnected
  /-- The realized outer cycle is the prescribed curve. -/
  outerSet_eq : R.outerSet = outer
  /-- Every nonboundary edge is a polygonal arc. -/
  isPolygonal : ∀ ⦃e⦄, e ∈ E(S.skel) → e ∉ E(S.outerGraph) → IsPolygonal (edgeArc R.drawing e)
  /-- Every nonboundary edge has its interior in the open domain. Endpoints may lie on the
  outer cycle, as for a crosscut. -/
  cell_subset : ∀ ⦃e⦄, e ∈ E(S.skel) → e ∉ E(S.outerGraph) → R.cell e ⊆ dom \ outer
  /-- The whole skeleton lies in the closed domain. -/
  skeletonSet_subset : R.skeletonSet ⊆ dom

/-- **An admissible realization** — `def:admissible-graph` in full. -/
structure IsAdmissible (R : S.Realization) (outer dom : Set Plane) : Prop
    extends R.IsWeaklyAdmissible outer dom where
  /-- The open nonboundary part `|Γ| ∖ C` is connected. -/
  isConnected_nonboundary : IsConnected R.nonboundary

end Realization

namespace SplitData.EarCrosscut

variable {S : CellStructure γ}
variable {d : S.SplitData} {R : S.Realization} {outer dom : Set Plane}
  {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}

/-- Weak admissibility is preserved by adjoining a polygonal ear inside one old face.  This is
the geometric bookkeeping common to the source and target halves of every ear step. -/
theorem isWeaklyAdmissible_realize (hE : d.EarCrosscut R earPos earDraw)
    (hR : R.IsWeaklyAdmissible outer dom) (hcd : R.IsCellDecomposition dom)
    (hpoly : ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (edgeArc earDraw e)) :
    (d.realize R earPos earDraw hE).IsWeaklyAdmissible outer dom where
  isTwoConnected := by
    change ((S.splitFace d).skel.map (d.splitPos R earPos)).IsTwoConnected
    rw [hE.splitGraph_eq]
    have hcompat : R.graph.Compatible (d.earGraph earPos) :=
      Graph.Compatible.of_disjoint_edgeSet (by
        rw [Realization.edgeSet_graph, d.edgeSet_earGraph]
        exact d.disjoint_edgeSet)
    exact hR.isTwoConnected.ear hcompat hE.isPathGraph_earGraph source_ne_target_pos
      (by rw [R.vertexSet_graph]; exact ⟨d.source, d.source_mem_skel, rfl⟩)
      (by rw [R.vertexSet_graph]; exact ⟨d.target, d.target_mem_skel, rfl⟩)
  outerSet_eq := by
    change Graph.pointSet ((S.splitFace d).outerGraph.map (d.splitPos R earPos))
      (d.splitDrawing R earDraw) = outer
    rw [CellStructure.splitFace_outerGraph]
    have hgraph : S.outerGraph.map (d.splitPos R earPos) = S.outerGraph.map R.pos :=
      Graph.map_eq_of_eqOn fun z hz => hE.splitPos_eq (S.outerGraph_le.vertexSet_mono hz)
    rw [hgraph]
    calc
      Graph.pointSet (S.outerGraph.map R.pos) (d.splitDrawing R earDraw) =
          Graph.pointSet (S.outerGraph.map R.pos) R.drawing := by
        apply Graph.pointSet_congr
        intro e he
        rw [Graph.edgeSet_map] at he
        exact d.edgeArc_splitDrawing_of_mem_skel (S.outerGraph_le.edgeSet_mono he)
      _ = R.outerSet := rfl
      _ = outer := hR.outerSet_eq
  isPolygonal := by
    intro e he houter
    change e ∈ E(d.skeleton) at he
    rw [CellStructure.splitFace_outerGraph] at houter
    rcases he with he | he
    · change IsPolygonal (edgeArc (d.splitDrawing R earDraw) e)
      rw [d.edgeArc_splitDrawing_of_mem_skel he]
      exact hR.isPolygonal he houter
    · change IsPolygonal (edgeArc (d.splitDrawing R earDraw) e)
      rw [d.edgeArc_splitDrawing_of_mem_ear he]
      exact hpoly he
  cell_subset := by
    intro e he houter
    change e ∈ E(d.skeleton) at he
    rw [CellStructure.splitFace_outerGraph] at houter
    rcases he with he | he
    · rw [CellStructure.SplitData.realize_cell,
        d.splitCell_of_mem_cells (S.mem_cells_of_mem_edgeSet he)]
      exact hR.cell_subset he houter
    · rw [CellStructure.SplitData.realize_cell, d.splitCell_earEdge he]
      intro x hx
      have hxEar : x ∈ d.earSet earPos earDraw :=
        edgeArc_subset_earSet he hx.1
      have hxEnds : x ∉ ({R.pos d.source, R.pos d.target} : Set Plane) := by
        rintro (rfl | rfl)
        · exact hx.2 ⟨d.source, d.source_mem_ear, hE.pos_source⟩
        · exact hx.2 ⟨d.target, d.target_mem_ear, hE.pos_target⟩
      have hxFace : x ∈ R.cell d.face := hE.subset_face ⟨hxEar, hxEnds⟩
      refine ⟨hcd.cell_subset_domain (S.mem_cells_of_mem_faces d.face_mem) hxFace, ?_⟩
      intro hxOuter
      have hxSkel : x ∈ R.skeletonSet := by
        apply R.outerSet_subset_skeletonSet
        rw [hR.outerSet_eq]
        exact hxOuter
      exact Set.disjoint_left.1 (R.disjoint_cell_skeletonSet hcd d.face_mem) hxFace hxSkel
  skeletonSet_subset := by
    rw [d.skeletonSet_realize hE]
    refine Set.union_subset hR.skeletonSet_subset ?_
    intro x hx
    by_cases hxEnds : x ∈ ({R.pos d.source, R.pos d.target} : Set Plane)
    · rcases hxEnds with rfl | rfl
      · exact hR.skeletonSet_subset (R.pos_mem_skeletonSet d.source_mem_skel)
      · exact hR.skeletonSet_subset (R.pos_mem_skeletonSet d.target_mem_skel)
    · exact hcd.cell_subset_domain (S.mem_cells_of_mem_faces d.face_mem)
        (hE.subset_face ⟨hx, hxEnds⟩)

end SplitData.EarCrosscut

namespace SplitData.EarCrosscut

variable {S : CellStructure γ} {d : S.SplitData} {R₁ R₂ : S.Realization}
  {srcPos : γ → Plane} {srcDraw : γ → ℝ → Plane}

/-- A set-level target crosscut can be divided into exactly the abstract edges of an already
drawn source ear.  The division is obtained by matching the parameters of the two whole arcs:
each target edge is the image of its source counterpart.  Closed subarcs of the polygonal
target crosscut are polygonal, so no relation between the number of straight segments on the
two sides is needed. -/
theorem exists_matched_target (hsrc : d.EarCrosscut R₁ srcPos srcDraw)
    {A : Set Plane} (hApoly : IsPolygonal A)
    (hAarc : IsArcBetween A (R₂.pos d.source) (R₂.pos d.target))
    (hAsub : A \ {R₂.pos d.source, R₂.pos d.target} ⊆ R₂.cell d.face)
    (hdisj : Disjoint (R₂.cell d.face) R₂.skeletonSet) :
    ∃ tgtPos : γ → Plane, ∃ tgtDraw : γ → ℝ → Plane,
      ∃ _ : d.EarHomeo srcPos srcDraw tgtPos tgtDraw,
      d.EarCrosscut R₂ tgtPos tgtDraw ∧
      ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (Graph.edgeArc tgtDraw e) := by
  classical
  let m : ArcHomeo (d.earSet srcPos srcDraw) A
      (R₁.pos d.source) (R₁.pos d.target) (R₂.pos d.source) (R₂.pos d.target) :=
    Classical.choice (exists_arcHomeo hsrc.isArcBetween_earSet hAarc)
  let tgtPos : γ → Plane := fun z => m.toFun (srcPos z)
  let tgtDraw : γ → ℝ → Plane := Graph.mapDrawing m srcDraw
  have hgraph : d.earGraph tgtPos = (d.earGraph srcPos).map m.toFun := by
    change d.ear.map tgtPos = (d.ear.map srcPos).map m.toFun
    rw [Graph.map_map]
    rfl
  have hset : d.earSet tgtPos tgtDraw = A := by
    rw [CellStructure.SplitData.earSet, hgraph,
      Graph.pointSet_map_mapDrawing (G := d.earGraph srcPos)]
    exact m.image_eq
  have htgt : d.EarCrosscut R₂ tgtPos tgtDraw := {
    pos_source := by
      change m.toFun (srcPos d.source) = R₂.pos d.source
      rw [hsrc.pos_source]
      exact m.map_left
    pos_target := by
      change m.toFun (srcPos d.target) = R₂.pos d.target
      rw [hsrc.pos_target]
      exact m.map_right
    injOn := by
      intro x hx y hy hxy
      apply hsrc.injOn hx hy
      apply m.injOn (CellStructure.SplitData.EarCrosscut.mem_earSet_of_mem_ear hx)
        (CellStructure.SplitData.EarCrosscut.mem_earSet_of_mem_ear hy)
      exact hxy
    isDrawing := by
      rw [hgraph]
      exact hsrc.isDrawing.map_arcHomeo m rfl
    subset_face := by
      intro x hx
      apply hAsub
      exact ⟨hset ▸ hx.1, hx.2⟩
    disjoint_skeleton := hdisj
    polygonal := hset ▸ hApoly
  }
  have hhomeo : d.EarHomeo srcPos srcDraw tgtPos tgtDraw := {
    toFun := m.toFun
    invFun := m.invFun
    continuousOn_toFun := m.continuousOn_toFun
    continuousOn_invFun := by
      rw [hset]
      exact m.continuousOn_invFun
    leftInvOn := m.leftInvOn
    rightInvOn := by
      rw [hset]
      exact m.rightInvOn
    earPos_apply := by intro z _; rfl
    edgeArc_image := by
      intro e _
      exact (Graph.edgeArc_mapDrawing m e).symm
  }
  refine ⟨tgtPos, tgtDraw, hhomeo, htgt, ?_⟩
  intro e he
  obtain ⟨x, y, hxy⟩ := d.ear.exists_isLink_of_mem_edgeSet he
  have hedge : IsArcBetween (Graph.edgeArc tgtDraw e) (tgtPos x) (tgtPos y) :=
    htgt.isDrawing.edge_isArcBetween (hxy.map tgtPos)
  exact hedge.isPolygonal_of_subset_arc hAarc hApoly
    (hset ▸ CellStructure.SplitData.EarCrosscut.edgeArc_subset_earSet he)

end SplitData.EarCrosscut

namespace Realization

variable {S : CellStructure γ}

/-! #### Where an ear can lie

*The interior of each ear lies in one current face, because it is connected and disjoint from the
current skeleton.* That is the second sentence of step 2, and it is proved here for an arbitrary
connected subset of the closed domain missing the skeleton.

The only input beyond assertion (i) is `Schoenflies.CellsAbsorb` — assertion (i) in the
"a connected set disjoint from the skeleton that meets a 2-cell lies in it" reading, which
`Schoenflies/SkeletonAccess.lean` also carries as its single hypothesis and which
`Schoenflies.cellsAbsorb_of_isComponent_in` discharges on the target side. -/

variable {R : S.Realization} {D N Q : Set Plane} {F σ : γ} {z : Plane}

/-- A cell whose open part contains a point off the skeleton is a 2-cell. -/
theorem mem_faces_of_notMem_skeletonSet (R : S.Realization) (hσ : σ ∈ S.cells)
    (hz : z ∈ R.cell σ) (hznot : z ∉ R.skeletonSet) : σ ∈ S.faces := by
  rcases hσ with hσ | hσ
  · exact absurd (cell_subset_skeletonSet hσ hz) hznot
  · exact hσ

namespace IsCellDecomposition

/-- The frontier of a Jordan face is part of the realized 1-skeleton.  Assertion (i) writes the
frontier as the union of strict subcells; assertion (vii) rules out a second face among those
subcells, leaving only vertices and edges. -/
theorem frontier_cell_subset_skeletonSet (h : R.IsCellDecomposition D)
    (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) : frontier (R.cell F) ⊆ R.skeletonSet := by
  rw [← hJ.faceBoundary_eq h hF, Realization.faceBoundary]
  rintro z hz
  obtain ⟨σ, ⟨⟨hσ, hσF⟩, hσne⟩, hz⟩ := Realization.mem_cellUnion_iff.1 hz
  rcases hσ with (hv | he) | hface
  · exact R.cell_subset_skeletonSet (Or.inl hv) hz
  · exact R.cell_subset_skeletonSet (Or.inr he) hz
  · exact absurd (h.sub_face_eq hJ hface hF hσF) hσne

/-- Assertions (i) and (vii) discharge the `CellsAbsorb` reading of the cellulation invariant:
a connected set missing the skeleton cannot cross the Jordan frontier of a face it meets. -/
theorem cellsAbsorb (h : R.IsCellDecomposition D) (hJ : R.IsFaceJordan) :
    CellsAbsorb R.skeletonSet {A | ∃ F ∈ S.faces, A = R.cell F} := by
  rintro N hN hNdisj A ⟨F, hF, rfl⟩ hmeet
  exact subset_of_isPreconnected_of_frontier_disjoint (hJ.isOpen hF) hN
    (hNdisj.mono_right (h.frontier_cell_subset_skeletonSet hJ hF)) hmeet

/-- A Jordan face contained in an ambient open set `Q` is a connected component of
`Q \ skeleton` as soon as its frontier belongs to the skeleton. -/
theorem face_eq_connectedComponentIn (h : R.IsCellDecomposition D) (hJ : R.IsFaceJordan)
    (hF : F ∈ S.faces) (hFQ : R.cell F ⊆ Q) (z : Plane)
    (hz : z ∈ R.cell F) :
    R.cell F = connectedComponentIn (Q \ R.skeletonSet) z := by
  symm
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint (hJ.isOpen hF)
    (hJ.isConnected hF).isPreconnected ?_ ?_ hz
  · exact fun x hx => ⟨hFQ hx,
      Set.disjoint_left.1 (R.disjoint_cell_skeletonSet h hF) hx⟩
  · refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro x ⟨hxfr, -, hxskel⟩
    exact hxskel (h.frontier_cell_subset_skeletonSet hJ hF hxfr)

/-- A 0-cell in the closure of an open 2-cell is a subcell of it — assertion (ix) read at a
vertex. This is how an ear's endpoint is recognised as lying on the boundary cycle of the face
its interior occupies. -/
theorem sub_of_pos_mem_closure_cell (h : R.IsCellDecomposition D) {a F : γ}
    (ha : a ∈ V(S.skel)) (hF : F ∈ S.faces) (hmem : R.pos a ∈ closure (R.cell F)) :
    S.sub a F := by
  refine h.sub_of_subset_closure (S.mem_cells_of_mem_vertexSet ha)
    (S.mem_cells_of_mem_faces hF) ?_
  rw [R.cell_vertex ha]
  exact Set.singleton_subset_iff.2 hmem

/-- **An ear lies in a single current face.** A nonempty connected subset of the closed domain
disjoint from the realized skeleton lies inside one open 2-cell, and inside only that one. -/
theorem exists_unique_face_subset_cell (h : R.IsCellDecomposition D)
    (hcells : CellsAbsorb R.skeletonSet {A | ∃ F ∈ S.faces, A = R.cell F})
    (hN : IsPreconnected N) (hNne : N.Nonempty) (hND : N ⊆ D)
    (hNdisj : Disjoint N R.skeletonSet) :
    ∃ F ∈ S.faces, N ⊆ R.cell F ∧ ∀ T ∈ S.faces, N ⊆ R.cell T → T = F := by
  obtain ⟨z, hz⟩ := hNne
  obtain ⟨F, hFc, hzF⟩ := h.exists_cell (hND hz)
  have hznot : z ∉ R.skeletonSet := Set.disjoint_left.1 hNdisj hz
  have hFf : F ∈ S.faces := R.mem_faces_of_notMem_skeletonSet hFc hzF hznot
  refine ⟨F, hFf, hcells N hN hNdisj (R.cell F) ⟨F, hFf, rfl⟩ ⟨z, hz, hzF⟩, fun T hT hNT => ?_⟩
  by_contra hne
  exact Set.disjoint_left.1 (h.disjoint (S.mem_cells_of_mem_faces hT) hFc hne) (hNT hz) hzF

/-- **One ear, placed — the source-side input of the induction step.** The open part `N` of the
ear is connected, inside the closed domain and disjoint from the current skeleton, so it lies in
a unique current 2-cell `F`; and each endpoint of the ear, being a 0-cell in the closure of `N`,
is a subcell of `F`, i.e. lies on its boundary cycle.

Feeding the two `S.sub` conclusions back through `IsCellDecomposition.subset_closure` in the
*other* realization is exactly `Schoenflies.exists_target_ear`'s two closure hypotheses. -/
theorem exists_face_of_ear (h : R.IsCellDecomposition D)
    (hcells : CellsAbsorb R.skeletonSet {A | ∃ F ∈ S.faces, A = R.cell F})
    (hN : IsPreconnected N) (hNne : N.Nonempty) (hND : N ⊆ D)
    (hNdisj : Disjoint N R.skeletonSet) {a b : γ}
    (ha : a ∈ V(S.skel)) (hb : b ∈ V(S.skel))
    (hacl : R.pos a ∈ closure N) (hbcl : R.pos b ∈ closure N) :
    ∃ F ∈ S.faces, N ⊆ R.cell F ∧ S.sub a F ∧ S.sub b F ∧
      ∀ T ∈ S.faces, N ⊆ R.cell T → T = F := by
  obtain ⟨F, hF, hNF, huniq⟩ := h.exists_unique_face_subset_cell hcells hN hNne hND hNdisj
  exact ⟨F, hF, hNF,
    h.sub_of_pos_mem_closure_cell ha hF (closure_mono hNF hacl),
    h.sub_of_pos_mem_closure_cell hb hF (closure_mono hNF hbcl), huniq⟩

end IsCellDecomposition

end Realization

end CellStructure

/-! ### A generated matched cell structure, with its geometry

`def:generated-structure` says what the *abstract* object is; `GeneratedStructure` in
`Schoenflies/GeneratedStructure.lean` is that. What a transfer produces, and what the
finite-transfer theorem consumes, is the abstract object together with its two realizations, the
skeleton homeomorphism between them, and the two cell decompositions of
`lem:cellulation-invariants`(i). That bundle is `GeneratedPair`.

It is data, not a `Prop`: a consumer reads `.src`, `.tgt`, `.homeo`, `.str` by name. -/

/-- **A generated matched cell structure with its two realizations.** The Lean form of
"`(Γ, Γ')` is a generated matched cellulation", except that only *weak* admissibility is a
field — `rem:intermediate-disconnection` — with the connected form carried separately by the
consumers that have it. -/
structure GeneratedPair (S₀ : CellStructure γ) (srcOuter srcDom tgtOuter tgtDom : Set Plane)
    where
  /-- The abstract cell structure. -/
  str : CellStructure γ
  /-- It is generated from the base by a finite sequence of elementary operations. -/
  generated : GeneratedStructure S₀ str
  /-- The maintained combinatorial invariants of the current abstract structure. -/
  str_combInvariants : str.CombInvariants
  /-- Every current face has a simple cyclic abstract boundary. -/
  str_boundaryCycles : str.BoundaryCycles
  /-- The realization in the closed Jordan domain. -/
  src : str.Realization
  /-- The realization in the closed square. -/
  tgt : str.Realization
  /-- The skeleton homeomorphism `g : |Γ| → |Γ'|` of `def:matched-pair`. -/
  homeo : CellStructure.SkeletonHomeo src tgt
  /-- **Assertion (i)** on the source side. -/
  src_isCellDecomposition : src.IsCellDecomposition srcDom
  /-- **Assertion (i)** on the target side. -/
  tgt_isCellDecomposition : tgt.IsCellDecomposition tgtDom
  /-- **Assertion (vii)** on the source side: every face is the inside of its Jordan frontier. -/
  src_isFaceJordan : src.IsFaceJordan
  /-- **Assertion (vii)** on the target side.  A split needs this geometric information in
  addition to the cell-decomposition clauses. -/
  tgt_isFaceJordan : tgt.IsFaceJordan
  /-- The open part of the target domain. -/
  tgtInterior_isOpen : IsOpen (tgtDom \ tgtOuter)
  /-- Its frontier is already part of the target skeleton. -/
  tgtInterior_frontier_subset : frontier (tgtDom \ tgtOuter) ⊆ tgt.skeletonSet
  /-- Every target edge is polygonal, including the distinguished outer edges. -/
  tgt_isPolygonal : ∀ ⦃e⦄, e ∈ E(str.skel) → IsPolygonal (edgeArc tgt.drawing e)
  /-- The source realization is weakly admissible. -/
  src_isWeaklyAdmissible : src.IsWeaklyAdmissible srcOuter srcDom
  /-- The target realization is weakly admissible. -/
  tgt_isWeaklyAdmissible : tgt.IsWeaklyAdmissible tgtOuter tgtDom

namespace GeneratedPair

variable {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- The combinatorial invariants hold at every generated stage, once they hold at the base —
`Schoenflies.GeneratedStructure.combInvariants`, read off the bundle. -/
theorem combInvariants (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (h₀ : S₀.CombInvariants) : P.str.CombInvariants :=
  P.generated.combInvariants h₀

/-- Every face of a generated pair has a simple cyclic boundary once this is true at the base.
This is the source of the two abstract boundary paths consumed by an ear split. -/
theorem boundaryCycles (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hcycles : S₀.BoundaryCycles) (h₀ : S₀.CombInvariants) :
    P.str.BoundaryCycles :=
  P.generated.boundaryCycles hcycles h₀

/-- The open nonboundary part of the source realization, read off the two clauses that pin the
skeleton and the outer cycle. -/
theorem src_nonboundary_eq (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    P.src.nonboundary = P.src.skeletonSet \ srcOuter := by
  rw [CellStructure.Realization.nonboundary, P.src_isWeaklyAdmissible.outerSet_eq]

/-- **The last paragraph of the proof of `thm:finite-transfer`, target half.** Once the source
realization's open nonboundary part is connected, so is the target's — this is part (b) of
`lem:combinatorial-invariance` — and the target realization, weakly admissible by construction,
is therefore admissible. -/
theorem tgt_isAdmissible (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (h : IsConnected P.src.nonboundary) : P.tgt.IsAdmissible tgtOuter tgtDom :=
  { P.tgt_isWeaklyAdmissible with
    isConnected_nonboundary := P.homeo.isConnected_nonboundary_iff.1 h }

/-- **The last paragraph of the proof, source half.** -/
theorem src_isAdmissible (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (h : IsConnected P.src.nonboundary) : P.src.IsAdmissible srcOuter srcDom :=
  { P.src_isWeaklyAdmissible with isConnected_nonboundary := h }

/-- Every target face lies in the open part of the prescribed target domain. -/
theorem tgt_face_subset_interior (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {F : γ} (hF : F ∈ P.str.faces) : P.tgt.cell F ⊆ tgtDom \ tgtOuter := by
  intro x hx
  refine ⟨P.tgt_isCellDecomposition.cell_subset_domain
    (P.str.mem_cells_of_mem_faces hF) hx, ?_⟩
  intro hxOuter
  have hxSkel : x ∈ P.tgt.skeletonSet := by
    rw [← P.tgt_isWeaklyAdmissible.outerSet_eq] at hxOuter
    exact P.tgt.outerSet_subset_skeletonSet hxOuter
  exact Set.disjoint_left.1
    (P.tgt.disjoint_cell_skeletonSet P.tgt_isCellDecomposition hF) hx hxSkel

/-- Target faces have the component presentation consumed by polygonal side accessibility. -/
theorem tgt_face_isComponent (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {F : γ} (hF : F ∈ P.str.faces) :
    P.tgt.cell F ⊆ tgtDom \ tgtOuter ∧
      ∃ z, P.tgt.cell F =
        connectedComponentIn ((tgtDom \ tgtOuter) \ P.tgt.skeletonSet) z := by
  have hne := P.tgt_isFaceJordan.nonempty hF
  obtain ⟨z, hz⟩ := hne
  exact ⟨P.tgt_face_subset_interior hF, z,
    P.tgt_isCellDecomposition.face_eq_connectedComponentIn P.tgt_isFaceJordan hF
      (P.tgt_face_subset_interior hF) z hz⟩

/-! #### The matched split constructor

`RealizeSplit` and `MatchedSplit` construct the two new realizations and their skeleton
homeomorphism.  The definition below is the missing bundle-level constructor: it installs those
objects in a `GeneratedPair` and records the propagated cell-decomposition and Jordan-face
invariants.  Weak admissibility is then derived from the old pair and the two polygonal ear
drawings by `EarCrosscut.isWeaklyAdmissible_realize`. -/

/-- Build the next generated pair from matching geometric realizations of one abstract face
split. -/
noncomputable def split (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hS : P.str.CombInvariants) (d : P.str.SplitData)
    (srcPos : γ → Plane) (srcDraw : γ → ℝ → Plane)
    (tgtPos : γ → Plane) (tgtDraw : γ → ℝ → Plane)
    (hsrc : d.EarCrosscut P.src srcPos srcDraw)
    (htgt : d.EarCrosscut P.tgt tgtPos tgtDraw)
    (m : d.EarHomeo srcPos srcDraw tgtPos tgtDraw)
    (hsrcEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (edgeArc srcDraw e))
    (htgtEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (edgeArc tgtDraw e)) :
    GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom where
  str := P.str.splitFace d
  generated := .splitFace P.generated d
  str_combInvariants := d.combInvariants hS
  str_boundaryCycles := d.boundaryCycles P.str_boundaryCycles hS
  src := d.realize P.src srcPos srcDraw hsrc
  tgt := d.realize P.tgt tgtPos tgtDraw htgt
  homeo := d.splitHomeo P.homeo hsrc htgt m
  src_isCellDecomposition :=
    (d.isCellDecomposition_and_isFaceJordan_realize hsrc hS
      P.src_isCellDecomposition P.src_isFaceJordan).1
  tgt_isCellDecomposition :=
    (d.isCellDecomposition_and_isFaceJordan_realize htgt hS
      P.tgt_isCellDecomposition P.tgt_isFaceJordan).1
  src_isFaceJordan :=
    (d.isCellDecomposition_and_isFaceJordan_realize hsrc hS
      P.src_isCellDecomposition P.src_isFaceJordan).2.1
  tgt_isFaceJordan :=
    (d.isCellDecomposition_and_isFaceJordan_realize htgt hS
      P.tgt_isCellDecomposition P.tgt_isFaceJordan).2.1
  tgtInterior_isOpen := P.tgtInterior_isOpen
  tgtInterior_frontier_subset := P.tgtInterior_frontier_subset.trans
    (d.skeletonSet_subset_realize htgt)
  tgt_isPolygonal := by
    intro e he
    change e ∈ E(d.skeleton) at he
    rcases he with he | he
    · change IsPolygonal (edgeArc (d.splitDrawing P.tgt tgtDraw) e)
      rw [CellStructure.SplitData.edgeArc_splitDrawing_of_mem_skel he]
      exact P.tgt_isPolygonal he
    · change IsPolygonal (edgeArc (d.splitDrawing P.tgt tgtDraw) e)
      rw [CellStructure.SplitData.edgeArc_splitDrawing_of_mem_ear he]
      exact htgtEdgePoly he
  src_isWeaklyAdmissible := hsrc.isWeaklyAdmissible_realize P.src_isWeaklyAdmissible
    P.src_isCellDecomposition hsrcEdgePoly
  tgt_isWeaklyAdmissible := htgt.isWeaklyAdmissible_realize P.tgt_isWeaklyAdmissible
    P.tgt_isCellDecomposition htgtEdgePoly

@[simp] theorem split_str (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hS : P.str.CombInvariants) (d : P.str.SplitData)
    (srcPos : γ → Plane) (srcDraw : γ → ℝ → Plane)
    (tgtPos : γ → Plane) (tgtDraw : γ → ℝ → Plane)
    (hsrc : d.EarCrosscut P.src srcPos srcDraw)
    (htgt : d.EarCrosscut P.tgt tgtPos tgtDraw)
    (m : d.EarHomeo srcPos srcDraw tgtPos tgtDraw)
    (hsrcEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (edgeArc srcDraw e))
    (htgtEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (edgeArc tgtDraw e)) :
    (P.split hS d srcPos srcDraw tgtPos tgtDraw hsrc htgt m hsrcEdgePoly
      htgtEdgePoly).str =
      P.str.splitFace d := rfl

end GeneratedPair

/-! ### The hypotheses of direction (a) on the given extension

*`H` is a finite 2-connected plane graph containing a subdivision of `Γ`, with outer cycle `C`,
with every nonboundary edge polygonal, and with `|H| ∖ C` connected.*

"Contains a subdivision of `Γ`" is recorded by three clauses: every old vertex is a vertex of
`H`; the old skeleton is inside `|H|`; and any edge of `H` whose nonvertex part meets an *open*
old edge lies inside that old edge. Together those say that each old edge is cut into a chain of
`H`-edges. A transverse crossing is allowed only at a vertex of `H`, exactly as produced by the
polygonal overlay.

"With outer cycle `C`, with every nonboundary edge polygonal" is `edge_dichotomy`: each edge of
`H` either lies inside the outer curve or is polygonal with its interior in the open domain.
Recording the outer cycle as a *subgraph* would put data inside a `Prop`; this reading is what
every step of the proof actually uses, and `outer ⊆ pointSet H Hdraw` comes for free from
`skeletonSet_subset`. -/

/-- **The hypotheses of `thm:finite-transfer`(a) on the extension `H`.** -/
structure IsSourceExtension {S : CellStructure γ} (R : S.Realization) (outer dom : Set Plane)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop where
  /-- `H` is finite. -/
  finite : H.Finite
  /-- `H` is a plane graph. -/
  isDrawing : IsDrawing H Hdraw
  /-- `H` is 2-connected. -/
  isTwoConnected : H.IsTwoConnected
  /-- Every 0-cell of `Γ` is a vertex of `H`. -/
  vertexSet_subset : V(R.graph) ⊆ V(H)
  /-- `|Γ| ⊆ |H|`. -/
  skeletonSet_subset : R.skeletonSet ⊆ pointSet H Hdraw
  /-- An edge of `H` whose interior meets an open edge of `Γ` runs inside it.  Intersections at
  vertices of `H` are deliberately excluded: a transverse crossing is first made a vertex by
  the polygonal overlay, and does not make either of its two incident branches part of the old
  edge. -/
  edge_subset : ∀ ⦃e⦄, e ∈ E(S.skel) → ∀ ⦃f⦄, f ∈ E(H) →
    (edgeArc Hdraw f ∩ (R.cell e \ V(H))).Nonempty →
      edgeArc Hdraw f ⊆ edgeArc R.drawing e
  /-- `H` is drawn in the closed domain. -/
  pointSet_subset : pointSet H Hdraw ⊆ dom
  /-- Each edge of `H` is an outer edge or a polygonal nonboundary edge with interior in the
  open domain. -/
  edge_dichotomy : ∀ ⦃f⦄, f ∈ E(H) → edgeArc Hdraw f ⊆ outer ∨
    (IsPolygonal (edgeArc Hdraw f) ∧ edgeArc Hdraw f \ V(H) ⊆ dom \ outer)
  /-- `|H| ∖ C` is connected. -/
  isConnected : IsConnected (pointSet H Hdraw \ outer)

namespace IsSourceExtension

variable {S : CellStructure γ} {R : S.Realization} {outer dom : Set Plane}
  {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}

/-- A plane graph has no loops, so `lem:relative-ear` applies to `H`. -/
theorem not_isLoopAt (h : IsSourceExtension R outer dom H Hdraw) ⦃f : γ⦄ ⦃x : Plane⦄ :
    ¬ H.IsLoopAt f x := h.isDrawing.not_isLoopAt f x

end IsSourceExtension

/-! ### The conclusion

`IsPartialTransferOf T P B par` is the invariant the induction of steps 2–3 carries: `T` is a
generated pair refining `P` along `par` whose source realization occupies exactly what the
current subgraph `B` of `H` occupies. It asks for **no** connectedness of the open nonboundary
part — `rem:intermediate-disconnection` — because an ear with both endpoints on the outer cycle
really does disconnect it, and later ears reconnect it.

`IsTransferOf` is the same with admissibility of both final realizations added; that is the
theorem's conclusion, and `GeneratedPair.src_isAdmissible` / `GeneratedPair.tgt_isAdmissible`
are what produce it from the connectedness hypothesis on `H`. -/

variable {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- A finite family of fresh names can be chosen injectively outside any finite used set.  This
is the name-supply lemma used by the concrete ear relabelling: vertex, edge, and face requests
are put in one finite sum type so their chosen names are automatically pairwise distinct. -/
theorem exists_injective_avoiding [Infinite γ] (used : Set γ) (hused : used.Finite)
    (ι : Type*) [Finite ι] :
    ∃ fresh : ι → γ, Function.Injective fresh ∧ ∀ i, fresh i ∉ used := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let code : ι ↪ ℕ := (Fintype.equivFin ι).toEmbedding.trans Fin.valEmbedding
  let supply : ℕ ↪ {x // x ∈ (usedᶜ : Set γ)} :=
    hused.infinite_compl.natEmbedding (usedᶜ : Set γ)
  refine ⟨fun i => supply (code i), ?_, fun i => (supply (code i)).2⟩
  intro i j hij
  exact code.injective (supply.injective (Subtype.ext hij))

/-- Extend two prescribed, distinct names to an injection on a finite set, with every other
value fresh outside a prescribed finite set. -/
theorem exists_injective_pinned_avoiding [Infinite γ]
    {used : Set γ} (hused : used.Finite) {u v : γ}
    (hu : u ∈ used) (hv : v ∈ used) (huv : u ≠ v)
    {s : Set α} (hs : s.Finite) {a b : α} (hab : a ≠ b) :
    ∃ name : α → γ, name a = u ∧ name b = v ∧ InjOn name s ∧
      ∀ x ∈ s, x ≠ a → x ≠ b → name x ∉ used := by
  classical
  let inner := {x : α // x ∈ s ∧ x ≠ a ∧ x ≠ b}
  let _ : Finite inner := Set.finite_coe_iff.mpr (hs.subset fun x hx => hx.1)
  obtain ⟨fresh, hfresh, havoid⟩ := exists_injective_avoiding used hused inner
  let name : α → γ := fun x =>
    if hxa : x = a then u else if hxb : x = b then v
    else if hx : x ∈ s then fresh ⟨x, hx, hxa, hxb⟩ else u
  have hnamea : name a = u := by simp [name]
  have hnameb : name b = v := by simp [name, Ne.symm hab]
  have hname_inner (x : α) (hx : x ∈ s) (hxa : x ≠ a) (hxb : x ≠ b) :
      name x = fresh (⟨x, hx, hxa, hxb⟩ : inner) := by
    simp [name, hxa, hxb, hx]
  refine ⟨name, hnamea, hnameb, ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hxa : x = a
    · subst x
      by_cases hya : y = a
      · exact hya.symm
      by_cases hyb : y = b
      · subst y
        exact absurd (hnamea.symm.trans (hxy.trans hnameb)) huv
      · exfalso
        apply havoid ⟨y, hy, hya, hyb⟩
        rw [← hname_inner y hy hya hyb, ← hxy, hnamea]
        exact hu
    · by_cases hxb : x = b
      · subst x
        by_cases hya : y = a
        · subst y
          exact absurd (hnameb.symm.trans (hxy.trans hnamea)) huv.symm
        by_cases hyb : y = b
        · exact hyb.symm
        · exfalso
          apply havoid ⟨y, hy, hya, hyb⟩
          rw [← hname_inner y hy hya hyb, ← hxy, hnameb]
          exact hv
      · by_cases hya : y = a
        · subst y
          exfalso
          apply havoid ⟨x, hx, hxa, hxb⟩
          rw [← hname_inner x hx hxa hxb, hxy, hnamea]
          exact hu
        by_cases hyb : y = b
        · subst y
          exfalso
          apply havoid ⟨x, hx, hxa, hxb⟩
          rw [← hname_inner x hx hxa hxb, hxy, hnameb]
          exact hv
        · have hsub : (⟨x, hx, hxa, hxb⟩ : inner) = ⟨y, hy, hya, hyb⟩ := by
            apply hfresh
            calc
            fresh (⟨x, hx, hxa, hxb⟩ : inner) = name x :=
              (hname_inner x hx hxa hxb).symm
            _ = name y := hxy
            _ = fresh (⟨y, hy, hya, hyb⟩ : inner) := hname_inner y hy hya hyb
          exact congrArg (fun z : inner => z.1) hsub
  · intro x hx hxa hxb
    rw [hname_inner x hx hxa hxb]
    exact havoid ⟨x, hx, hxa, hxb⟩

/-- **An intermediate stage of the transfer.** -/
structure IsPartialTransferOf (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (par : γ → γ) : Prop where
  /-- The new source realization refines the old one along `par` — assertion (iv). -/
  refines_src : T.src.Refines P.src par
  /-- The new target realization refines the old one along the *same* parent map. That sharing
  is `lem:refinement-compatibility`(c). -/
  refines_tgt : T.tgt.Refines P.tgt par
  /-- The evolving source skeleton contains the original source skeleton. -/
  sourceSkeletonSet_subset : P.src.skeletonSet ⊆ T.src.skeletonSet
  /-- On the original source skeleton, the evolving skeleton map is still the original map. -/
  homeo_eqOn : Set.EqOn T.homeo.toFun P.homeo.toFun P.src.skeletonSet
  /-- The new source skeleton occupies exactly what the current subgraph occupies. -/
  skeletonSet_eq : T.src.skeletonSet = pointSet B Hdraw
  /-- Every vertex of the current subgraph is a 0-cell of the new structure: the new structure
  realizes a subdivision of `B`, so it has at least `B`'s vertices. -/
  vertexSet_subset : V(B) ⊆ V(T.src.graph)

/-! #### The output data of one realized ear

The former `EarStep` interface ended directly in an existential `GeneratedPair`.  That hid all
of the actual constructor data and made the last half of the proof impossible to reuse or
inspect.  `EarStepData` exposes the abstract split, its two geometric crosscuts, and the chosen
map between them.  Its `pair` and `isPartialTransferOf_pair` declarations below perform the
assembly. -/

/-- Complete constructor data for adjoining the geometric path `D` to a partial transfer. -/
structure EarStepData (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (a : Plane) (D : List γ) where
  /-- The abstract face split, including the freshly named copy of the ear. -/
  splitData : T.str.SplitData
  /-- The source positions and edge parametrizations of that abstract ear. -/
  srcPos : γ → Plane
  srcDraw : γ → ℝ → Plane
  /-- The target positions and edge parametrizations. -/
  tgtPos : γ → Plane
  tgtDraw : γ → ℝ → Plane
  /-- Both drawings are crosscuts of the corresponding old face. -/
  srcCrosscut : splitData.EarCrosscut T.src srcPos srcDraw
  tgtCrosscut : splitData.EarCrosscut T.tgt tgtPos tgtDraw
  /-- The cellwise homeomorphism used to extend the old skeleton homeomorphism. -/
  earHomeo : splitData.EarHomeo srcPos srcDraw tgtPos tgtDraw
  /-- Every edge of both realized ears is polygonal. -/
  srcEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) →
    IsPolygonal (edgeArc srcDraw e)
  tgtEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) →
    IsPolygonal (edgeArc tgtDraw e)
  /-- The relabelled source ear occupies exactly the path supplied by the ambient graph. -/
  srcEarSet_eq : splitData.earSet srcPos srcDraw = Graph.edgesCover Hdraw D
  /-- Every old or newly introduced graph vertex is a vertex of the new realization. -/
  vertexSet_subset :
    V(B.union (H.pathGraphOf a D)) ⊆
      V((splitData.realize T.src srcPos srcDraw srcCrosscut).graph)

namespace EarStepData

variable {T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
  {B H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {a : Plane} {D : List γ}

/-- The generated pair assembled from the data of one realized ear. -/
noncomputable def pair (w : EarStepData T B H Hdraw a D) :
    GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom :=
  T.split T.str_combInvariants w.splitData w.srcPos w.srcDraw w.tgtPos w.tgtDraw
    w.srcCrosscut w.tgtCrosscut w.earHomeo w.srcEdgePolygonal w.tgtEdgePolygonal

@[simp] theorem pair_src (w : EarStepData T B H Hdraw a D) :
    w.pair.src = w.splitData.realize T.src w.srcPos w.srcDraw w.srcCrosscut := rfl

@[simp] theorem pair_tgt (w : EarStepData T B H Hdraw a D) :
    w.pair.tgt = w.splitData.realize T.tgt w.tgtPos w.tgtDraw w.tgtCrosscut := rfl

/-- The exposed constructor data really performs one `EarStep`: the pair it builds refines the
original pair along the composite parent map, occupies the enlarged source graph, and contains
all of that graph's vertices as 0-cells. -/
theorem isPartialTransferOf_pair
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom} {b : Plane}
    {par : γ → γ} (w : EarStepData T B H Hdraw a D)
    (hdraw : H.IsDrawing Hdraw) (hpath : H.IsPath a D b) (hab : a ≠ b)
    (hT : IsPartialTransferOf T P B Hdraw par) :
    IsPartialTransferOf w.pair P (B.union (H.pathGraphOf a D)) Hdraw
      (par ∘ w.splitData.parent) where
  refines_src :=
    ((w.splitData.isCellDecomposition_and_isFaceJordan_realize w.srcCrosscut
      T.str_combInvariants T.src_isCellDecomposition T.src_isFaceJordan).2.2).trans hT.refines_src
  refines_tgt :=
    ((w.splitData.isCellDecomposition_and_isFaceJordan_realize w.tgtCrosscut
      T.str_combInvariants T.tgt_isCellDecomposition T.tgt_isFaceJordan).2.2).trans hT.refines_tgt
  sourceSkeletonSet_subset :=
    hT.sourceSkeletonSet_subset.trans
      (w.splitData.skeletonSet_subset_realize w.srcCrosscut)
  homeo_eqOn := by
    intro x hx
    calc
      w.pair.homeo.toFun x = T.homeo.toFun x :=
        w.splitData.splitHomeo_eqOn
          (g := T.homeo) (hE₁ := w.srcCrosscut) (hE₂ := w.tgtCrosscut)
          (m := w.earHomeo) (hT.sourceSkeletonSet_subset hx)
      _ = P.homeo.toFun x := hT.homeo_eqOn hx
  skeletonSet_eq := by
    change (w.splitData.realize T.src w.srcPos w.srcDraw w.srcCrosscut).skeletonSet = _
    rw [w.splitData.skeletonSet_realize, hT.skeletonSet_eq, w.srcEarSet_eq,
      Graph.pointSet_union, hdraw.pointSet_pathGraphOf hpath.isWalk (hpath.ne_nil hab)]
  vertexSet_subset := by
    change V(B.union (H.pathGraphOf a D)) ⊆
      V((w.splitData.realize T.src w.srcPos w.srcDraw w.srcCrosscut).graph)
    exact w.vertexSet_subset

end EarStepData

/-! #### Locating the source face of a graph-theoretic ear -/

/-- A nontrivial graph-theoretic ear determines two abstract endpoint vertices and a unique
source face containing its open arc.  This is the complete source-side input needed to choose
the boundary paths of `SplitData`; in particular `CellsAbsorb` is no longer an extra
hypothesis. -/
theorem exists_source_face_of_ear
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    {a b : Plane} {D : List γ} {par : γ → γ}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hBH : B ≤ H) (hpath : H.IsPath a D b) (hab : a ≠ b)
    (haB : a ∈ V(B)) (hbB : b ∈ V(B))
    (hint : ∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B))
    (hT : IsPartialTransferOf T P B Hdraw par) :
    ∃ u v F, u ∈ V(T.str.skel) ∧ v ∈ V(T.str.skel) ∧ u ≠ v ∧
      T.src.pos u = a ∧ T.src.pos v = b ∧ F ∈ T.str.faces ∧
      Graph.edgesCover Hdraw D \ {a, b} ⊆ T.src.cell F ∧
      T.str.sub u F ∧ T.str.sub v F := by
  have haT := hT.vertexSet_subset haB
  have hbT := hT.vertexSet_subset hbB
  rw [CellStructure.Realization.vertexSet_graph] at haT hbT
  obtain ⟨u, hu, hua⟩ := haT
  obtain ⟨v, hv, hvb⟩ := hbT
  have huv : u ≠ v := by
    intro huv
    apply hab
    rw [← hua, ← hvb, huv]
  have harc : IsArcBetween (Graph.edgesCover Hdraw D) a b :=
    hH.isDrawing.path_isArcBetween hpath (hpath.ne_nil hab)
  let N := Graph.edgesCover Hdraw D \ {a, b}
  have hNconn : IsPreconnected N := harc.isConnected_diff.isPreconnected
  have hNne : N.Nonempty := harc.isConnected_diff.nonempty
  have hND : N ⊆ srcDom := by
    intro x hx
    exact hH.pointSet_subset
      (Graph.edgesCover_subset_pointSet (fun g hg => hpath.edge_mem hg) hx.1)
  have hNdisj : Disjoint N T.src.skeletonSet := by
    rw [hT.skeletonSet_eq]
    refine Set.disjoint_left.2 fun x hx hxB ↦ hx.2 ?_
    exact hH.isDrawing.edgesCover_inter_pointSet hBH hpath hint hnew ⟨hx.1, hxB⟩
  obtain ⟨F, hF, hNF, huF, hvF, -⟩ :=
    T.src_isCellDecomposition.exists_face_of_ear
      (T.src_isCellDecomposition.cellsAbsorb T.src_isFaceJordan)
      hNconn hNne hND hNdisj hu hv
      (hua ▸ harc.left_mem_closure_diff) (hvb ▸ harc.right_mem_closure_diff)
  exact ⟨u, v, F, hu, hv, huv, hua, hvb, hF, hNF, huF, hvF⟩

/-- Every edge of a genuine source ear is polygonal.  The source-extension dichotomy allows an
edge to be nonpolygonal only when its whole arc lies in the outer curve.  But that curve is in
the current skeleton, whereas the open ear lies in one current face and hence misses the
skeleton; a nondegenerate drawn edge cannot then remain. -/
theorem source_ear_edge_polygonal
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    {a b : Plane} {D : List γ} {F : γ}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hpath : H.IsPath a D b) (hF : F ∈ T.str.faces)
    (hinside : Graph.edgesCover Hdraw D \ {a, b} ⊆ T.src.cell F) :
    ∀ e ∈ D, IsPolygonal (edgeArc Hdraw e) := by
  intro e he
  rcases hH.edge_dichotomy (hpath.edge_mem he) with houter | hpoly
  · exfalso
    have houterSkel : srcOuter ⊆ T.src.skeletonSet := by
      intro z hz
      apply T.src.outerSet_subset_skeletonSet
      rw [T.src_isWeaklyAdmissible.outerSet_eq]
      exact hz
    have harcPair : edgeArc Hdraw e ⊆ ({a, b} : Set Plane) := by
      intro z hz
      by_contra hzpair
      have hzCell : z ∈ T.src.cell F :=
        hinside ⟨Graph.mem_edgesCover he hz, hzpair⟩
      have hzSkel : z ∈ T.src.skeletonSet := houterSkel (houter hz)
      exact Set.disjoint_left.1
        (T.src.disjoint_cell_skeletonSet T.src_isCellDecomposition hF) hzCell hzSkel
    obtain ⟨x, y, hxy⟩ := H.exists_isLink_of_mem_edgeSet (hpath.edge_mem he)
    have harc := hH.isDrawing.edge_isArcBetween hxy
    have hxyne := hH.isDrawing.ne_of_isLink hxy
    rcases harcPair harc.left_mem with rfl | rfl <;>
      rcases harcPair harc.right_mem with rfl | rfl
    · exact hxyne rfl
    · exact harc.not_subset_pair harcPair
    · exact harc.not_subset_pair (by simpa [Set.pair_comm] using harcPair)
    · exact hxyne rfl
  · exact hpoly.1

/-- **The conclusion of `thm:finite-transfer`(a).** -/
structure IsTransferOf (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (par : γ → γ) : Prop
    extends IsPartialTransferOf T P H Hdraw par where
  /-- The transferred source realization is admissible. -/
  src_isAdmissible : T.src.IsAdmissible srcOuter srcDom
  /-- The transferred target realization is admissible — "`H` can be transferred to an
  admissible target realization `H'`". -/
  tgt_isAdmissible : T.tgt.IsAdmissible tgtOuter tgtDom

/-! ### The two assumed steps

Both are strictly weaker than `thm:finite-transfer`(a) itself, and both are statements a later
module can discharge without circularity.

`CommonSubdivision` is **step 1**: after overlaying the proposed polygonal nonboundary edges
with the old polygonal nonboundary skeleton and subdividing at every intersection — and
transferring each new point to the other realization along the chosen edge parametrization —
the old skeleton is literally a subgraph of the new one on both sides. In Lean that is: some
2-connected subgraph `K ≤ H` carries a generated pair refining the given one. It is not the
theorem: it makes only edge subdivisions, inserts no ear, and its conclusion is about a subgraph
of `H`, not about `H`.

`EarStep` is **step 3**: one ear insertion — at most two edge subdivisions followed by one
2-cell split — carries a partial transfer of `B` to a partial transfer of `B` with the ear glued
on. Its geometric core in direction (a) is `Schoenflies.exists_target_crosscut_split` below,
which is proved here; only the abstract-data bookkeeping around it is assumed.

**`EarStep` carries `[Infinite γ]`, and without it the hypothesis is false.** Every cell of
every structure in sight is a *name* drawn from the one type `γ`: `V(skel)`, `E(skel)` and
`faces` are three disjoint subsets of it. An ear insertion consumes fresh names — one per
interior vertex of the ear, one per ear edge, and two for the 2-cells the split creates
(`SplitData.edge_fresh`, `.vertex_fresh`, `.face₁_notMem`, `.face₂_notMem`) — while the
conclusion `IsPartialTransferOf T' P (B ∪ ear) Hdraw par'` forces `T'` to realize a subdivision
of the enlarged graph, so `V(B ∪ ear) ⊆ V(T'.src.graph) = T'.src.pos '' V(T'.str.skel)` and the
new skeleton must occupy strictly more of the plane than the old one. On a finite `γ` those
demands eventually exceed the supply: a structure realizing a subdivision of a 2-connected graph
with `e` edges needs at least `e` edge names, at least as many vertex names, and at least one
face name per complementary region, all pairwise distinct inside `γ`. A `γ` large enough to
carry the transfer of `B` and too small to carry the transfer of `B` with one more ear makes the
hypotheses of `EarStep` satisfiable and its conclusion unsatisfiable.

That argument is prose, not machine-checked: pinning it down needs a `GeneratedPair` over an
exactly-exhausted finite `γ`, which is a page of construction for a defect the type class
removes outright. What *is* machine-checked is that nothing below needs more than `Infinite γ`,
and the consumer instantiates `γ := ℕ`. The rule that found this is the standing one: a
hypothesis must be a statement one believes, and `EarStep` without a supply of fresh names is
not one. -/

/-- **Step 1, the common subdivision**, as an interface. -/
def CommonSubdivision (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∃ (K : Graph Plane γ) (T₀ : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par₀ : γ → γ),
    K.IsTwoConnected ∧ K ≤ H ∧ IsPartialTransferOf T₀ P K Hdraw par₀

/-- **Step 3, one ear insertion**, as an interface.

The data handed to the step is exactly what `Graph.IsTwoConnected.ear_decomposition` supplies:
the current subgraph `B`, the ear `D` as a path of `H` between two distinct vertices of `B`, and
the freshness of the ear's interior — which is what makes the ear's interior lie in a single
current face, since it is connected and disjoint from the current skeleton.

`Infinite γ` is not decoration: the step consumes fresh cell names, and on a finite `γ` the
statement is false. See the section docstring above. -/
def EarStep [Infinite γ] (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsPartialTransferOf T P B Hdraw par →
      ∃ (T' : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par' : γ → γ),
        IsPartialTransferOf T' P (B.union (H.pathGraphOf a D)) Hdraw par'

/-- The constructive content needed in the nontrivial branch of `EarStep`: for an ear whose
edges are genuinely new, produce the explicit split and its two realized crosscuts.  The
degenerate branch in which the proposed path was already in `B` is handled by
`earStep_of_data`. -/
def EarStepConstruction [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (_hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    (∀ g ∈ D, g ∉ E(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsPartialTransferOf T P B Hdraw par → Nonempty (EarStepData T B H Hdraw a D)

structure SourceEarStepData (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (a : Plane) (D : List γ) where
  splitData : T.str.SplitData
  srcPos : γ → Plane
  srcDraw : γ → ℝ → Plane
  srcCrosscut : splitData.EarCrosscut T.src srcPos srcDraw
  srcEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) → IsPolygonal (Graph.edgeArc srcDraw e)
  srcEarSet_eq : splitData.earSet srcPos srcDraw = Graph.edgesCover Hdraw D
  vertexSet_subset :
    V(B.union (H.pathGraphOf a D)) ⊆
      V((splitData.realize T.src srcPos srcDraw srcCrosscut).graph)

/-- The ambient path is injectively renamed with fresh abstract vertex and edge cells, two more
fresh names become the new faces, and the resulting abstract split is realized on the source. -/
theorem exists_sourceEarStepData [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) :
    ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
      H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
      (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
      (∀ g ∈ D, g ∉ E(B)) →
      ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
        IsPartialTransferOf T P B Hdraw par → Nonempty (SourceEarStepData T B H Hdraw a D) := by
  classical
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  obtain ⟨u, v, F, hu, hv, huv, hua, hvb, hF, hinside, huF, hvF⟩ :=
    exists_source_face_of_ear hH hBH hpath hab haB hbB hint hnew hT
  let paths := T.str_boundaryCycles.boundaryPaths F hF u v hu hv huF hvF huv
  let Q : Graph Plane γ := H.pathGraphOf a D
  have hQle : Q ≤ H := Graph.pathGraphOf_le hpath.isWalk
  have hQpath : Q.IsPathGraph a D b := hpath.isPathGraph_pathGraphOf
  have haQ : a ∈ V(Q) := Graph.mem_vertexSet_pathGraphOf_self
  have hbQ : b ∈ V(Q) := by
    rw [Graph.pathGraphOf_vertexSet]
    exact hpath.target_mem_walkVertices
  have hQfinV : V(Q).Finite := hpath.isWalk.finite_vertexSet_pathGraphOf
  have hQfinE : E(Q).Finite := hpath.isWalk.finite_edgeSet_pathGraphOf
  have huCell : u ∈ T.str.cells := T.str.mem_cells_of_mem_vertexSet hu
  have hvCell : v ∈ T.str.cells := T.str.mem_cells_of_mem_vertexSet hv
  obtain ⟨vname, vname_a, vname_b, vname_inj, vname_fresh⟩ :=
    exists_injective_pinned_avoiding T.str.finite_cells huCell hvCell huv
      hQfinV hab
  let newVertices : Set γ := vname '' (V(Q) \ {a, b})
  have hnewVertices_fin : newVertices.Finite := hQfinV.sdiff.image vname
  have hnewVertices_avoid : Disjoint newVertices T.str.cells := by
    rw [Set.disjoint_left]
    rintro z ⟨x, ⟨hxQ, hxab⟩, rfl⟩ hzCell
    exact vname_fresh x hxQ (fun h => hxab (Or.inl h)) (fun h => hxab (Or.inr h)) hzCell
  let edgeUsed : Set γ := T.str.cells ∪ newVertices
  have hedgeUsed_fin : edgeUsed.Finite := T.str.finite_cells.union hnewVertices_fin
  let _ : Finite E(Q) := Set.finite_coe_iff.mpr hQfinE
  obtain ⟨freshEdge, freshEdge_inj, freshEdge_avoid⟩ :=
    exists_injective_avoiding edgeUsed hedgeUsed_fin E(Q)
  let ename : γ → γ := fun e => if he : e ∈ E(Q) then freshEdge ⟨e, he⟩ else u
  have ename_apply {e : γ} (he : e ∈ E(Q)) : ename e = freshEdge ⟨e, he⟩ := by
    simp [ename, he]
  have ename_inj : InjOn ename E(Q) := by
    intro e he f hf hef
    have hsub : (⟨e, he⟩ : E(Q)) = ⟨f, hf⟩ := by
      apply freshEdge_inj
      calc
        freshEdge ⟨e, he⟩ = ename e := (ename_apply he).symm
        _ = ename f := hef
        _ = freshEdge ⟨f, hf⟩ := ename_apply hf
    exact congrArg (fun z : E(Q) => z.1) hsub
  have ename_avoid {e : γ} (he : e ∈ E(Q)) : ename e ∉ edgeUsed := by
    rw [ename_apply he]
    exact freshEdge_avoid ⟨e, he⟩
  let newEdges : Set γ := ename '' E(Q)
  have hnewEdges_fin : newEdges.Finite := hQfinE.image ename
  have hnewEdges_avoid : Disjoint newEdges edgeUsed := by
    rw [Set.disjoint_left]
    rintro z ⟨e, he, rfl⟩
    exact ename_avoid he
  let faceUsed : Set γ := edgeUsed ∪ newEdges
  have hfaceUsed_fin : faceUsed.Finite := hedgeUsed_fin.union hnewEdges_fin
  obtain ⟨freshFace, freshFace_inj, freshFace_avoid⟩ :=
    exists_injective_avoiding faceUsed hfaceUsed_fin (Fin 2)
  let face₁ : γ := freshFace 0
  let face₂ : γ := freshFace 1
  let relabelled : Graph Plane γ := Q.relabelEdges ename ename_inj
  let ear : Graph γ γ := relabelled.map vname
  have hVear : V(ear) = vname '' V(Q) := by simp [ear, relabelled]
  have hEear : E(ear) = ename '' E(Q) := by simp [ear, relabelled]
  have hearPath : ear.IsPathGraph u (D.map ename) v := by
    have hrel := hQpath.relabelEdges ename_inj
    have hmap := hrel.map (by simpa [relabelled] using vname_inj)
    simpa [ear, relabelled, vname_a, vname_b] using hmap
  have hear_disjoint : Disjoint V(ear) E(ear) := by
    rw [Set.disjoint_left]
    rintro z hzV hzE
    rw [hVear] at hzV
    rw [hEear] at hzE
    obtain ⟨x, hxQ, rfl⟩ := hzV
    obtain ⟨e, heQ, heq⟩ := hzE
    have hedgeAvoid := ename_avoid heQ
    apply hedgeAvoid
    rcases eq_or_ne x a with rfl | hxa
    · exact Or.inl (by rw [heq, vname_a]; exact huCell)
    rcases eq_or_ne x b with rfl | hxb
    · exact Or.inl (by rw [heq, vname_b]; exact hvCell)
    · exact Or.inr ⟨x, ⟨hxQ, by simp [hxa, hxb]⟩, heq.symm⟩
  have hvertex_inter : V(ear) ∩ V(T.str.skel) = {u, v} := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzEar, hzOld⟩
      rw [hVear] at hzEar
      obtain ⟨x, hxQ, rfl⟩ := hzEar
      rcases eq_or_ne x a with rfl | hxa
      · simp [vname_a]
      rcases eq_or_ne x b with rfl | hxb
      · simp [vname_b]
      exfalso
      exact vname_fresh x hxQ hxa hxb
        (T.str.mem_cells_of_mem_vertexSet hzOld)
    · rintro z (rfl | rfl)
      · exact ⟨hVear ▸ ⟨a, haQ, vname_a⟩, hu⟩
      · exact ⟨hVear ▸ ⟨b, hbQ, vname_b⟩, hv⟩
  have hface₁Avoid : face₁ ∉ faceUsed := freshFace_avoid 0
  have hface₂Avoid : face₂ ∉ faceUsed := freshFace_avoid 1
  let d : T.str.SplitData := {
    face := F
    face₁ := face₁
    face₂ := face₂
    ear := ear
    source := u
    target := v
    earWalk := D.map ename
    path₁ := paths.path₁
    path₂ := paths.path₂
    isPathGraph := hearPath
    isPath₁ := paths.isPath₁
    isPath₂ := paths.isPath₂
    ear_disjoint := hear_disjoint
    source_ne_target := huv
    face_mem := hF
    vertexSet_inter := hvertex_inter
    edge_fresh := by
      intro e he
      rw [hEear] at he
      obtain ⟨f, hf, rfl⟩ := he
      exact fun hmem => ename_avoid hf (Or.inl hmem)
    vertex_fresh := by
      intro z hz hzu hzv
      rw [hVear] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hxa : x ≠ a := fun h => hzu (h ▸ vname_a)
      have hxb : x ≠ b := fun h => hzv (h ▸ vname_b)
      exact vname_fresh x hx hxa hxb
    face₁_notMem := fun h => hface₁Avoid (Or.inl (Or.inl h))
    face₂_notMem := fun h => hface₂Avoid (Or.inl (Or.inl h))
    face₁_notMem_ear := by
      rintro (hz | hz)
      · rw [hVear] at hz
        obtain ⟨x, hx, heq⟩ := hz
        rcases eq_or_ne x a with rfl | hxa
        · apply hface₁Avoid (Or.inl (Or.inl (show face₁ ∈ T.str.cells by
            rw [← heq, vname_a]; exact huCell)))
        rcases eq_or_ne x b with rfl | hxb
        · apply hface₁Avoid (Or.inl (Or.inl (show face₁ ∈ T.str.cells by
            rw [← heq, vname_b]; exact hvCell)))
        · exact hface₁Avoid (Or.inl (Or.inr ⟨x, ⟨hx, by simp [hxa, hxb]⟩, heq⟩))
      · rw [hEear] at hz
        exact hface₁Avoid (Or.inr hz)
    face₂_notMem_ear := by
      rintro (hz | hz)
      · rw [hVear] at hz
        obtain ⟨x, hx, heq⟩ := hz
        rcases eq_or_ne x a with rfl | hxa
        · apply hface₂Avoid (Or.inl (Or.inl (show face₂ ∈ T.str.cells by
            rw [← heq, vname_a]; exact huCell)))
        rcases eq_or_ne x b with rfl | hxb
        · apply hface₂Avoid (Or.inl (Or.inl (show face₂ ∈ T.str.cells by
            rw [← heq, vname_b]; exact hvCell)))
        · exact hface₂Avoid (Or.inl (Or.inr ⟨x, ⟨hx, by simp [hxa, hxb]⟩, heq⟩))
      · rw [hEear] at hz
        exact hface₂Avoid (Or.inr hz)
    face_ne := fun h => Fin.zero_ne_one (freshFace_inj h)
    sub_face := paths.sub_face
    paths_meet := paths.paths_meet
  }
  let srcPos : γ → Plane := Function.invFunOn vname V(Q)
  let srcDraw : γ → ℝ → Plane := Graph.relabelDrawing Q ename Hdraw
  have hQdraw : Graph.IsDrawing Q Hdraw := hH.isDrawing.mono hQle
  have hrelDraw : Graph.IsDrawing relabelled srcDraw := by
    exact hQdraw.relabelEdges ename_inj
  have hearGraph : d.earGraph srcPos = relabelled := by
    change (relabelled.map vname).map srcPos = relabelled
    simpa [srcPos, relabelled] using
      (Graph.map_map_invFunOn (G := relabelled) (f := vname)
        (by simpa [relabelled] using vname_inj))
  have hsrcSet : d.earSet srcPos srcDraw = Graph.edgesCover Hdraw D := by
    rw [CellStructure.SplitData.earSet, hearGraph, Graph.pointSet_relabelEdges ename_inj]
    simpa [Q] using hH.isDrawing.pointSet_pathGraphOf hpath.isWalk (hpath.ne_nil hab)
  have hsrcEdgeOrig := source_ear_edge_polygonal hH hpath hF hinside
  have hsrcEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) →
      IsPolygonal (Graph.edgeArc srcDraw e) := by
    intro e he
    change e ∈ E(ear) at he
    rw [hEear] at he
    obtain ⟨f, hfQ, rfl⟩ := he
    rw [Graph.edgeArc_relabelDrawing ename_inj hfQ]
    apply hsrcEdgeOrig f
    rwa [Graph.pathGraphOf_edgeSet hpath.isWalk] at hfQ
  have hsrcPoly : IsPolygonal (d.earSet srcPos srcDraw) := by
    rw [hsrcSet]
    exact hQdraw.isPolygonal_edgesCover
      (fun f hfQ => hsrcEdgeOrig f (by rwa [Graph.pathGraphOf_edgeSet hpath.isWalk] at hfQ))
      hpath.pathGraphOf.isWalk (hpath.ne_nil hab)
  have hsrc : d.EarCrosscut T.src srcPos srcDraw := {
    pos_source := by
      change srcPos u = T.src.pos u
      rw [hua]
      change Function.invFunOn vname V(Q) u = a
      rw [← vname_a, vname_inj.leftInvOn_invFunOn haQ]
    pos_target := by
      change srcPos v = T.src.pos v
      rw [hvb]
      change Function.invFunOn vname V(Q) v = b
      rw [← vname_b, vname_inj.leftInvOn_invFunOn hbQ]
    injOn := by
      change InjOn (Function.invFunOn vname V(Q)) V(ear)
      rw [hVear]
      exact Function.invFunOn_injOn_image vname V(Q)
    isDrawing := by rw [hearGraph]; exact hrelDraw
    subset_face := by
      rw [hsrcSet]
      simpa [d, hua, hvb] using hinside
    disjoint_skeleton := T.src.disjoint_cell_skeletonSet T.src_isCellDecomposition hF
    polygonal := hsrcPoly
  }
  refine ⟨{
    splitData := d
    srcPos := srcPos
    srcDraw := srcDraw
    srcCrosscut := hsrc
    srcEdgePolygonal := hsrcEdgePoly
    srcEarSet_eq := hsrcSet
    vertexSet_subset := ?_
  }⟩
  change V(B.union (H.pathGraphOf a D)) ⊆
    V((T.str.splitFace d).skel.map (d.splitPos T.src srcPos))
  rw [hsrc.splitGraph_eq]
  intro x hx
  rcases hx with hxB | hxQ
  · exact Or.inl (hT.vertexSet_subset hxB)
  · apply Or.inr
    rw [hearGraph, Graph.vertexSet_relabelEdges]
    exact hxQ

/-- **`EarStep`, assembled from explicit constructor data.**  This is the end-to-end
bookkeeping theorem: the nontrivial branch is realized by `EarStepData.pair`; if the proposed
ear contains an old edge, `Graph.ear_edges_notMem_or_union_eq` shows that the union did not
change and the current transfer itself is the answer. -/
theorem earStep_of_data [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hbuild : EarStepConstruction P H Hdraw hH) :
    EarStep P H Hdraw := by
  intro B a b D hB hBH hpath hab haB hbB hint T par hT
  rcases Graph.ear_edges_notMem_or_union_eq hBH hpath hab haB hbB hint with hnew | hsame
  · obtain ⟨w⟩ := hbuild B a b D hB hBH hpath hab haB hbB hint hnew T par hT
    exact ⟨w.pair, par ∘ w.splitData.parent,
      w.isPartialTransferOf_pair hH.isDrawing hpath hab hT⟩
  · refine ⟨T, par, ?_⟩
    rw [hsame]
    exact hT

/-! ### Steps 2 and 3: the induction through the ear sequence -/

/-- **Steps 2 and 3 of the proof of `thm:finite-transfer`.** By `lem:relative-ear` the new finite
2-connected graph is obtained from the old subdivided graph by a finite sequence of ears; each
ear insertion is at most two edge subdivisions plus one 2-cell split, so every intermediate stage
is a generated matched cell structure. Given step 1 and one ear, the whole extension transfers.

The invariant carried through the induction is `IsPartialTransferOf`, which does **not** mention
connectedness of the open nonboundary part: `rem:intermediate-disconnection` says an
intermediate stage may genuinely have it disconnected, and nothing here assumes otherwise. -/
theorem transfer_of_ears_of_commonSubdivision_of_earStep [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsub : CommonSubdivision P H Hdraw) (hstep : EarStep P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsPartialTransferOf T P H Hdraw par := by
  let _ := hH.finite
  obtain ⟨K, T₀, par₀, hK, hKH, hbase⟩ := hsub
  refine hH.isTwoConnected.ear_decomposition
    (motive := fun B => ∃ T par, IsPartialTransferOf T P B Hdraw par)
    (fun g x => hH.isDrawing.not_isLoopAt g x) hK hKH ⟨T₀, par₀, hbase⟩ ?_
  rintro B a b D hB - hBH ⟨T, par, hT⟩ hpath hab haB hbB hint
  exact hstep B a b D hB hBH hpath hab haB hbB hint T par hT

/-! ### `thm:finite-transfer`(a) -/

/-- **`thm:finite-transfer`, direction (a): transfer toward the square.**

Let `(Γ, Γ')` be a generated matched cellulation. Suppose `H` is a finite 2-connected plane graph
containing a subdivision of `Γ`, with outer cycle `C`, with every nonboundary edge polygonal, and
with `|H| ∖ C` connected. Then the common subdivision can be made on `Γ'`, and `H` can be
transferred to an admissible target realization `H'`; the resulting generated matched cellulation
refines the old one by an explicit parent map.

This compatibility form accepts both step interfaces as arguments. `earStep` discharges the
second, while `commonSubdivision` in `CommonSubdivision.lean` discharges the first. -/
theorem finite_transfer_toward_square_of_commonSubdivision_of_earStep [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsub : CommonSubdivision P H Hdraw) (hstep : EarStep P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTransferOf T P H Hdraw par := by
  obtain ⟨T, par, hT⟩ :=
    transfer_of_ears_of_commonSubdivision_of_earStep hH hsub hstep
  -- The final source realization occupies `|H|`, so its open nonboundary part is `|H| ∖ C`,
  -- which the hypothesis on `H` says is connected. Combinatorial invariance moves that to the
  -- target, and both realizations are then admissible.
  have hconn : IsConnected T.src.nonboundary := by
    rw [T.src_nonboundary_eq, hT.skeletonSet_eq]
    exact hH.isConnected
  exact ⟨T, par, hT, T.src_isAdmissible hconn, T.tgt_isAdmissible hconn⟩

/-! ### Step 4, direction (a): the target crosscut

*In part (a), `F*` is a polygonal Jordan region in the square, by
`lem:cellulation-invariants`(vii). Every point of its boundary is polygonally accessible from its
interior. `lem:accessible-endpoints` therefore gives a polygonal crosscut `P* ⊆ closure F*` from
`v*` to `w*`.* Then: *`thm:general-crosscut` says that the crosscut splits the face into exactly
the two Jordan regions bounded by the crosscut together with those two paths.*

That whole paragraph is proved below. It is stated for a *target* face — a
member of a family of components of `Q ∖ |G|` for an ambient open region `Q` whose frontier
belongs to the skeleton — because that is the shape
`Graph.polygonal_side_accessibility_target` consumes, and it is the shape a target realization
of a generated structure has: `Q` is the open square, `|G|` the target skeleton, and the family
is the set of realized open 2-cells. -/

section TargetEar

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
  {Q F J P A₁ A₂ : Set Plane} {cells : Set (Set Plane)} {v w : Plane}

/-- A target 2-cell is an open connected set disjoint from the skeleton. Everything the crosscut
construction needs about it, read off the presentation as a component of `Q ∖ |G|`. -/
theorem isOpen_isPreconnected_disjoint_of_target_cell [G.Finite] (h : IsDrawing G drawing)
    (hQ : IsOpen Q)
    (hcell : ∀ R ∈ cells, R ⊆ Q ∧ ∃ z, R = connectedComponentIn (Q \ pointSet G drawing) z)
    (hF : F ∈ cells) :
    IsOpen F ∧ IsPreconnected F ∧ Disjoint F (pointSet G drawing) := by
  obtain ⟨-, z, rfl⟩ := hcell F hF
  have hopen : IsOpen (Q \ pointSet G drawing) := hQ.sdiff h.isClosed_pointSet
  exact ⟨hopen.connectedComponentIn, isPreconnected_connectedComponentIn,
    Set.disjoint_left.2 fun _ hx => (connectedComponentIn_subset _ _ hx).2⟩

/-- **The target crosscut of `thm:finite-transfer`(a), step 4.** Two distinct points of a curve
`J` inside the target skeleton, both in the closure of a target 2-cell `F`, are joined by a
simple polygonal arc lying in `F` apart from its two endpoints and meeting `J` exactly there.

The three inputs are the three the blueprint names: `lem:polygonal-side-accessibility` on the
target side for the accessibility of each endpoint, and `lem:accessible-endpoints` in its
crosscut form for the join. Nothing is assumed. -/
theorem exists_target_crosscut [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hQ : IsOpen Q) (hQK : frontier Q ⊆ pointSet G drawing)
    (hcell : ∀ R ∈ cells, R ⊆ Q ∧ ∃ z, R = connectedComponentIn (Q \ pointSet G drawing) z)
    (hF : F ∈ cells) (hJ : J ⊆ pointSet G drawing)
    (hvw : v ≠ w) (hvJ : v ∈ J) (hwJ : w ∈ J)
    (hv : v ∈ closure F) (hw : w ∈ closure F) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P v w ∧ P \ {v, w} ⊆ F ∧ P ∩ J = {v, w} := by
  obtain ⟨hopen, hconn, hdisj⟩ :=
    isOpen_isPreconnected_disjoint_of_target_cell h hQ hcell hF
  obtain ⟨ws, -, -, -, hsub, harc, hmeet⟩ :=
    exists_crosscut_of_polyAccessible hopen hconn (hdisj.mono_right hJ) hvw hvJ hwJ
      (Graph.polygonal_side_accessibility_target h hpoly hQ hQK hcell hF hv)
      (Graph.polygonal_side_accessibility_target h hpoly hQ hQK hcell hF hw)
  exact ⟨poly ws, ⟨ws, rfl⟩, harc, hsub, hmeet⟩

/-- **Step 4 in full: the target crosscut splits the target face into exactly two Jordan
regions.** By `lem:cellulation-invariants`(vii) the target 2-cell `F` is the bounded
complementary region of the Jordan curve `J` realizing its boundary walk; the crosscut of
`Schoenflies.exists_target_crosscut` is then a crosscut of `J` in the sense of
`thm:general-crosscut`, which decomposes `F` into the two Jordan regions bounded by the crosscut
together with the two boundary paths.

The conclusion is returned in the shape assertion (i) consumes at a 2-cell split
(`Schoenflies.crosscut_cell_partition`): the old open 2-cell is the disjoint union of the two new
open 2-cells and the open crosscut, each new 2-cell is open and nonempty, and the closure of each
is that open 2-cell together with its own boundary curve. -/
theorem exists_target_crosscut_split [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hQ : IsOpen Q) (hQK : frontier Q ⊆ pointSet G drawing)
    (hcell : ∀ R ∈ cells, R ⊆ Q ∧ ∃ z, R = connectedComponentIn (Q \ pointSet G drawing) z)
    (hF : F ∈ cells) (hJ : J ⊆ pointSet G drawing) (hJc : IsJordanCurve J) (hFJ : F = inside J)
    (hvw : v ≠ w) (hvJ : v ∈ J) (hwJ : w ∈ J)
    (hv : v ∈ closure F) (hw : w ∈ closure F) (hcut : IsCutPair J v w A₁ A₂) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P v w ∧ P \ {v, w} ⊆ F ∧ P ∩ J = {v, w} ∧
      IsCrosscut J P v w ∧
      F = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∪ (P \ {v, w}) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      Disjoint (inside (A₁ ∪ P)) (P \ {v, w}) ∧
      Disjoint (inside (A₂ ∪ P)) (P \ {v, w}) ∧
      IsOpen (inside (A₁ ∪ P)) ∧ IsOpen (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      closure (inside (A₁ ∪ P)) = inside (A₁ ∪ P) ∪ (A₁ ∪ P) ∧
      closure (inside (A₂ ∪ P)) = inside (A₂ ∪ P) ∪ (A₂ ∪ P) := by
  obtain ⟨P, hPpoly, hParc, hPsub, hPmeet⟩ :=
    exists_target_crosscut h hpoly hQ hQK hcell hF hJ hvw hvJ hwJ hv hw
  have hcross : IsCrosscut J P v w :=
    ⟨hJc, hParc, hPpoly, hvJ, hwJ, by rw [← hFJ]; exact hPsub⟩
  have hpart := crosscut_cell_partition (fun _ hS => jordan_curve_theorem hS) hcross hcut
    hcross.hasArcCollars
  exact ⟨P, hPpoly, hParc, hPsub, hPmeet, hcross, by rw [hFJ]; exact hpart.1, hpart.2.1,
    hpart.2.2.1, hpart.2.2.2.1, hpart.2.2.2.2.1, hpart.2.2.2.2.2.1, hpart.2.2.2.2.2.2.1,
    hpart.2.2.2.2.2.2.2.1, hpart.2.2.2.2.2.2.2.2.1, hpart.2.2.2.2.2.2.2.2.2⟩

end TargetEar

/-- A face and two distinct boundary vertices of a generated pair admit the target polygonal
crosscut needed by an ear insertion.  All accessibility hypotheses are discharged from the
fields maintained by `GeneratedPair`. -/
theorem GeneratedPair.exists_target_crosscut
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {u v F : γ} (hu : u ∈ V(P.str.skel)) (hv : v ∈ V(P.str.skel))
    (huv : u ≠ v) (hF : F ∈ P.str.faces) (huF : P.str.sub u F)
    (hvF : P.str.sub v F) :
    ∃ A : Set Plane, IsPolygonal A ∧
      IsArcBetween A (P.tgt.pos u) (P.tgt.pos v) ∧
      A \ {P.tgt.pos u, P.tgt.pos v} ⊆ P.tgt.cell F ∧
      A ∩ frontier (P.tgt.cell F) = {P.tgt.pos u, P.tgt.pos v} := by
  have hucl : P.tgt.pos u ∈ closure (P.tgt.cell F) := by
    have hsub := P.tgt_isCellDecomposition.subset_closure
      (P.str.mem_cells_of_mem_vertexSet hu) (P.str.mem_cells_of_mem_faces hF) huF
    rw [P.tgt.cell_vertex hu] at hsub
    exact hsub (Set.mem_singleton _)
  have hvcl : P.tgt.pos v ∈ closure (P.tgt.cell F) := by
    have hsub := P.tgt_isCellDecomposition.subset_closure
      (P.str.mem_cells_of_mem_vertexSet hv) (P.str.mem_cells_of_mem_faces hF) hvF
    rw [P.tgt.cell_vertex hv] at hsub
    exact hsub (Set.mem_singleton _)
  have huJ : P.tgt.pos u ∈ frontier (P.tgt.cell F) := by
    rw [(P.tgt_isFaceJordan.isOpen hF).frontier_eq]
    refine ⟨hucl, ?_⟩
    exact fun hmem => Set.disjoint_left.1
      (P.tgt.disjoint_cell_skeletonSet P.tgt_isCellDecomposition hF) hmem
      (P.tgt.pos_mem_skeletonSet hu)
  have hvJ : P.tgt.pos v ∈ frontier (P.tgt.cell F) := by
    rw [(P.tgt_isFaceJordan.isOpen hF).frontier_eq]
    refine ⟨hvcl, ?_⟩
    exact fun hmem => Set.disjoint_left.1
      (P.tgt.disjoint_cell_skeletonSet P.tgt_isCellDecomposition hF) hmem
      (P.tgt.pos_mem_skeletonSet hv)
  let _ : (P.str.skel.map P.tgt.pos).Finite := {
    finite_vertexSet := by
      rw [Graph.vertexSet_map]
      exact P.str.finite_vertexSet.image _
    finite_edgeSet := by
      rw [Graph.edgeSet_map]
      exact P.str.finite_edgeSet
  }
  have hcell : ∀ A ∈ {A : Set Plane | ∃ T ∈ P.str.faces, A = P.tgt.cell T},
      A ⊆ tgtDom \ tgtOuter ∧
        ∃ z, A = connectedComponentIn ((tgtDom \ tgtOuter) \ P.tgt.skeletonSet) z := by
    rintro A ⟨T, hT, rfl⟩
    exact P.tgt_face_isComponent hT
  have hfaceMem : P.tgt.cell F ∈
      {A : Set Plane | ∃ T ∈ P.str.faces, A = P.tgt.cell T} := ⟨F, hF, rfl⟩
  exact Schoenflies.exists_target_crosscut P.tgt.isDrawing P.tgt_isPolygonal
    P.tgtInterior_isOpen P.tgtInterior_frontier_subset
    hcell hfaceMem
    (P.tgt_isCellDecomposition.frontier_cell_subset_skeletonSet P.tgt_isFaceJordan hF)
    (fun h => huv (P.tgt.injOn_pos hu hv h)) huJ hvJ hucl hvcl

/-! ### Completing the ear step -/

/-- **The constructive ear interface.** The source half is the freshly
renamed path supplied by `exists_sourceEarStepData`; the target half is a polygonal crosscut of
the corresponding face, divided edge-for-edge by `EarCrosscut.exists_matched_target`. -/
theorem earStepConstruction [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) :
    EarStepConstruction P H Hdraw hH := by
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  obtain ⟨w⟩ := exists_sourceEarStepData P H Hdraw hH
    B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  let d := w.splitData
  have hsourceSub : T.str.sub d.source d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.source_mem_cells₁))
  have htargetSub : T.str.sub d.target d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.target_mem_cells₁))
  obtain ⟨A, hApoly, hAarc, hAsub, -⟩ :=
    T.exists_target_crosscut d.source_mem_skel d.target_mem_skel d.source_ne_target
      d.face_mem hsourceSub htargetSub
  obtain ⟨tgtPos, tgtDraw, earHomeo, htgt, htgtEdgePoly⟩ :=
    w.srcCrosscut.exists_matched_target hApoly hAarc hAsub
      (T.tgt.disjoint_cell_skeletonSet T.tgt_isCellDecomposition d.face_mem)
  exact ⟨{
    splitData := d
    srcPos := w.srcPos
    srcDraw := w.srcDraw
    tgtPos := tgtPos
    tgtDraw := tgtDraw
    srcCrosscut := w.srcCrosscut
    tgtCrosscut := htgt
    earHomeo := earHomeo
    srcEdgePolygonal := w.srcEdgePolygonal
    tgtEdgePolygonal := htgtEdgePoly
    srcEarSet_eq := w.srcEarSet_eq
    vertexSet_subset := w.vertexSet_subset
  }⟩

/-- **One ear insertion, with no remaining hypothesis.** -/
theorem earStep [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) : EarStep P H Hdraw :=
  earStep_of_data hH (earStepConstruction P H Hdraw hH)

/-- Steps 2 and 3 of finite transfer, parametrized by the step-1 interface. -/
theorem transfer_of_ears_of_commonSubdivision [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsub : CommonSubdivision P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsPartialTransferOf T P H Hdraw par :=
  transfer_of_ears_of_commonSubdivision_of_earStep hH hsub (earStep P H Hdraw hH)

/-- **Finite transfer toward the square from an explicitly supplied common subdivision.** -/
theorem finite_transfer_toward_square_of_commonSubdivision [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsub : CommonSubdivision P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTransferOf T P H Hdraw par :=
  finite_transfer_toward_square_of_commonSubdivision_of_earStep hH hsub
    (earStep P H Hdraw hH)

/-! ### The ear's endpoints, transferred

*Let `F*, v*, w*` be the corresponding face and endpoints in the other realization.* Under the
representation of `Schoenflies/CombinatorialInvariance.lean` there is nothing to transport: `F`
and the two endpoint 0-cells are cells of the **one** abstract structure both realizations
realize, and assertion (ix) turns "the source endpoint lies on the boundary of the source face"
into the abstract statement `a ≼ F`, which reads back in the target realization. -/

section EndpointTransfer

variable {S : CellStructure γ} {R₁ R₂ : S.Realization} {D₁ D₂ Q J A₁ A₂ : Set Plane} {a b F : γ}

/-- **The endpoints of the ear transfer to the other realization.** A 0-cell on the boundary of a
2-cell in one realization is on the boundary of the same 2-cell in the other. -/
theorem CellStructure.Realization.pos_mem_closure_cell_congr
    (h₁ : R₁.IsCellDecomposition D₁) (h₂ : R₂.IsCellDecomposition D₂)
    (ha : a ∈ V(S.skel)) (hF : F ∈ S.faces) (hmem : R₁.pos a ∈ closure (R₁.cell F)) :
    R₂.pos a ∈ closure (R₂.cell F) := by
  have := h₂.subset_closure (S.mem_cells_of_mem_vertexSet ha) (S.mem_cells_of_mem_faces hF)
    (h₁.sub_of_pos_mem_closure_cell ha hF hmem)
  rw [R₂.cell_vertex ha] at this
  exact this (Set.mem_singleton _)

/-- **The geometric half of one ear insertion, direction (a).**

The source ear lies in a current source 2-cell `F` and its two endpoints are 0-cells on the
boundary of `F` (`hacl`, `hbcl`). The target realization of `F` is a polygonal Jordan region in
the open square `Q` (`hFJ` — assertion (vii)) whose 2-cells are the components of
`Q ∖ |Γ'|` (`hcell` — assertion (i) on the target side). Then the corresponding target endpoints
are joined by a polygonal crosscut inside the closure of the target face, which splits that face
into exactly the two Jordan regions bounded by the crosscut and the two boundary paths.

This is the fourth paragraph of the blueprint's proof of `thm:finite-transfer`(a), assembled;
what is left of the induction step is the abstract-data bookkeeping around it. -/
theorem exists_target_ear (h₁ : R₁.IsCellDecomposition D₁) (h₂ : R₂.IsCellDecomposition D₂)
    (hpoly : ∀ ⦃e⦄, e ∈ E(S.skel) → IsPolygonal (edgeArc R₂.drawing e))
    (hQ : IsOpen Q) (hQK : frontier Q ⊆ R₂.skeletonSet)
    (hcell : ∀ T ∈ S.faces, R₂.cell T ⊆ Q ∧
      ∃ z, R₂.cell T = connectedComponentIn (Q \ R₂.skeletonSet) z)
    (hF : F ∈ S.faces) (hJ : J ⊆ R₂.skeletonSet) (hJc : IsJordanCurve J)
    (hFJ : R₂.cell F = inside J)
    (ha : a ∈ V(S.skel)) (hb : b ∈ V(S.skel)) (hab : R₂.pos a ≠ R₂.pos b)
    (haJ : R₂.pos a ∈ J) (hbJ : R₂.pos b ∈ J)
    (hacl : R₁.pos a ∈ closure (R₁.cell F)) (hbcl : R₁.pos b ∈ closure (R₁.cell F))
    (hcut : IsCutPair J (R₂.pos a) (R₂.pos b) A₁ A₂) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P (R₂.pos a) (R₂.pos b) ∧
      P \ {R₂.pos a, R₂.pos b} ⊆ R₂.cell F ∧ P ∩ J = {R₂.pos a, R₂.pos b} ∧
      IsCrosscut J P (R₂.pos a) (R₂.pos b) ∧
      R₂.cell F = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∪ (P \ {R₂.pos a, R₂.pos b}) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      Disjoint (inside (A₁ ∪ P)) (P \ {R₂.pos a, R₂.pos b}) ∧
      Disjoint (inside (A₂ ∪ P)) (P \ {R₂.pos a, R₂.pos b}) ∧
      IsOpen (inside (A₁ ∪ P)) ∧ IsOpen (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      closure (inside (A₁ ∪ P)) = inside (A₁ ∪ P) ∪ (A₁ ∪ P) ∧
      closure (inside (A₂ ∪ P)) = inside (A₂ ∪ P) ∪ (A₂ ∪ P) := by
  -- The family of target 2-cells, in the shape `lem:polygonal-side-accessibility` consumes.
  have hcell' : ∀ T ∈ {A : Set Plane | ∃ T ∈ S.faces, A = R₂.cell T},
      T ⊆ Q ∧ ∃ z, T = connectedComponentIn (Q \ pointSet R₂.graph R₂.drawing) z := by
    rintro T ⟨T', hT', rfl⟩
    exact hcell T' hT'
  have hpoly' : ∀ e ∈ E(R₂.graph), IsPolygonal (edgeArc R₂.drawing e) := by
    intro e he
    rw [CellStructure.Realization.edgeSet_graph] at he
    exact hpoly he
  have hdraw : IsDrawing R₂.graph R₂.drawing := R₂.isDrawing
  exact exists_target_crosscut_split hdraw hpoly' hQ hQK hcell'
    ⟨F, hF, rfl⟩ hJ hJc hFJ hab haJ hbJ
    (CellStructure.Realization.pos_mem_closure_cell_congr h₁ h₂ ha hF hacl)
    (CellStructure.Realization.pos_mem_closure_cell_congr h₁ h₂ hb hF hbcl) hcut

end EndpointTransfer

/-! ### Step 1: the overlay

*By `lem:polygonal-overlay`, using the convention of `rem:polygonal-overlay-convention`, first
overlay the proposed polygonal nonboundary edges with the old polygonal nonboundary skeleton and
subdivide at all intersections.*

`Schoenflies.polygonal_overlay` does that for a **list of segments**. What step 1 has instead is
a finite family of polygonal *arcs* — the old nonboundary edges and the proposed new ones — so
the two have to be bridged. `Schoenflies.exists_overlay_of_biUnion_finite` is that bridge, and it
is the half of step 1 that is proved here: the union of finitely many nondegenerate polygonal
sets is the point set of a finite plane graph drawn by straight segments, whose vertices are the
ends of the subdivided pieces and therefore include every intersection point.

The nondegeneracy hypothesis is necessary, not cosmetic: a one-point set is polygonal
(`poly [a] = {a}`) and is not the point set of any overlay graph, whose vertices are the ends of
nondegenerate segments.

The matching-subdivision half of step 1 is completed in `CommonSubdivision.lean`: every source
subdivision point is transported through the chosen edge parametrization to the other
realization. -/

/-- **`lem:polygonal-overlay` for a finite family of polygonal sets.** The union of finitely many
nondegenerate polygonal sets is the point set of a finite plane graph whose edges are straight
segments — the overlay, subdivided at every intersection.

This is the first half of step 1 of the proof of `thm:finite-transfer`. -/
theorem exists_overlay_of_biUnion_finite {ι : Type*} {s : Set ι} {A : ι → Set Plane}
    (hs : s.Finite) (hA : ∀ i ∈ s, IsPolygonal (A i))
    (hnd : ∀ i ∈ s, ∃ a ∈ A i, ∃ b ∈ A i, a ≠ b) :
    ∃ G : Graph Plane Piece, Graph.Finite G ∧ IsDrawing G segmentDrawing ∧
      pointSet G segmentDrawing = ⋃ i ∈ s, A i := by
  classical
  -- A vertex list for each member of the family, chosen once and for all.
  have hex : ∀ i : ι, ∃ ws : List Plane, i ∈ s → A i = poly ws := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨ws, hws⟩ := hA i hi
      exact ⟨ws, fun _ => hws⟩
    · exact ⟨[], fun h => absurd h hi⟩
  choose vsf hvsf using hex
  -- Enumerate the index set; the enumeration only feeds the list-indexed overlay.
  set l : List ι := hs.toFinset.toList with hl
  have hlmem : ∀ i, i ∈ l ↔ i ∈ s := by
    intro i; rw [hl, Finset.mem_toList, hs.mem_toFinset]
  -- A nondegenerate polygonal set is exactly what its own segments occupy.
  have hAcov : ∀ i ∈ s, cover (segsOf (vsf i)) = A i := by
    intro i hi
    obtain ⟨a, ha, b, hb, hab⟩ := hnd i hi
    rw [hvsf i hi] at ha hb ⊢
    exact cover_segsOf_eq ha hb hab
  have hcov : cover (l.flatMap fun i => segsOf (vsf i)) = ⋃ i ∈ s, A i := by
    rw [cover_flatMap_list]
    exact Set.iUnion_congr fun i => Set.iUnion_congr_Prop (hlmem i) fun hi => hAcov i hi
  have hnd' : ∀ P ∈ l.flatMap fun i => segsOf (vsf i), P.Nondeg := by
    intro P hP
    obtain ⟨i, -, hPi⟩ := List.mem_flatMap.1 hP
    exact segsOf_nondeg _ P hPi
  obtain ⟨G, hfin, hdraw, hpt⟩ := polygonal_overlay _ hnd'
  exact ⟨G, hfin, hdraw, by rw [hpt, hcov]⟩

/-! ### The interface, exercised

`thm:finite-transfer` exists to feed the recursion of the quantitative-refinement section, which
consumes a transfer only through `Realization.Refines`. This anonymous example is a
machine-checked statement that the conclusion of `finite_transfer_toward_square` delivers exactly
what that recursion reads: the source carrier refines (`lem:refinement-compatibility`(a)), the
same parent map serves both sides (part (c)), and the closed target star of a fixed source point
shrinks (`T_{n+1}(x) \subseteq T_n(x)`).

Nothing below mentions how the transfer was built. If a later change to `IsTransferOf` stopped
serving that recursion, this would break. -/
example [Nonempty γ] {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}
    (h₀ : S₀.CombInvariants) (P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (hT : IsTransferOf T P H Hdraw par) {x : Plane} (hx : x ∈ srcDom) :
    par (T.src.carrier x) = P.src.carrier x ∧
      T.tgt.star (T.src.carrier x) ⊆ P.tgt.star (P.src.carrier x) :=
  ⟨hT.refines_src.parent_carrier P.src_isCellDecomposition T.src_isCellDecomposition hx,
    hT.refines_src.target_star_subset hT.refines_tgt (T.combInvariants h₀)
      P.src_isCellDecomposition T.src_isCellDecomposition hx⟩

end Schoenflies
