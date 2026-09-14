/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.QuantitativeStages
import LeanPool.Schoenflies.GridAttach

/-!
# Finite segment overlays on the source side

The outer source curve is deliberately not polygonal, but every nonouter source edge of a
generated pair is polygonal.  This module extracts an exact finite straight-segment cover of
that compact nonboundary carrier and overlays it with the local window grid.  It is the finite
geometric core of the forward half of the quantitative-refinement recursion.

## Blueprint

* `Schoenflies.SourceNonboundarySegmentCover` — an exact finite segment presentation of the
  current source nonboundary skeleton.
* `Schoenflies.GeneratedPair.exists_sourceNonboundarySegmentCover` — every generated pair has
  such a presentation.
* `Schoenflies.SourceNonboundarySegmentCover.localOverlay` — the old compact source core
  overlaid with one fine local grid.
* `Schoenflies.SourceNonboundarySegmentCover.LocalOverlayRelabeling.graph` — the finite inner
  overlay, freshly relabelled and adjoined to the old wild outer graph.
* `Schoenflies.SourceNonboundarySegmentCover.LocalOverlayRelabeling.isSourceExtension` — all
  local source-extension fields, leaving only the two global attachment properties explicit.
* `Schoenflies.SourceNonboundarySegmentCover.LocalOverlayRelabeling.
  isSourceExtension_of_source_connected_two_common` — the global properties follow from the
  carried source-connectedness invariant and two distinct common source/grid vertices.
-/

open Set
open scoped Graph

namespace Schoenflies

open Graph

namespace Graph

variable {β : Type*} {G H : Graph Plane β} {drawing drawing' : β → ℝ → Plane}

/-- Replacing a drawing by a pointwise equal parametrization on the graph's own edges preserves
all drawing axioms. -/
theorem isDrawing_congr_of_eqOn (h : G.IsDrawing drawing)
    (heq : ∀ {e : β}, e ∈ E(G) → drawing' e = drawing e) :
    G.IsDrawing drawing' where
  edge_param := by
    intro e he
    rw [heq he]
    exact h.edge_param he
  vertex_mem_edgeArc := by
    intro e x y v hxy hv hve
    rw [edgeArc, heq hxy.edge_mem] at hve
    exact h.vertex_mem_edgeArc hxy hv hve
  edge_inter := by
    intro e f he hf hef p hpe hpf
    rw [edgeArc, heq he] at hpe
    rw [edgeArc, heq hf] at hpf
    exact h.edge_inter he hf hef hpe hpf

/-- Compatible plane drawings whose carriers meet only at common vertices form a plane drawing
on their union. -/
theorem isDrawing_union_of_common_vertices (hG : G.IsDrawing drawing)
    (hH : H.IsDrawing drawing) (hcompat : G.Compatible H)
    (hcross : ∀ {p : Plane}, p ∈ pointSet G drawing → p ∈ pointSet H drawing →
      p ∈ V(G) ∧ p ∈ V(H)) :
    (G.union H).IsDrawing drawing := by
  have hGle : G ≤ G.union H := Graph.left_le_union _ _
  have hHle : H ≤ G.union H := hcompat.right_le_union
  have inc_of_mem (K : Graph Plane β) (hK : K.IsDrawing drawing)
      {e : β} (he : e ∈ E(K)) {p : Plane} (hpV : p ∈ V(K))
      (hpe : p ∈ edgeArc drawing e) : K.Inc e p := by
    obtain ⟨x, y, hxy⟩ := K.exists_isLink_of_mem_edgeSet he
    rcases hK.vertex_mem_edgeArc hxy hpV hpe with rfl | rfl
    · exact hxy.inc_left
    · exact hxy.inc_right
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases he with he | he
    · obtain ⟨hc, hi, hlink⟩ := hG.edge_param he
      exact ⟨hc, hi, hGle.isLink_mono hlink⟩
    · obtain ⟨hc, hi, hlink⟩ := hH.edge_param he
      exact ⟨hc, hi, hHle.isLink_mono hlink⟩
  · intro e x y v hxy hv hve
    rcases (hcompat.union_isLink).1 hxy with hxyG | hxyH
    · have hvG : v ∈ V(G) := by
        rcases hv with hvG | hvH
        · exact hvG
        · exact (hcross (Graph.edgeArc_subset_pointSet hxyG.edge_mem hve)
            (Graph.vertexSet_subset_pointSet hvH)).1
      exact hG.vertex_mem_edgeArc hxyG hvG hve
    · have hvH : v ∈ V(H) := by
        rcases hv with hvG | hvH
        · exact (hcross (Graph.vertexSet_subset_pointSet hvG)
            (Graph.edgeArc_subset_pointSet hxyH.edge_mem hve)).2
        · exact hvH
      exact hH.vertex_mem_edgeArc hxyH hvH hve
  · intro e f he hf hef p hpe hpf
    rcases he with heG | heH <;> rcases hf with hfG | hfH
    · obtain ⟨hpV, hpeInc, hpfInc⟩ := hG.edge_inter heG hfG hef hpe hpf
      exact ⟨Or.inl hpV, hpeInc.mono hGle, hpfInc.mono hGle⟩
    · obtain ⟨hpVG, hpVH⟩ := hcross
        (Graph.edgeArc_subset_pointSet heG hpe)
        (Graph.edgeArc_subset_pointSet hfH hpf)
      exact ⟨Or.inl hpVG, (inc_of_mem G hG heG hpVG hpe).mono hGle,
        (inc_of_mem H hH hfH hpVH hpf).mono hHle⟩
    · obtain ⟨hpVG, hpVH⟩ := hcross
        (Graph.edgeArc_subset_pointSet hfG hpf)
        (Graph.edgeArc_subset_pointSet heH hpe)
      exact ⟨Or.inl hpVG, (inc_of_mem H hH heH hpVH hpe).mono hHle,
        (inc_of_mem G hG hfG hpVG hpf).mono hGle⟩
    · obtain ⟨hpV, hpeInc, hpfInc⟩ := hH.edge_inter heH hfH hef hpe hpf
      exact ⟨Or.inr hpV, hpeInc.mono hHle, hpfInc.mono hHle⟩

/-- A nonempty walk in a plane drawing has connected geometric carrier. -/
theorem IsDrawing.isConnected_edgesCover_of_isWalk (h : G.IsDrawing drawing)
    {u v : Plane} {W : List β} (hW : G.IsWalk u W v) (hne : W ≠ []) :
    IsConnected (Graph.edgesCover drawing W) := by
  induction hW with
  | nil => exact (hne rfl).elim
  | @cons u w v e W hlink htail ih =>
      rw [Graph.edgesCover_cons]
      by_cases hWnil : W = []
      · subst W
        rw [Graph.edgesCover_nil, Set.union_empty]
        exact (h.edge_isArcBetween hlink).isArc.isConnected
      · apply IsConnected.union
          (Hs := (h.edge_isArcBetween hlink).isArc.isConnected)
          (Ht := ih hWnil)
        refine ⟨w, h.inc_mem_edgeArc hlink.inc_right, ?_⟩
        rw [← h.pointSet_pathGraphOf htail hWnil]
        apply Graph.vertexSet_subset_pointSet
        rw [Graph.pathGraphOf_vertexSet]
        exact Graph.mem_walkVertices_self

/-- The point set of a connected plane drawing is connected. -/
theorem IsDrawing.isConnected_pointSet (h : G.IsDrawing drawing) (hG : G.Connected) :
    IsConnected (Graph.pointSet G drawing) := by
  obtain ⟨c, hc⟩ := hG.nonempty
  have bridge : ∀ {u : Plane}, u ∈ V(G) →
      ∃ A : Set Plane, A ⊆ Graph.pointSet G drawing ∧ c ∈ A ∧ u ∈ A ∧ IsConnected A := by
    intro u hu
    by_cases hcu : c = u
    · subst u
      exact ⟨{c}, fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        exact hz ▸ Graph.vertexSet_subset_pointSet hc,
        Set.mem_singleton c, Set.mem_singleton c, isConnected_singleton⟩
    · obtain ⟨W, hW⟩ := hG.reaches hc hu
      have hWne : W ≠ [] := by
        intro hnil
        subst W
        exact hcu hW.eq_of_nil
      have hsubset : Graph.edgesCover drawing W ⊆ Graph.pointSet G drawing := by
        intro z hz
        obtain ⟨e, heW, hze⟩ := Graph.mem_edgesCover_iff.1 hz
        exact Graph.edgeArc_subset_pointSet (hW.edge_mem heW) hze
      have hcW : c ∈ Graph.edgesCover drawing W := by
        rw [← h.pointSet_pathGraphOf hW hWne]
        apply Graph.vertexSet_subset_pointSet
        rw [Graph.pathGraphOf_vertexSet]
        exact Graph.mem_walkVertices_self
      have huW : u ∈ Graph.edgesCover drawing W := by
        rw [← h.pointSet_pathGraphOf hW hWne]
        apply Graph.vertexSet_subset_pointSet
        rw [Graph.pathGraphOf_vertexSet]
        exact hW.target_mem_walkVertices
      exact ⟨Graph.edgesCover drawing W, hsubset, hcW, huW,
        Schoenflies.Graph.IsDrawing.isConnected_edgesCover_of_isWalk h hW hWne⟩
  refine ⟨⟨c, Graph.vertexSet_subset_pointSet hc⟩, isPreconnected_of_forall c ?_⟩
  intro y hy
  rcases hy with hyV | hyE
  · obtain ⟨A, hA, hcA, hyA, hAconn⟩ := bridge hyV
    exact ⟨A, hA, hcA, hyA, hAconn.isPreconnected⟩
  · obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.1 hyE
    obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet he
    obtain ⟨A, hA, hcA, huA, hAconn⟩ := bridge huv.left_mem
    let B := Graph.edgeArc drawing e
    have hBconn : IsConnected B := (h.edge_isArcBetween huv).isArc.isConnected
    have huB : u ∈ B := h.inc_mem_edgeArc huv.inc_left
    refine ⟨A ∪ B, Set.union_subset hA (Graph.edgeArc_subset_pointSet he),
      Or.inl hcA, Or.inr hye, ?_⟩
    exact (IsConnected.union ⟨u, huA, huB⟩ hAconn hBconn).isPreconnected

end Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}
  {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}

/-- A finite exact straight-segment presentation of the compact nonboundary source skeleton. -/
structure SourceNonboundarySegmentCover
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) where
  /-- The straight segments covering the nonboundary carrier. -/
  pieces : List Piece
  /-- No listed segment is degenerate. -/
  nondeg : ∀ Q ∈ pieces, Q.Nondeg
  /-- The listed segments occupy exactly the compact nonboundary source graph. -/
  cover_eq : cover pieces =
    Graph.pointSet P.sourceNonboundaryGraph P.src.drawing
  /-- Every listed segment came from one old nonouter source edge. -/
  source : ∀ Q ∈ pieces, ∃ e ∈ E(P.str.skel),
    e ∉ E(P.str.outerGraph) ∧ Q.seg ⊆ edgeArc P.src.drawing e

namespace GeneratedPair

/-- Every generated pair has a finite exact segment presentation of its compact polygonal
nonboundary source skeleton. -/
theorem exists_sourceNonboundarySegmentCover
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    Nonempty (SourceNonboundarySegmentCover P) := by
  let G := P.sourceNonboundaryGraph
  have hdraw : G.IsDrawing P.src.drawing :=
    P.src.isDrawing.mono P.sourceNonboundaryGraph_le
  have hincident : ∀ z ∈ V(G), ∃ e, G.Inc e z := by
    intro z hz
    change z ∈ P.sourceNonboundaryVertices at hz
    obtain ⟨e, he, heOuter, hinc⟩ := hz
    obtain ⟨w, hlink⟩ := hinc
    have hz' : z ∈ P.sourceNonboundaryVertices :=
      ⟨e, he, heOuter, ⟨w, hlink⟩⟩
    have hw : w ∈ P.sourceNonboundaryVertices :=
      ⟨e, he, heOuter, hlink.inc_right⟩
    have hdeleted :
        (P.src.graph.deleteEdges E(P.str.outerGraph)).IsLink e z w := by
      rw [← Graph.restrict_edgeSet_sdiff_eq_deleteEdges, Graph.restrict_isLink]
      exact ⟨⟨he, heOuter⟩, hlink⟩
    exact ⟨e, w, hdeleted, hz', hw⟩
  have hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc P.src.drawing e) := by
    intro e he
    obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
    have heDeleted : e ∈ E(P.src.graph.deleteEdges E(P.str.outerGraph)) :=
      hxy.1.edge_mem
    obtain ⟨heSrc, heOuter⟩ := Graph.mem_edgeSet_deleteEdges_iff.1 heDeleted
    have heAbstract : e ∈ E(P.str.skel) := by
      rwa [P.src.edgeSet_graph] at heSrc
    exact P.src_isWeaklyAdmissible.isPolygonal heAbstract heOuter
  obtain ⟨pieces, hnd, hcover, hsource⟩ :=
    hdraw.exists_segmentCover hpoly hincident
  refine ⟨⟨pieces, hnd, hcover, ?_⟩⟩
  intro Q hQ
  obtain ⟨e, heG, hsub⟩ := hsource Q hQ
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet heG
  have heDeleted : e ∈ E(P.src.graph.deleteEdges E(P.str.outerGraph)) :=
    hxy.1.edge_mem
  obtain ⟨heSrc, heOuter⟩ := Graph.mem_edgeSet_deleteEdges_iff.1 heDeleted
  exact ⟨e, by rwa [P.src.edgeSet_graph] at heSrc, heOuter, hsub⟩

end GeneratedPair

namespace SourceNonboundarySegmentCover

variable (Q : SourceNonboundarySegmentCover P)

/-- The two finite segment families in the source local-grid overlay. -/
noncomputable def localPieces (p : Plane) (s epsilon : ℝ) : List Piece :=
  Q.pieces ++ localGridEdges p s (localGridCount s epsilon)

/-- The compact old source core overlaid with a fine local grid.  Old nonboundary vertices and
any prescribed attachment points are retained as overlay vertices. -/
noncomputable def localOverlay (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) : Graph Plane Piece :=
  attachGraph (Q.localPieces p s epsilon)
    (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)

instance localOverlay_finite (p : Plane) (s epsilon : ℝ) (extra : List Plane) :
    (Q.localOverlay p s epsilon extra).Finite := attachGraph_finite _ _

/-- Every source segment of the local overlay is nondegenerate. -/
theorem localPieces_nondeg {p : Plane} {s epsilon : ℝ} (hs : 0 < s) :
    ∀ R ∈ Q.localPieces p s epsilon, R.Nondeg := by
  intro R hR
  rcases List.mem_append.1 hR with hR | hR
  · exact Q.nondeg R hR
  · exact localGridEdges_nondeg hs (one_le_localGridCount s epsilon) R hR

/-- The source local overlay is a finite straight-line plane graph. -/
theorem localOverlay_isDrawing {p : Plane} {s epsilon : ℝ} (hs : 0 < s)
    (extra : List Plane) :
    Graph.IsDrawing (Q.localOverlay p s epsilon extra) segmentDrawing :=
  attachGraph_isDrawing (Q.localPieces_nondeg hs) _

/-- The local overlay occupies exactly the old compact source core together with the grid. -/
theorem localOverlay_pointSet (p : Plane) (s epsilon : ℝ) (extra : List Plane) :
    Graph.pointSet (Q.localOverlay p s epsilon extra) segmentDrawing =
      Graph.pointSet P.sourceNonboundaryGraph P.src.drawing ∪
        cover (localGridEdges p s (localGridCount s epsilon)) := by
  rw [localOverlay, attachGraph_pointSet, localPieces, cover_append, Q.cover_eq]

/-- The whole old compact source core is retained by the local overlay. -/
theorem sourceCore_subset_localOverlay (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) :
    Graph.pointSet P.sourceNonboundaryGraph P.src.drawing ⊆
      Graph.pointSet (Q.localOverlay p s epsilon extra) segmentDrawing := by
  rw [Q.localOverlay_pointSet]
  exact subset_union_left

/-- The whole fine local grid is retained by the source overlay. -/
theorem localGrid_subset_localOverlay (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) :
    cover (localGridEdges p s (localGridCount s epsilon)) ⊆
      Graph.pointSet (Q.localOverlay p s epsilon extra) segmentDrawing := by
  rw [Q.localOverlay_pointSet]
  exact subset_union_right

/-- Every vertex of the raw local grid is retained as a vertex of the combined straight-line
overlay. -/
theorem localGridVertices_subset_localOverlay {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (extra : List Plane) :
    V(localGrid p s (localGridCount s epsilon)) ⊆
      V(Q.localOverlay p s epsilon extra) := by
  intro x hx
  rw [localGrid_eq, pieceListGraph_vertexSet] at hx
  simp only [endSet, Set.mem_ofPred_eq] at hx
  obtain ⟨R, hR, hxR⟩ := hx
  change x ∈ V(overlayGraph (Q.localPieces p s epsilon)
    (attachPoints (Q.localPieces p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.localPieces_nondeg hs)
  · exact attachPoints_endsAreCut _ _ R
      (List.mem_append_right Q.pieces hR) x hxR
  · exact mem_cover_iff.2 ⟨R, List.mem_append_right Q.pieces hR, by
      rcases hxR with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _⟩

/-- Away from overlay vertices, an overlay edge meeting a raw local-grid edge is one of its
subdivision pieces. -/
theorem localOverlay_grid_edge_subset {p : Plane} {s epsilon : ℝ} (hs : 0 < s)
    (extra : List Plane) :
    ∀ {A : Piece}, A ∈ E(localGrid p s (localGridCount s epsilon)) → ∀ {R : Piece},
      R ∈ E(Q.localOverlay p s epsilon extra) →
      (edgeArc segmentDrawing R ∩
        (edgeArc segmentDrawing A \ V(Q.localOverlay p s epsilon extra))).Nonempty →
      edgeArc segmentDrawing R ⊆ edgeArc segmentDrawing A := by
  intro A hA R hR hmeet
  have hAList : A ∈ localGridEdges p s (localGridCount s epsilon) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA
  obtain ⟨z, hzR, hzA, hznotOverlay⟩ := hmeet
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (Q.localPieces p s epsilon)
        (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList))
      (P₀ := A) (List.mem_append_right Q.pieces hAList)
      (by rwa [edgeArc_segmentDrawing] at hzA)
  have hzR'Arc : z ∈ edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.localOverlay_isDrawing hs extra).unique_edge_at
      hR hR' hznotOverlay hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing, edgeArc_segmentDrawing]
  exact hR'A

/-- The straight-line local overlay contains a plane subdivision of the raw local grid. -/
theorem localGrid_isPlaneSubdivisionExtension {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (extra : List Plane) :
    IsPlaneSubdivisionExtension
      (localGrid p s (localGridCount s epsilon)) segmentDrawing
      (Q.localOverlay p s epsilon extra) segmentDrawing where
  finite := inferInstance
  oldIsDrawing := localGrid_isDrawing hs (one_le_localGridCount s epsilon)
  isDrawing := Q.localOverlay_isDrawing hs extra
  vertexSet_subset := Q.localGridVertices_subset_localOverlay hs extra
  pointSet_subset := by
    rw [localGrid_eq, pieceListGraph_pointSet]
    exact Q.localGrid_subset_localOverlay p s epsilon extra
  edge_subset := by
    intro A hA R hR hmeet
    exact Q.localOverlay_grid_edge_subset hs extra hA hR hmeet

/-- Every edge of the source local overlay is a subsegment either of the old nonboundary
source cover or of the local grid. -/
theorem localOverlay_edge_source {p : Plane} {s epsilon : ℝ} {extra : List Plane}
    {R : Piece} (hR : R ∈ E(Q.localOverlay p s epsilon extra)) :
    (∃ A ∈ Q.pieces, R.seg ⊆ A.seg) ∨
      ∃ A ∈ localGridEdges p s (localGridCount s epsilon), R.seg ⊆ A.seg := by
  change R ∈ overlayPieces (Q.localPieces p s epsilon)
    (attachPoints (Q.localPieces p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)) at hR
  obtain ⟨R₀, hR₀, rfl⟩ := mem_overlayPieces.1 hR
  obtain ⟨A, hA, hsub, -⟩ := subdivide_subset _ _ R₀ hR₀
  rw [orientPiece_seg]
  rcases List.mem_append.1 hA with hA | hA
  · exact Or.inl ⟨A, hA, hsub⟩
  · exact Or.inr ⟨A, hA, hsub⟩

/-- Every vertex of the compact old source core is explicitly retained as a vertex of the
local overlay. -/
theorem sourceCoreVertices_subset_localOverlay {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (extra : List Plane) :
    V(P.sourceNonboundaryGraph) ⊆ V(Q.localOverlay p s epsilon extra) := by
  intro x hx
  change x ∈ V(overlayGraph (Q.localPieces p s epsilon)
    (attachPoints (Q.localPieces p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.localPieces_nondeg hs)
  · apply mem_attachPoints_of_mem
    exact List.mem_append_right extra (by
      rw [Finset.mem_toList, mem_vertexFinset]
      exact hx)
  · rw [localPieces, cover_append, Q.cover_eq]
    exact Or.inl (Graph.vertexSet_subset_pointSet hx)

/-- Every old nonouter edge belongs to the compact source-core graph. -/
theorem sourceNonboundaryGraph_edge_mem {e : γ} (he : e ∈ E(P.str.skel))
    (heOuter : e ∉ E(P.str.outerGraph)) :
    e ∈ E(P.sourceNonboundaryGraph) := by
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have habSrc := hab.map P.src.pos
  have heSrc : e ∈ E(P.src.graph) := by rwa [P.src.edgeSet_graph]
  have hdeleted : (P.src.graph.deleteEdges E(P.str.outerGraph)).IsLink
      e (P.src.pos a) (P.src.pos b) := by
    rw [← Graph.restrict_edgeSet_sdiff_eq_deleteEdges, Graph.restrict_isLink]
    exact ⟨⟨heSrc, heOuter⟩, habSrc⟩
  have ha : P.src.pos a ∈ P.sourceNonboundaryVertices :=
    ⟨e, heSrc, heOuter, habSrc.inc_left⟩
  have hb : P.src.pos b ∈ P.sourceNonboundaryVertices :=
    ⟨e, heSrc, heOuter, habSrc.inc_right⟩
  exact ⟨P.src.pos a, P.src.pos b, hdeleted, ha, hb⟩

/-- Away from overlay vertices, an inner-overlay edge meeting an old open nonboundary edge is
one of that edge's subdivision pieces. -/
theorem localOverlay_edge_subset {p : Plane} {s epsilon : ℝ} (hs : 0 < s)
    (extra : List Plane) :
    ∀ {e : γ}, e ∈ E(P.str.skel) → e ∉ E(P.str.outerGraph) → ∀ {R : Piece},
      R ∈ E(Q.localOverlay p s epsilon extra) →
      (edgeArc segmentDrawing R ∩
        (P.src.cell e \ V(Q.localOverlay p s epsilon extra))).Nonempty →
      edgeArc segmentDrawing R ⊆ edgeArc P.src.drawing e := by
  intro e he heOuter R hR hmeet
  obtain ⟨z, hzR, hzCell, hznotOverlay⟩ := hmeet
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have hzOldArc : z ∈ edgeArc P.src.drawing e := by
    rw [P.src.cell_edge hab] at hzCell
    exact hzCell.1
  have hzCore : z ∈ Graph.pointSet P.sourceNonboundaryGraph P.src.drawing :=
    Graph.edgeArc_subset_pointSet
      (sourceNonboundaryGraph_edge_mem (P := P) he heOuter) hzOldArc
  have hzCover : z ∈ cover Q.pieces := by rwa [Q.cover_eq]
  obtain ⟨A, hA, hzA⟩ := ClosedPolygon.exists_of_mem_cover hzCover
  obtain ⟨g, hg, hgOuter, hAg⟩ := Q.source A hA
  have hzg : z ∈ edgeArc P.src.drawing g := hAg hzA
  have hznotOldVertex : z ∉ V(P.src.graph) := by
    intro hzV
    rcases P.src.isDrawing.vertex_mem_edgeArc (hab.map P.src.pos) hzV hzOldArc with
      hza | hzb
    · rw [P.src.cell_edge hab] at hzCell
      exact hzCell.2 (by simp [hza])
    · rw [P.src.cell_edge hab] at hzCell
      exact hzCell.2 (by simp [hzb])
  have heg : e = g := P.src.isDrawing.unique_edge_at
    (by change e ∈ E(P.str.skel); exact he)
    (by change g ∈ E(P.str.skel); exact hg)
    hznotOldVertex hzOldArc hzg
  have hAold : A.seg ⊆ edgeArc P.src.drawing e := by rwa [heg]
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (Q.localPieces p s epsilon)
        (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList))
      (P₀ := A) (List.mem_append_left _ hA) hzA
  have hzR'Arc : z ∈ edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.localOverlay_isDrawing hs extra).unique_edge_at
      hR hR' hznotOverlay hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing]
  exact hR'A.trans hAold

/-! ### Containment in the source domain -/

/-- Every grid point with indices in range lies in the local grid's closed square. -/
theorem localGridPoint_mem_closedSquare {p : Plane} {s : ℝ} {k i j : ℕ}
    (hs : 0 < s) (hk : 1 ≤ k) (hi : i ≤ k) (hj : j ≤ k) :
    gridPt (localGridX p s k) (localGridY p s k) i j ∈ Plane.closedSquare p s := by
  have hxmono := (localGridX_strictMono (p := p) hs hk).monotone
  have hymono := (localGridY_strictMono (p := p) hs hk).monotone
  rw [Plane.closedSquare_eq_inter]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, gridPt]
  constructor
  · constructor
    · calc
        p 0 - s = localGridX p s k 0 := (localGridX_zero p s k).symm
        _ ≤ localGridX p s k i := hxmono (Nat.zero_le i)
    · calc
        localGridX p s k i ≤ localGridX p s k k := hxmono hi
        _ = p 0 + s := localGridX_last hk
  · constructor
    · calc
        p 1 - s = localGridY p s k 0 := (localGridY_zero p s k).symm
        _ ≤ localGridY p s k j := hymono (Nat.zero_le j)
    · calc
        localGridY p s k j ≤ localGridY p s k k := hymono hj
        _ = p 1 + s := localGridY_last hk

/-- The complete local grid carrier lies in its closed square window. -/
theorem cover_localGridEdges_subset_closedSquare {p : Plane} {s : ℝ} {k : ℕ}
    (hs : 0 < s) (hk : 1 ≤ k) :
    cover (localGridEdges p s k) ⊆ Plane.closedSquare p s := by
  intro z hz
  obtain ⟨R, hR, hzR⟩ := mem_cover_iff.1 hz
  rcases (mem_gridEdges_iff hk hk).1 hR with
      ⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, rfl⟩
  · exact (Plane.convex_closedSquare p s).segment_subset
      (localGridPoint_mem_closedSquare hs hk (by omega) hj)
      (localGridPoint_mem_closedSquare hs hk (by omega) hj) hzR
  · exact (Plane.convex_closedSquare p s).segment_subset
      (localGridPoint_mem_closedSquare hs hk hi (by omega))
      (localGridPoint_mem_closedSquare hs hk hi (by omega)) hzR

/-- If the closed local window lies in the source domain, then so does the complete finite
inner overlay of the old nonboundary source skeleton with that grid. -/
theorem localOverlay_pointSet_subset {p : Plane} {s epsilon : ℝ} (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom) (extra : List Plane) :
    Graph.pointSet (Q.localOverlay p s epsilon extra) segmentDrawing ⊆ srcDom := by
  rw [Q.localOverlay_pointSet]
  apply Set.union_subset
  · exact (Graph.pointSet_mono P.sourceNonboundaryGraph_le).trans
      P.src_isWeaklyAdmissible.skeletonSet_subset
  · exact (cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon)).trans hwindow

/-- Every edge of the finite inner overlay is polygonal and its nonvertex points lie in the
open source domain.  For an old nonouter edge, weak admissibility puts its open 1-cell in the
interior; if the old arc touches the wild boundary, the touching point is an old core vertex
and hence an overlay vertex.  Grid-sourced edges lie in the chosen interior window. -/
theorem localOverlay_edge_dichotomy {p : Plane} {s epsilon : ℝ} (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) (extra : List Plane) :
    ∀ {R : Piece}, R ∈ E(Q.localOverlay p s epsilon extra) →
      IsPolygonal (edgeArc segmentDrawing R) ∧
        edgeArc segmentDrawing R \ V(Q.localOverlay p s epsilon extra) ⊆
          srcDom \ srcOuter := by
  intro R hR
  refine ⟨by rw [edgeArc_segmentDrawing]; exact isPolygonal_segment _ _, ?_⟩
  intro x hx
  have hxSeg : x ∈ R.seg := by
    rw [← edgeArc_segmentDrawing]
    exact hx.1
  rcases Q.localOverlay_edge_source hR with hOld | hGrid
  · obtain ⟨A, hA, hRA⟩ := hOld
    obtain ⟨e, he, heNotOuter, hAe⟩ := Q.source A hA
    obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
    have hxe : x ∈ edgeArc P.src.drawing e := hAe (hRA hxSeg)
    have hxCell : x ∈ P.src.cell e := by
      rw [P.src.cell_edge hab]
      refine ⟨hxe, ?_⟩
      intro hxEnds
      have habSrc := hab.map P.src.pos
      rcases hxEnds with hxa | hxb
      · apply hx.2
        rw [hxa]
        apply Q.sourceCoreVertices_subset_localOverlay hs extra
        exact ⟨e, by rwa [P.src.edgeSet_graph], heNotOuter, habSrc.inc_left⟩
      · apply hx.2
        rw [hxb]
        apply Q.sourceCoreVertices_subset_localOverlay hs extra
        exact ⟨e, by rwa [P.src.edgeSet_graph], heNotOuter, habSrc.inc_right⟩
    exact P.src_isWeaklyAdmissible.cell_subset he heNotOuter hxCell
  · obtain ⟨A, hA, hRA⟩ := hGrid
    exact hwindow (cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon) (mem_cover_iff.2 ⟨A, hA, hRA hxSeg⟩))

/-- The compact nonboundary source carrier meets the wild outer curve only at vertices common
to the nonboundary and outer source graphs. -/
theorem sourceCore_inter_outer_vertices {x : Plane}
    (hxCore : x ∈ Graph.pointSet P.sourceNonboundaryGraph P.src.drawing)
    (hxOuter : x ∈ srcOuter) :
    x ∈ V(P.sourceNonboundaryGraph) ∧
      x ∈ V(P.str.outerGraph.map P.src.pos) := by
  have hxOuterSet : x ∈ P.src.outerSet := by
    rw [P.src_isWeaklyAdmissible.outerSet_eq]
    exact hxOuter
  change x ∈ Graph.pointSet (P.str.outerGraph.map P.src.pos) P.src.drawing at hxOuterSet
  have hxCoreV : x ∈ V(P.sourceNonboundaryGraph) := by
    rcases hxCore with hxV | hxE
    · exact hxV
    · obtain ⟨e, heCore, hxe⟩ := Set.mem_iUnion₂.1 hxE
      obtain ⟨a, b, habCore⟩ :=
        P.sourceNonboundaryGraph.exists_isLink_of_mem_edgeSet heCore
      have habSrc := P.sourceNonboundaryGraph_le.isLink_mono habCore
      have heDeleted : e ∈ E(P.src.graph.deleteEdges E(P.str.outerGraph)) :=
        habCore.1.edge_mem
      obtain ⟨heSrc, heNotOuter⟩ := Graph.mem_edgeSet_deleteEdges_iff.1 heDeleted
      have hxSrcV : x ∈ V(P.src.graph) := by
        rcases hxOuterSet with hxOuterV | hxOuterE
        · exact (P.str.outerGraph_le.map P.src.pos).vertexSet_mono hxOuterV
        · obtain ⟨f, hfOuterGraph, hxf⟩ := Set.mem_iUnion₂.1 hxOuterE
          have hfOuter : f ∈ E(P.str.outerGraph) := by
            rwa [Graph.edgeSet_map] at hfOuterGraph
          have hfSrc : f ∈ E(P.src.graph) := by
            rw [P.src.edgeSet_graph]
            exact P.str.outerGraph_le.edgeSet_mono hfOuter
          have hef : e ≠ f := fun hef => heNotOuter (hef ▸ hfOuter)
          exact (P.src.isDrawing.edge_inter heSrc hfSrc hef hxe hxf).1
      rcases P.src.isDrawing.vertex_mem_edgeArc habSrc hxSrcV hxe with hxa | hxb
      · exact hxa.symm ▸ habCore.left_mem
      · exact hxb.symm ▸ habCore.right_mem
  refine ⟨hxCoreV, ?_⟩
  rcases hxOuterSet with hxOuterV | hxOuterE
  · exact hxOuterV
  · obtain ⟨f, hfOuter, hxf⟩ := Set.mem_iUnion₂.1 hxOuterE
    obtain ⟨a, b, habOuter⟩ :=
      (P.str.outerGraph.map P.src.pos).exists_isLink_of_mem_edgeSet hfOuter
    have habSrc := (P.str.outerGraph_le.map P.src.pos).isLink_mono habOuter
    have hxSrcV := P.sourceNonboundaryGraph_le.vertexSet_mono hxCoreV
    rcases P.src.isDrawing.vertex_mem_edgeArc habSrc hxSrcV hxf with hxa | hxb
    · exact hxa.symm ▸ habOuter.left_mem
    · exact hxb.symm ▸ habOuter.right_mem

/-! ### Relabelling and adjoining the wild outer graph -/

/-- Fresh abstract edge names for the finite straight-line inner overlay. -/
structure LocalOverlayRelabeling (p : Plane) (s epsilon : ℝ) (extra : List Plane) where
  name : Piece → γ
  name_inj : InjOn name E(Q.localOverlay p s epsilon extra)
  name_fresh : ∀ R ∈ E(Q.localOverlay p s epsilon extra), name R ∉ P.str.cells

/-- An infinite cell-name type supplies a relabelling of the inner overlay disjoint from every
name already used by the current generated structure. -/
theorem exists_localOverlayRelabeling [Infinite γ]
    (p : Plane) (s epsilon : ℝ) (extra : List Plane) :
    Nonempty (Q.LocalOverlayRelabeling p s epsilon extra) := by
  obtain ⟨name, hname, hfresh⟩ := exists_finiteGraph_edgeRelabeling_avoiding γ
    (Q.localOverlay p s epsilon extra) P.str.cells P.str.finite_cells
  exact ⟨⟨name, hname, hfresh⟩⟩

namespace LocalOverlayRelabeling

variable {Q : SourceNonboundarySegmentCover P} {p : Plane} {s epsilon : ℝ}
  {extra : List Plane} (w : Q.LocalOverlayRelabeling p s epsilon extra)

/-- The old outer graph realized on the wild source curve. -/
abbrev outerGraph (_w : Q.LocalOverlayRelabeling p s epsilon extra) : Graph Plane γ :=
  P.str.outerGraph.map P.src.pos

/-- The finite inner overlay after allocation of fresh abstract edge names. -/
noncomputable abbrev innerGraph : Graph Plane γ :=
  (Q.localOverlay p s epsilon extra).relabelEdges w.name w.name_inj

/-- The mixed source extension graph. -/
noncomputable def graph : Graph Plane γ := w.outerGraph.union w.innerGraph

/-- The mixed drawing uses the original parametrizations on the wild outer edges and straight
segments on every freshly named inner edge. -/
noncomputable def drawing : γ → ℝ → Plane := by
  classical
  exact fun e =>
    if e ∈ E(P.str.outerGraph) then P.src.drawing e
    else (Q.localOverlay p s epsilon extra).relabelDrawing w.name segmentDrawing e

/-- The two edge families are disjoint and therefore compatible. -/
theorem compatible : w.outerGraph.Compatible w.innerGraph := by
  apply Graph.Compatible.of_disjoint_edgeSet
  rw [Set.disjoint_left, Graph.edgeSet_map, Graph.edgeSet_relabelEdges]
  intro e heOuter heInner
  obtain ⟨R, hR, hname⟩ := heInner
  rw [← hname] at heOuter
  exact w.name_fresh R hR
    (P.str.mem_cells_of_mem_edgeSet (P.str.outerGraph_le.edgeSet_mono heOuter))

/-- On an old outer edge the mixed drawing is the old source drawing. -/
theorem drawing_of_outer {e : γ} (he : e ∈ E(P.str.outerGraph)) :
    w.drawing e = P.src.drawing e := by simp [drawing, he]

/-- On an inner edge the mixed drawing is the relabelled straight-line drawing. -/
theorem drawing_of_inner {e : γ} (he : e ∈ E(w.innerGraph)) :
    w.drawing e =
      (Q.localOverlay p s epsilon extra).relabelDrawing w.name segmentDrawing e := by
  rw [drawing, ite_eq_right]
  obtain ⟨R, hR, rfl⟩ := he
  exact fun heOuter => w.name_fresh R hR
    (P.str.mem_cells_of_mem_edgeSet (P.str.outerGraph_le.edgeSet_mono heOuter))

/-- The mixed drawing restricts to a plane drawing on the old wild outer graph. -/
theorem outer_isDrawing : w.outerGraph.IsDrawing w.drawing := by
  apply Schoenflies.Graph.isDrawing_congr_of_eqOn
    (P.src.isDrawing.mono (P.str.outerGraph_le.map P.src.pos))
  intro e he
  apply w.drawing_of_outer
  rwa [Graph.edgeSet_map] at he

/-- The mixed drawing restricts to a plane drawing on the straight-line inner overlay. -/
theorem inner_isDrawing (hs : 0 < s) : w.innerGraph.IsDrawing w.drawing := by
  apply Schoenflies.Graph.isDrawing_congr_of_eqOn
    ((Q.localOverlay_isDrawing hs extra).relabelEdges w.name_inj)
  intro e he
  exact w.drawing_of_inner he

/-- The old outer part of the mixed graph occupies exactly the wild source curve. -/
theorem outer_pointSet : Graph.pointSet w.outerGraph w.drawing = srcOuter := by
  calc
    Graph.pointSet w.outerGraph w.drawing =
        Graph.pointSet w.outerGraph P.src.drawing := by
      apply Graph.pointSet_congr
      intro e he
      simpa only [Graph.edgeArc] using congrArg (fun f : ℝ → Plane => f '' unitInterval)
        (w.drawing_of_outer (by rwa [Graph.edgeSet_map] at he))
    _ = P.src.outerSet := rfl
    _ = srcOuter := P.src_isWeaklyAdmissible.outerSet_eq

/-- The inner part occupies exactly the finite straight-line local overlay. -/
theorem inner_pointSet :
    Graph.pointSet w.innerGraph w.drawing =
      Graph.pointSet (Q.localOverlay p s epsilon extra) segmentDrawing := by
  calc
    Graph.pointSet w.innerGraph w.drawing =
        Graph.pointSet w.innerGraph
          ((Q.localOverlay p s epsilon extra).relabelDrawing w.name segmentDrawing) := by
      apply Graph.pointSet_congr
      intro e he
      simpa only [Graph.edgeArc] using congrArg (fun f : ℝ → Plane => f '' unitInterval)
        (w.drawing_of_inner he)
    _ = Graph.pointSet (Q.localOverlay p s epsilon extra) segmentDrawing :=
      Graph.pointSet_relabelEdges w.name_inj

/-- The mixed outer/inner source graph is a plane drawing whenever the local window lies in
the open source domain. -/
theorem graph_isDrawing (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    w.graph.IsDrawing w.drawing := by
  apply Schoenflies.Graph.isDrawing_union_of_common_vertices
    w.outer_isDrawing (w.inner_isDrawing hs) w.compatible
  intro x hxOuter hxInner
  rw [w.outer_pointSet] at hxOuter
  rw [w.inner_pointSet, Q.localOverlay_pointSet] at hxInner
  rcases hxInner with hxCore | hxGrid
  · obtain ⟨hxCoreV, hxOuterV⟩ :=
      sourceCore_inter_outer_vertices (P := P) hxCore hxOuter
    refine ⟨hxOuterV, ?_⟩
    rw [Graph.vertexSet_relabelEdges]
    exact Q.sourceCoreVertices_subset_localOverlay hs extra hxCoreV
  · have hxWindow := cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon) hxGrid
    exact ((hwindow hxWindow).2 hxOuter).elim

/-- The mixed source graph is finite. -/
theorem graph_finite : w.graph.Finite where
  finite_vertexSet := by
    rw [graph, Graph.vertexSet_union, outerGraph, Graph.vertexSet_map,
      Graph.vertexSet_relabelEdges]
    exact ((P.str.finite_vertexSet.subset P.str.outerGraph_le.vertexSet_mono).image
      P.src.pos).union (Graph.finite_vertexSet (Q.localOverlay p s epsilon extra))
  finite_edgeSet := by
    rw [graph, Graph.edgeSet_union, outerGraph, Graph.edgeSet_map,
      Graph.edgeSet_relabelEdges]
    exact (P.str.finite_edgeSet.subset P.str.outerGraph_le.edgeSet_mono).union
      ((Graph.finite_edgeSet (Q.localOverlay p s epsilon extra)).image w.name)

/-- The mixed source graph occupies the wild outer curve, the old compact nonboundary
carrier, and the complete local grid. -/
theorem graph_pointSet :
    Graph.pointSet w.graph w.drawing =
      srcOuter ∪ (Graph.pointSet P.sourceNonboundaryGraph P.src.drawing ∪
        cover (localGridEdges p s (localGridCount s epsilon))) := by
  rw [graph, Graph.pointSet_union, w.outer_pointSet, w.inner_pointSet,
    Q.localOverlay_pointSet]

/-- The complete old source skeleton is retained by the mixed graph. -/
theorem sourceSkeleton_subset_graph :
    P.src.skeletonSet ⊆ Graph.pointSet w.graph w.drawing := by
  rw [P.skeletonSet_eq_sourceNonboundaryGraph_union, w.graph_pointSet]
  intro x hx
  rcases hx with hxCore | hxOuter
  · exact Or.inr (Or.inl hxCore)
  · exact Or.inl hxOuter

/-- Every old source vertex is explicitly retained as a mixed-graph vertex. -/
theorem sourceVertices_subset_graph (hs : 0 < s) :
    V(P.src.graph) ⊆ V(w.graph) := by
  intro x hx
  obtain ⟨z, hz, hzx, -⟩ :=
    P.src_isWeaklyAdmissible.isTwoConnected.hasThreeVertices.exists_ne_ne x x
  obtain ⟨D, hD⟩ :=
    P.src_isWeaklyAdmissible.isTwoConnected.connected.exists_isPath hx hz
  obtain ⟨e, heD, hinc⟩ :=
    hD.isWalk.exists_inc_source (hD.ne_nil (Ne.symm hzx))
  have heSrc : e ∈ E(P.src.graph) := hD.edge_mem heD
  by_cases heOuter : e ∈ E(P.str.outerGraph)
  · rw [graph, Graph.vertexSet_union]
    exact Or.inl
      (((P.str.outerGraph_le.map P.src.pos).inc_congr
        (by rwa [Graph.edgeSet_map])).2 hinc).vertex_mem
  · have hxCore : x ∈ V(P.sourceNonboundaryGraph) := by
      change x ∈ P.sourceNonboundaryVertices
      exact ⟨e, heSrc, heOuter, hinc⟩
    rw [graph, Graph.vertexSet_union]
    exact Or.inr (by
      rw [Graph.vertexSet_relabelEdges]
      exact Q.sourceCoreVertices_subset_localOverlay hs extra hxCore)

/-- The mixed source graph stays in the closed source domain. -/
theorem graph_pointSet_subset (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    Graph.pointSet w.graph w.drawing ⊆ srcDom := by
  rw [graph, Graph.pointSet_union]
  apply Set.union_subset
  · rw [w.outer_pointSet, ← P.src_isWeaklyAdmissible.outerSet_eq]
    exact (Graph.pointSet_mono (P.str.outerGraph_le.map P.src.pos)).trans
      P.src_isWeaklyAdmissible.skeletonSet_subset
  · rw [w.inner_pointSet]
    exact Q.localOverlay_pointSet_subset hs (hwindow.trans sdiff_subset) extra

/-- Every mixed edge is either an old outer edge on the wild curve or a polygonal inner edge
whose nonvertex points lie in the open source domain. -/
theorem graph_edge_dichotomy (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    ∀ {e : γ}, e ∈ E(w.graph) → edgeArc w.drawing e ⊆ srcOuter ∨
      (IsPolygonal (edgeArc w.drawing e) ∧
        edgeArc w.drawing e \ V(w.graph) ⊆ srcDom \ srcOuter) := by
  intro e he
  rcases he with heOuter | heInner
  · exact Or.inl (by
      intro x hx
      rw [← w.outer_pointSet]
      exact Graph.edgeArc_subset_pointSet heOuter hx)
  · obtain ⟨R, hR, rfl⟩ := heInner
    have hname : w.name R ∈ E(w.innerGraph) := ⟨R, hR, rfl⟩
    have hdrawing := w.drawing_of_inner hname
    have harc : edgeArc w.drawing (w.name R) = edgeArc segmentDrawing R := by
      calc
        edgeArc w.drawing (w.name R) =
            edgeArc ((Q.localOverlay p s epsilon extra).relabelDrawing
              w.name segmentDrawing) (w.name R) := by
          simpa only [Graph.edgeArc] using congrArg
            (fun f : ℝ → Plane => f '' unitInterval) hdrawing
        _ = edgeArc segmentDrawing R :=
          Graph.edgeArc_relabelDrawing w.name_inj hR
    rw [harc]
    obtain ⟨hpoly, hinterior⟩ := Q.localOverlay_edge_dichotomy hs hwindow extra hR
    refine Or.inr ⟨hpoly, ?_⟩
    intro x hx
    apply hinterior
    refine ⟨hx.1, ?_⟩
    intro hxVertex
    apply hx.2
    rw [graph, Graph.vertexSet_union]
    exact Or.inr (by rwa [Graph.vertexSet_relabelEdges])

/-- An edge of the mixed graph meeting an old open source edge away from mixed vertices is one
of that edge's subdivision pieces. -/
theorem graph_edge_subset (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    ∀ {e : γ}, e ∈ E(P.str.skel) → ∀ {f : γ}, f ∈ E(w.graph) →
      (edgeArc w.drawing f ∩ (P.src.cell e \ V(w.graph))).Nonempty →
      edgeArc w.drawing f ⊆ edgeArc P.src.drawing e := by
  intro e he f hf hmeet
  obtain ⟨z, hzf, hzCell, hznotGraph⟩ := hmeet
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have hze : z ∈ edgeArc P.src.drawing e := by
    rw [P.src.cell_edge hab] at hzCell
    exact hzCell.1
  rcases hf with hfOuter | hfInner
  · have hfAbstract : f ∈ E(P.str.outerGraph) := by
      rwa [Graph.edgeSet_map] at hfOuter
    have hzfSrc : z ∈ edgeArc P.src.drawing f := by
      have hdraw := w.drawing_of_outer hfAbstract
      simpa only [Graph.edgeArc] using
        (congrArg (fun g : ℝ → Plane => g '' unitInterval) hdraw ▸ hzf)
    have hznotOld : z ∉ V(P.src.graph) := fun hzOld =>
      hznotGraph (w.sourceVertices_subset_graph hs hzOld)
    have hef : e = f := P.src.isDrawing.unique_edge_at
      (by rw [Graph.edgeSet_map]; exact he)
      (by rw [Graph.edgeSet_map]; exact P.str.outerGraph_le.edgeSet_mono hfAbstract)
      hznotOld hze hzfSrc
    subst f
    have hdraw := w.drawing_of_outer hfAbstract
    rw [Graph.edgeArc, hdraw]
    intro y hy
    exact hy
  · obtain ⟨R, hR, rfl⟩ := hfInner
    have hname : w.name R ∈ E(w.innerGraph) := ⟨R, hR, rfl⟩
    have hdrawing := w.drawing_of_inner hname
    have harc : edgeArc w.drawing (w.name R) = edgeArc segmentDrawing R := by
      calc
        edgeArc w.drawing (w.name R) =
            edgeArc ((Q.localOverlay p s epsilon extra).relabelDrawing
              w.name segmentDrawing) (w.name R) := by
          simpa only [Graph.edgeArc] using congrArg
            (fun g : ℝ → Plane => g '' unitInterval) hdrawing
        _ = edgeArc segmentDrawing R :=
          Graph.edgeArc_relabelDrawing w.name_inj hR
    by_cases heOuter : e ∈ E(P.str.outerGraph)
    · exfalso
      have heMixed : e ∈ E(w.graph) := Or.inl (by
        rw [Graph.edgeSet_map]
        exact heOuter)
      have hne : e ≠ w.name R := fun heq =>
        w.name_fresh R hR (heq ▸ P.str.mem_cells_of_mem_edgeSet he)
      have hzeMixed : z ∈ edgeArc w.drawing e := by
        have hdraw := w.drawing_of_outer heOuter
        simpa only [Graph.edgeArc] using
          (congrArg (fun g : ℝ → Plane => g '' unitInterval) hdraw ▸ hze)
      have hzVertex :=
        (w.graph_isDrawing hs hwindow).edge_inter heMixed (Or.inr hname) hne
          hzeMixed hzf |>.1
      exact hznotGraph hzVertex
    · rw [harc]
      apply Q.localOverlay_edge_subset hs extra he heOuter hR
      refine ⟨z, harc ▸ hzf, hzCell, ?_⟩
      intro hzLocal
      apply hznotGraph
      rw [graph, Graph.vertexSet_union]
      exact Or.inr (by rwa [Graph.vertexSet_relabelEdges])

/-- The mixed graph contains a plane subdivision of the complete old source drawing. -/
theorem source_isPlaneSubdivisionExtension (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    IsPlaneSubdivisionExtension P.src.graph P.src.drawing w.graph w.drawing where
  finite := w.graph_finite
  oldIsDrawing := P.src.isDrawing
  isDrawing := w.graph_isDrawing hs hwindow
  vertexSet_subset := w.sourceVertices_subset_graph hs
  pointSet_subset := w.sourceSkeleton_subset_graph
  edge_subset := by
    intro e he f hf hmeet
    have heAbstract : e ∈ E(P.str.skel) := by
      simpa only [P.src.edgeSet_graph] using he
    obtain ⟨z, hzf, hze, hznot⟩ := hmeet
    obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet heAbstract
    apply w.graph_edge_subset hs hwindow heAbstract hf
    refine ⟨z, hzf, ?_, hznot⟩
    rw [P.src.cell_edge hab]
    refine ⟨hze, ?_⟩
    rintro (rfl | rfl)
    · exact hznot (w.sourceVertices_subset_graph hs (hab.map P.src.pos).left_mem)
    · exact hznot (w.sourceVertices_subset_graph hs (hab.map P.src.pos).right_mem)

/-- The trace of the old source skeleton in the mixed graph remains 2-connected. -/
theorem sourceTrace_isTwoConnected (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    (Graph.traceGraph w.graph w.drawing P.src.skeletonSet).IsTwoConnected :=
  (w.source_isPlaneSubdivisionExtension hs hwindow).trace_isTwoConnected
    P.src_isWeaklyAdmissible.isTwoConnected

/-- Every raw local-grid vertex is retained in the mixed graph. -/
theorem localGridVertices_subset_graph (hs : 0 < s) :
    V(localGrid p s (localGridCount s epsilon)) ⊆ V(w.graph) := by
  intro x hx
  rw [graph, Graph.vertexSet_union]
  exact Or.inr (by
    rw [Graph.vertexSet_relabelEdges]
    exact Q.localGridVertices_subset_localOverlay hs extra hx)

/-- The entire raw local-grid carrier is retained in the mixed graph. -/
theorem localGrid_subset_graph :
    Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing ⊆
      Graph.pointSet w.graph w.drawing := by
  rw [localGrid_eq, pieceListGraph_pointSet, w.graph_pointSet]
  intro x hx
  exact Or.inr (Or.inr hx)

/-- An edge of the mixed graph meeting a raw local-grid edge away from mixed vertices is a
subdivision piece of that grid edge.  An old outer edge cannot meet the grid at all because
the grid window is strictly inside the source domain. -/
theorem graph_grid_edge_subset (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    ∀ {A : Piece}, A ∈ E(localGrid p s (localGridCount s epsilon)) → ∀ {f : γ},
      f ∈ E(w.graph) →
      (edgeArc w.drawing f ∩
        (edgeArc segmentDrawing A \ V(w.graph))).Nonempty →
      edgeArc w.drawing f ⊆ edgeArc segmentDrawing A := by
  intro A hA f hf hmeet
  obtain ⟨z, hzf, hzA, hznotGraph⟩ := hmeet
  have hAList : A ∈ localGridEdges p s (localGridCount s epsilon) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA
  have hzWindow : z ∈ Plane.closedSquare p s :=
    cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon)
      (mem_cover_iff.2 ⟨A, hAList, by rwa [edgeArc_segmentDrawing] at hzA⟩)
  rcases hf with hfOuter | hfInner
  · exfalso
    have hzOuter : z ∈ srcOuter := by
      rw [← w.outer_pointSet]
      exact Graph.edgeArc_subset_pointSet hfOuter hzf
    exact (hwindow hzWindow).2 hzOuter
  · obtain ⟨R, hR, rfl⟩ := hfInner
    have hname : w.name R ∈ E(w.innerGraph) := ⟨R, hR, rfl⟩
    have hdrawing := w.drawing_of_inner hname
    have harc : edgeArc w.drawing (w.name R) = edgeArc segmentDrawing R := by
      calc
        edgeArc w.drawing (w.name R) =
            edgeArc ((Q.localOverlay p s epsilon extra).relabelDrawing
              w.name segmentDrawing) (w.name R) := by
          simpa only [Graph.edgeArc] using congrArg
            (fun g : ℝ → Plane => g '' unitInterval) hdrawing
        _ = edgeArc segmentDrawing R :=
          Graph.edgeArc_relabelDrawing w.name_inj hR
    rw [harc]
    apply Q.localOverlay_grid_edge_subset hs extra hA hR
    refine ⟨z, harc ▸ hzf, hzA, ?_⟩
    intro hzLocal
    apply hznotGraph
    rw [graph, Graph.vertexSet_union]
    exact Or.inr (by rwa [Graph.vertexSet_relabelEdges])

/-- The mixed graph also contains a plane subdivision of the raw local grid. -/
theorem localGrid_isPlaneSubdivisionExtension (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    IsPlaneSubdivisionExtension
      (localGrid p s (localGridCount s epsilon)) segmentDrawing
      w.graph w.drawing where
  finite := w.graph_finite
  oldIsDrawing := localGrid_isDrawing hs (one_le_localGridCount s epsilon)
  isDrawing := w.graph_isDrawing hs hwindow
  vertexSet_subset := w.localGridVertices_subset_graph hs
  pointSet_subset := w.localGrid_subset_graph
  edge_subset := by
    intro A hA f hf hmeet
    exact w.graph_grid_edge_subset hs hwindow hA hf hmeet

/-- The local-grid trace inside the mixed graph remains 2-connected. -/
theorem localGridTrace_isTwoConnected (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) :
    (Graph.traceGraph w.graph w.drawing
      (Graph.pointSet (localGrid p s (localGridCount s epsilon))
        segmentDrawing)).IsTwoConnected :=
  (w.localGrid_isPlaneSubdivisionExtension hs hwindow).trace_isTwoConnected
    (localGrid_isTwoConnected hs (one_le_localGridCount s epsilon))

/-- Two distinct mixed vertices lying on both the old source skeleton and the local grid make
the whole mixed graph 2-connected.  The two plane-subdivision traces are 2-connected and
together contain every mixed vertex. -/
theorem graph_isTwoConnected_of_two_common (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    {a b : Plane} (hab : a ≠ b) (haV : a ∈ V(w.graph)) (hbV : b ∈ V(w.graph))
    (haSource : a ∈ P.src.skeletonSet) (hbSource : b ∈ P.src.skeletonSet)
    (haGrid : a ∈ Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing)
    (hbGrid : b ∈ Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing) :
    w.graph.IsTwoConnected := by
  let T := Graph.traceGraph w.graph w.drawing P.src.skeletonSet
  let K := Graph.traceGraph w.graph w.drawing
    (Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing)
  have hT2 : T.IsTwoConnected := w.sourceTrace_isTwoConnected hs hwindow
  have hK2 : K.IsTwoConnected := w.localGridTrace_isTwoConnected hs hwindow
  have haT : a ∈ V(T) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨haV, haSource⟩
  have hbT : b ∈ V(T) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hbV, hbSource⟩
  have haK : a ∈ V(K) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨haV, haGrid⟩
  have hbK : b ∈ V(K) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hbV, hbGrid⟩
  have hcompat : T.Compatible K :=
    Graph.Compatible.of_le_le (Graph.traceGraph_le _) (Graph.traceGraph_le _)
  have hU2 : (T.union K).IsTwoConnected :=
    hT2.union hcompat hK2 hab haT haK hbT hbK
  apply hU2.of_le_of_vertexSet_subset
    (Graph.union_le (Graph.traceGraph_le _) (Graph.traceGraph_le _))
  intro x hx
  rw [Graph.vertexSet_union]
  have hxPoint : x ∈ Graph.pointSet w.graph w.drawing :=
    Graph.vertexSet_subset_pointSet hx
  rw [w.graph_pointSet] at hxPoint
  rcases hxPoint with hxOuter | hxCore | hxGrid
  · exact Or.inl (by
      rw [Graph.traceGraph_vertexSet]
      exact ⟨hx, by
        rw [P.skeletonSet_eq_sourceNonboundaryGraph_union]
        exact Or.inr hxOuter⟩)
  · exact Or.inl (by
      rw [Graph.traceGraph_vertexSet]
      exact ⟨hx, by
        rw [P.skeletonSet_eq_sourceNonboundaryGraph_union]
        exact Or.inl hxCore⟩)
  · exact Or.inr (by
      rw [Graph.traceGraph_vertexSet, localGrid_eq, pieceListGraph_pointSet]
      exact ⟨hx, hxGrid⟩)

/-- If the old open source skeleton is connected and meets the local grid, then the mixed
carrier remains connected after the wild outer curve is removed. -/
theorem graph_isConnected_diff_of_source_connected (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hsource : IsConnected (P.src.skeletonSet \ srcOuter))
    (hmeet : ((P.src.skeletonSet \ srcOuter) ∩
      Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing).Nonempty) :
    IsConnected (Graph.pointSet w.graph w.drawing \ srcOuter) := by
  let Kset := Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing
  have hKconn : IsConnected Kset :=
    Schoenflies.Graph.IsDrawing.isConnected_pointSet
      (localGrid_isDrawing hs (one_le_localGridCount s epsilon))
      (localGrid_isTwoConnected hs (one_le_localGridCount s epsilon)).connected
  have hKmiss : Kset ⊆ srcOuterᶜ := by
    intro x hxK hxOuter
    have hxCover : x ∈ cover (localGridEdges p s (localGridCount s epsilon)) := by
      simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hxK
    have hxWindow := cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon) hxCover
    exact (hwindow hxWindow).2 hxOuter
  have hcarrier : Graph.pointSet w.graph w.drawing \ srcOuter =
      (P.src.skeletonSet \ srcOuter) ∪ Kset := by
    ext x
    rw [Set.mem_sdiff, Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro ⟨hxGraph, hxNotOuter⟩
      rw [w.graph_pointSet] at hxGraph
      rcases hxGraph with hxOuter | hxCore | hxGrid
      · exact (hxNotOuter hxOuter).elim
      · exact Or.inl ⟨by
          rw [P.skeletonSet_eq_sourceNonboundaryGraph_union]
          exact Or.inl hxCore, hxNotOuter⟩
      · exact Or.inr (by
          simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hxGrid)
    · rintro (⟨hxSource, hxNotOuter⟩ | hxK)
      · refine ⟨?_, hxNotOuter⟩
        rw [P.skeletonSet_eq_sourceNonboundaryGraph_union] at hxSource
        rw [w.graph_pointSet]
        rcases hxSource with hxCore | hxOuter
        · exact Or.inr (Or.inl hxCore)
        · exact Or.inl hxOuter
      · refine ⟨?_, hKmiss hxK⟩
        rw [w.graph_pointSet]
        exact Or.inr (Or.inr (by
          simpa only [Kset, localGrid_eq, pieceListGraph_pointSet] using hxK))
  rw [hcarrier]
  exact IsConnected.union hmeet hsource hKconn

/-- The mixed graph is a complete source extension once its two global attachment properties
are supplied.  All finiteness, drawing, subdivision, containment, and edge-geometry fields are
automatic from the exact source cover and the interior-window hypothesis. -/
theorem isSourceExtension (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (htwo : w.graph.IsTwoConnected)
    (hconnected : IsConnected (Graph.pointSet w.graph w.drawing \ srcOuter)) :
    IsSourceExtension P.src srcOuter srcDom w.graph w.drawing where
  finite := w.graph_finite
  isDrawing := w.graph_isDrawing hs hwindow
  isTwoConnected := htwo
  vertexSet_subset := w.sourceVertices_subset_graph hs
  skeletonSet_subset := w.sourceSkeleton_subset_graph
  edge_subset := by
    intro e he f hf hmeet
    exact w.graph_edge_subset hs hwindow he hf hmeet
  pointSet_subset := w.graph_pointSet_subset hs hwindow
  edge_dichotomy := by
    intro f hf
    exact w.graph_edge_dichotomy hs hwindow hf
  isConnected := hconnected

/-- With two common source/grid vertices, only connectedness off the wild outer curve remains
to obtain the complete source extension. -/
theorem isSourceExtension_of_two_common (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    {a b : Plane} (hab : a ≠ b) (haV : a ∈ V(w.graph)) (hbV : b ∈ V(w.graph))
    (haSource : a ∈ P.src.skeletonSet) (hbSource : b ∈ P.src.skeletonSet)
    (haGrid : a ∈ Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing)
    (hbGrid : b ∈ Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing)
    (hconnected : IsConnected (Graph.pointSet w.graph w.drawing \ srcOuter)) :
    IsSourceExtension P.src srcOuter srcDom w.graph w.drawing :=
  w.isSourceExtension hs hwindow
    (w.graph_isTwoConnected_of_two_common hs hwindow hab haV hbV
      haSource hbSource haGrid hbGrid)
    hconnected

/-- At an admissible stage, two distinct common source/grid vertices give the complete source
extension.  One common point joins the two connected carriers off the boundary; both common
vertices make their 2-connected subdivision traces glue. -/
theorem isSourceExtension_of_source_connected_two_common (hs : 0 < s)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter)
    (hsource : IsConnected P.src.nonboundary)
    {a b : Plane} (hab : a ≠ b) (haV : a ∈ V(w.graph)) (hbV : b ∈ V(w.graph))
    (haSource : a ∈ P.src.skeletonSet) (hbSource : b ∈ P.src.skeletonSet)
    (haGrid : a ∈ Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing)
    (hbGrid : b ∈ Graph.pointSet (localGrid p s (localGridCount s epsilon)) segmentDrawing) :
    IsSourceExtension P.src srcOuter srcDom w.graph w.drawing := by
  have hsource' : IsConnected (P.src.skeletonSet \ srcOuter) := by
    rwa [P.src_nonboundary_eq] at hsource
  have haNotOuter : a ∉ srcOuter := by
    intro haOuter
    have haCover : a ∈ cover (localGridEdges p s (localGridCount s epsilon)) := by
      simpa only [localGrid_eq, pieceListGraph_pointSet] using haGrid
    have haWindow := cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon) haCover
    exact (hwindow haWindow).2 haOuter
  apply w.isSourceExtension_of_two_common hs hwindow hab haV hbV
    haSource hbSource haGrid hbGrid
  apply w.graph_isConnected_diff_of_source_connected hs hwindow hsource'
  exact ⟨a, ⟨haSource, haNotOuter⟩, haGrid⟩

end LocalOverlayRelabeling

end SourceNonboundarySegmentCover

end Schoenflies
