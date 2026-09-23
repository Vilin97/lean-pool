/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.CellulationInvariants
public import LeanPool.Schoenflies.JordanClosed
public import LeanPool.Schoenflies.Graph.PathGraph

/-!
# Realizing a 2-cell split

`Schoenflies/CellulationInvariants.lean` proves the *step* theorems of the second elementary
operation: given a realization `R'` of `S.splitFace d` standing in the relation
`SplitData.IsCrosscutSplit` to a realization `R` of `S`, the two invariants of
`lem:cellulation-invariants` propagate. Nothing built such an `R'`. This module does.

## Blueprint

* `def:generated-structure`, operation 2 — the 2-cell split whose realization is constructed
  here.
* `lem:cellulation-invariants` (i), (vii) — the invariants that
  `SplitData.IsCrosscutSplit.isCellDecomposition_and_isFaceJordan` derives from the output of
  this module.
* `thm:general-crosscut` (`Schoenflies.crosscut_theorem`) — what turns the constructed ear into
  the two new open 2-cells; it is applied inside `IsCrosscutSplit.isRefinement`, and this module
  supplies its hypotheses.

## What is constructed

* `Schoenflies.CellStructure.SplitData.EarCrosscut` — the geometric input: an assignment of
  points to the ear's vertices and of parametrizations to the ear's edges, drawing the ear as a
  polygonal crosscut of the realized open 2-cell.
* `Schoenflies.CellStructure.SplitData.realize` — the realization of `S.splitFace d` built from
  `R` and such an ear. It is a `def` with lemmas, not an existential: `splitPos`,
  `splitDrawing`, `splitCell` are its three components, each with its own reduction lemmas
  (`splitCell_face₁`, `splitCell_of_mem_cells`, `splitCell_earVertex`, `splitCell_earEdge`, …),
  and `realize_pos` / `realize_drawing` / `realize_cell` connect them to the record.
* `Schoenflies.CellStructure.SplitData.isCrosscutSplit_realize` — the constructed realization
  stands in the relation `IsCrosscutSplit` to `R`. Composed with
  `IsCrosscutSplit.isCellDecomposition_and_isFaceJordan` this is the full induction step.

## What is assumed, and who discharges it

`realize` itself asks only for `EarCrosscut`, whose six fields — `pos_source`, `pos_target`,
`injOn`, `isDrawing`, `subset_face`, `polygonal` — say that the ear is drawn as a simple
polygonal arc from `R.pos d.source` to `R.pos d.target` whose interior lies in the open 2-cell,
plus the seventh, `disjoint_skeleton`, which is a fact about `R` alone and is discharged by
`Realization.disjoint_cell_skeletonSet` from assertion (i). A producer that starts from
`Schoenflies.exists_crosscut_of_polyAccessible` — a polygonal arc inside the face with both
ends on its boundary — and cuts that arc into the ear's edges has all seven in hand.

`isCrosscutSplit_realize` asks in addition only for `R.IsCellDecomposition D` and
`R.IsFaceJordan`.

It used to ask for a third thing — that the two boundary paths of the split 2-cell share nothing
but their two ends — because `SplitData` did not imply it: its field `paths_disjoint` forbade
the two paths a common *edge* but said nothing about a common interior *vertex*, and with a
common interior vertex the two realized paths meet in a third point, so the `IsCutPair` clause
of `IsCrosscutSplit` is false. That gap has since been closed at the source: `SplitData` now
carries `paths_meet` and derives `paths_disjoint` from it. What follows is the record of a
condition that
producer of the `SplitData` chooses them (as the two arcs of one boundary cycle) and so can
supply it. If a later wave prefers it as a field of `SplitData`, that is the right place for it.

## The general lemmas this needed

Three facts about drawings and paths had no home on `main` and are proved here in the root
`Graph` namespace. If a second consumer appears they belong in `Schoenflies/Graph/`:

* `Graph.IsPath.map`, `Graph.walkVertices_map`, `Graph.IsPathGraph.map` — a path pushes forward
  along an injective relabelling of the vertices. `Graph.IsWalk.map` was already on `main` (in
  `Schoenflies/CombinatorialInvariance.lean`); the path version needs the injectivity, because
  the freshness clause is a *non*-membership.
* `Graph.IsDrawing.isArcBetween_walkPointSet` — **the point set of a drawn path is a simple
  arc between its two ends.** This is the workhorse: it is what makes the realized ear an arc
  (so `IsCrosscut` applies) and what makes each realized boundary path an arc (so `IsCutPair`
  applies). The induction is on `Graph.IsPath`, and the freshness clause of a path is exactly
  what rules out the returning point that would break `IsArcBetween.concatenate`.
-/

@[expose] public section

open Set Schoenflies
open scoped Graph

namespace Graph

/-! ### Pushing a path forward along a relabelling -/

section Map

variable {α α' β : Type*} {G : Graph α β} {f : α → α'} {u v : α} {W : List β}

theorem coveredVertices_map (f : α → α') :
    (G.map f).coveredVertices W = f '' G.coveredVertices W := by
  ext x
  simp only [mem_coveredVertices_iff, map_inc, Set.mem_image]
  constructor
  · rintro ⟨e, he, v, hv, rfl⟩
    exact ⟨v, ⟨e, he, hv⟩, rfl⟩
  · rintro ⟨v, ⟨e, he, hv⟩, rfl⟩
    exact ⟨e, he, v, hv, rfl⟩

theorem walkVertices_map (f : α → α') (u : α) (W : List β) :
    (G.map f).walkVertices (f u) W = f '' G.walkVertices u W := by
  rw [walkVertices, walkVertices, coveredVertices_map, Set.image_insert_eq]

/-- **A path pushes forward along an injective relabelling.** Unlike `Graph.IsWalk.map` this
needs the injectivity: the freshness clause is a non-membership, and only an injective map
reflects it. -/
theorem IsPath.map (hf : InjOn f V(G)) (h : G.IsPath u W v) : (G.map f).IsPath (f u) W (f v) := by
  induction h with
  | nil hx => exact .nil (by simpa using Set.mem_image_of_mem f hx)
  | @cons u w v e W hl hW hfresh ih =>
    refine .cons (hl.map f) ih ?_
    rw [walkVertices_map]
    rintro ⟨z, hz, hzf⟩
    have hzV : z ∈ V(G) := walkVertices_subset_vertexSet hW.isWalk.left_mem hz
    exact hfresh (hf hzV hl.left_mem hzf ▸ hz)

/-- Relabelling commutes with the union. Both sides resolve a shared edge name in favour of
the left-hand graph, and `Graph.map` keeps the edge set, so the two resolutions agree. -/
theorem map_union (G H : Graph α β) (f : α → α') :
    (G.union H).map f = (G.map f).union (H.map f) := by
  refine Graph.ext (by simp [Set.image_union]) fun e x y => ?_
  simp only [map_isLink, union_isLink, Relation.map_apply, edgeSet_map]
  constructor
  · rintro ⟨a, b, hab | ⟨he, hab⟩, rfl, rfl⟩
    · exact Or.inl ⟨a, b, hab, rfl, rfl⟩
    · exact Or.inr ⟨he, a, b, hab, rfl, rfl⟩
  · rintro (⟨a, b, hab, rfl, rfl⟩ | ⟨he, a, b, hab, rfl, rfl⟩)
    · exact ⟨a, b, Or.inl hab, rfl, rfl⟩
    · exact ⟨a, b, Or.inr ⟨he, hab⟩, rfl, rfl⟩

theorem IsPathGraph.map {P : Graph α β} (hf : InjOn f V(P)) (h : P.IsPathGraph u W v) :
    (P.map f).IsPathGraph (f u) W (f v) where
  isPath := h.isPath.map hf
  edgeSet_eq := by rw [edgeSet_map]; exact h.edgeSet_eq
  vertexSet_eq := by rw [vertexSet_map, walkVertices_map, h.vertexSet_eq]

end Map

section Drawing

variable {β : Type*} {H K : Graph Plane β} {drw : β → ℝ → Plane}

/-! ### The point set of a drawn path

`Graph.pointSet` reads the vertex set and the edge set of a graph. Along a walk both are read
off the list instead, and that is the form the induction below runs on. -/

/-- The point set a walk occupies: the vertices it visits together with the arcs of its
edges. For a path graph this is the whole of `Graph.pointSet` (`walkPointSet_eq_pointSet`). -/
def walkPointSet (H : Graph Plane β) (drw : β → ℝ → Plane) (u : Plane) (W : List β) : Set Plane :=
  H.walkVertices u W ∪ ⋃ e ∈ ({e | e ∈ W} : Set β), edgeArc drw e

theorem walkPointSet_eq_pointSet {u v : Plane} {W : List β} (h : H.IsPathGraph u W v) :
    walkPointSet H drw u W = pointSet H drw := by
  rw [walkPointSet, pointSet, h.vertexSet_eq, h.edgeSet_eq]

theorem walkPointSet_nil (u : Plane) : walkPointSet H drw u ([] : List β) = {u} := by
  rw [walkPointSet, walkVertices_nil]
  simp

/-- Peeling the first step off a walk peels its arc off the point set. The vertex the step
departs from is an end of that arc, which is why nothing is left behind. -/
theorem walkPointSet_cons (hD : IsDrawing H drw) {e : β} {u w : Plane} {W : List β}
    (hl : H.IsLink e u w) :
    walkPointSet H drw u (e :: W) = edgeArc drw e ∪ walkPointSet H drw w W := by
  have hu : u ∈ edgeArc drw e := (hD.edge_isArcBetween hl).left_mem
  have hset : ({f | f ∈ e :: W} : Set β) = insert e {f | f ∈ W} := by
    ext f; simp [List.mem_cons]
  rw [walkPointSet, walkPointSet, walkVertices_cons hl, hset, Set.biUnion_insert]
  refine Set.Subset.antisymm ?_ ?_
  · rintro z (hz | hz)
    · rcases hz with rfl | hz
      · exact Or.inl hu
      · exact Or.inr (Or.inl hz)
    · rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (Or.inr hz)
  · rintro z (hz | hz | hz)
    · exact Or.inr (Or.inl hz)
    · exact Or.inl (Or.inr hz)
    · exact Or.inr (Or.inr hz)

/-- **The point set of a drawn path is a simple arc between its two ends.**

The two pieces glued at each step are the arc of the first edge and the point set of the rest
of the path, and `IsArcBetween.concatenate` asks that they meet only at the vertex between
them. That is precisely the freshness clause of `Graph.IsPath`: the vertex the path departs
from is not among those the rest of it visits, and every point the first arc shares with the
rest of the drawing is a vertex the rest visits — a vertex by `vertex_mem_edgeArc` if it is
one of the rest's vertices, and by `edge_inter` if it lies on one of the rest's arcs. -/
theorem IsDrawing.isArcBetween_walkPointSet (hD : IsDrawing H drw) :
    ∀ {u v : Plane} {W : List β}, H.IsPath u W v → u ≠ v →
      IsArcBetween (walkPointSet H drw u W) u v := by
  intro u v W hp
  induction hp with
  | nil => exact fun h => absurd rfl h
  | @cons u w v e W hl hW hfresh ih =>
    intro _
    rw [walkPointSet_cons hD hl]
    have harc : IsArcBetween (edgeArc drw e) u w := hD.edge_isArcBetween hl
    by_cases hwv : w = v
    · subst hwv
      rw [hW.eq_nil_of_eq, walkPointSet_nil,
        Set.union_eq_self_of_subset_right (Set.singleton_subset_iff.2 harc.right_mem)]
      exact harc
    · refine harc.concatenate (ih hwv) ?_
      intro z hz hz'
      -- every point the first arc shares with the rest is a vertex the rest visits
      have hzw : z ∈ H.walkVertices w W := by
        rcases hz' with hz' | hz'
        · exact hz'
        · obtain ⟨f, hf, hzf⟩ := Set.mem_iUnion₂.1 hz'
          have hfe : e ≠ f := by
            rintro rfl
            exact (List.nodup_cons.1 (IsPath.cons hl hW hfresh).nodup).1 hf
          exact mem_walkVertices_of_mem_covered ⟨f, hf,
            (hD.edge_inter hl.edge_mem (hW.isWalk.edge_mem hf) hfe hz hzf).2.2⟩
      have hzV : z ∈ V(H) := walkVertices_subset_vertexSet hW.isWalk.left_mem hzw
      rcases hD.vertex_mem_edgeArc hl hzV hz with rfl | rfl
      · exact absurd hzw hfresh
      · rfl

theorem IsDrawing.isArcBetween_pointSet (hD : IsDrawing H drw) {u v : Plane} {W : List β}
    (h : H.IsPathGraph u W v) (huv : u ≠ v) : IsArcBetween (pointSet H drw) u v := by
  rw [← walkPointSet_eq_pointSet h]
  exact hD.isArcBetween_walkPointSet h.isPath huv

end Drawing

end Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-! ## What a realization does to a walk

Two facts about an existing realization, both of the shape "the realized cells of a piece of
the skeleton occupy the point set that piece of the drawing occupies". They are what let the
crosscut theorem, which speaks of point sets, be fed from the cell structure, which speaks of
cells. -/

namespace Realization

variable (R : S.Realization)

theorem walkVertices_graph (u : γ) (W : List γ) :
    R.graph.walkVertices (R.pos u) W = R.pos '' S.skel.walkVertices u W :=
  Graph.walkVertices_map _ _ _

/-- **The realized cells of a path occupy the point set the drawn path occupies.** The two
differ only in the endpoints an open 1-cell drops, and those are the points of the 0-cells the
walk visits. -/
theorem cellUnion_pathCells {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v) :
    R.cellUnion (S.pathCells u W) = Graph.walkPointSet R.graph R.drawing (R.pos u) W := by
  have hsub : S.skel.walkVertices u W ⊆ V(S.skel) :=
    Graph.walkVertices_subset_vertexSet h.left_mem
  have hV : R.cellUnion (S.skel.walkVertices u W) = R.pos '' S.skel.walkVertices u W := by
    refine Set.Subset.antisymm (cellUnion_subset fun z hz => ?_) ?_
    · rw [R.cell_vertex (hsub hz)]
      exact Set.singleton_subset_iff.2 ⟨z, hz, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact cell_subset_cellUnion hz (by rw [R.cell_vertex (hsub hz)]; rfl)
  rw [CellStructure.pathCells, cellUnion_union, hV, Graph.walkPointSet, R.walkVertices_graph]
  refine Set.Subset.antisymm ?_ ?_
  · refine Set.union_subset (cellUnion_subset fun f hf => ?_) Set.subset_union_left
    obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet (h.edge_mem hf)
    rw [R.cell_edge hl]
    exact fun x hx => Or.inr (Set.mem_biUnion hf hx.1)
  · refine Set.union_subset Set.subset_union_right (Set.iUnion₂_subset fun f hf x hx => ?_)
    obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet (h.edge_mem hf)
    by_cases hxab : x ∈ ({R.pos a, R.pos b} : Set Plane)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxab
      rcases hxab with rfl | rfl
      · exact Or.inr ⟨a, Graph.mem_walkVertices_of_mem_covered ⟨f, hf, hl.inc_left⟩, rfl⟩
      · exact Or.inr ⟨b, Graph.mem_walkVertices_of_mem_covered ⟨f, hf, hl.inc_right⟩, rfl⟩
    · exact Or.inl (cell_subset_cellUnion hf (by rw [R.cell_edge hl]; exact ⟨hx, hxab⟩))

/-- The drawn skeleton is covered by the open cells of dimension 0 and 1. -/
theorem skeletonSet_subset_cellUnion :
    R.skeletonSet ⊆ R.cellUnion (V(S.skel) ∪ E(S.skel)) := by
  intro x hx
  rcases hx with hx | hx
  · rw [Realization.vertexSet_graph] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    refine cell_subset_cellUnion (Set.mem_union_left _ hz) ?_
    rw [R.cell_vertex hz]
    rfl
  · obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 hx
    rw [Realization.edgeSet_graph] at hf
    obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet hf
    by_cases hxab : x ∈ ({R.pos a, R.pos b} : Set Plane)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxab
      rcases hxab with rfl | rfl
      · refine cell_subset_cellUnion (Set.mem_union_left _ hl.left_mem) ?_
        rw [R.cell_vertex hl.left_mem]
        rfl
      · refine cell_subset_cellUnion (Set.mem_union_left _ hl.right_mem) ?_
        rw [R.cell_vertex hl.right_mem]
        rfl
    · refine cell_subset_cellUnion (Set.mem_union_right _ hf) ?_
      rw [R.cell_edge hl]
      exact ⟨hxf, hxab⟩

/-- **An open 2-cell misses the drawn skeleton.** Immediate from the disjointness clause of
assertion (i): the skeleton is covered by cells of lower dimension. -/
theorem disjoint_cell_skeletonSet {D : Set Plane} (hcd : R.IsCellDecomposition D) {F : γ}
    (hF : F ∈ S.faces) : Disjoint (R.cell F) R.skeletonSet := by
  refine Set.disjoint_right.2 fun x hx hxF => ?_
  obtain ⟨σ, hσ, hxσ⟩ := mem_cellUnion_iff.1 (R.skeletonSet_subset_cellUnion hx)
  have hne : F ≠ σ := by
    rintro rfl
    rcases hσ with hσ | hσ
    exacts [Set.disjoint_left.1 S.disjoint_faces_vertexSet hF hσ,
      Set.disjoint_left.1 S.disjoint_faces_edgeSet hF hσ]
  have hσc : σ ∈ S.cells := by
    rcases hσ with hσ | hσ
    exacts [S.mem_cells_of_mem_vertexSet hσ, S.mem_cells_of_mem_edgeSet hσ]
  exact Set.disjoint_left.1 (hcd.disjoint (S.mem_cells_of_mem_faces hF) hσc hne) hxF hxσ

end Realization

/-! ## The ear, drawn

`SplitData` fixes the *abstract* ear: a path graph `d.ear` glued to the skeleton at
`d.source` and `d.target`. Drawing it means choosing a point for each of its vertices and a
parametrization for each of its edges. `EarCrosscut` is the bundle of conditions under which
that drawing is a polygonal crosscut of the realized open 2-cell `R.cell d.face`. -/

namespace SplitData

variable (d : S.SplitData)

theorem source_mem_ear : d.source ∈ V(d.ear) :=
  (d.vertexSet_inter ▸ (Set.mem_insert _ _ : d.source ∈ ({d.source, d.target} : Set γ))).1

theorem target_mem_ear : d.target ∈ V(d.ear) :=
  (d.vertexSet_inter ▸
    (Set.mem_insert_of_mem _ rfl : d.target ∈ ({d.source, d.target} : Set γ))).1

theorem source_mem_cells₂ : d.source ∈ d.cells₂ :=
  Or.inr Graph.mem_walkVertices_self

theorem target_mem_cells₂ : d.target ∈ d.cells₂ :=
  Or.inr d.isPath₂.isWalk.target_mem_walkVertices

/-- **The cells strictly below the split 2-cell are the cells of its two boundary paths.**
This is `SplitData.sub_face` read as a set identity; with assertion (i) it identifies the
frontier of the old open 2-cell with the two realized boundary paths. -/
theorem subcells_face_diff : S.subcells d.face \ {d.face} = d.cells₁ ∪ d.cells₂ := by
  ext σ
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, CellStructure.mem_subcells_iff, Set.mem_union]
  constructor
  · rintro ⟨⟨-, hsub⟩, hne⟩
    rcases d.sub_face.1 hsub with rfl | h
    · exact absurd rfl hne
    · exact h
  · intro h
    refine ⟨⟨?_, d.sub_face.2 (Or.inr h)⟩, ?_⟩
    · rcases h with h | h
      exacts [d.cells₁_subset h, d.cells₂_subset h]
    · rcases h with h | h
      exacts [d.cells₁_ne_face h, d.cells₂_ne_face h]

/-- The drawn ear: the abstract ear pushed into the plane along the chosen positions. -/
def earGraph (d : S.SplitData) (earPos : γ → Plane) : Graph Plane γ := d.ear.map earPos

@[simp] theorem vertexSet_earGraph (earPos : γ → Plane) :
    V(d.earGraph earPos) = earPos '' V(d.ear) := Graph.vertexSet_map _ _

@[simp] theorem edgeSet_earGraph (earPos : γ → Plane) :
    E(d.earGraph earPos) = E(d.ear) := Graph.edgeSet_map _ _

/-- The point set the drawn ear occupies: the crosscut `P` of `thm:general-crosscut`. -/
def earSet (d : S.SplitData) (earPos : γ → Plane) (earDraw : γ → ℝ → Plane) : Set Plane :=
  Graph.pointSet (d.earGraph earPos) earDraw

/-- **The geometric input of one 2-cell split.** A position for each vertex of the abstract
ear and a parametrization for each of its edges, drawing the ear as a polygonal crosscut of
the realized open 2-cell `R.cell d.face`.

Every clause is a statement about the ear's own drawing, and every one of them is what the
finite-transfer module has in hand when it produces a crosscut from
`Schoenflies.exists_crosscut_of_polyAccessible`: it starts from a simple polygonal arc `P`
inside the face with its two ends on the boundary, and cuts `P` into the ear's edges. -/
structure EarCrosscut (d : S.SplitData) (R : S.Realization) (earPos : γ → Plane)
    (earDraw : γ → ℝ → Plane) : Prop where
  /-- The ear starts where the old 0-cell `d.source` sits. -/
  pos_source : earPos d.source = R.pos d.source
  /-- …and ends where `d.target` sits. -/
  pos_target : earPos d.target = R.pos d.target
  /-- Distinct vertices of the ear are drawn at distinct points. -/
  injOn : InjOn earPos V(d.ear)
  /-- The ear is drawn as a plane graph. -/
  isDrawing : Graph.IsDrawing (d.earGraph earPos) earDraw
  /-- Every point of the drawn ear but its two ends is inside the old open 2-cell. -/
  subset_face : d.earSet earPos earDraw \ {R.pos d.source, R.pos d.target} ⊆ R.cell d.face
  /-- The old open 2-cell misses the old drawn skeleton. This is a property of `R` alone, not
  of the ear; it is carried here so that the construction below depends on no ambient domain.
  `Realization.disjoint_cell_skeletonSet` discharges it from assertion (i). -/
  disjoint_skeleton : Disjoint (R.cell d.face) R.skeletonSet
  /-- The drawn ear is polygonal. -/
  polygonal : IsPolygonal (d.earSet earPos earDraw)

namespace EarCrosscut

variable {d} {R : S.Realization} {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}
theorem source_ne_target_pos : R.pos d.source ≠ R.pos d.target := fun h =>
  d.source_ne_target (R.injOn_pos d.source_mem_skel d.target_mem_skel h)

theorem mem_earSet_of_mem_ear {z : γ} (hz : z ∈ V(d.ear)) : earPos z ∈ d.earSet earPos earDraw :=
  Graph.vertexSet_subset_pointSet (by rw [d.vertexSet_earGraph]; exact ⟨z, hz, rfl⟩)

theorem edgeArc_subset_earSet {f : γ} (hf : f ∈ E(d.ear)) :
    Graph.edgeArc earDraw f ⊆ d.earSet earPos earDraw :=
  Graph.edgeArc_subset_pointSet (by rw [d.edgeSet_earGraph]; exact hf)

variable (hE : d.EarCrosscut R earPos earDraw)

include hE

/-- On the two ends — the only vertices the ear shares with the old skeleton — the ear's
positions agree with the old ones. -/
theorem earPos_eq {z : γ} (hz : z ∈ V(d.ear)) (hz' : z ∈ V(S.skel)) : earPos z = R.pos z := by
  have : z ∈ ({d.source, d.target} : Set γ) := d.vertexSet_inter ▸ ⟨hz, hz'⟩
  rcases this with rfl | rfl
  exacts [hE.pos_source, hE.pos_target]

theorem pos_source_mem_earSet : R.pos d.source ∈ d.earSet earPos earDraw :=
  hE.pos_source ▸ mem_earSet_of_mem_ear d.source_mem_ear

theorem pos_target_mem_earSet : R.pos d.target ∈ d.earSet earPos earDraw :=
  hE.pos_target ▸ mem_earSet_of_mem_ear d.target_mem_ear

/-- An interior vertex of the ear is drawn strictly inside the old open 2-cell. -/
theorem earPos_mem_cell_face {z : γ} (hz : z ∈ V(d.ear)) (hs : z ≠ d.source)
    (ht : z ≠ d.target) : earPos z ∈ R.cell d.face := by
  refine hE.subset_face ⟨mem_earSet_of_mem_ear hz, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (h | h)
  · exact hs (hE.injOn hz d.source_mem_ear (h.trans hE.pos_source.symm))
  · exact ht (hE.injOn hz d.target_mem_ear (h.trans hE.pos_target.symm))

/-- **The drawn ear meets the old skeleton exactly in its two ends.** The interior of the ear
is inside the open 2-cell, and an open 2-cell misses the drawn skeleton. -/
theorem earSet_inter_skeletonSet :
    d.earSet earPos earDraw ∩ R.skeletonSet ⊆ {R.pos d.source, R.pos d.target} := by
  rintro x ⟨hx, hx'⟩
  by_contra hcon
  exact Set.disjoint_left.1 hE.disjoint_skeleton (hE.subset_face ⟨hx, hcon⟩) hx'

/-- **An ear edge's arc meets the ear's vertices exactly at its own two ends**, so dropping
all of the ear's vertices from it is the same as dropping its own two ends. This is what makes
the definition of the new open 1-cells independent of a choice of orientation. -/
theorem edgeArc_diff {f a b : γ} (hl : d.ear.IsLink f a b) :
    Graph.edgeArc earDraw f \ earPos '' V(d.ear) =
      Graph.edgeArc earDraw f \ {earPos a, earPos b} := by
  have hlm : (d.earGraph earPos).IsLink f (earPos a) (earPos b) := hl.map earPos
  refine Set.Subset.antisymm (Set.sdiff_subset_sdiff_right ?_) (fun x ⟨hx, hx'⟩ => ⟨hx, ?_⟩)
  · rintro _ (rfl | rfl)
    exacts [⟨a, hl.left_mem, rfl⟩, ⟨b, hl.right_mem, rfl⟩]
  · rintro ⟨w, hw, rfl⟩
    have hwV : earPos w ∈ V(d.earGraph earPos) := by
      rw [d.vertexSet_earGraph]; exact ⟨w, hw, rfl⟩
    exact hx' (hE.isDrawing.vertex_mem_edgeArc hlm hwV hx)

end EarCrosscut

/-! ## The realization built from a drawn ear -/

open scoped Classical in
/-- Where the split puts each 0-cell: the ear's vertices go where the ear's drawing puts them,
everything else stays. On the ear's two ends the two prescriptions agree. -/
noncomputable def splitPos (d : S.SplitData) (R : S.Realization) (earPos : γ → Plane) :
    γ → Plane := fun z => if z ∈ V(d.ear) then earPos z else R.pos z

open scoped Classical in
/-- How the split draws each 1-cell. -/
noncomputable def splitDrawing (d : S.SplitData) (R : S.Realization)
    (earDraw : γ → ℝ → Plane) : γ → ℝ → Plane :=
  fun f => if f ∈ E(d.ear) then earDraw f else R.drawing f

open scoped Classical in
/-- The point set of each open cell after the split: the two new 2-cells are the two sides of
the crosscut, the ear's vertices and edges are their points and their open arcs, and every
surviving cell keeps its old point set. -/
noncomputable def splitCell (d : S.SplitData) (R : S.Realization) (earPos : γ → Plane)
    (earDraw : γ → ℝ → Plane) : γ → Set Plane := fun σ =>
  if σ = d.face₁ then inside (R.cellUnion d.cells₁ ∪ d.earSet earPos earDraw)
  else if σ = d.face₂ then inside (R.cellUnion d.cells₂ ∪ d.earSet earPos earDraw)
  else if σ ∈ V(d.ear) ∧ σ ∉ V(S.skel) then {earPos σ}
  else if σ ∈ E(d.ear) then Graph.edgeArc earDraw σ \ earPos '' V(d.ear)
  else R.cell σ

variable {d} {R : S.Realization} {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}

theorem splitPos_of_mem_ear {z : γ} (hz : z ∈ V(d.ear)) : d.splitPos R earPos z = earPos z := by
  classical
  simp only [splitPos,
          ite_eq_left hz]

theorem splitPos_of_notMem_ear {z : γ} (hz : z ∉ V(d.ear)) : d.splitPos R earPos z = R.pos z := by
  classical
  simp only [splitPos,
      ite_eq_right hz]

theorem EarCrosscut.splitPos_eq (hE : d.EarCrosscut R earPos earDraw) {z : γ}
    (hz : z ∈ V(S.skel)) : d.splitPos R earPos z = R.pos z := by
  by_cases hz' : z ∈ V(d.ear)
  · rw [splitPos_of_mem_ear hz', hE.earPos_eq hz' hz]
  · rw [splitPos_of_notMem_ear hz']

theorem splitDrawing_of_mem_ear {f : γ} (hf : f ∈ E(d.ear)) :
    d.splitDrawing R earDraw f = earDraw f := by
  classical
  simp only [splitDrawing,
          ite_eq_left hf]

theorem splitDrawing_of_mem_skel {f : γ} (hf : f ∈ E(S.skel)) :
    d.splitDrawing R earDraw f = R.drawing f := by
  classical
  simp only [splitDrawing,
      ite_eq_right (Set.disjoint_left.1 d.disjoint_edgeSet hf)]

theorem splitCell_face₁ : d.splitCell R earPos earDraw d.face₁ =
    inside (R.cellUnion d.cells₁ ∪ d.earSet earPos earDraw) := by
  classical
  unfold splitCell
  rw [ite_eq_left rfl]

theorem splitCell_face₂ : d.splitCell R earPos earDraw d.face₂ =
    inside (R.cellUnion d.cells₂ ∪ d.earSet earPos earDraw) := by
  classical
  unfold splitCell
  rw [ite_eq_right (Ne.symm d.face_ne),
          ite_eq_left rfl]

theorem splitCell_of_mem_cells {σ : γ} (hσ : σ ∈ S.cells) :
    d.splitCell R earPos earDraw σ = R.cell σ := by
  classical
  have h₁ : σ ≠ d.face₁ := by rintro rfl; exact d.face₁_notMem hσ
  have h₂ : σ ≠ d.face₂ := by rintro rfl; exact d.face₂_notMem hσ
  have h₃ : ¬ (σ ∈ V(d.ear) ∧ σ ∉ V(S.skel)) := by
    rintro ⟨hv, hnv⟩
    rcases d.mem_cells_of_mem_ear_vertexSet hv hσ with rfl | rfl
    exacts [hnv d.source_mem_skel, hnv d.target_mem_skel]
  have h₄ : σ ∉ E(d.ear) := fun h => d.edge_fresh h hσ
  unfold splitCell
  rw [ite_eq_right h₁,
      ite_eq_right h₂,
      ite_eq_right h₃,
      ite_eq_right h₄]

theorem EarCrosscut.splitCell_earVertex (hE : d.EarCrosscut R earPos earDraw) {z : γ}
    (hz : z ∈ V(d.ear)) : d.splitCell R earPos earDraw z = {earPos z} := by
  classical
  by_cases hz' : z ∈ V(S.skel)
  · rw [splitCell_of_mem_cells (S.mem_cells_of_mem_vertexSet hz'), R.cell_vertex hz',
      hE.earPos_eq hz hz']
  · have h₁ : z ≠ d.face₁ := by rintro rfl; exact d.face₁_notMem_ear (Or.inl hz)
    have h₂ : z ≠ d.face₂ := by rintro rfl; exact d.face₂_notMem_ear (Or.inl hz)
    unfold splitCell
    rw [ite_eq_right h₁,
      ite_eq_right h₂,
          ite_eq_left (show z ∈ V(d.ear) ∧ z ∉ V(S.skel) from ⟨hz, hz'⟩)]

theorem splitCell_earEdge {f : γ} (hf : f ∈ E(d.ear)) :
    d.splitCell R earPos earDraw f = Graph.edgeArc earDraw f \ earPos '' V(d.ear) := by
  classical
  have h₁ : f ≠ d.face₁ := by rintro rfl; exact d.face₁_notMem_ear (Or.inr hf)
  have h₂ : f ≠ d.face₂ := by rintro rfl; exact d.face₂_notMem_ear (Or.inr hf)
  have h₃ : ¬ (f ∈ V(d.ear) ∧ f ∉ V(S.skel)) := fun h =>
    Set.disjoint_left.1 d.ear_disjoint h.1 hf
  unfold splitCell
  rw [ite_eq_right h₁,
      ite_eq_right h₂,
      ite_eq_right h₃,
          ite_eq_left hf]

theorem edgeArc_splitDrawing_of_mem_skel {f : γ} (hf : f ∈ E(S.skel)) :
    Graph.edgeArc (d.splitDrawing R earDraw) f = Graph.edgeArc R.drawing f := by
  rw [Graph.edgeArc, Graph.edgeArc, splitDrawing_of_mem_skel hf]

theorem edgeArc_splitDrawing_of_mem_ear {f : γ} (hf : f ∈ E(d.ear)) :
    Graph.edgeArc (d.splitDrawing R earDraw) f = Graph.edgeArc earDraw f := by
  rw [Graph.edgeArc, Graph.edgeArc, splitDrawing_of_mem_ear hf]

namespace EarCrosscut

variable (hE : d.EarCrosscut R earPos earDraw)

include hE

/-- The skeleton of the split structure, drawn: the old drawn skeleton with the drawn ear
glued on. -/
theorem splitGraph_eq :
    (S.splitFace d).skel.map (d.splitPos R earPos) = R.graph.union (d.earGraph earPos) := by
  change (S.skel.union d.ear).map (d.splitPos R earPos) = _
  rw [Graph.map_union]
  congr 1
  · exact Graph.map_eq_of_eqOn fun z hz => hE.splitPos_eq hz
  · exact Graph.map_eq_of_eqOn fun z hz => splitPos_of_mem_ear hz

/-- **The old drawn skeleton with the drawn ear glued on is a plane graph.** The three clauses
of `Graph.IsDrawing` all reduce, on a mixed pair, to the same fact: the ear meets the old
drawing only at its two ends, because its interior lies in an open 2-cell and an open 2-cell
misses the drawn skeleton. -/
theorem isDrawing_split :
    Graph.IsDrawing (R.graph.union (d.earGraph earPos)) (d.splitDrawing R earDraw) := by
  have hEskel : E(R.graph) = E(S.skel) := Realization.edgeSet_graph R
  have hcompat : R.graph.Compatible (d.earGraph earPos) :=
    Graph.Compatible.of_disjoint_edgeSet (by
      rw [hEskel, d.edgeSet_earGraph]; exact d.disjoint_edgeSet)
  have hle₁ : R.graph ≤ R.graph.union (d.earGraph earPos) := Graph.left_le_union _ _
  have hle₂ : d.earGraph earPos ≤ R.graph.union (d.earGraph earPos) := hcompat.right_le_union
  have hmeet := hE.earSet_inter_skeletonSet
  have hends : ∀ {x : Plane}, x ∈ ({R.pos d.source, R.pos d.target} : Set Plane) →
      x ∈ V(R.graph) ∧ x ∈ V(d.earGraph earPos) := by
    rintro x (rfl | rfl)
    · exact ⟨by rw [Realization.vertexSet_graph]; exact ⟨_, d.source_mem_skel, rfl⟩,
        by rw [d.vertexSet_earGraph]; exact ⟨d.source, d.source_mem_ear, hE.pos_source⟩⟩
    · exact ⟨by rw [Realization.vertexSet_graph]; exact ⟨_, d.target_mem_skel, rfl⟩,
        by rw [d.vertexSet_earGraph]; exact ⟨d.target, d.target_mem_ear, hE.pos_target⟩⟩
  have hcross : ∀ {x : Plane}, x ∈ d.earSet earPos earDraw → x ∈ R.skeletonSet →
      x ∈ V(R.graph) ∧ x ∈ V(d.earGraph earPos) := fun hx hx' => hends (hmeet ⟨hx, hx'⟩)
  have hmix : ∀ {p : Plane} {e g : γ}, e ∈ E(S.skel) → g ∈ E(d.ear) →
      p ∈ Graph.edgeArc R.drawing e → p ∈ Graph.edgeArc earDraw g →
      p ∈ V(R.graph.union (d.earGraph earPos)) ∧
        (R.graph.union (d.earGraph earPos)).Inc e p ∧
        (R.graph.union (d.earGraph earPos)).Inc g p := by
    intro p e g he hg hpe hpg
    have hp1 : p ∈ R.skeletonSet :=
      Graph.edgeArc_subset_pointSet (by rwa [hEskel]) hpe
    have hp2 : p ∈ d.earSet earPos earDraw := edgeArc_subset_earSet hg hpg
    obtain ⟨hpV1, hpV2⟩ := hcross hp2 hp1
    obtain ⟨a, b, hlab⟩ := Graph.exists_isLink_of_mem_edgeSet (show e ∈ E(R.graph) by rwa [hEskel])
    obtain ⟨c, c', hlcc⟩ := Graph.exists_isLink_of_mem_edgeSet
      (show g ∈ E(d.earGraph earPos) by rwa [d.edgeSet_earGraph])
    have hInc1 : R.graph.Inc e p := by
      rcases R.isDrawing.vertex_mem_edgeArc hlab hpV1 hpe with rfl | rfl
      exacts [hlab.inc_left, hlab.inc_right]
    have hInc2 : (d.earGraph earPos).Inc g p := by
      rcases hE.isDrawing.vertex_mem_edgeArc hlcc hpV2 hpg with rfl | rfl
      exacts [hlcc.inc_left, hlcc.inc_right]
    exact ⟨Or.inl hpV1, hInc1.mono hle₁, hInc2.mono hle₂⟩
  refine ⟨?_, ?_, ?_⟩
  · -- each edge is drawn by its own parametrization
    intro e he
    rcases he with he | he
    · rw [hEskel] at he
      obtain ⟨hc, hi, hl⟩ := R.isDrawing.edge_param (by rwa [Graph.edgeSet_map])
      rw [splitDrawing_of_mem_skel he]
      exact ⟨hc, hi, Graph.union_isLink.2 (Or.inl hl)⟩
    · rw [d.edgeSet_earGraph] at he
      obtain ⟨hc, hi, hl⟩ := hE.isDrawing.edge_param (by rwa [d.edgeSet_earGraph])
      rw [splitDrawing_of_mem_ear he]
      exact ⟨hc, hi, Graph.union_isLink.2
        (Or.inr ⟨by rw [hEskel]; exact Set.disjoint_right.1 d.disjoint_edgeSet he, hl⟩)⟩
  · -- an edge's arc meets the vertices only at its own ends
    intro e x y v hl hv hmem
    rcases Graph.union_isLink.1 hl with hl | ⟨-, hl⟩
    · have he : e ∈ E(S.skel) := by rw [← hEskel]; exact hl.edge_mem
      rw [edgeArc_splitDrawing_of_mem_skel he] at hmem
      have hvg : v ∈ V(R.graph) := by
        rcases hv with hv | hv
        · exact hv
        · exact (hcross (Graph.vertexSet_subset_pointSet hv)
            (Graph.edgeArc_subset_pointSet (by rwa [hEskel]) hmem)).1
      exact R.isDrawing.vertex_mem_edgeArc hl hvg hmem
    · have he : e ∈ E(d.ear) := by rw [← d.edgeSet_earGraph]; exact hl.edge_mem
      rw [edgeArc_splitDrawing_of_mem_ear he] at hmem
      have hvg : v ∈ V(d.earGraph earPos) := by
        rcases hv with hv | hv
        · exact (hcross (edgeArc_subset_earSet he hmem)
            (Graph.vertexSet_subset_pointSet hv)).2
        · exact hv
      exact hE.isDrawing.vertex_mem_edgeArc hl hvg hmem
  · -- two distinct edges meet only at shared vertices
    intro e f he hf hef p hpe hpf
    rcases he with he | he <;> rcases hf with hf | hf
    · rw [hEskel] at he hf
      rw [edgeArc_splitDrawing_of_mem_skel he] at hpe
      rw [edgeArc_splitDrawing_of_mem_skel hf] at hpf
      obtain ⟨hpV, hIe, hIf⟩ := R.isDrawing.edge_inter (by rwa [Graph.edgeSet_map])
        (by rwa [Graph.edgeSet_map]) hef hpe hpf
      exact ⟨Or.inl hpV, hIe.mono hle₁, hIf.mono hle₁⟩
    · rw [hEskel] at he
      rw [d.edgeSet_earGraph] at hf
      rw [edgeArc_splitDrawing_of_mem_skel he] at hpe
      rw [edgeArc_splitDrawing_of_mem_ear hf] at hpf
      exact hmix he hf hpe hpf
    · rw [d.edgeSet_earGraph] at he
      rw [hEskel] at hf
      rw [edgeArc_splitDrawing_of_mem_ear he] at hpe
      rw [edgeArc_splitDrawing_of_mem_skel hf] at hpf
      obtain ⟨hv, h1, h2⟩ := hmix hf he hpf hpe
      exact ⟨hv, h2, h1⟩
    · rw [d.edgeSet_earGraph] at he hf
      rw [edgeArc_splitDrawing_of_mem_ear he] at hpe
      rw [edgeArc_splitDrawing_of_mem_ear hf] at hpf
      obtain ⟨hpV, hIe, hIf⟩ := hE.isDrawing.edge_inter (by rwa [d.edgeSet_earGraph])
        (by rwa [d.edgeSet_earGraph]) hef hpe hpf
      exact ⟨Or.inr hpV, hIe.mono hle₂, hIf.mono hle₂⟩

end EarCrosscut

/-- **The frontier of the old open 2-cell is the union of its two realized boundary paths.**
`SplitData.sub_face` says which cells lie below the split 2-cell, and assertion (i) turns the
union of those open cells into the topological frontier. -/
theorem frontier_cell_face {D : Set Plane} (hcd : R.IsCellDecomposition D)
    (hJ : R.IsFaceJordan) :
    frontier (R.cell d.face) = R.cellUnion d.cells₁ ∪ R.cellUnion d.cells₂ := by
  rw [← hJ.faceBoundary_eq hcd d.face_mem, Realization.faceBoundary, d.subcells_face_diff,
    Realization.cellUnion_union]

theorem pos_source_mem_cellUnion_cells₁ : R.pos d.source ∈ R.cellUnion d.cells₁ :=
  Realization.cell_subset_cellUnion d.source_mem_cells₁
    (by rw [R.cell_vertex d.source_mem_skel]; rfl)

theorem pos_source_mem_cellUnion_cells₂ : R.pos d.source ∈ R.cellUnion d.cells₂ :=
  Realization.cell_subset_cellUnion d.source_mem_cells₂
    (by rw [R.cell_vertex d.source_mem_skel]; rfl)

theorem pos_target_mem_cellUnion_cells₁ : R.pos d.target ∈ R.cellUnion d.cells₁ :=
  Realization.cell_subset_cellUnion d.target_mem_cells₁
    (by rw [R.cell_vertex d.target_mem_skel]; rfl)

theorem pos_target_mem_cellUnion_cells₂ : R.pos d.target ∈ R.cellUnion d.cells₂ :=
  Realization.cell_subset_cellUnion d.target_mem_cells₂
    (by rw [R.cell_vertex d.target_mem_skel]; rfl)

/-- **A realized boundary path is a simple arc between the ear's two ends.** -/
theorem isArcBetween_cellUnion_cells₁ :
    IsArcBetween (R.cellUnion d.cells₁) (R.pos d.source) (R.pos d.target) := by
  rw [cells₁, R.cellUnion_pathCells d.isPath₁.isWalk]
  exact R.isDrawing.isArcBetween_walkPointSet (d.isPath₁.map R.injOn_pos)
    (fun h => d.source_ne_target (R.injOn_pos d.source_mem_skel d.target_mem_skel h))

theorem isArcBetween_cellUnion_cells₂ :
    IsArcBetween (R.cellUnion d.cells₂) (R.pos d.source) (R.pos d.target) := by
  rw [cells₂, R.cellUnion_pathCells d.isPath₂.isWalk]
  exact R.isDrawing.isArcBetween_walkPointSet (d.isPath₂.map R.injOn_pos)
    (fun h => d.source_ne_target (R.injOn_pos d.source_mem_skel d.target_mem_skel h))

/-- **The two boundary paths cut the old 2-cell's boundary curve in two.**

This is where `SplitData.paths_meet` is spent, and it is the only place: `paths_disjoint` alone
forbids the two paths a common *edge* but not a common interior *vertex*, and with a common
interior vertex the two realized paths meet in more than the two cut points. See the module
docstring. -/
theorem isCutPair_of_inter {D : Set Plane} (hcd : R.IsCellDecomposition D)
    (hJ : R.IsFaceJordan) :
    IsCutPair (frontier (R.cell d.face)) (R.pos d.source) (R.pos d.target)
      (R.cellUnion d.cells₁) (R.cellUnion d.cells₂) where
  fst := isArcBetween_cellUnion_cells₁
  snd := isArcBetween_cellUnion_cells₂
  union_eq := (frontier_cell_face hcd hJ).symm
  inter_eq := by
    refine Set.Subset.antisymm (fun x ⟨hx₁, hx₂⟩ => ?_) ?_
    · obtain ⟨σ, hσ, hxσ⟩ := Realization.mem_cellUnion_iff.1 hx₁
      obtain ⟨τ, hτ, hxτ⟩ := Realization.mem_cellUnion_iff.1 hx₂
      have hστ : σ = τ := by
        by_contra hne
        exact Set.disjoint_left.1
          (hcd.disjoint (d.cells₁_subset hσ) (d.cells₂_subset hτ) hne) hxσ hxτ
      subst hστ
      have hmem : σ ∈ ({d.source, d.target} : Set γ) := d.paths_meet ▸ ⟨hσ, hτ⟩
      rcases hmem with rfl | rfl
      · rw [R.cell_vertex d.source_mem_skel] at hxσ
        exact Or.inl hxσ
      · rw [R.cell_vertex d.target_mem_skel] at hxσ
        exact Or.inr hxσ
    · rintro x (rfl | rfl)
      exacts [⟨pos_source_mem_cellUnion_cells₁, pos_source_mem_cellUnion_cells₂⟩,
        ⟨pos_target_mem_cellUnion_cells₁, pos_target_mem_cellUnion_cells₂⟩]

namespace EarCrosscut

variable (hE : d.EarCrosscut R earPos earDraw)

include hE

/-- The drawn ear is a path graph in the plane. -/
theorem isPathGraph_earGraph :
    (d.earGraph earPos).IsPathGraph (R.pos d.source) d.earWalk (R.pos d.target) := by
  have := d.isPathGraph.map hE.injOn
  rwa [hE.pos_source, hE.pos_target] at this

/-- **The drawn ear is a simple arc between the two old 0-cells it is glued to.** -/
theorem isArcBetween_earSet :
    IsArcBetween (d.earSet earPos earDraw) (R.pos d.source) (R.pos d.target) :=
  hE.isDrawing.isArcBetween_pointSet hE.isPathGraph_earGraph source_ne_target_pos

/-- **The drawn ear is a crosscut of the old Jordan face.** -/
theorem isCrosscut_earSet {D : Set Plane} (hcd : R.IsCellDecomposition D)
    (hJ : R.IsFaceJordan) :
    IsCrosscut (frontier (R.cell d.face)) (d.earSet earPos earDraw)
      (R.pos d.source) (R.pos d.target) where
  curve := hJ.isJordanCurve d.face_mem
  arc := hE.isArcBetween_earSet
  polygonal := hE.polygonal
  left_mem := (frontier_cell_face hcd hJ) ▸ Or.inl pos_source_mem_cellUnion_cells₁
  right_mem := (frontier_cell_face hcd hJ) ▸ Or.inl pos_target_mem_cellUnion_cells₁
  sdiff_subset := by
    rw [← hJ.cell_eq_inside d.face_mem]
    exact hE.subset_face

/-- The closure of an ear edge's open arc is the closed arc. -/
theorem closure_edgeArc_diff {f a b : γ} (hl : d.ear.IsLink f a b) :
    closure (Graph.edgeArc earDraw f \ {earPos a, earPos b}) = Graph.edgeArc earDraw f := by
  have harc : IsArcBetween (Graph.edgeArc earDraw f) (earPos a) (earPos b) :=
    hE.isDrawing.edge_isArcBetween (hl.map earPos)
  refine Set.Subset.antisymm (closure_minimal Set.sdiff_subset harc.isArc.isCompact.isClosed) ?_
  intro x hx
  by_cases hxab : x ∈ ({earPos a, earPos b} : Set Plane)
  · rcases hxab with rfl | rfl
    exacts [harc.left_mem_closure_diff, harc.right_mem_closure_diff]
  · exact subset_closure ⟨hx, hxab⟩

end EarCrosscut

/-! ## The realization -/

/-- **The realization of a 2-cell split.**

The old realization `R`, a drawing of the ear as a polygonal crosscut of the old open 2-cell,
and assertion (i) at the old stage produce a realization of `S.splitFace d`:

* the ear's interior 0-cells go where the ear's drawing puts them, and its 1-cells to their
  open arcs;
* the two new 2-cells go to the two sides of the crosscut, `inside (Bᵢ ∪ P)`;
* every surviving cell keeps its old point set.

This is the object the whole split step of `lem:cellulation-invariants` was missing:
`SplitData.isCrosscutSplit_realize` puts it in the relation `IsCrosscutSplit` to `R`, and
`IsCrosscutSplit.isCellDecomposition_and_isFaceJordan` then propagates both invariants. -/
noncomputable def realize (R : S.Realization) (d : S.SplitData) (earPos : γ → Plane)
    (earDraw : γ → ℝ → Plane) (hE : d.EarCrosscut R earPos earDraw) :
    (S.splitFace d).Realization where
  pos := d.splitPos R earPos
  drawing := d.splitDrawing R earDraw
  injOn_pos := by
    have hsep : ∀ ⦃x y : γ⦄, x ∈ V(S.skel) → y ∈ V(d.ear) → y ∉ V(S.skel) →
        d.splitPos R earPos x ≠ d.splitPos R earPos y := by
      intro x y hx hy hyn hxy
      rw [hE.splitPos_eq hx, splitPos_of_mem_ear hy] at hxy
      have h1 : R.pos x ∈ R.cell d.face := by
        rw [hxy]
        exact hE.earPos_mem_cell_face hy (fun h => hyn (h ▸ d.source_mem_skel))
          (fun h => hyn (h ▸ d.target_mem_skel))
      have h2 : R.pos x ∈ R.skeletonSet :=
        Graph.vertexSet_subset_pointSet (by rw [Realization.vertexSet_graph]; exact ⟨x, hx, rfl⟩)
      exact Set.disjoint_left.1 hE.disjoint_skeleton h1 h2
    intro x hx y hy hxy
    have hx' : x ∈ V(S.skel) ∪ V(d.ear) := hx
    have hy' : y ∈ V(S.skel) ∪ V(d.ear) := hy
    rcases hx' with hxs | hxe <;> rcases hy' with hys | hye
    · rw [hE.splitPos_eq hxs, hE.splitPos_eq hys] at hxy
      exact R.injOn_pos hxs hys hxy
    · by_cases hyy : y ∈ V(S.skel)
      · rw [hE.splitPos_eq hxs, hE.splitPos_eq hyy] at hxy
        exact R.injOn_pos hxs hyy hxy
      · exact absurd hxy (hsep hxs hye hyy)
    · by_cases hxx : x ∈ V(S.skel)
      · rw [hE.splitPos_eq hxx, hE.splitPos_eq hys] at hxy
        exact R.injOn_pos hxx hys hxy
      · exact absurd hxy.symm (hsep hys hxe hxx)
    · rw [splitPos_of_mem_ear hxe, splitPos_of_mem_ear hye] at hxy
      exact hE.injOn hxe hye hxy
  isDrawing := by
    rw [hE.splitGraph_eq]
    exact hE.isDrawing_split
  cell := d.splitCell R earPos earDraw
  cell_vertex := by
    intro v hv
    have hv' : v ∈ V(S.skel) ∪ V(d.ear) := hv
    rcases hv' with hv' | hv'
    · rw [splitCell_of_mem_cells (S.mem_cells_of_mem_vertexSet hv'), R.cell_vertex hv',
        hE.splitPos_eq hv']
    · rw [hE.splitCell_earVertex hv', splitPos_of_mem_ear hv']
  cell_edge := by
    intro e x y hl
    have hl' : (S.skel.union d.ear).IsLink e x y := hl
    rcases Graph.union_isLink.1 hl' with hk | ⟨-, hk⟩
    · rw [splitCell_of_mem_cells (S.mem_cells_of_mem_edgeSet hk.edge_mem), R.cell_edge hk,
        edgeArc_splitDrawing_of_mem_skel hk.edge_mem, hE.splitPos_eq hk.left_mem,
        hE.splitPos_eq hk.right_mem]
    · rw [splitCell_earEdge hk.edge_mem, hE.edgeArc_diff hk,
        edgeArc_splitDrawing_of_mem_ear hk.edge_mem, splitPos_of_mem_ear hk.left_mem,
        splitPos_of_mem_ear hk.right_mem]

variable (hE : d.EarCrosscut R earPos earDraw)

@[simp] theorem realize_pos : (realize R d earPos earDraw hE).pos = d.splitPos R earPos := rfl

@[simp] theorem realize_drawing :
    (realize R d earPos earDraw hE).drawing = d.splitDrawing R earDraw := rfl

@[simp] theorem realize_cell :
    (realize R d earPos earDraw hE).cell = d.splitCell R earPos earDraw := rfl

include hE

/-- **The realized ear is the drawn ear.** The open cells of the ear together with the two old
0-cells at its ends occupy exactly the crosscut. -/
theorem cellUnion_earCells :
    (realize R d earPos earDraw hE).cellUnion d.earCells = d.earSet earPos earDraw := by
  refine Set.Subset.antisymm (Realization.cellUnion_subset fun σ hσ => ?_) ?_
  · have hσ' : σ ∈ V(d.ear) ∪ E(d.ear) := hσ
    rcases hσ' with hσ' | hσ'
    · rw [realize_cell, hE.splitCell_earVertex hσ']
      exact Set.singleton_subset_iff.2 (EarCrosscut.mem_earSet_of_mem_ear hσ')
    · rw [realize_cell, splitCell_earEdge hσ']
      exact Set.Subset.trans Set.sdiff_subset (EarCrosscut.edgeArc_subset_earSet hσ')
  · intro x hx
    have hx' : x ∈ V(d.earGraph earPos) ∪
        ⋃ e ∈ E(d.earGraph earPos), Graph.edgeArc earDraw e := hx
    by_cases hxv : x ∈ earPos '' V(d.ear)
    · obtain ⟨z, hz, rfl⟩ := hxv
      refine Realization.cell_subset_cellUnion (Set.mem_union_left _ hz) ?_
      rw [realize_cell, hE.splitCell_earVertex hz]
      rfl
    · rcases hx' with hx' | hx'
      · rw [d.vertexSet_earGraph] at hx'
        exact absurd hx' hxv
      · obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 hx'
        rw [d.edgeSet_earGraph] at hf
        refine Realization.cell_subset_cellUnion (Set.mem_union_right _ hf) ?_
        rw [realize_cell, splitCell_earEdge hf]
        exact ⟨hxf, hxv⟩

/-- **The open cells the ear creates are the crosscut minus its two endpoints.** -/
theorem cellUnion_earNewCells :
    (realize R d earPos earDraw hE).cellUnion d.earNewCells =
      d.earSet earPos earDraw \ {R.pos d.source, R.pos d.target} := by
  refine Set.Subset.antisymm (Realization.cellUnion_subset fun σ hσ => ?_) ?_
  · have hσ' : σ ∈ (V(d.ear) \ {d.source, d.target}) ∪ E(d.ear) := hσ
    rcases hσ' with ⟨hσV, hσn⟩ | hσE
    · rw [realize_cell, hE.splitCell_earVertex hσV]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσn
      push Not at hσn
      refine Set.singleton_subset_iff.2 ⟨EarCrosscut.mem_earSet_of_mem_ear hσV, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h)
      · exact hσn.1 (hE.injOn hσV d.source_mem_ear (h.trans hE.pos_source.symm))
      · exact hσn.2 (hE.injOn hσV d.target_mem_ear (h.trans hE.pos_target.symm))
    · rw [realize_cell, splitCell_earEdge hσE]
      rintro x ⟨hxa, hxv⟩
      refine ⟨EarCrosscut.edgeArc_subset_earSet hσE hxa, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact hxv ⟨d.source, d.source_mem_ear, hE.pos_source⟩
      · exact hxv ⟨d.target, d.target_mem_ear, hE.pos_target⟩
  · rintro x ⟨hx, hxn⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxn
    push Not at hxn
    have hx' : x ∈ V(d.earGraph earPos) ∪
        ⋃ e ∈ E(d.earGraph earPos), Graph.edgeArc earDraw e := hx
    by_cases hxv : x ∈ earPos '' V(d.ear)
    · obtain ⟨z, hz, rfl⟩ := hxv
      have hzs : z ≠ d.source := fun h => hxn.1 (by rw [h, hE.pos_source])
      have hzt : z ≠ d.target := fun h => hxn.2 (by rw [h, hE.pos_target])
      have hzmem : z ∈ V(d.ear) \ ({d.source, d.target} : Set γ) := by
        refine ⟨hz, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        push Not
        exact ⟨hzs, hzt⟩
      refine Realization.cell_subset_cellUnion (Set.mem_union_left _ hzmem) ?_
      rw [realize_cell, hE.splitCell_earVertex hz]
      rfl
    · rcases hx' with hx' | hx'
      · rw [d.vertexSet_earGraph] at hx'
        exact absurd hx' hxv
      · obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 hx'
        rw [d.edgeSet_earGraph] at hf
        refine Realization.cell_subset_cellUnion (Set.mem_union_right _ hf) ?_
        rw [realize_cell, splitCell_earEdge hf]
        exact ⟨hxf, hxv⟩

/-- **The constructed realization is a crosscut split of the old one** — every clause of
`SplitData.IsCrosscutSplit`, discharged.

Composed with `IsCrosscutSplit.isCellDecomposition_and_isFaceJordan` this is the whole
induction step of `lem:cellulation-invariants` over the second elementary operation. -/
theorem isCrosscutSplit_realize {D : Set Plane} (hcd : R.IsCellDecomposition D)
    (hJ : R.IsFaceJordan) :
    d.IsCrosscutSplit R (realize R d earPos earDraw hE) where
  cell_eq := fun _ hσ _ => splitCell_of_mem_cells hσ
  isCrosscut := by
    rw [cellUnion_earCells]
    exact hE.isCrosscut_earSet hcd hJ
  isCutPair := isCutPair_of_inter hcd hJ
  cell_face₁ := by rw [realize_cell, splitCell_face₁, cellUnion_earCells]
  cell_face₂ := by rw [realize_cell, splitCell_face₂, cellUnion_earCells]
  cellUnion_earNewCells := by rw [cellUnion_earNewCells, cellUnion_earCells]
  earNonempty := by
    intro σ hσ
    have hσ' : σ ∈ (V(d.ear) \ {d.source, d.target}) ∪ E(d.ear) := hσ
    rcases hσ' with ⟨hσV, -⟩ | hσE
    · rw [realize_cell, hE.splitCell_earVertex hσV]
      exact ⟨earPos σ, rfl⟩
    · obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet hσE
      rw [realize_cell, splitCell_earEdge hσE, hE.edgeArc_diff hl]
      exact (hE.isDrawing.edge_isArcBetween (hl.map earPos)).nonempty_diff
  earDisjoint := by
    intro σ τ hσ hτ hne
    have hσ' : σ ∈ (V(d.ear) \ {d.source, d.target}) ∪ E(d.ear) := hσ
    have hτ' : τ ∈ (V(d.ear) \ {d.source, d.target}) ∪ E(d.ear) := hτ
    rcases hσ' with ⟨hσV, -⟩ | hσE <;> rcases hτ' with ⟨hτV, -⟩ | hτE
    · rw [realize_cell, hE.splitCell_earVertex hσV, hE.splitCell_earVertex hτV]
      refine Set.disjoint_left.2 ?_
      rintro x rfl hx
      exact hne (hE.injOn hσV hτV (Set.mem_singleton_iff.1 hx))
    · rw [realize_cell, hE.splitCell_earVertex hσV, splitCell_earEdge hτE]
      refine Set.disjoint_left.2 ?_
      rintro x rfl hx
      exact hx.2 ⟨σ, hσV, rfl⟩
    · rw [realize_cell, splitCell_earEdge hσE, hE.splitCell_earVertex hτV]
      refine Set.disjoint_right.2 ?_
      rintro x rfl hx
      exact hx.2 ⟨τ, hτV, rfl⟩
    · rw [realize_cell, splitCell_earEdge hσE, splitCell_earEdge hτE]
      refine Set.disjoint_left.2 fun x hx hx' => hx.2 ?_
      have hmem := hE.isDrawing.edge_inter (by rwa [d.edgeSet_earGraph])
        (by rwa [d.edgeSet_earGraph]) hne hx.1 hx'.1
      rw [d.vertexSet_earGraph] at hmem
      exact hmem.1
  closure_earVertex := by
    intro z hz _ _
    rw [realize_cell, hE.splitCell_earVertex hz]
    exact closure_singleton
  closure_earEdge := by
    intro f a b hl
    have harc := hE.isDrawing.edge_isArcBetween (hl.map earPos)
    rw [realize_cell, splitCell_earEdge hl.edge_mem, hE.edgeArc_diff hl,
      hE.splitCell_earVertex hl.left_mem, hE.splitCell_earVertex hl.right_mem,
      hE.closure_edgeArc_diff hl]
    refine Set.Subset.antisymm (fun x hx => ?_) ?_
    · by_cases hxab : x ∈ ({earPos a, earPos b} : Set Plane)
      · rcases hxab with rfl | rfl
        exacts [Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]
      · exact Or.inl ⟨hx, hxab⟩
    · rintro x (hx | hx | hx)
      · exact hx.1
      · rw [Set.mem_singleton_iff.1 hx]
        exact harc.left_mem
      · rw [Set.mem_singleton_iff.1 hx]
        exact harc.right_mem

/-- **The induction step of `lem:cellulation-invariants` over the second elementary operation,
end to end.** From a realization of `S` satisfying assertions (i) and (vii) and a drawing of
the ear as a polygonal crosscut, a realization of `S.splitFace d` satisfying (i) and (vii),
refining it along `SplitData.parent`. -/
theorem isCellDecomposition_and_isFaceJordan_realize (hS : S.CombInvariants) {D : Set Plane}
    (hcd : R.IsCellDecomposition D) (hJ : R.IsFaceJordan) :
    (realize R d earPos earDraw hE).IsCellDecomposition D ∧
      (realize R d earPos earDraw hE).IsFaceJordan ∧
      (realize R d earPos earDraw hE).Refines R d.parent :=
  (isCrosscutSplit_realize hE hcd hJ).isCellDecomposition_and_isFaceJordan hS hcd hJ

end SplitData

end CellStructure

end Schoenflies
