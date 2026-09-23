/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Graph.PathGraph
public import LeanPool.Schoenflies.Graph.Drawing
public import LeanPool.Schoenflies.Graph.TwoConnected

/-!
# Relabelling the edges of a multigraph

Mathlib's `Graph.map` changes vertex names and deliberately leaves edge names fixed.  The ear
construction needs the complementary operation: give the finitely many edges of an ambient path
fresh abstract cell names while retaining every vertex and every incidence.

The relabelling map only has to be injective on the graph's edge set.  Walks, paths, and path
graphs then push forward by mapping their edge lists.
-/

@[expose] public section

open Set
open Schoenflies
open unitInterval
open scoped Graph

namespace Graph

variable {α β δ : Type*} {G : Graph α β} {f : β → δ}

/-- Relabel every edge of `G` by a map injective on `E(G)`, without changing its vertices. -/
def relabelEdges (G : Graph α β) (f : β → δ) (hf : InjOn f E(G)) : Graph α δ where
  vertexSet := V(G)
  edgeSet := f '' E(G)
  IsLink d x y := ∃ e ∈ E(G), f e = d ∧ G.IsLink e x y
  isLink_symm := by
    intro d _
    constructor
    intro x y
    rintro ⟨e, he, rfl, hxy⟩
    exact ⟨e, he, rfl, hxy.symm⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro d x y v w ⟨e, he, hfe, hxy⟩ ⟨e', he', hfe', hvw⟩
    have heq : e = e' := hf he he' (hfe.trans hfe'.symm)
    exact hxy.left_eq_or_eq (heq ▸ hvw)
  edge_mem_iff_exists_isLink := by
    intro d
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
      exact ⟨x, y, e, he, rfl, hxy⟩
    · rintro ⟨x, y, e, he, rfl, -⟩
      exact ⟨e, he, rfl⟩
  left_mem_of_isLink := by
    rintro d x y ⟨e, -, -, hxy⟩
    exact hxy.left_mem

@[simp] theorem vertexSet_relabelEdges (G : Graph α β) (f : β → δ) (hf : InjOn f E(G)) :
    V(G.relabelEdges f hf) = V(G) := rfl

@[simp] theorem edgeSet_relabelEdges (G : Graph α β) (f : β → δ) (hf : InjOn f E(G)) :
    E(G.relabelEdges f hf) = f '' E(G) := rfl

@[simp] theorem relabelEdges_isLink (G : Graph α β) (f : β → δ) (hf : InjOn f E(G))
    (d : δ) (x y : α) :
    (G.relabelEdges f hf).IsLink d x y ↔
      ∃ e ∈ E(G), f e = d ∧ G.IsLink e x y :=
  Iff.rfl

/-- An old link survives after its edge receives its new name. -/
theorem IsLink.relabelEdges (hf : InjOn f E(G)) (h : G.IsLink e x y) :
    (G.relabelEdges f hf).IsLink (f e) x y :=
  ⟨e, h.edge_mem, rfl, h⟩

/-- Incidence in an edge-relabelled graph is exactly incidence of the uniquely represented
old edge. -/
theorem relabelEdges_inc (G : Graph α β) (f : β → δ) (hf : InjOn f E(G))
    (d : δ) (x : α) :
    (G.relabelEdges f hf).Inc d x ↔
      ∃ e ∈ E(G), f e = d ∧ G.Inc e x := by
  constructor
  · rintro ⟨y, e, he, hfe, hxy⟩
    exact ⟨e, he, hfe, y, hxy⟩
  · rintro ⟨e, he, rfl, y, hxy⟩
    exact ⟨y, hxy.relabelEdges hf⟩

/-- Relabelling an edge list does not change the vertices it covers. -/
theorem coveredVertices_relabelEdges (hf : InjOn f E(G)) {W : List β}
    (hW : ∀ e ∈ W, e ∈ E(G)) :
    (G.relabelEdges f hf).coveredVertices (W.map f) = G.coveredVertices W := by
  ext x
  constructor
  · rintro ⟨d, hd, y, hdy⟩
    obtain ⟨e, heW, rfl⟩ := List.mem_map.1 hd
    rcases hdy with ⟨g, hg, hge, hgy⟩
    have hgeq : g = e := hf hg (hW e heW) hge
    exact ⟨e, heW, y, hgeq ▸ hgy⟩
  · rintro ⟨e, heW, y, hey⟩
    exact ⟨f e, List.mem_map_of_mem heW, y, hey.relabelEdges hf⟩

/-- Relabelling a walk's edge list does not change its visited vertices. -/
theorem walkVertices_relabelEdges (hf : InjOn f E(G)) (u : α) {W : List β}
    (hW : ∀ e ∈ W, e ∈ E(G)) :
    (G.relabelEdges f hf).walkVertices u (W.map f) = G.walkVertices u W := by
  rw [walkVertices, walkVertices, coveredVertices_relabelEdges hf hW]

/-- A walk pushes forward along an injective relabelling of its edges. -/
theorem IsWalk.relabelEdges (hf : InjOn f E(G)) (h : G.IsWalk u W v) :
    (G.relabelEdges f hf).IsWalk u (W.map f) v := by
  induction h with
  | nil hx => exact .nil hx
  | cons hl _ ih => exact .cons (hl.relabelEdges hf) ih

/-- A path pushes forward along an injective relabelling of its edges. -/
theorem IsPath.relabelEdges (hf : InjOn f E(G)) (h : G.IsPath u W v) :
    (G.relabelEdges f hf).IsPath u (W.map f) v := by
  induction h with
  | nil hx => exact .nil hx
  | @cons u w v e W hl hW fresh ih =>
    refine .cons (hl.relabelEdges hf) ih ?_
    rw [walkVertices_relabelEdges hf w hW.isWalk.edgeSet_subset]
    exact fresh

/-- A graph which is exactly a path remains so after an injective edge relabelling. -/
theorem IsPathGraph.relabelEdges {P : Graph α β} (hf : InjOn f E(P))
    (h : P.IsPathGraph u W v) :
    (P.relabelEdges f hf).IsPathGraph u (W.map f) v where
  isPath := h.isPath.relabelEdges hf
  edgeSet_eq := by
    rw [edgeSet_relabelEdges, h.edgeSet_eq]
    ext d
    simp
  vertexSet_eq := by
    rw [vertexSet_relabelEdges, walkVertices_relabelEdges hf u h.isWalk.edgeSet_subset,
      h.vertexSet_eq]

/-- Relabelling preserves graph finiteness. -/
theorem Finite.relabelEdges [G.Finite] (hf : InjOn f E(G)) :
    (G.relabelEdges f hf).Finite where
  finite_vertexSet := by
    rw [vertexSet_relabelEdges]
    exact _root_.Graph.finite_vertexSet G
  finite_edgeSet := by
    rw [edgeSet_relabelEdges]
    exact (_root_.Graph.finite_edgeSet G).image f

/-- Relabelling preserves connectedness because every old walk pushes forward. -/
theorem Connected.relabelEdges (h : G.Connected) (hf : InjOn f E(G)) :
    (G.relabelEdges f hf).Connected := by
  constructor
  · simpa using h.nonempty
  · intro u hu v hv
    obtain ⟨W, hW⟩ := h.reaches (by simpa using hu) (by simpa using hv)
    exact ⟨W.map f, hW.relabelEdges hf⟩

/-- A walk surviving a vertex deletion still survives that deletion after edge relabelling. -/
theorem IsWalk.relabelEdges_deleteVerts {X : Set α} {u v : α} {W : List β}
    (hf : InjOn f E(G)) (h : (G.deleteVerts X).IsWalk u W v) :
    ((G.relabelEdges f hf).deleteVerts X).IsWalk u (W.map f) v := by
  induction h with
  | nil hx =>
      apply IsWalk.nil
      rw [vertexSet_deleteVerts, vertexSet_relabelEdges]
      simpa only [vertexSet_deleteVerts] using hx
  | cons hl hW ih =>
      apply IsWalk.cons _ ih
      rw [deleteVerts_isLink] at hl ⊢
      exact ⟨hl.1.relabelEdges hf, hl.2.1, hl.2.2⟩

/-- Edge relabelling preserves 2-connectivity, including connectedness after deleting any one
vertex. -/
theorem IsTwoConnected.relabelEdges (h : G.IsTwoConnected) (hf : InjOn f E(G)) :
    (G.relabelEdges f hf).IsTwoConnected where
  hasThreeVertices := by
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := h.hasThreeVertices
    exact ⟨a, by simpa, b, by simpa, c, by simpa, hab, hac, hbc⟩
  connected := h.connected.relabelEdges hf
  deleteVerts_connected := by
    intro x hx
    have hxG : x ∈ V(G) := by simpa using hx
    have hdel := h.deleteVerts_connected hxG
    constructor
    · simpa only [vertexSet_deleteVerts, vertexSet_relabelEdges] using hdel.nonempty
    · intro u hu v hv
      have huG : u ∈ V(G.deleteVerts {x}) := by
        simpa only [vertexSet_deleteVerts, vertexSet_relabelEdges] using hu
      have hvG : v ∈ V(G.deleteVerts {x}) := by
        simpa only [vertexSet_deleteVerts, vertexSet_relabelEdges] using hv
      obtain ⟨W, hW⟩ := hdel.reaches huG hvG
      exact ⟨W.map f, hW.relabelEdges_deleteVerts hf⟩

/-! ### Relabelling a drawing -/

section Drawing

variable {G : Graph Plane β} {drawing : β → ℝ → Plane}

/-- The drawing with its edge argument translated back through an injective relabelling. -/
noncomputable def relabelDrawing [Nonempty β] (G : Graph α β) (f : β → δ)
    (drawing : β → ℝ → Plane) : δ → ℝ → Plane :=
  fun d => drawing (Function.invFunOn f E(G) d)

@[simp] theorem relabelDrawing_apply [Nonempty β] (hf : InjOn f E(G))
    {e : β} (he : e ∈ E(G)) :
    relabelDrawing G f drawing (f e) = drawing e := by
  rw [relabelDrawing, hf.leftInvOn_invFunOn he]

theorem edgeArc_relabelDrawing [Nonempty β] (hf : InjOn f E(G))
    {e : β} (he : e ∈ E(G)) :
    edgeArc (relabelDrawing G f drawing) (f e) = edgeArc drawing e := by
  change relabelDrawing G f drawing (f e) '' I = drawing e '' I
  rw [relabelDrawing_apply hf he]

/-- Edge relabelling changes neither the occupied point set nor any geometric edge arc. -/
theorem pointSet_relabelEdges [Nonempty β] (hf : InjOn f E(G)) :
    pointSet (G.relabelEdges f hf) (relabelDrawing G f drawing) = pointSet G drawing := by
  rw [pointSet, pointSet, vertexSet_relabelEdges, edgeSet_relabelEdges]
  congr 1
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun d hd => ?_
    obtain ⟨e, he, rfl⟩ := hd
    rw [edgeArc_relabelDrawing hf he]
    intro x hx
    exact Set.mem_iUnion₂_of_mem he hx
  · refine Set.iUnion₂_subset fun e he => ?_
    rw [← edgeArc_relabelDrawing hf he]
    intro x hx
    exact Set.mem_iUnion₂_of_mem (show f e ∈ f '' E(G) from ⟨e, he, rfl⟩) hx

/-- Injectively changing edge names preserves a plane drawing and all of its drawn arcs. -/
theorem IsDrawing.relabelEdges [Nonempty β] (h : IsDrawing G drawing)
    (hf : InjOn f E(G)) :
    IsDrawing (G.relabelEdges f hf) (relabelDrawing G f drawing) where
  edge_param := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := hd
    rw [relabelDrawing_apply hf he]
    obtain ⟨hc, hi, hlink⟩ := h.edge_param he
    exact ⟨hc, hi, hlink.relabelEdges hf⟩
  vertex_mem_edgeArc := by
    intro d x y v hlink hv hz
    rcases hlink with ⟨e, he, rfl, hxy⟩
    rw [edgeArc_relabelDrawing hf he] at hz
    exact h.vertex_mem_edgeArc hxy hv hz
  edge_inter := by
    intro d g hd hg hdg z hzd hzg
    obtain ⟨e, he, rfl⟩ := hd
    obtain ⟨e', he', rfl⟩ := hg
    rw [edgeArc_relabelDrawing hf he] at hzd
    rw [edgeArc_relabelDrawing hf he'] at hzg
    have hee' : e ≠ e' := fun hEq => hdg (congrArg f hEq)
    obtain ⟨hzV, ⟨x, hex⟩, ⟨y, he'y⟩⟩ := h.edge_inter he he' hee' hzd hzg
    exact ⟨hzV, ⟨x, hex.relabelEdges hf⟩, ⟨y, he'y.relabelEdges hf⟩⟩

end Drawing

end Graph
