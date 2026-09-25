/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.Basic

/-!
# Induced subgraphs

This module restricts a chip-firing graph to a nonempty finite set of vertices.
Raw edge occurrences are filtered before their endpoints are bundled into the
subtype, so parallel edges are retained without identification.
-/

open Multiset Finset

namespace Utilities

universe u

/-- The raw edges of `G` whose two endpoints belong to `S`. -/
private noncomputable def inducedEdges (G : CFGraph.{u}) (S : Finset G.V) :
    Multiset (G.V × G.V) := by
  classical
  exact G.edges.filter (fun edge => edge.1 ∈ S ∧ edge.2 ∈ S)

private def restrictInducedEdge (G : CFGraph.{u}) (S : Finset G.V) (edge : G.V × G.V)
    (hEdge : edge.1 ∈ S ∧ edge.2 ∈ S) :
    {v : G.V // v ∈ S} × {v : G.V // v ∈ S} :=
  (⟨edge.1, hEdge.1⟩, ⟨edge.2, hEdge.2⟩)

private theorem inducedEdges_all (G : CFGraph.{u}) (S : Finset G.V) :
    ∀ edge ∈ inducedEdges G S, edge.1 ∈ S ∧ edge.2 ∈ S := by
  classical
  intro edge hEdge
  exact (Multiset.mem_filter.mp hEdge).2

/-- The subgraph of `G` induced by the nonempty finite vertex set `S`. -/
noncomputable abbrev inducedSubgraph (G : CFGraph.{u}) (S : Finset G.V)
    (hS : S.Nonempty) : CFGraph where
  V := {v : G.V // v ∈ S}
  instNonempty := by
    rcases hS with ⟨v, hv⟩
    exact ⟨⟨v, hv⟩⟩
  edges := (inducedEdges G S).pmap (restrictInducedEdge G S)
    (inducedEdges_all G S)
  loopless := by
    classical
    intro vertex hMem
    rw [Multiset.mem_pmap] at hMem
    obtain ⟨edge, hEdge, hEq⟩ := hMem
    have hOriginal : edge ∈ G.edges :=
      (Multiset.mem_filter.mp hEdge).1
    have hFirst := congrArg (fun pair => pair.1.val) hEq
    have hSecond := congrArg (fun pair => pair.2.val) hEq
    have hLoop : edge = (vertex.val, vertex.val) := by
      apply Prod.ext
      · exact hFirst
      · exact hSecond
    rw [hLoop] at hOriginal
    exact G.loopless vertex.val hOriginal

@[simp] theorem inducedSubgraph_vertices (G : CFGraph.{u}) (S : Finset G.V)
    (hS : S.Nonempty) :
    (inducedSubgraph G S hS).V = {v : G.V // v ∈ S} := rfl

@[simp] theorem inducedSubgraph_edges (G : CFGraph.{u}) (S : Finset G.V)
    (hS : S.Nonempty) :
    (inducedSubgraph G S hS).edges =
      (inducedEdges G S).pmap (restrictInducedEdge G S) (inducedEdges_all G S) := rfl

/-- The inclusion of the induced vertex set into the original graph. -/
def inducedSubgraphInclusion (G : CFGraph.{u}) (S : Finset G.V)
    (hS : S.Nonempty) : (inducedSubgraph G S hS).V → G.V :=
  fun x => x.val

@[simp] theorem inducedSubgraphInclusion_apply (G : CFGraph.{u}) (S : Finset G.V)
    (hS : S.Nonempty) (x : (inducedSubgraph G S hS).V) :
    inducedSubgraphInclusion G S hS x = x.val := rfl

theorem inducedSubgraphInclusion_injective (G : CFGraph.{u}) (S : Finset G.V)
    (hS : S.Nonempty) : Function.Injective (inducedSubgraphInclusion G S hS) := by
  intro x y hxy
  exact Subtype.ext hxy

@[simp] theorem inducedSubgraph_edge_card (G : CFGraph.{u}) (S : Finset G.V)
    (hS : S.Nonempty) :
    (inducedSubgraph G S hS).edges.card = (inducedEdges G S).card := by
  simp [inducedSubgraph]

/-- The edge count of an induced subgraph is the number of ambient edge
occurrences whose two endpoints lie in the inducing set.  This public form is
useful for occurrence-level certificate calculations; in particular, it does
not pass through a set of endpoint pairs and therefore retains parallel
edges. -/
theorem inducedSubgraph_edge_card_eq_filter (G : CFGraph.{u})
    (S : Finset G.V) (hS : S.Nonempty) :
    (inducedSubgraph G S hS).edges.card =
      (G.edges.filter (fun edge => edge.1 ∈ S ∧ edge.2 ∈ S)).card := by
  rw [inducedSubgraph_edge_card]
  rfl

private theorem filter_inducedEdges_endpoints (G : CFGraph.{u}) (S : Finset G.V)
    (x y : {v : G.V // v ∈ S}) :
    (inducedEdges G S).filter
        (fun edge =>
          edge = (x.val, y.val) ∨ edge = (y.val, x.val)) =
      G.edges.filter
        (fun edge =>
          edge = (x.val, y.val) ∨ edge = (y.val, x.val)) := by
  classical
  rw [inducedEdges, Multiset.filter_filter]
  apply Multiset.filter_congr
  intro edge _hEdge
  constructor
  · intro h
    exact h.1
  · intro hEndpoints
    refine ⟨hEndpoints, ?_⟩
    rcases hEndpoints with hEndpoints | hEndpoints
    · rw [hEndpoints]
      exact ⟨x.property, y.property⟩
    · rw [hEndpoints]
      exact ⟨y.property, x.property⟩

/-- Inducing on `S` preserves edge multiplicities between vertices of `S`. -/
@[simp] theorem num_edges_inducedSubgraph (G : CFGraph.{u}) (S : Finset G.V)
    (hS : S.Nonempty) (x y : {v : G.V // v ∈ S}) :
    numEdges (inducedSubgraph G S hS) x y = numEdges G x.val y.val := by
  classical
  change
    ((Multiset.pmap (restrictInducedEdge G S) (inducedEdges G S)
      (inducedEdges_all G S)).filter
        (fun edge => edge = (x, y) ∨ edge = (y, x))).card =
      (G.edges.filter
        (fun edge => edge = (x.val, y.val) ∨ edge = (y.val, x.val))).card
  rw [Multiset.pmap_eq_map_attach, Multiset.filter_map, Multiset.card_map]
  have hFiltered :
      (inducedEdges G S).attach.filter
          (((fun edge : {v : G.V // v ∈ S} × {v : G.V // v ∈ S} =>
              edge = (x, y) ∨ edge = (y, x)) ∘
            (fun attached : {edge // edge ∈ inducedEdges G S} =>
              restrictInducedEdge G S attached.val
                (inducedEdges_all G S attached.val attached.property)))) =
        (inducedEdges G S).attach.filter
          (fun attached =>
            attached.val = (x.val, y.val) ∨
              attached.val = (y.val, x.val)) := by
    apply Multiset.filter_congr
    rintro ⟨⟨a, b⟩, hEdge⟩ _hAttached
    simp only [Function.comp_apply, restrictInducedEdge, Prod.mk.injEq,
      Subtype.ext_iff]
  rw [hFiltered]
  calc
    ((inducedEdges G S).attach.filter
        (fun attached =>
          attached.val = (x.val, y.val) ∨
            attached.val = (y.val, x.val))).card =
        ((inducedEdges G S).filter
          (fun edge =>
            edge = (x.val, y.val) ∨ edge = (y.val, x.val))).card := by
          simpa only [Multiset.card_map, Multiset.card_attach] using
            congrArg Multiset.card
              (Multiset.filter_attach (inducedEdges G S)
                (fun edge =>
                  edge = (x.val, y.val) ∨ edge = (y.val, x.val)))
    _ = _ := by rw [filter_inducedEdges_endpoints]

@[simp] theorem inducedSubgraph_vertex_card (G : CFGraph.{u}) (S : Finset G.V)
    (hS : S.Nonempty) :
    Fintype.card (inducedSubgraph G S hS).V = S.card := by
  exact Fintype.card_coe S

end Utilities
