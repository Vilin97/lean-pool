/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — Yuster : the triangle hypergraph on the EDGE vertex type

Standalone, Mathlib-only. Fixes the encoding issue for applying `NibbleTheorem`: the nibble's bound
`|M| ≥ (1-β)·(Fintype.card W)/r` uses the full vertex-type cardinality, and `NearlyRegular` requires
every vertex active. So the triangle hypergraph must live on the vertex type of ACTUAL EDGES.

Edges are `2`-cliques, so the correct vertex type is `↥(G.cliqueFinset 2)` — a `Fintype` of
cardinality `|E(G)|`. The triangle hypergraph `triangleHypergraphSub` puts each triangle's three
edges (its `2`-subsets, all of which are `2`-cliques) as a hyperedge over this type. It is
`3`-uniform
and, crucially, `Fintype.card ↥(G.cliqueFinset 2) = |E(G)|`, so `NibbleTheorem` here yields a
triangle
packing of size `≥ (1-β)·|E(G)|/3`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Tactic.Bound

/-! # YusterEdgeType -/

public section

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **edge vertex type** of `G`: its edges, viewed as `2`-cliques. A `Fintype` of card
`|E(G)|`. -/
abbrev EdgeV : Type _ := {e : Finset V // e ∈ G.cliqueFinset 2}

/-- The edge vertex type has cardinality `|E(G)|` (the number of edges). -/
theorem card_EdgeV : Fintype.card (EdgeV G) = (G.cliqueFinset 2).card :=
  Fintype.card_coe _

/-- The **triangle hypergraph on the edge vertex type**: each triangle contributes the hyperedge of
its three edges (its `2`-subsets, lifted to the edge type). -/
@[expose] def triangleHypergraphSub : Finset (Finset (EdgeV G)) :=
  (G.cliqueFinset 3).image (fun t => (t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2))

/-- Every `2`-subset of a `3`-clique is a `2`-clique (an edge). -/
theorem powersetCard_two_subset_cliqueFinset {t : Finset V} (ht : G.IsNClique 3 t) :
    t.powersetCard 2 ⊆ G.cliqueFinset 2 := by
  intro e he
  rw [Finset.mem_powersetCard] at he
  rw [SimpleGraph.mem_cliqueFinset_iff]
  exact ⟨ht.isClique.subset he.1, he.2⟩

/-- **The edge-type triangle hypergraph is 3-uniform.** -/
theorem triangleHypergraphSub_uniform : IsUniform (triangleHypergraphSub G) 3 := by
  intro E hE
  rw [triangleHypergraphSub, Finset.mem_image] at hE
  obtain ⟨t, ht, rfl⟩ := hE
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht
  rw [Finset.card_subtype,
    Finset.filter_true_of_mem (fun e he => powersetCard_two_subset_cliqueFinset G ht he)]
  simp [Finset.card_powersetCard, ht.card_eq]

/-- **Codegree ≤ 1 on the edge-type triangle hypergraph.** Two distinct edges lie in at most one
common triangle. This is the (sharp) `CodegreeBounded` input for `NibbleTheorem` on the correct
vertex type. -/
theorem triangleHypergraphSub_codegree_le_one {E E' : EdgeV G} (hne : E ≠ E') :
    codegree (triangleHypergraphSub G) E E' ≤ 1 := by
  rw [codegree]
  have hvne : E.val ≠ E'.val := fun h => hne (Subtype.ext h)
  have key : ∀ T ∈ (triangleHypergraphSub G).filter (fun T => E ∈ T ∧ E' ∈ T),
      T = ((E.val ∪ E'.val).powersetCard 2).subtype (· ∈ G.cliqueFinset 2) := by
    intro T hT
    rw [Finset.mem_filter, triangleHypergraphSub, Finset.mem_image] at hT
    obtain ⟨⟨t, ht, rfl⟩, hET, hE'T⟩ := hT
    rw [SimpleGraph.mem_cliqueFinset_iff] at ht
    rw [Finset.mem_subtype] at hET hE'T
    rw [Finset.mem_powersetCard] at hET hE'T
    have hsub : E.val ∪ E'.val ⊆ t := Finset.union_subset hET.1 hE'T.1
    have hcard3 : (E.val ∪ E'.val).card = 3 := by
      have hle : (E.val ∪ E'.val).card ≤ 3 := (Finset.card_le_card hsub).trans ht.card_eq.le
      have hadd := Finset.card_union_add_card_inter E.val E'.val
      rw [hET.2, hE'T.2] at hadd
      have hinter : (E.val ∩ E'.val).card < 2 := by
        rcases Nat.lt_or_ge (E.val ∩ E'.val).card 2 with h | h
        · exact h
        · exfalso
          have h2 : (E.val ∩ E'.val).card = 2 :=
            le_antisymm ((Finset.card_le_card Finset.inter_subset_left).trans hET.2.le) h
          have hee : E.val ∩ E'.val = E.val :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hET.2, h2])
          have hee' : E.val ∩ E'.val = E'.val :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hE'T.2, h2])
          exact hvne (hee.symm.trans hee')
      omega
    have het : E.val ∪ E'.val = t :=
      Finset.eq_of_subset_of_card_le hsub (by rw [ht.card_eq, hcard3])
    rw [het]
  rw [Finset.card_le_one]
  intro T hT T' hT'
  rw [key T hT, key T' hT']

end Nibble.YusterE
