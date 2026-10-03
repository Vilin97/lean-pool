/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.PaperIVCliqueTree.Gluing

/-!
# Exact edge accounting for clique gluing

All counts use Mathlib's induced graphs and literal edge finsets. The edges
in the overlap are counted twice by the pieces and once by the whole graph.
-/

public section

namespace SimpleGraph.CliqueGluing

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] {A B : Finset V} (h : G.CliqueGluing A B)

include h

/-- The ambient edge sets of the two induced pieces cover the graph edges. -/
theorem union_piece_edges :
    {e ∈ G.edgeFinset | e.toFinset ⊆ A} ∪
      {e ∈ G.edgeFinset | e.toFinset ⊆ B} = G.edgeFinset := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_union.mp he with he | he <;> exact (Finset.mem_filter.mp he).1
  · intro he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      rcases h.edge_in_piece huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · apply Finset.mem_union.mpr
        exact Or.inl (Finset.mem_filter.mpr ⟨he, by
          simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
            Finset.singleton_subset_iff] using And.intro hu hv⟩)
      · apply Finset.mem_union.mpr
        exact Or.inr (Finset.mem_filter.mpr ⟨he, by
          simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
            Finset.singleton_subset_iff] using And.intro hu hv⟩)

omit h in
/-- The common edges are exactly those induced by the overlap. -/
theorem inter_piece_edges :
    {e ∈ G.edgeFinset | e.toFinset ⊆ A} ∩
      {e ∈ G.edgeFinset | e.toFinset ⊆ B} =
        {e ∈ G.edgeFinset | e.toFinset ⊆ A ∩ B} := by
  ext e
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.subset_inter_iff]
  tauto

/-- Edge accounting in terms of the three literal induced subgraphs. -/
theorem card_edges_add_overlap :
    G.edgeFinset.card + (G.induce (↑(A ∩ B) : Set V)).edgeFinset.card =
      (G.induce (↑A : Set V)).edgeFinset.card +
        (G.induce (↑B : Set V)).edgeFinset.card := by
  have hc := Finset.card_union_add_card_inter
    {e ∈ G.edgeFinset | e.toFinset ⊆ A} {e ∈ G.edgeFinset | e.toFinset ⊆ B}
  rw [h.union_piece_edges, inter_piece_edges] at hc
  simpa only [SimpleGraph.card_filter_edgeFinset_toFinset_subset] using hc

/-- A retained clique overlap has exactly one edge per pair of distinct vertices. -/
theorem card_overlap_edges :
    (G.induce (↑(A ∩ B) : Set V)).edgeFinset.card = (A ∩ B).card.choose 2 := by
  classical
  have hc (H : SimpleGraph (↑(A ∩ B) : Set V)) [DecidableRel H.Adj] :
      H.edgeFinset.card = Nat.card H.edgeSet := by
    rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  rw [hc, G.induce_eq_top.mpr h.overlap_isClique]
  have ht := SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    (V := (↑(A ∩ B) : Set V))
  rw [hc] at ht
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using ht

/-- The clique-overlap form of inclusion-exclusion for graph edges. -/
theorem card_edges_add_choose_overlap :
    G.edgeFinset.card + (A ∩ B).card.choose 2 =
      (G.induce (↑A : Set V)).edgeFinset.card +
        (G.induce (↑B : Set V)).edgeFinset.card := by
  rw [← h.card_overlap_edges]
  exact h.card_edges_add_overlap

end SimpleGraph.CliqueGluing
