/-
Copyright (c) 2026 Juan Pablo Traverso Giannini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Giannini
-/
module

public import LeanPool.PaperIVCliqueTree.SubtreeHelly
public import LeanPool.PaperIVCliqueTree.TreeDecomposition
public import LeanPool.PaperIVCliqueTree.Characterization
import LeanPool.PaperIVCliqueTree.Helly

/-!
# Cliques in arbitrary tree decompositions and exact chordal treewidth

Helly applies to vertex-occurrence subtrees in any tree decomposition. This
gives the universal clique lower bound; the clique-forest adapter attains it
for finite chordal graphs. The successor form excludes the empty vertex type.
-/

public section

namespace Utilities.Treewidth

variable {V : Type*} {G : SimpleGraph V}

/-- Every finite clique is contained in one bag of any tree decomposition. -/
theorem TreeDecomposition.exists_clique_subset_bag (D : TreeDecomposition G)
    {K : Finset V} (hK : G.IsClique (K : Set V)) : ∃ t, K ⊆ D.bag t := by
  classical
  apply D.isTree.finite_subtree_helly K (fun v => {t | v ∈ D.bag t})
  · exact fun v _ => D.coherent v
  · intro v hv w hw
    rcases eq_or_ne v w with rfl | hne
    · obtain ⟨t, ht⟩ := D.cover_vertex v
      exact ⟨t, ht, ht⟩
    · obtain ⟨t, htv, htw⟩ := D.cover_edge v w (hK hv hw hne)
      exact ⟨t, htv, htw⟩

/-- Clique number is a lower bound on the largest bag of every decomposition. -/
theorem TreeDecomposition.cliqueNum_le_width_succ [Finite V]
    (D : TreeDecomposition G) : G.cliqueNum ≤ D.width + 1 := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨K, hK, hcard⟩ := G.exists_isNClique_cliqueNum
  obtain ⟨t, ht⟩ := D.exists_clique_subset_bag hK
  rw [← hcard]
  exact (Finset.card_le_card ht).trans (D.card_bag_le_width_succ t)

/-- Every finite graph has treewidth at least its clique number minus one. -/
theorem cliqueNum_le_treewidth_succ [Finite V] (G : SimpleGraph V) :
    G.cliqueNum ≤ treewidth G + 1 := by
  obtain ⟨D, hD⟩ := exists_treeDecomposition_width_eq_treewidth G
  exact hD ▸ D.cliqueNum_le_width_succ

end Utilities.Treewidth

namespace SimpleGraph

variable {V : Type} {G : SimpleGraph V}

/-- The clique decomposition of a finite nonempty chordal graph is optimal. -/
theorem IsChordal.exists_optimal_treeDecomposition [Finite V] [Nonempty V]
    (hG : G.IsChordal) :
    ∃ D : Utilities.Treewidth.TreeDecomposition G, D.width + 1 = G.cliqueNum := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Classical.decRel G.Adj
  obtain ⟨ord, hord⟩ := hG.exists_isPEO
  let T := hord.cliqueTree
  refine ⟨T.toTreeDecomposition, ?_⟩
  rw [T.toTreeDecomposition_width, ← T.cliqueNum_eq_sup_card_bag]
  have hpos : 0 < G.cliqueNum := by
    obtain ⟨v⟩ := ‹Nonempty V›
    have hcl : G.IsClique (({v} : Finset V) : Set V) := by simp
    have := hcl.card_le_cliqueNum
    simp only [Finset.card_singleton] at this
    omega
  omega

/-- Finite nonempty chordal graphs have treewidth exactly clique number minus one. -/
theorem IsChordal.treewidth_succ_eq_cliqueNum [Finite V] [Nonempty V]
    (hG : G.IsChordal) : Utilities.Treewidth.treewidth G + 1 = G.cliqueNum := by
  obtain ⟨D, hD⟩ := hG.exists_optimal_treeDecomposition
  apply le_antisymm
  · have h := Utilities.Treewidth.treewidth_le_width D
    omega
  · exact Utilities.Treewidth.cliqueNum_le_treewidth_succ G

end SimpleGraph
