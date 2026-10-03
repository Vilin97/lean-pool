/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.PaperIVCliqueTree.Characterization
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Gluing induced graph pieces along a retained clique

Both pieces are induced subgraphs of one graph, cover its vertices and have
no edges between their exclusive parts. Every edge of the shared clique is
retained. This is not the convention of clique sums allowing separator-edge
deletion. Edge accounting does not imply additivity of packing optima.
-/

public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A graph is the union of two induced pieces with a retained clique overlap. -/
structure CliqueGluing (G : SimpleGraph V) (A B : Finset V) : Prop where
  /-- The two pieces cover every vertex. -/
  cover : A ∪ B = Finset.univ
  /-- The shared vertices form a clique in the original graph. -/
  overlap_isClique : G.IsClique (↑(A ∩ B) : Set V)
  /-- No edge joins the two exclusive parts. -/
  no_cross : ∀ u ∈ A, u ∉ B → ∀ v ∈ B, v ∉ A → ¬ G.Adj u v

namespace CliqueGluing

variable {A B : Finset V} (h : G.CliqueGluing A B)

include h

/-- Every vertex belongs to at least one piece. -/
theorem mem_left_or_right (v : V) : v ∈ A ∨ v ∈ B := by
  have hv : v ∈ A ∪ B := h.cover.symm ▸ Finset.mem_univ v
  exact Finset.mem_union.mp hv

/-- All neighbours of a vertex exclusive to the left piece stay in that piece. -/
theorem neighbor_mem_left {u v : V} (hu : u ∈ A) (huB : u ∉ B)
    (huv : G.Adj u v) : v ∈ A := by
  rcases h.mem_left_or_right v with hv | hv
  · exact hv
  · by_contra hvA
    exact h.no_cross u hu huB v hv hvA huv

/-- Every edge is entirely contained in one of the induced pieces. -/
theorem edge_in_piece {u v : V} (huv : G.Adj u v) :
    (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B) := by
  by_cases huA : u ∈ A
  · by_cases huB : u ∈ B
    · exact (h.mem_left_or_right v).imp (fun hv => ⟨huA, hv⟩) (fun hv => ⟨huB, hv⟩)
    · exact Or.inl ⟨huA, h.neighbor_mem_left huA huB huv⟩
  · have huB := (h.mem_left_or_right u).resolve_left huA
    by_cases hvB : v ∈ B
    · exact Or.inr ⟨huB, hvB⟩
    · have hvA := (h.mem_left_or_right v).resolve_right hvB
      exact False.elim (h.no_cross v hvA hvB u huB huA huv.symm)

/-- Vertex accounting counts the overlap only once. -/
theorem card_vertices_add_overlap :
    Fintype.card V + (A ∩ B).card = A.card + B.card := by
  simpa only [h.cover, Finset.card_univ] using Finset.card_union_add_card_inter A B

end CliqueGluing

end SimpleGraph
