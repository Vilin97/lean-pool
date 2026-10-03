/-
Copyright (c) 2026 Juan Pablo Traverso Giannini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Giannini
-/
module

public import LeanPool.PaperIVCliqueTree.TreeDecomposition
public import LeanPool.PaperIVCliqueTree.Characterization

/-!
# Subtree representations of chordal graphs

This module provides the chordal-to-subtree direction of Gavril's classical
characterization. It does not assert the converse for arbitrary families.
The empty connector joins components without changing vertex occurrences.
This constructor uses one extra host node; it does not claim a minimal or
maximal-clique-indexed host tree.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- An exact representation by nonempty connected vertex sets of a finite tree. -/
structure SubtreeRepresentation (G : SimpleGraph V) where
  /-- Vertices of the host tree. -/
  Node : Type
  [nodeFintype : Fintype Node]
  /-- The host tree. -/
  tree : SimpleGraph Node
  /-- The host is connected and acyclic. -/
  isTree : tree.IsTree
  /-- The subtree assigned to each graph vertex. -/
  subtree : V → Set Node
  /-- Every assigned subtree is connected, hence nonempty. -/
  connected : ∀ v, (tree.induce (subtree v)).Connected
  /-- Distinct vertices are adjacent exactly when their subtrees intersect. -/
  adjacency : ∀ u v, u ≠ v → (G.Adj u v ↔ (subtree u ∩ subtree v).Nonempty)

attribute [instance] SubtreeRepresentation.nodeFintype

/-- A clique forest supplies an exact subtree representation, even when disconnected. -/
noncomputable def CliqueTree.toSubtreeRepresentation {ι : Type} [Fintype ι]
    (T : G.CliqueTree ι) : SubtreeRepresentation G where
  Node := Option ι
  tree := T.connectorGraph
  isTree := T.connectorGraph_isTree
  subtree := fun v => {x | v ∈ T.connectorBag x}
  connected := T.vertexBagGraph_connected
  adjacency := fun u v hne => by
    constructor
    · intro huv
      obtain ⟨i, hui, hvi⟩ := T.exists_bag_of_adj huv
      exact ⟨some i, hui, hvi⟩
    · rintro ⟨i, hui, hvi⟩
      cases i with
      | none => exact (Finset.notMem_empty u hui).elim
      | some i => exact T.bag_isClique i hui hvi hne

variable {V : Type} {G : SimpleGraph V}

/-- Every finite chordal graph has a subtree representation on a finite host tree. -/
theorem IsChordal.nonempty_subtreeRepresentation [Finite V] (hG : G.IsChordal) :
    Nonempty (SubtreeRepresentation G) := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Classical.decRel G.Adj
  obtain ⟨ord, hord⟩ := hG.exists_isPEO
  exact ⟨hord.cliqueTree.toSubtreeRepresentation⟩

end SimpleGraph
