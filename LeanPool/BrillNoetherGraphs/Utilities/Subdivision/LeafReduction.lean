/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.LeafPruning

/-!
# One-step reduction across a degree-one vertex

`LeafPruning` identifies a graph with a degree-one vertex, up to a
Laplacian-preserving relabeling, with an explicit `LeafExtension.addLeaf` of
the graph obtained by deleting that vertex.  This file records the invariant
facts needed to use that construction recursively:

* deleting the leaf preserves genus;
* deleting the leaf preserves connectivity when the original graph is
  connected; and
* a recursive rank-one existence result on the smaller connected graph lifts
  to the original graph.

The last theorem is deliberately a one-step interface.  A global iteration
still needs a well-founded wrapper (for example, recursion on the number of
vertices) and a choice of a degree-one vertex at every nonterminal step.
-/

namespace Utilities.Certificate

open Finset

universe u v

namespace LaplacianEquiv

variable {G : CFGraph.{u}} {H : CFGraph.{v}}

/-- A Laplacian-preserving vertex equivalence preserves every vertex degree. -/
theorem vertexDegree_eq (equivalence : LaplacianEquiv G H) (x : G.V) :
    vertexDegree H (equivalence x) = vertexDegree G x := by
  unfold vertexDegree
  apply Fintype.sum_equiv equivalence.toEquiv.symm
  intro y
  simpa using
    equivalence.num_edges_eq x (equivalence.toEquiv.symm y)

/-- A Laplacian-preserving vertex equivalence preserves the edge count. -/
theorem cardEdges_eq (equivalence : LaplacianEquiv G H) :
    H.edges.card = G.edges.card := by
  have hDegrees :
      (∑ y : H.V, vertexDegree H y) =
        ∑ x : G.V, vertexDegree G x := by
    symm
    apply Fintype.sum_equiv equivalence.toEquiv
    intro x
    exact (equivalence.vertexDegree_eq x).symm
  rw [sum_vertex_degree_eq_twice_card_edges,
    sum_vertex_degree_eq_twice_card_edges] at hDegrees
  omega

/-- A Laplacian-preserving vertex equivalence preserves cyclomatic genus. -/
theorem genus_eq (equivalence : LaplacianEquiv G H) :
    genus H = genus G := by
  unfold genus
  rw [equivalence.cardEdges_eq]
  have hVertices : Fintype.card H.V = Fintype.card G.V :=
    Fintype.card_congr equivalence.toEquiv.symm
  rw [hVertices]

end LaplacianEquiv

namespace LeafReduction

open LeafExtension LeafPruning

variable (H : CFGraph.{u}) (root : H.V)

/-- If the graph obtained by adjoining a leaf is connected, then the original
graph was connected.  In the lifted cut, the new leaf is placed on the same
side as its root, so the new edge cannot witness the cut. -/
theorem graph_connected_of_addLeaf
    (hExtended : graphConnected (addLeaf H root)) :
    graphConnected H := by
  intro S hS
  let lifted : Finset (Option H.V) :=
    if root ∈ S then insert none (S.map Function.Embedding.some)
    else S.map Function.Embedding.some
  have some_mem_lifted (z : H.V) : some z ∈ lifted ↔ z ∈ S := by
    by_cases hRoot : root ∈ S
    · simp [lifted, hRoot, Finset.mem_map]
    · simp [lifted, hRoot, Finset.mem_map]
  have none_mem_lifted : none ∈ lifted ↔ root ∈ S := by
    by_cases hRoot : root ∈ S
    · simp [lifted, hRoot, Finset.mem_map]
    · simp [lifted, hRoot, Finset.mem_map]
  obtain ⟨x, y, hx, hy⟩ := hS
  have hxLifted : some x ∈ lifted := by
    exact (some_mem_lifted x).2 hx
  have hyLifted : some y ∉ lifted := by
    exact fun h => hy ((some_mem_lifted y).1 h)
  obtain ⟨v, hv, w, hw, hvw⟩ :=
    hExtended lifted ⟨some x, some y, hxLifted, hyLifted⟩
  cases v with
  | none =>
      have hRootMem : root ∈ S := none_mem_lifted.mp hv
      cases w with
      | none => exact (hw hv).elim
      | some z =>
          have hzRoot : z = root := by
            by_contra hzNe
            simp only [num_edges_none_some, if_neg hzNe] at hvw
            omega
          subst z
          exact (hw ((some_mem_lifted root).2 hRootMem)).elim
  | some a =>
      have haS : a ∈ S := (some_mem_lifted a).1 hv
      cases w with
      | none =>
          have hRootNotMem : root ∉ S :=
            fun hRoot => hw (none_mem_lifted.mpr hRoot)
          have haRoot : a = root := by
            by_contra haNe
            simp only [num_edges_some_none, if_neg haNe] at hvw
            omega
          subst a
          exact (hRootNotMem haS).elim
      | some b =>
          have hbS : b ∉ S := by
            exact fun hb => hw ((some_mem_lifted b).2 hb)
          exact ⟨a, haS, b, hbS, by simpa using hvw⟩

/-- Connectivity is equivalent before and after adjoining one leaf. -/
theorem graph_connected_addLeaf_iff :
    graphConnected (addLeaf H root) ↔ graphConnected H :=
  ⟨graph_connected_of_addLeaf H root,
    graph_connected_addLeaf H root⟩

variable (G : CFGraph.{u}) (leaf : G.V)

/-- Deleting one leaf removes exactly one vertex.  This is the decreasing
measure needed by a future well-founded pruning loop. -/
theorem card_vertices_deleteLeaf_add_one
    (hDegree : vertexDegree G leaf = 1) :
    Fintype.card (deleteLeaf G leaf hDegree).V + 1 =
      Fintype.card G.V := by
  have hCard :=
    Fintype.card_congr (vertexEquiv G leaf hDegree)
  change Fintype.card (Remaining G leaf) + 1 = Fintype.card G.V
  change Fintype.card G.V = Fintype.card (Option (Remaining G leaf)) at hCard
  simpa using hCard.symm

/-- The pruned graph is strictly smaller in its number of vertices. -/
theorem card_vertices_deleteLeaf_lt
    (hDegree : vertexDegree G leaf = 1) :
    Fintype.card (deleteLeaf G leaf hDegree).V <
      Fintype.card G.V := by
  rw [← card_vertices_deleteLeaf_add_one G leaf hDegree]
  omega

/-- Deleting a degree-one vertex preserves genus. -/
@[simp] theorem genus_deleteLeaf
    (hDegree : vertexDegree G leaf = 1) :
    genus (deleteLeaf G leaf hDegree) = genus G := by
  have hEquivGenus :=
    (laplacianEquivDeleteLeafAddLeaf G leaf hDegree).genus_eq
  simpa using hEquivGenus

/-- Deleting a degree-one vertex from a connected graph leaves a connected
graph.  No positive-genus assumption is required. -/
theorem graph_connected_deleteLeaf
    (hG : graphConnected G)
    (hDegree : vertexDegree G leaf = 1) :
    graphConnected (deleteLeaf G leaf hDegree) := by
  have hExtended :
      graphConnected
        (addLeaf (deleteLeaf G leaf hDegree)
          (rootInDeleteLeaf G leaf hDegree)) :=
    (laplacianEquivDeleteLeafAddLeaf G leaf hDegree).graphConnected hG
  exact graph_connected_of_addLeaf _ _ hExtended

/-- Under the exact degree-one hypothesis, connectivity is equivalent before
and after deleting the leaf. -/
theorem graph_connected_deleteLeaf_iff
    (hDegree : vertexDegree G leaf = 1) :
    graphConnected (deleteLeaf G leaf hDegree) ↔ graphConnected G := by
  constructor
  · intro hPruned
    have hExtended :=
      graph_connected_addLeaf
        (deleteLeaf G leaf hDegree) (rootInDeleteLeaf G leaf hDegree)
        hPruned
    exact
      (laplacianEquivDeleteLeafAddLeaf G leaf hDegree).graphConnected_iff.mpr
        hExtended
  · intro hG
    exact graph_connected_deleteLeaf G leaf hG hDegree

/-- One recursive leaf-pruning step for rank-one Brill--Noether existence.

The recursive continuation receives the smaller graph together with the two
invariants normally needed by a genus-fixed core classification. -/
theorem bnExists_rank_one_leafStep
    (hG : graphConnected G)
    (hDegree : vertexDegree G leaf = 1)
    {d : ℤ}
    (recursive :
      graphConnected (deleteLeaf G leaf hDegree) →
      genus (deleteLeaf G leaf hDegree) = genus G →
      BNExists (deleteLeaf G leaf hDegree) 1 d) :
    BNExists G 1 d := by
  apply bnExists_rank_one_of_deleteLeaf G leaf hG hDegree
  exact recursive
    (graph_connected_deleteLeaf G leaf hG hDegree)
    (genus_deleteLeaf G leaf hDegree)

/-- Genus-four specialization of the recursive leaf-removal step. -/
theorem bnExists_rank_one_degree_three_genus_four_leafStep
    (hG : graphConnected G)
    (hGenus : genus G = 4)
    (hDegree : vertexDegree G leaf = 1)
    (recursive :
      graphConnected (deleteLeaf G leaf hDegree) →
      genus (deleteLeaf G leaf hDegree) = 4 →
      BNExists (deleteLeaf G leaf hDegree) 1 3) :
    BNExists G 1 3 := by
  apply bnExists_rank_one_leafStep G leaf hG hDegree
  intro hConnected hSameGenus
  exact recursive hConnected (hSameGenus.trans hGenus)

/-- A rank-one existence theorem for connected leafless graphs of a fixed
genus automatically extends across every pendant tree.  This genus- and
degree-independent form is the pruning boundary needed by the
Atanasov--Ranganathan genus-five argument. -/
theorem bnExists_rank_one_of_leafless
    (targetGenus degree : ℤ)
    (terminal : ∀ H : CFGraph.{u},
      graphConnected H →
      genus H = targetGenus →
      (∀ vertex : H.V, vertexDegree H vertex ≠ 1) →
      BNExists H 1 degree)
    (G : CFGraph.{u})
    (hG : graphConnected G)
    (hGenus : genus G = targetGenus) :
    BNExists G 1 degree := by
  let statement : ℕ → Prop := fun bound =>
    ∀ H : CFGraph.{u},
      Fintype.card H.V = bound →
      graphConnected H →
      genus H = targetGenus →
      BNExists H 1 degree
  have recurse : ∀ bound, statement bound := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound inductionHypothesis =>
        intro H hCard hConnected hTargetGenus
        by_cases hLeaf : ∃ leaf : H.V, vertexDegree H leaf = 1
        · obtain ⟨leaf, hDegree⟩ := hLeaf
          apply bnExists_rank_one_leafStep H leaf hConnected hDegree
          intro hPrunedConnected hSameGenus
          have hPrunedGenus :
              genus (deleteLeaf H leaf hDegree) = targetGenus :=
            hSameGenus.trans hTargetGenus
          have hSmaller :
              Fintype.card (deleteLeaf H leaf hDegree).V < bound := by
            simpa [hCard] using
              card_vertices_deleteLeaf_lt H leaf hDegree
          exact inductionHypothesis
            (Fintype.card (deleteLeaf H leaf hDegree).V)
            hSmaller (deleteLeaf H leaf hDegree) rfl
            hPrunedConnected hPrunedGenus
        · apply terminal H hConnected hTargetGenus
          intro vertex hDegree
          exact hLeaf ⟨vertex, hDegree⟩
  exact recurse (Fintype.card G.V) G rfl hG hGenus

/-- A theorem for connected leafless genus-four graphs automatically extends
to every connected genus-four graph.  The recursion is internal and uses only
the strictly decreasing vertex count of `deleteLeaf`; callers never need to
choose or expose a globally pruned graph. -/
theorem bnExists_rank_one_degree_three_genus_four_of_leafless
    (terminal : ∀ H : CFGraph.{u},
      graphConnected H →
      genus H = 4 →
      (∀ vertex : H.V, vertexDegree H vertex ≠ 1) →
      BNExists H 1 3)
    (G : CFGraph.{u})
    (hG : graphConnected G)
    (hGenus : genus G = 4) :
    BNExists G 1 3 := by
  exact bnExists_rank_one_of_leafless 4 3 terminal G hG hGenus

end LeafReduction

end Utilities.Certificate
