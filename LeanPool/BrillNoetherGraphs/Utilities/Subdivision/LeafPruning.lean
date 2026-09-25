/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.LaplacianEquiv
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.LeafExtension

/-!
# Pruning a degree-one vertex

This is the structural inverse to `LeafExtension.addLeaf`.  From a vertex of
valence exactly one we construct the graph on the remaining subtype, identify
the unique neighbor, and exhibit the original graph as a `LaplacianEquiv` of
the corresponding explicit leaf extension.  The rank-one lifting theorem is
then an immediate composition of the two small certificate interfaces.
-/

namespace Utilities.Certificate

open Multiset Finset

universe u

namespace LeafPruning

variable (G : CFGraph.{u}) (leaf : G.V)

/-- The vertices remaining after deleting `leaf`. -/
abbrev Remaining := {x : G.V // x ≠ leaf}

/-! ## The unique neighbor of a degree-one vertex -/

structure LeafData where
  root : G.V
  count_root : numEdges G leaf root = 1
  count_other : ∀ x : G.V, x ≠ root → numEdges G leaf x = 0

theorem exists_leafData (hDegree : vertexDegree G leaf = 1) :
    Nonempty (LeafData G leaf) := by
  have hSumInt : ∑ x : G.V, (numEdges G leaf x : ℤ) = 1 := by
    simpa [vertexDegree] using hDegree
  have hSum : ∑ x : G.V, numEdges G leaf x = 1 := by
    exact_mod_cast hSumInt
  have hSumNe : ∑ x : G.V, numEdges G leaf x ≠ 0 := by
    omega
  obtain ⟨root, _hRootMem, hRootNe⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hSumNe
  have hRootPos : 0 < numEdges G leaf root :=
    Nat.pos_of_ne_zero hRootNe
  have hRootLe : numEdges G leaf root ≤
      ∑ x : G.V, numEdges G leaf x := by
    exact Finset.single_le_sum
      (fun x _ => Nat.zero_le (numEdges G leaf x)) (Finset.mem_univ root)
  have hRootOne : numEdges G leaf root = 1 := by omega
  refine ⟨⟨root, hRootOne, ?_⟩⟩
  intro x hx
  have hRootNeX : root ≠ x := fun h => hx h.symm
  have hPair :
      numEdges G leaf root + numEdges G leaf x ≤
        ∑ y : G.V, numEdges G leaf y := by
    have hSubset : ({root, x} : Finset G.V) ⊆ Finset.univ := by simp
    have hBound := Finset.sum_le_sum_of_subset_of_nonneg hSubset
      (fun y _hy _hnot => Nat.zero_le (numEdges G leaf y))
    simpa [Finset.sum_pair hRootNeX] using hBound
  omega

noncomputable def leafData (hDegree : vertexDegree G leaf = 1) :
    LeafData G leaf :=
  Classical.choice (exists_leafData G leaf hDegree)

noncomputable def root (hDegree : vertexDegree G leaf = 1) :
    Remaining G leaf :=
  ⟨(leafData G leaf hDegree).root, by
    intro hEq
    have hSelf : numEdges G leaf leaf = 1 := by
      simpa [hEq] using (leafData G leaf hDegree).count_root
    have hZero : numEdges G leaf leaf = 0 := num_edges_self_zero G leaf
    omega⟩

private theorem num_edges_leaf_eq (hDegree : vertexDegree G leaf = 1)
    (x : G.V) :
    numEdges G leaf x =
      if x = (leafData G leaf hDegree).root then 1 else 0 := by
  by_cases hx : x = (leafData G leaf hDegree).root
  · subst x
    simp [(leafData G leaf hDegree).count_root]
  · simp [hx, (leafData G leaf hDegree).count_other x hx]

/-- An edge has both endpoints away from the deleted leaf. -/
def NonLeafEdge (edge : G.V × G.V) : Prop :=
  edge.1 ≠ leaf ∧ edge.2 ≠ leaf

private noncomputable def keptEdges : Multiset (G.V × G.V) := by
  classical
  exact G.edges.filter (NonLeafEdge G leaf)

private def restrictEdge (edge : G.V × G.V)
    (hEdge : NonLeafEdge G leaf edge) :
    Remaining G leaf × Remaining G leaf :=
  (⟨edge.1, hEdge.1⟩, ⟨edge.2, hEdge.2⟩)

private theorem keptEdges_all :
    ∀ edge ∈ keptEdges G leaf, NonLeafEdge G leaf edge := by
  classical
  intro edge hEdge
  exact (Multiset.mem_filter.mp hEdge).2

/-- Delete `leaf`, retaining precisely the edges whose endpoints remain. -/
noncomputable abbrev deleteLeaf
    (hDegree : vertexDegree G leaf = 1) : CFGraph where
  V := Remaining G leaf
  instNonempty := ⟨root G leaf hDegree⟩
  edges := (keptEdges G leaf).pmap (restrictEdge G leaf)
    (keptEdges_all G leaf)
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

@[simp] theorem deleteLeaf_edges
    (hDegree : vertexDegree G leaf = 1) :
    (deleteLeaf G leaf hDegree).edges =
      (keptEdges G leaf).pmap (restrictEdge G leaf)
        (keptEdges_all G leaf) := rfl

private theorem filter_keptEdges_endpoints
    (x y : Remaining G leaf) :
    (keptEdges G leaf).filter
        (fun edge =>
          edge = (x.val, y.val) ∨ edge = (y.val, x.val)) =
      G.edges.filter
        (fun edge =>
          edge = (x.val, y.val) ∨ edge = (y.val, x.val)) := by
  classical
  rw [keptEdges, Multiset.filter_filter]
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

/-- Deleting a leaf does not change edge multiplicities among old vertices. -/
@[simp] theorem num_edges_deleteLeaf
    (hDegree : vertexDegree G leaf = 1) (x y : Remaining G leaf) :
    numEdges (deleteLeaf G leaf hDegree) x y = numEdges G x.val y.val := by
  classical
  change
    ((Multiset.pmap (restrictEdge G leaf) (keptEdges G leaf)
      (keptEdges_all G leaf)).filter
        (fun edge => edge = (x, y) ∨ edge = (y, x))).card =
      (G.edges.filter
        (fun edge =>
          edge = (x.val, y.val) ∨ edge = (y.val, x.val))).card
  rw [Multiset.pmap_eq_map_attach, Multiset.filter_map, Multiset.card_map]
  have hFiltered :
      (keptEdges G leaf).attach.filter
          (((fun edge : Remaining G leaf × Remaining G leaf =>
              edge = (x, y) ∨ edge = (y, x)) ∘
            (fun attached : {edge // edge ∈ keptEdges G leaf} =>
              restrictEdge G leaf attached.val
                (keptEdges_all G leaf attached.val attached.property)))) =
        (keptEdges G leaf).attach.filter
          (fun attached =>
            attached.val = (x.val, y.val) ∨
              attached.val = (y.val, x.val)) := by
    apply Multiset.filter_congr
    rintro ⟨⟨a, b⟩, hEdge⟩ _hAttached
    simp only [Function.comp_apply, restrictEdge, Prod.mk.injEq,
      Subtype.ext_iff]
  rw [hFiltered]
  calc
    ((keptEdges G leaf).attach.filter
        (fun attached =>
          attached.val = (x.val, y.val) ∨
            attached.val = (y.val, x.val))).card =
        ((keptEdges G leaf).filter
          (fun edge =>
            edge = (x.val, y.val) ∨
              edge = (y.val, x.val))).card := by
          simpa only [Multiset.card_map, Multiset.card_attach] using
            congrArg Multiset.card
              (Multiset.filter_attach (keptEdges G leaf)
                (fun edge =>
                  edge = (x.val, y.val) ∨
                    edge = (y.val, x.val)))
    _ = _ := by rw [filter_keptEdges_endpoints]

/-! ## Structural equivalence and rank-one lifting -/

/-- The chosen neighbor, regarded as a vertex of the bundled pruned graph. -/
noncomputable def rootInDeleteLeaf
    (hDegree : vertexDegree G leaf = 1) :
    (deleteLeaf G leaf hDegree).V := by
  change Remaining G leaf
  exact root G leaf hDegree

@[simp] theorem mk_eq_rootInDeleteLeaf_iff
    (hDegree : vertexDegree G leaf = 1) (x : G.V) (hx : x ≠ leaf) :
    (show (deleteLeaf G leaf hDegree).V from ⟨x, hx⟩) =
        rootInDeleteLeaf G leaf hDegree ↔
      x = (leafData G leaf hDegree).root := by
  change
    (⟨x, hx⟩ : Remaining G leaf) = root G leaf hDegree ↔
      x = (leafData G leaf hDegree).root
  rw [Subtype.ext_iff]
  rfl

/-- The canonical relabeling from the original vertices to a new leaf plus
the remaining vertices. -/
noncomputable def vertexEquiv
    (hDegree : vertexDegree G leaf = 1) :
    G.V ≃
      (LeafExtension.addLeaf (deleteLeaf G leaf hDegree)
        (rootInDeleteLeaf G leaf hDegree)).V := by
  change G.V ≃ Option (Remaining G leaf)
  exact (Equiv.optionSubtypeNe leaf).symm

@[simp] theorem vertexEquiv_leaf
    (hDegree : vertexDegree G leaf = 1) :
    vertexEquiv G leaf hDegree leaf = none := by
  change (Equiv.optionSubtypeNe leaf).symm leaf = none
  exact Equiv.optionSubtypeNe_symm_self leaf

@[simp] theorem vertexEquiv_of_ne
    (hDegree : vertexDegree G leaf = 1) (x : G.V) (hx : x ≠ leaf) :
    vertexEquiv G leaf hDegree x = some ⟨x, hx⟩ := by
  change (Equiv.optionSubtypeNe leaf).symm x = some ⟨x, hx⟩
  exact Equiv.optionSubtypeNe_symm_of_ne hx
/-- A graph with a degree-one vertex is the explicit leaf extension of the
graph on the remaining subtype, up to Laplacian-preserving relabeling. -/
noncomputable def laplacianEquivDeleteLeafAddLeaf
    (hDegree : vertexDegree G leaf = 1) :
    LaplacianEquiv G
      (LeafExtension.addLeaf (deleteLeaf G leaf hDegree)
        (rootInDeleteLeaf G leaf hDegree)) where
  toEquiv := vertexEquiv G leaf hDegree
  num_edges_eq := by
    intro x y
    by_cases hx : x = leaf
    · subst x
      by_cases hy : y = leaf
      · subst y
        simp
      · rw [vertexEquiv_leaf,
          vertexEquiv_of_ne G leaf hDegree y hy]
        calc
          _ = if (⟨y, hy⟩ : (deleteLeaf G leaf hDegree).V) =
              rootInDeleteLeaf G leaf hDegree then 1 else 0 :=
            LeafExtension.num_edges_none_some (deleteLeaf G leaf hDegree)
              (rootInDeleteLeaf G leaf hDegree) ⟨y, hy⟩
          _ = _ := by
            simpa only [rootInDeleteLeaf, root, id_eq, Subtype.mk.injEq] using
              (num_edges_leaf_eq G leaf hDegree y).symm
    · by_cases hy : y = leaf
      · subst y
        rw [vertexEquiv_of_ne G leaf hDegree x hx,
          vertexEquiv_leaf]
        calc
          _ = if (⟨x, hx⟩ : (deleteLeaf G leaf hDegree).V) =
              rootInDeleteLeaf G leaf hDegree then 1 else 0 :=
            LeafExtension.num_edges_some_none (deleteLeaf G leaf hDegree)
              (rootInDeleteLeaf G leaf hDegree) ⟨x, hx⟩
          _ = _ := by
            rw [num_edges_symmetric]
            simpa only [rootInDeleteLeaf, root, id_eq, Subtype.mk.injEq] using
              (num_edges_leaf_eq G leaf hDegree x).symm
      · rw [vertexEquiv_of_ne G leaf hDegree x hx,
          vertexEquiv_of_ne G leaf hDegree y hy]
        exact (LeafExtension.num_edges_some_some (deleteLeaf G leaf hDegree)
          (rootInDeleteLeaf G leaf hDegree) ⟨x, hx⟩ ⟨y, hy⟩).trans
          (num_edges_deleteLeaf G leaf hDegree ⟨x, hx⟩ ⟨y, hy⟩)

/-- Rank-one Brill--Noether existence on the pruned graph lifts back to the
original connected graph.  The local lifting calculation uses only the exact
valence-one hypothesis. -/
theorem bnExists_rank_one_of_deleteLeaf
    (_hG : graphConnected G)
    (hDegree : vertexDegree G leaf = 1) {d : ℤ}
    (hPruned : BNExists (deleteLeaf G leaf hDegree) 1 d) :
    BNExists G 1 d := by
  have hExtended :
      BNExists
        (LeafExtension.addLeaf (deleteLeaf G leaf hDegree)
          (rootInDeleteLeaf G leaf hDegree))
        1 d :=
    LeafExtension.bnExists_rank_one_addLeaf
      (deleteLeaf G leaf hDegree) (rootInDeleteLeaf G leaf hDegree) hPruned
  exact ((laplacianEquivDeleteLeafAddLeaf G leaf hDegree).bnExists_iff 1 d).2
    hExtended

end LeafPruning

end Utilities.Certificate
