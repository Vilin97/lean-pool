/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.PaperIVCliqueTree.Connector
public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.TreeDecomposition

/-!
# From clique forests to tree decompositions

The adapter preserves every original bag and gives the added connector an empty
bag. Nodes containing a vertex still connect through that vertex's original
`top` node; they never need to pass through the connector. In particular,
joining several roots does not increase the maximal bag size or the width.

The target interface fixes its node universe to `Type`, so the adapter uses
finite node types in that universe. Graph vertices may live in any universe.
-/

public section

namespace SimpleGraph.CliqueTree

variable {V : Type*} {ι : Type} {G : SimpleGraph V} (T : G.CliqueTree ι)

/-- Extend the original bags by an empty bag at the connector. -/
@[expose]
def connectorBag : Option ι → Finset V
  | none => ∅
  | some i => T.bag i

/-- The subtree induced by bags containing a fixed vertex. -/
@[expose]
def vertexBagGraph (v : V) : SimpleGraph {x : Option ι // v ∈ T.connectorBag x} :=
  T.connectorGraph.induce {x | v ∈ T.connectorBag x}

/-- Every bag containing a vertex reaches its original top bag without leaving
the induced graph of bags containing that vertex. -/
theorem vertexBagGraph_reachable_top (v : V) (i : ι) (hi : v ∈ T.bag i) :
    (T.vertexBagGraph v).Reachable ⟨some i, hi⟩ ⟨some (T.top v), T.mem_bag_top v⟩ := by
  generalize hn : T.rank i = n
  induction n using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    by_cases hitop : i = T.top v
    · subst i
      exact Reachable.rfl
    · obtain ⟨j, hp, hj⟩ := T.mem_bag_parent hi hitop
      have hedge : (T.vertexBagGraph v).Adj ⟨some i, hi⟩ ⟨some j, hj⟩ := by
        change T.connectorGraph.Adj (some i) (some j)
        rw [← hp]
        exact T.connectorGraph_adj_parent i
      exact hedge.reachable.trans (ih _ (hn ▸ T.rank_parent_lt hp) j hj rfl)

/-- Vertex-bag coherence survives joining roots with an empty connector bag. -/
theorem vertexBagGraph_connected (v : V) : (T.vertexBagGraph v).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨some (T.top v), T.mem_bag_top v⟩, ?_⟩
  rintro ⟨x, hx⟩
  cases x with
  | none => exact (Finset.notMem_empty v hx).elim
  | some i => exact (T.vertexBagGraph_reachable_top v i hx).symm

/-- Convert a finite rooted clique forest into the existing tree-decomposition
interface, preserving original bags and adding only an empty connector bag. -/
@[expose]
noncomputable def toTreeDecomposition [Fintype ι] :
    Utilities.Treewidth.TreeDecomposition G := by
  classical
  exact {
    Node := Option ι
    tree := T.connectorGraph
    isTree := T.connectorGraph_isTree
    bag := T.connectorBag
    cover_vertex := fun v => ⟨some (T.top v), T.mem_bag_top v⟩
    cover_edge := fun _ _ hadj => by
      obtain ⟨i, hi, hj⟩ := T.exists_bag_of_adj hadj
      exact ⟨some i, hi, hj⟩
    coherent := T.vertexBagGraph_connected
  }

/-- The connector contributes no vertices to a bag. -/
@[simp] theorem toTreeDecomposition_bag_none [Fintype ι] :
    T.toTreeDecomposition.bag none = ∅ := rfl

/-- Each original bag is unchanged by the adapter. -/
@[simp] theorem toTreeDecomposition_bag_some [Fintype ι] (i : ι) :
    T.toTreeDecomposition.bag (some i) = T.bag i := rfl

/-- The maximum bag size is unchanged, including the empty-index case. -/
theorem toTreeDecomposition_max_bag_card [Fintype ι] :
    Finset.univ.sup (fun x : T.toTreeDecomposition.Node =>
      (T.toTreeDecomposition.bag x).card) =
      Finset.univ.sup (fun i : ι => (T.bag i).card) := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro x _
    cases x with
    | none => simp
    | some i => exact Finset.le_sup (f := fun i => (T.bag i).card) (Finset.mem_univ i)
  · apply Finset.sup_le
    intro i _
    exact Finset.le_sup (f := fun x => (T.toTreeDecomposition.bag x).card)
      (Finset.mem_univ (some i))

/-- The adapter has exactly the original maximum bag size minus one. -/
theorem toTreeDecomposition_width [Fintype ι] :
    T.toTreeDecomposition.width =
      (Finset.univ.sup fun i : ι => (T.bag i).card) - 1 := by
  unfold Utilities.Treewidth.TreeDecomposition.width
  rw [T.toTreeDecomposition_max_bag_card]

/-- A clique forest directly supplies a treewidth bound through the existing API. -/
theorem treewidth_le_max_bag_card_sub_one [Fintype ι] :
    Utilities.Treewidth.treewidth G ≤
      (Finset.univ.sup fun i : ι => (T.bag i).card) - 1 := by
  rw [← T.toTreeDecomposition_width]
  exact Utilities.Treewidth.treewidth_le_width T.toTreeDecomposition

end SimpleGraph.CliqueTree
