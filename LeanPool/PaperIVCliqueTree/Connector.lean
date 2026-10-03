/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.PaperIVCliqueTree.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Joining a rooted clique forest by one connector

The new node `none` is joined to every original root. Original parent edges
are unchanged. The resulting graph is a tree, including for an empty forest.
Strict rank descent proves connectivity; a maximal-rank vertex on a putative
cycle would have two different lower neighbours, contradicting unique parenthood.
-/

public section

namespace SimpleGraph.CliqueTree

variable {V ι : Type*} {G : SimpleGraph V} (T : G.CliqueTree ι)

/-- Parent in the connected augmentation; the connector is its own parent. -/
def connectorParent : Option ι → Option ι
  | none => none
  | some i => T.parent i

/-- The connector has rank zero and original nodes have their rank shifted by one. -/
def connectorRank : Option ι → ℕ
  | none => 0
  | some i => T.rank i + 1

/-- Every original node has a strictly lower parent in the augmentation. -/
theorem connectorParent_rank_lt {x : Option ι} (hx : x ≠ none) :
    T.connectorRank (T.connectorParent x) < T.connectorRank x := by
  cases x with
  | none => exact (hx rfl).elim
  | some i =>
    cases hp : T.parent i with
    | none => simp [connectorParent, connectorRank, hp]
    | some j =>
      simpa [connectorParent, connectorRank, hp] using T.rank_parent_lt hp

/-- The undirected parent graph, with each root joined to a new connector. -/
def connectorGraph : SimpleGraph (Option ι) where
  Adj x y := (x ≠ none ∧ T.connectorParent x = y) ∨
    (y ≠ none ∧ T.connectorParent y = x)
  symm.symm := by
    intro x y h
    exact h.symm
  loopless.irrefl x := by
    rintro (⟨hx, hp⟩ | ⟨hx, hp⟩)
    all_goals
      have hlt := T.connectorParent_rank_lt hx
      rw [hp] at hlt
      exact (lt_irrefl _ hlt)

/-- An original node is adjacent to its augmented parent, even if it is a root. -/
theorem connectorGraph_adj_parent (i : ι) :
    T.connectorGraph.Adj (some i) (T.parent i) :=
  Or.inl ⟨Option.some_ne_none i, rfl⟩

/-- Exactly the original roots are adjacent to the connector. -/
@[simp] theorem connectorGraph_adj_none_some (i : ι) :
    T.connectorGraph.Adj none (some i) ↔ T.parent i = none := by
  simp [connectorGraph, connectorParent]

/-- Adjacency between original nodes is exactly their original parent relation. -/
@[simp] theorem connectorGraph_adj_some_some (i j : ι) :
    T.connectorGraph.Adj (some i) (some j) ↔
      T.parent i = some j ∨ T.parent j = some i := by
  simp [connectorGraph, connectorParent]

/-- Every node reaches the connector by repeatedly following its parent. -/
theorem connectorGraph_reachable_connector (x : Option ι) :
    T.connectorGraph.Reachable x none := by
  cases x with
  | none => exact Reachable.rfl
  | some i =>
    generalize hn : T.rank i = n
    induction n using Nat.strong_induction_on generalizing i with
    | _ n ih =>
      have hedge := T.connectorGraph_adj_parent i
      cases hp : T.parent i with
      | none => exact (hp ▸ hedge).reachable
      | some j =>
        exact (hp ▸ hedge).reachable.trans
          (ih _ (hn ▸ T.rank_parent_lt hp) j rfl)

/-- The connector joins all roots into a single connected graph. -/
theorem connectorGraph_connected : T.connectorGraph.Connected := by
  rw [connected_iff_exists_forall_reachable]
  exact ⟨none, fun x => (T.connectorGraph_reachable_connector x).symm⟩

/-- A neighbour with no larger rank must be the unique augmented parent. -/
theorem connectorParent_eq_of_adj_of_rank_le {x y : Option ι}
    (hxy : T.connectorGraph.Adj x y) (hy : T.connectorRank y ≤ T.connectorRank x) :
    T.connectorParent x = y := by
  rcases hxy with ⟨_, hp⟩ | ⟨hy', hp⟩
  · exact hp
  · have hlt := T.connectorParent_rank_lt hy'
    rw [hp] at hlt
    exact (not_lt_of_ge hy hlt).elim

/-- No cycle can have two different neighbours of its maximal-rank vertex. -/
theorem connectorGraph_isAcyclic : T.connectorGraph.IsAcyclic := by
  classical
  intro x p hp
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image p.support.toFinset T.connectorRank
    (by exact ⟨x, List.mem_toFinset.mpr p.start_mem_support⟩)
  have hm' : m ∈ p.support := List.mem_toFinset.mp hm
  let q := p.rotate m hm'
  have hq : q.IsCycle := hp.rotate hm'
  have hs : q.snd ∈ p.support :=
    (p.mem_support_rotate_iff m hm').mp (q.getVert_mem_support 1)
  have ht : q.penultimate ∈ p.support :=
    (p.mem_support_rotate_iff m hm').mp
      (q.getVert_mem_support (q.length - 1))
  have hparentS := T.connectorParent_eq_of_adj_of_rank_le
    (q.adj_snd hq.not_nil) (hmax _ (List.mem_toFinset.mpr hs))
  have hparentT := T.connectorParent_eq_of_adj_of_rank_le
    (q.adj_penultimate hq.not_nil).symm (hmax _ (List.mem_toFinset.mpr ht))
  exact hq.snd_ne_penultimate (hparentS.symm.trans hparentT)

/-- Connecting the roots of a clique forest produces a genuine tree. -/
theorem connectorGraph_isTree : T.connectorGraph.IsTree :=
  ⟨T.connectorGraph_connected, T.connectorGraph_isAcyclic⟩

end SimpleGraph.CliqueTree
