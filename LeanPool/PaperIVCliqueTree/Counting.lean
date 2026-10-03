/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.PaperIVCliqueTree.Basic

/-!
# The bag-counting identity of a clique tree

For every clique tree, the bag sizes and the sizes of the separators sitting on the tree edges
recover the number of vertices:
`∑ i, |bag i| − ∑ (tree edges i → j), |bag i ∩ bag j| = |V|`.
This is the general form of the perfect-elimination-order count
`SimpleGraph.IsPEO.card_edgeFinset_add_card_eq_sum_card_peoBag`, and the companion of the edge
count `SimpleGraph.CliqueTree.card_edgeFinset_eq_sum_fiber`.

The proof is a double count: a vertex `v` lies in the bags of a nonempty set of nodes, exactly one
of which — the node `top v` — does not pass `v` on to its parent.

## Main definitions

* `SimpleGraph.CliqueTree.parentSep` — the separator attached to a node: `bag i ∩ bag (parent i)`,
  and `∅` at a root.

## Main results

* `SimpleGraph.CliqueTree.card_eq_sum_card_bag_sub_sum_card_inter`
-/

public section

namespace SimpleGraph

namespace CliqueTree

variable {V : Type*} {G : SimpleGraph V} {ι : Type*}

section Sep

variable [DecidableEq V]

/-- The separator of the tree edge above `i`: the intersection of `bag i` with the bag of its
parent, and `∅` if `i` is a root. -/
def parentSep (T : CliqueTree G ι) (i : ι) : Finset V :=
  (T.parent i).elim ∅ fun j => T.bag i ∩ T.bag j

theorem parentSep_eq_of_parent {T : CliqueTree G ι} {i j : ι} (h : T.parent i = some j) :
    T.parentSep i = T.bag i ∩ T.bag j := by simp [parentSep, h]

theorem parentSep_eq_empty_of_root {T : CliqueTree G ι} {i : ι} (h : T.parent i = none) :
    T.parentSep i = ∅ := by simp [parentSep, h]

theorem card_parentSep (T : CliqueTree G ι) (i : ι) :
    (T.parentSep i).card = (T.parent i).elim 0 fun j => (T.bag i ∩ T.bag j).card := by
  cases h : T.parent i with
  | none => simp [parentSep_eq_empty_of_root h]
  | some j => simp [parentSep_eq_of_parent h]

/-- The vertices of the separator above `i` are exactly the vertices of `bag i` that `i` passes on
to its parent, i.e. the vertices of `bag i` whose top node is not `i`. -/
theorem mem_parentSep_iff {T : CliqueTree G ι} {i : ι} {v : V} :
    v ∈ T.parentSep i ↔ v ∈ T.bag i ∧ i ≠ T.top v := by
  constructor
  · intro hv
    cases h : T.parent i with
    | none => rw [parentSep_eq_empty_of_root h] at hv; simp at hv
    | some j =>
        rw [parentSep_eq_of_parent h] at hv
        obtain ⟨hvi, hvj⟩ := Finset.mem_inter.1 hv
        refine ⟨hvi, ?_⟩
        rintro rfl
        exact absurd (T.rank_parent_lt h)
          (by rw [(isAncestor_parent h).antisymm (isAncestor_top_of_mem_bag hvj)]
              exact lt_irrefl _)
  · rintro ⟨hvi, hne⟩
    obtain ⟨j, hj, hvj⟩ := T.mem_bag_parent hvi hne
    rw [parentSep_eq_of_parent hj]
    exact Finset.mem_inter.2 ⟨hvi, hvj⟩

end Sep

private theorem sum_card_eq_sum_card_filter [Fintype V] [DecidableEq V] [Fintype ι]
    (B : ι → Finset V) :
    ∑ i : ι, (B i).card = ∑ v : V, (Finset.univ.filter fun i => v ∈ B i).card := by
  classical
  have hB : ∀ i : ι, (B i).card = ∑ v : V, if v ∈ B i then 1 else 0 := by
    intro i
    rw [← Finset.card_filter]
    congr 1
    ext v
    simp
  simp_rw [hB, Finset.card_filter, Finset.sum_comm (γ := ι)]

/-- **The bag-counting identity.** The total bag size, minus the total size of the separators
sitting on the edges of the clique tree, is the number of vertices. -/
theorem card_eq_sum_card_bag_sub_sum_card_inter [Fintype V] [DecidableEq V] [Fintype ι]
    (T : CliqueTree G ι) :
    Fintype.card V + ∑ i : ι, ((T.parent i).elim 0 fun j => (T.bag i ∩ T.bag j).card)
      = ∑ i : ι, (T.bag i).card := by
  classical
  simp_rw [← card_parentSep]
  rw [sum_card_eq_sum_card_filter (B := T.parentSep),
    sum_card_eq_sum_card_filter (B := T.bag), Fintype.card_eq_sum_ones, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hfilter : (Finset.univ.filter fun i => v ∈ T.parentSep i) =
      (Finset.univ.filter fun i => v ∈ T.bag i).erase (T.top v) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, mem_parentSep_iff]
    exact ⟨fun h => ⟨fun hEq => h.2 hEq, h.1⟩, fun h => ⟨h.2, fun hEq => h.1 hEq⟩⟩
  have htop : T.top v ∈ Finset.univ.filter fun i => v ∈ T.bag i := by
    simp [T.mem_bag_top v]
  rw [hfilter, Finset.card_erase_of_mem htop]
  have hpos : 0 < (Finset.univ.filter fun i => v ∈ T.bag i).card :=
    Finset.card_pos.2 ⟨_, htop⟩
  omega

/-- **The bag-counting identity, summed over the edges of the tree.** Only the non-root nodes, the
ones carrying a tree edge, contribute a separator. -/
theorem card_add_sum_card_parentSep [Fintype V] [DecidableEq V] [Fintype ι]
    (T : CliqueTree G ι) :
    Fintype.card V + ∑ i ∈ Finset.univ.filter fun i => (T.parent i).isSome,
        (T.parentSep i).card = ∑ i : ι, (T.bag i).card := by
  classical
  rw [← T.card_eq_sum_card_bag_sub_sum_card_inter]
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases h : T.parent i with
  | none => simp
  | some j => simp [parentSep_eq_of_parent h]

end CliqueTree

end SimpleGraph
