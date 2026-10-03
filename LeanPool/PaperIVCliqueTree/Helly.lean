/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.PaperIVCliqueTree.PEO

/-!
# The Helly property of clique trees and the clique number

The bags of a clique tree have the **Helly property**: every clique of the graph is contained in a
single bag.  Together with the fact that bags are cliques this identifies the clique number of the
graph with the size of the largest bag, and shows that some bag is a maximum clique.

## Main results

* `SimpleGraph.CliqueTree.exists_subset_bag` — every nonempty clique is contained in a bag
* `SimpleGraph.CliqueTree.exists_subset_bag'` — the same without the nonemptiness assumption,
  for a nonempty index type
* `SimpleGraph.CliqueTree.exists_subset_bag_set` — the version for clique *sets*
* `SimpleGraph.CliqueTree.cliqueNum_eq_sup_card_bag` — the clique number is the largest bag size
* `SimpleGraph.CliqueTree.exists_isMaximumClique_bag` — some bag is a maximum clique
* `SimpleGraph.IsPEO.cliqueNum_eq_sup_card_peoBag` — the same for the bags of a perfect
  elimination order
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {ι : Type*} {T : CliqueTree G ι}

namespace CliqueTree

/-- The top nodes of two vertices sharing a bag are comparable. -/
theorem top_comparable_of_mem_bag {k : ι} {u v : V} (hu : u ∈ T.bag k) (hv : v ∈ T.bag k) :
    T.IsAncestor (T.top u) (T.top v) ∨ T.IsAncestor (T.top v) (T.top u) :=
  (isAncestor_top_of_mem_bag hu).comparable (isAncestor_top_of_mem_bag hv)

/-- If `u` and `v` share a bag and the top node of `v` has the smaller rank, then the top node of
`v` is an ancestor of the top node of `u`. -/
theorem isAncestor_top_of_rank_le {k : ι} {u v : V} (hu : u ∈ T.bag k) (hv : v ∈ T.bag k)
    (hrank : T.rank (T.top v) ≤ T.rank (T.top u)) : T.IsAncestor (T.top u) (T.top v) := by
  rcases top_comparable_of_mem_bag hu hv with h | h
  · exact h
  · exact (T.rank_injective (le_antisymm hrank h.rank_le)) ▸ isAncestor_refl _

/-- If `u` and `v` share a bag and the top node of `v` has the smaller rank, then `v` already lies
in the top bag of `u`. -/
theorem mem_bag_top_of_rank_le {k : ι} {u v : V} (hu : u ∈ T.bag k) (hv : v ∈ T.bag k)
    (hrank : T.rank (T.top v) ≤ T.rank (T.top u)) : v ∈ T.bag (T.top u) :=
  mem_bag_of_isAncestor hv (isAncestor_top_of_mem_bag hu)
    (isAncestor_top_of_rank_le hu hv hrank)

/-- **Helly property of the bags.** Every nonempty clique of `G` is contained in a single bag,
namely in the top bag of any of its vertices of largest rank. -/
theorem exists_subset_bag (T : CliqueTree G ι) {K : Finset V} (hK : K.Nonempty)
    (hKc : G.IsClique (K : Set V)) : ∃ i, K ⊆ T.bag i := by
  classical
  obtain ⟨v, hvK, hvmax⟩ := Finset.exists_max_image K (fun u => T.rank (T.top u)) hK
  refine ⟨T.top v, fun u huK => ?_⟩
  rcases eq_or_ne u v with rfl | hne
  · exact T.mem_bag_top u
  · obtain ⟨k, hvk, huk⟩ := T.exists_bag_of_adj (hKc (by simpa using hvK) (by simpa using huK)
      (Ne.symm hne))
    exact mem_bag_top_of_rank_le hvk huk (hvmax u huK)

/-- **Helly property of the bags**, without a nonemptiness assumption on the clique. -/
theorem exists_subset_bag' [Nonempty ι] (T : CliqueTree G ι) {K : Finset V}
    (hKc : G.IsClique (K : Set V)) : ∃ i, K ⊆ T.bag i := by
  rcases K.eq_empty_or_nonempty with rfl | hK
  · exact ⟨Classical.arbitrary ι, by simp⟩
  · exact T.exists_subset_bag hK hKc

/-- **Helly property of the bags**, for a clique given as a finite set of vertices. -/
theorem exists_subset_bag_set [Finite V] [Nonempty ι] (T : CliqueTree G ι)
    {K : Set V} (hKc : G.IsClique K) : ∃ i, K ⊆ (T.bag i : Set V) := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  obtain ⟨i, hi⟩ := T.exists_subset_bag' (K := K.toFinset) (by simpa using hKc)
  exact ⟨i, by intro x hx; exact_mod_cast hi (by simpa using hx)⟩

/-- **The clique number is the size of the largest bag.** -/
theorem cliqueNum_eq_sup_card_bag [Finite V] [Fintype ι] [Nonempty ι]
    (T : CliqueTree G ι) : G.cliqueNum = Finset.univ.sup fun i => (T.bag i).card := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  refine le_antisymm ?_ (Finset.sup_le fun i _ => (T.bag_isClique i).card_le_cliqueNum)
  obtain ⟨s, hsclique, hscard⟩ := G.exists_isNClique_cliqueNum
  obtain ⟨i, hi⟩ := T.exists_subset_bag' hsclique
  calc G.cliqueNum = s.card := hscard.symm
    _ ≤ (T.bag i).card := Finset.card_le_card hi
    _ ≤ _ := Finset.le_sup (f := fun j => (T.bag j).card) (Finset.mem_univ i)

/-- **Some bag is a maximum clique.** -/
theorem exists_isMaximumClique_bag [Finite V] [Finite ι] [Nonempty ι]
    (T : CliqueTree G ι) : ∃ i, G.IsMaximumClique (T.bag i) := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) (fun i => (T.bag i).card)
      Finset.univ_nonempty
  refine ⟨i, T.bag_isClique i, fun t ht => ?_⟩
  have hsup : (T.bag i).card = Finset.univ.sup fun j => (T.bag j).card :=
    le_antisymm (Finset.le_sup (f := fun j => (T.bag j).card) (Finset.mem_univ i))
      (Finset.sup_le fun j _ => hi j
      (Finset.mem_univ j))
  rw [hsup, ← T.cliqueNum_eq_sup_card_bag]
  exact ht.card_le_cliqueNum

end CliqueTree

/-- **The clique number is the size of the largest bag of a perfect elimination order.** -/
theorem IsPEO.cliqueNum_eq_sup_card_peoBag [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Nonempty V] {ord : V → ℕ} (h : G.IsPEO ord) :
    G.cliqueNum = Finset.univ.sup fun v => (peoBag G ord v).card :=
  h.cliqueTree.cliqueNum_eq_sup_card_bag

end SimpleGraph
