/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.PaperIVCliqueTree.Maximal

/-!
# Maximal cliques: the bridge to Mathlib, and how many there are

Two complements to `CliqueTree/Maximal.lean`.

* The relative notion `SimpleGraph.IsMaximalCliqueOn G S K` used in this library agrees, for
  `S = Finset.univ`, with the order-theoretic `Maximal G.IsClique` of Mathlib
  (`SimpleGraph.isMaximalCliqueOn_univ_iff`).  The relative notion is kept because Mathlib does not
  cover cliques of induced subgraphs.
* A clique tree whose bags are the maximal cliques has at most `Fintype.card V` nodes, because
  every node is the top node of one of its own vertices.  Hence a finite chordal graph has at most
  `Fintype.card V` maximal cliques.

## Main results

* `SimpleGraph.isMaximalCliqueOn_univ_iff`
* `SimpleGraph.MaxCliqueForest.size_le`
* `SimpleGraph.CliqueTree.card_le_card_of_isMaximalCliqueOn`
* `SimpleGraph.IsChordal.exists_maximalCliqueTree_card_le`
* `SimpleGraph.IsChordal.card_maximalCliques_le`
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### The bridge to `Maximal G.IsClique` -/

/-- **Bridge to Mathlib's notion.** For `S = Finset.univ` the relative maximal cliques of this
library are exactly the maximal cliques in the sense of `Maximal G.IsClique`. -/
theorem isMaximalCliqueOn_univ_iff [Fintype V] {K : Finset V} :
    G.IsMaximalCliqueOn Finset.univ K ↔ Maximal G.IsClique (K : Set V) := by
  classical
  rw [isMaximalClique_iff]
  constructor
  · rintro ⟨-, hclique, hmax⟩
    refine ⟨hclique, fun t ht hsub => ?_⟩
    have := hmax t.toFinset (Finset.subset_univ _) (by simpa using ht)
      (fun x hx => by simpa using hsub (by simpa using hx))
    intro x hx
    have : x ∈ t.toFinset := by simpa using hx
    rw [‹t.toFinset = K›] at this
    simpa using this
  · rintro ⟨hclique, hmax⟩
    refine ⟨Finset.subset_univ _, hclique, fun K' _ hK' hsub => ?_⟩
    exact Finset.coe_injective (Set.Subset.antisymm (hmax _ hK' (by exact_mod_cast hsub))
      (by exact_mod_cast hsub))

/-! ### Counting the maximal cliques -/

namespace MaxCliqueForest

variable {S : Finset V}

/-- Every node of a maximal-clique forest is the top node of one of its own vertices. -/
theorem exists_top_eq (F : G.MaxCliqueForest S) {i : ℕ} (hi : i < F.size)
    (hne : (F.bag i).Nonempty) : ∃ v ∈ F.bag i, F.top v = i := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨j, hj, -⟩ := F.climb i hi v₀ hv₀ (fun h => hcon v₀ hv₀ h.symm)
  have hsub : F.bag i ⊆ F.bag j := by
    intro u hu
    obtain ⟨j', hj', huj⟩ := F.climb i hi u hu (fun h => hcon u hu h.symm)
    rwa [Option.some_inj.1 (hj'.symm.trans hj)] at huj
  have hjlt : j < i := F.parent_lt hi hj
  have hji : j < F.size := lt_trans hjlt hi
  have hEq : F.bag j = F.bag i :=
    (F.bag_maximal i hi).eq_of_subset (F.bag_maximal j hji).subset
      (F.bag_maximal j hji).isClique hsub
  exact absurd (F.bag_inj i hi j hji hEq.symm) (Nat.ne_of_gt hjlt)

/-- If the vertex set is nonempty then so is every bag. -/
theorem bag_nonempty (F : G.MaxCliqueForest S) {i : ℕ} (hi : i < F.size) (hS : S.Nonempty) :
    (F.bag i).Nonempty := by
  rcases (F.bag i).eq_empty_or_nonempty with hempty | hne
  · obtain ⟨s, hs⟩ := hS
    have hsingle : ({s} : Finset V) = F.bag i :=
      (F.bag_maximal i hi).eq_of_subset (by simpa using hs)
        (by simp) (by simp [hempty])
    exact absurd (hsingle.trans hempty) (by simp)
  · exact hne

/-- **A maximal-clique forest on a nonempty vertex set has at most one node per vertex.** -/
theorem size_le_card (F : G.MaxCliqueForest S) (hS : S.Nonempty) : F.size ≤ S.card := by
  classical
  obtain ⟨s₀, hs₀⟩ := hS
  have key : ∀ i : ℕ, ∃ v : V, i < F.size → (v ∈ F.bag i ∧ F.top v = i) := by
    intro i
    by_cases hi : i < F.size
    · obtain ⟨v, hv, htop⟩ := F.exists_top_eq hi (F.bag_nonempty hi ⟨s₀, hs₀⟩)
      exact ⟨v, fun _ => ⟨hv, htop⟩⟩
    · exact ⟨s₀, fun h => absurd h hi⟩
  choose f hf using key
  have hcard := Finset.card_le_card_of_injOn (s := Finset.range F.size) (t := S) f
    (fun i hi => (F.bag_maximal i (Finset.mem_range.1 hi)).subset
      (hf i (Finset.mem_range.1 hi)).1)
    (fun i hi j hj hij => by
      have h₁ := (hf i (Finset.mem_range.1 (by simpa using hi))).2
      have h₂ := (hf j (Finset.mem_range.1 (by simpa using hj))).2
      rw [← h₁, ← h₂, hij])
  simpa using hcard

/-- **A maximal-clique forest has at most `S.card + 1` nodes**, the extra node occurring only for
the empty vertex set (whose unique maximal clique is `∅`). -/
theorem size_le (F : G.MaxCliqueForest S) : F.size ≤ S.card + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · by_contra hcon
    push Not at hcon
    have h0 : F.bag 0 = F.bag 1 := by
      have e : ∀ i < F.size, F.bag i = ∅ :=
        fun i hi => Finset.subset_empty.1 (F.bag_maximal i hi).subset
      rw [e 0 (by omega), e 1 (by omega)]
    exact absurd (F.bag_inj 0 (by omega) 1 (by omega) h0) (by omega)
  · exact le_trans (F.size_le_card hS) (Nat.le_succ _)

end MaxCliqueForest

namespace CliqueTree

variable {ι : Type*}

/-- In a clique tree whose bags are maximal cliques and pairwise distinct, every node is the top
node of one of its own vertices. -/
theorem exists_top_eq [Fintype V] [Nonempty V] (T : CliqueTree G ι)
    (hmax : ∀ i, G.IsMaximalCliqueOn Finset.univ (T.bag i)) (hinj : Function.Injective T.bag)
    (i : ι) : ∃ v, T.top v = i := by
  classical
  have hne : (T.bag i).Nonempty := by
    rcases (T.bag i).eq_empty_or_nonempty with hempty | hne
    · have hsingle : ({Classical.arbitrary V} : Finset V) = T.bag i :=
        (hmax i).eq_of_subset (Finset.subset_univ _) (by simp) (by simp [hempty])
      exact absurd (hsingle.trans hempty) (by simp)
    · exact hne
  by_contra hcon
  push Not at hcon
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨j, hj, -⟩ := T.mem_bag_parent hv₀ (fun h => hcon v₀ h.symm)
  have hsub : T.bag i ⊆ T.bag j := by
    intro u hu
    obtain ⟨j', hj', huj⟩ := T.mem_bag_parent hu (fun h => hcon u h.symm)
    rwa [Option.some_inj.1 (hj'.symm.trans hj)] at huj
  have hEq : T.bag j = T.bag i :=
    (hmax i).eq_of_subset (Finset.subset_univ _) (hmax j).isClique hsub
  exact absurd (T.rank_parent_lt hj) (by rw [hinj hEq]; exact lt_irrefl _)

/-- **A clique tree of maximal cliques has at most one node per vertex.** -/
theorem card_le_card_of_isMaximalCliqueOn [Fintype V] [Nonempty V] [Fintype ι]
    (T : CliqueTree G ι) (hmax : ∀ i, G.IsMaximalCliqueOn Finset.univ (T.bag i))
    (hinj : Function.Injective T.bag) : Fintype.card ι ≤ Fintype.card V :=
  Fintype.card_le_of_surjective T.top (T.exists_top_eq hmax hinj)

end CliqueTree

/-- **The clique tree of maximal cliques, with the classical bound on the number of bags.** -/
theorem IsChordal.exists_maximalCliqueTree_card_le [Fintype V] [Nonempty V]
    (hG : G.IsChordal) :
    ∃ (n : ℕ) (T : CliqueTree G (Fin n)),
      n ≤ Fintype.card V ∧
      (∀ i, G.IsMaximalCliqueOn Finset.univ (T.bag i)) ∧
      (∀ K, G.IsMaximalCliqueOn Finset.univ K → ∃ i, T.bag i = K) ∧
      Function.Injective T.bag := by
  obtain ⟨n, T, hmax, hsurj, hinj⟩ := hG.exists_maximalCliqueTree
  refine ⟨n, T, ?_, hmax, hsurj, hinj⟩
  simpa using T.card_le_card_of_isMaximalCliqueOn hmax hinj

/-- **A finite chordal graph has at most `Fintype.card V` maximal cliques.** -/
theorem IsChordal.card_maximalCliques_le [Fintype V] [Nonempty V]
    [DecidablePred (G.IsMaximalCliqueOn Finset.univ)] (hG : G.IsChordal) :
    (Finset.univ.powerset.filter fun K => G.IsMaximalCliqueOn Finset.univ K).card
      ≤ Fintype.card V := by
  classical
  obtain ⟨n, T, hn, hmax, hsurj, hinj⟩ := hG.exists_maximalCliqueTree_card_le
  have hsub : (Finset.univ.powerset.filter fun K => G.IsMaximalCliqueOn Finset.univ K) ⊆
      Finset.image T.bag Finset.univ := by
    intro K hK
    obtain ⟨i, hi⟩ := hsurj K (Finset.mem_filter.1 hK).2
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, hi⟩
  calc (Finset.univ.powerset.filter fun K => G.IsMaximalCliqueOn Finset.univ K).card
      ≤ (Finset.image T.bag Finset.univ).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := by simp
    _ ≤ Fintype.card V := hn

end SimpleGraph
