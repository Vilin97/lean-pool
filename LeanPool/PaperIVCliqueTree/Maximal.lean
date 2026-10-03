/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.PaperIVCliqueTree.PEO

/-!
# The clique tree of maximal cliques

The bag decomposition attached to a perfect elimination order (`CliqueTree/PEO.lean`) does not ask
the bags to be maximal cliques, so it usually contains *redundant* bags.  This file removes them:
for a finite chordal graph we build a clique tree whose bags are **exactly** the maximal cliques of
the graph, each occurring once (`bag` is injective).

The construction is by elimination of simplicial vertices.  Writing `S' = S \ {v}` for a simplicial
vertex `v` of `G[S]` and `C = N(v) ∩ S'`:

* if `C` is already a maximal clique of `G[S']`, the bag `C` is *replaced* by `C ∪ {v}`;
* otherwise a new leaf bag `C ∪ {v}` is attached to a maximal clique of `G[S']` containing `C`.

Both steps preserve the running-intersection property, the maximality of every bag and the fact
that every maximal clique occurs as a bag.

## Main definitions

* `SimpleGraph.IsMaximalCliqueOn` — maximal cliques of the subgraph induced on a finite vertex set
* `SimpleGraph.MaxCliqueForest` — the data produced by the induction

## Main results

* `SimpleGraph.IsChordal.exists_maximalCliqueTree` — a finite chordal graph has a clique tree whose
  bags are precisely its maximal cliques, without repetitions
* `SimpleGraph.IsPEO.exists_eq_peoBag_of_isMaximalCliqueOn` — every maximal clique is one of the
  PEO bags, namely the bag of its earliest vertex (so removing redundant bags loses nothing)
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- `K` is a maximal clique of the subgraph of `G` induced on `S`. -/
@[expose]
def IsMaximalCliqueOn (G : SimpleGraph V) (S K : Finset V) : Prop :=
  K ⊆ S ∧ G.IsClique (K : Set V) ∧ ∀ K', K' ⊆ S → G.IsClique (K' : Set V) → K ⊆ K' → K' = K

theorem IsMaximalCliqueOn.subset {S K : Finset V} (h : G.IsMaximalCliqueOn S K) : K ⊆ S := h.1

theorem IsMaximalCliqueOn.isClique {S K : Finset V} (h : G.IsMaximalCliqueOn S K) :
    G.IsClique (K : Set V) := h.2.1

theorem IsMaximalCliqueOn.eq_of_subset {S K K' : Finset V} (h : G.IsMaximalCliqueOn S K)
    (hK' : K' ⊆ S) (hclique : G.IsClique (K' : Set V)) (hsub : K ⊆ K') : K' = K :=
  h.2.2 K' hK' hclique hsub

variable [DecidableEq V]

omit [DecidableEq V] in
/-- Every clique inside `S` extends to a maximal clique inside `S`. -/
theorem exists_isMaximalCliqueOn {S K : Finset V} (hKS : K ⊆ S)
    (hK : G.IsClique (K : Set V)) : ∃ M, K ⊆ M ∧ G.IsMaximalCliqueOn S M := by
  classical
  set F : Finset (Finset V) := S.powerset.filter (fun T => K ⊆ T ∧ G.IsClique (T : Set V)) with hF
  have hKF : K ∈ F := by
    simp only [hF, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hKS, Finset.Subset.refl K, hK⟩
  obtain ⟨M, hMF, hMmax⟩ := Finset.exists_max_image F Finset.card ⟨K, hKF⟩
  simp only [hF, Finset.mem_filter, Finset.mem_powerset] at hMF
  refine ⟨M, hMF.2.1, hMF.1, hMF.2.2, ?_⟩
  intro K' hK'S hK'clique hMK'
  have hK'F : K' ∈ F := by
    simp only [hF, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hK'S, hMF.2.1.trans hMK', hK'clique⟩
  exact (Finset.eq_of_subset_of_card_le hMK' (hMmax K' hK'F)).symm

/-! ### Simplicial elimination: how the maximal cliques change -/

section Elimination

variable {S C : Finset V} {v : V}

/-- The closed neighbourhood of a simplicial vertex is a clique. -/
theorem isClique_insert_of_simplicial
    (hsimp : ∀ a ∈ S, ∀ b ∈ S, G.Adj v a → G.Adj v b → a ≠ b → G.Adj a b)
    (hC : ∀ u, u ∈ C ↔ (u ∈ S.erase v ∧ G.Adj v u)) :
    G.IsClique ((insert v C : Finset V) : Set V) := by
  intro a ha b hb hab
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact ((hC b).1 hb).2
  · rcases hb with rfl | hb
    · exact ((hC a).1 ha).2.symm
    · have ha' := (hC a).1 ha
      have hb' := (hC b).1 hb
      exact hsimp a (Finset.mem_of_mem_erase ha'.1) b (Finset.mem_of_mem_erase hb'.1)
        ha'.2 hb'.2 hab

/-- The open neighbourhood of a simplicial vertex is a clique. -/
theorem isClique_of_simplicial
    (hsimp : ∀ a ∈ S, ∀ b ∈ S, G.Adj v a → G.Adj v b → a ≠ b → G.Adj a b)
    (hC : ∀ u, u ∈ C ↔ (u ∈ S.erase v ∧ G.Adj v u)) : G.IsClique (C : Set V) := by
  intro a ha b hb hab
  have ha' := (hC a).1 (by simpa using ha)
  have hb' := (hC b).1 (by simpa using hb)
  exact hsimp a (Finset.mem_of_mem_erase ha'.1) b (Finset.mem_of_mem_erase hb'.1) ha'.2 hb'.2 hab

/-- The closed neighbourhood of a simplicial vertex is a maximal clique. -/
theorem isMaximalCliqueOn_insert (hv : v ∈ S)
    (hsimp : ∀ a ∈ S, ∀ b ∈ S, G.Adj v a → G.Adj v b → a ≠ b → G.Adj a b)
    (hC : ∀ u, u ∈ C ↔ (u ∈ S.erase v ∧ G.Adj v u)) :
    G.IsMaximalCliqueOn S (insert v C) := by
  refine ⟨?_, isClique_insert_of_simplicial hsimp hC, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · exact hv
    · exact Finset.mem_of_mem_erase ((hC u).1 hu).1
  · intro K' hK'S hK'clique hsub
    refine Finset.Subset.antisymm ?_ hsub
    intro u hu
    rcases eq_or_ne u v with rfl | hne
    · exact Finset.mem_insert_self _ _
    · have hadj : G.Adj v u :=
        hK'clique (by simpa using hsub (Finset.mem_insert_self v C)) (by simpa using hu)
          (Ne.symm hne)
      exact Finset.mem_insert_of_mem ((hC u).2 ⟨Finset.mem_erase.2 ⟨hne, hK'S hu⟩, hadj⟩)

/-- A maximal clique containing the eliminated vertex is its closed neighbourhood. -/
theorem eq_insert_of_isMaximalCliqueOn_of_mem {K : Finset V} (hv : v ∈ S)
    (hsimp : ∀ a ∈ S, ∀ b ∈ S, G.Adj v a → G.Adj v b → a ≠ b → G.Adj a b)
    (hC : ∀ u, u ∈ C ↔ (u ∈ S.erase v ∧ G.Adj v u))
    (hK : G.IsMaximalCliqueOn S K) (hvK : v ∈ K) : K = insert v C := by
  have hsub : K ⊆ insert v C := by
    intro u hu
    rcases eq_or_ne u v with rfl | hne
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        ((hC u).2 ⟨Finset.mem_erase.2 ⟨hne, hK.subset hu⟩,
          hK.isClique (by simpa using hvK) (by simpa using hu) (Ne.symm hne)⟩)
  have hmax := isMaximalCliqueOn_insert (G := G) hv hsimp hC
  exact (hK.eq_of_subset hmax.subset hmax.isClique hsub).symm

/-- A maximal clique avoiding the eliminated vertex stays maximal after the elimination. -/
theorem isMaximalCliqueOn_erase_of_notMem {K : Finset V}
    (hK : G.IsMaximalCliqueOn S K) (hvK : v ∉ K) : G.IsMaximalCliqueOn (S.erase v) K := by
  refine ⟨fun u hu => Finset.mem_erase.2 ⟨fun h => hvK (h ▸ hu), hK.subset hu⟩, hK.isClique, ?_⟩
  intro K' hK'S hK'clique hsub
  exact hK.eq_of_subset (fun u hu => Finset.mem_of_mem_erase (hK'S hu)) hK'clique hsub

/-- Conversely, a maximal clique of the smaller graph other than the neighbourhood `C` is still a
maximal clique of the bigger one. -/
theorem isMaximalCliqueOn_of_erase {K : Finset V}
    (hsimp : ∀ a ∈ S, ∀ b ∈ S, G.Adj v a → G.Adj v b → a ≠ b → G.Adj a b)
    (hC : ∀ u, u ∈ C ↔ (u ∈ S.erase v ∧ G.Adj v u))
    (hK : G.IsMaximalCliqueOn (S.erase v) K) (hne : K ≠ C) : G.IsMaximalCliqueOn S K := by
  refine ⟨fun u hu => Finset.mem_of_mem_erase (hK.subset hu), hK.isClique, ?_⟩
  intro K' hK'S hK'clique hsub
  by_cases hvK' : v ∈ K'
  · exfalso
    have hK'sub : K' ⊆ insert v C := by
      intro u hu
      rcases eq_or_ne u v with rfl | hune
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem
          ((hC u).2 ⟨Finset.mem_erase.2 ⟨hune, hK'S hu⟩,
            hK'clique (by simpa using hvK') (by simpa using hu) (Ne.symm hune)⟩)
    have hKC : K ⊆ C := by
      intro u hu
      have hune : u ≠ v := (Finset.mem_erase.1 (hK.subset hu)).1
      rcases Finset.mem_insert.1 (hK'sub (hsub hu)) with h | h
      · exact absurd h hune
      · exact h
    have hCsub : C ⊆ S.erase v := fun u hu => ((hC u).1 hu).1
    exact hne (hK.eq_of_subset hCsub (isClique_of_simplicial hsimp hC) hKC).symm
  · have hK'sub : K' ⊆ S.erase v :=
      fun u hu => Finset.mem_erase.2 ⟨fun h => hvK' (h ▸ hu), hK'S hu⟩
    exact hK.eq_of_subset hK'sub hK'clique hsub

end Elimination

/-! ### The maximal-clique forest -/

/-- The data assembled by the simplicial-elimination induction: a rooted forest of bags indexed by
naturals below `size`, whose bags are exactly the maximal cliques of `G[S]`. -/
structure MaxCliqueForest (G : SimpleGraph V) (S : Finset V) where
  /-- Number of nodes. -/
  size : ℕ
  /-- The bag of a node. -/
  bag : ℕ → Finset V
  /-- The parent of a node. -/
  parent : ℕ → Option ℕ
  /-- The highest node whose bag contains a given vertex. -/
  top : V → ℕ
  /-- There is at least one node. -/
  size_pos : 0 < size
  /-- Parents have smaller indices. -/
  parent_lt : ∀ {i j}, i < size → parent i = some j → j < i
  /-- Every bag is a maximal clique of `G[S]`. -/
  bag_maximal : ∀ i < size, G.IsMaximalCliqueOn S (bag i)
  /-- Every maximal clique of `G[S]` is a bag. -/
  exists_bag : ∀ K, G.IsMaximalCliqueOn S K → ∃ i < size, bag i = K
  /-- No bag is repeated. -/
  bag_inj : ∀ i < size, ∀ j < size, bag i = bag j → i = j
  /-- Tops are nodes. -/
  top_lt : ∀ v, top v < size
  /-- Every vertex of `S` lies in its top bag. -/
  mem_bag_top : ∀ v ∈ S, v ∈ bag (top v)
  /-- Local running-intersection property. -/
  climb : ∀ i < size, ∀ v ∈ bag i, i ≠ top v → ∃ j, parent i = some j ∧ v ∈ bag j

omit [DecidableEq V] in
/-- The empty vertex set carries a one-node forest. -/
theorem nonempty_maxCliqueForest_empty : Nonempty (G.MaxCliqueForest (∅ : Finset V)) := by
  refine ⟨⟨1, fun _ => ∅, fun _ => none, fun _ => 0, one_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i j _ h
    simp at h
  · intro i _
    refine ⟨Finset.Subset.refl _, by simp, ?_⟩
    intro K' hK' _ _
    exact Finset.subset_empty.1 hK'
  · intro K hK
    exact ⟨0, one_pos, (Finset.subset_empty.1 hK.subset).symm⟩
  · intro i hi j hj _
    omega
  · intro _
    exact one_pos
  · intro u hu
    simp at hu
  · intro i _ u hu
    simp at hu

/-- Elimination step when the neighbourhood of the simplicial vertex is already a maximal clique:
the corresponding bag is enlarged by the eliminated vertex. -/
theorem nonempty_maxCliqueForest_step_of_maximal {S : Finset V} {v : V} (hv : v ∈ S)
    (hsimp : ∀ a ∈ S, ∀ b ∈ S, G.Adj v a → G.Adj v b → a ≠ b → G.Adj a b)
    (F : G.MaxCliqueForest (S.erase v)) {C : Finset V}
    (hC : ∀ u, u ∈ C ↔ (u ∈ S.erase v ∧ G.Adj v u))
    (hCmax : G.IsMaximalCliqueOn (S.erase v) C) : Nonempty (G.MaxCliqueForest S) := by
  classical
  have hvS' : v ∉ S.erase v := Finset.notMem_erase v S
  have hvbag : ∀ i < F.size, v ∉ F.bag i := fun i hi hmem =>
    hvS' ((F.bag_maximal i hi).subset hmem)
  have hinsmax : G.IsMaximalCliqueOn S (insert v C) := isMaximalCliqueOn_insert hv hsimp hC
  obtain ⟨i₀, hi₀, hbag₀⟩ := F.exists_bag C hCmax
  have hsubnew : ∀ k, F.bag k ⊆ (if k = i₀ then insert v C else F.bag k) := by
    intro k
    by_cases hk : k = i₀
    · subst hk
      rw [ite_eq_left rfl, hbag₀]
      exact Finset.subset_insert _ _
    · rw [ite_eq_right hk]
  refine ⟨⟨F.size, fun i => if i = i₀ then insert v C else F.bag i, F.parent,
    fun u => if u = v then i₀ else F.top u, F.size_pos, F.parent_lt, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i hi
    by_cases hii : i = i₀
    · rw [ite_eq_left hii]
      exact hinsmax
    · rw [ite_eq_right hii]
      refine isMaximalCliqueOn_of_erase hsimp hC (F.bag_maximal i hi) ?_
      intro hEq
      exact hii (F.bag_inj i hi i₀ hi₀ (by rw [hEq, hbag₀]))
  · intro K hK
    by_cases hvK : v ∈ K
    · refine ⟨i₀, hi₀, ?_⟩
      rw [ite_eq_left rfl]
      exact (eq_insert_of_isMaximalCliqueOn_of_mem hv hsimp hC hK hvK).symm
    · have hK' : G.IsMaximalCliqueOn (S.erase v) K := isMaximalCliqueOn_erase_of_notMem hK hvK
      have hKC : K ≠ C := by
        rintro rfl
        have heq := hK.eq_of_subset hinsmax.subset hinsmax.isClique (Finset.subset_insert _ _)
        exact hvK (heq ▸ Finset.mem_insert_self v K)
      obtain ⟨i, hi, hbag⟩ := F.exists_bag K hK'
      have hne : i ≠ i₀ := by
        rintro rfl
        exact hKC (by rw [← hbag, hbag₀])
      refine ⟨i, hi, ?_⟩
      rw [ite_eq_right hne]
      exact hbag
  · intro i hi j hj hEq
    by_cases hii : i = i₀ <;> by_cases hjj : j = i₀
    · rw [hii, hjj]
    · rw [ite_eq_left hii, ite_eq_right hjj] at hEq
      exact absurd (hEq ▸ Finset.mem_insert_self v C) (hvbag j hj)
    · rw [ite_eq_right hii, ite_eq_left hjj] at hEq
      exact absurd (hEq.symm ▸ Finset.mem_insert_self v C) (hvbag i hi)
    · rw [ite_eq_right hii, ite_eq_right hjj] at hEq
      exact F.bag_inj i hi j hj hEq
  · intro u
    by_cases hu : u = v
    · rw [ite_eq_left hu]
      exact hi₀
    · rw [ite_eq_right hu]
      exact F.top_lt u
  · intro u hu
    by_cases huv : u = v
    · subst huv
      rw [ite_eq_left rfl, ite_eq_left rfl]
      exact Finset.mem_insert_self _ _
    · rw [ite_eq_right huv]
      exact hsubnew _ (F.mem_bag_top u (Finset.mem_erase.2 ⟨huv, hu⟩))
  · intro i hi u hu hne
    by_cases huv : u = v
    · exfalso
      subst huv
      rw [ite_eq_left rfl] at hne
      by_cases hii : i = i₀
      · exact hne hii
      · rw [ite_eq_right hii] at hu
        exact hvbag i hi hu
    · rw [ite_eq_right huv] at hne
      have huF : u ∈ F.bag i := by
        by_cases hii : i = i₀
        · rw [ite_eq_left hii] at hu
          rcases Finset.mem_insert.1 hu with h | h
          · exact absurd h huv
          · rw [hii, hbag₀]
            exact h
        · rwa [ite_eq_right hii] at hu
      obtain ⟨j, hj, huj⟩ := F.climb i hi u huF hne
      exact ⟨j, hj, hsubnew j huj⟩

/-- Elimination step when the neighbourhood of the simplicial vertex is not maximal: a new leaf bag
is attached to a maximal clique containing it. -/
theorem nonempty_maxCliqueForest_step_of_not_maximal {S : Finset V} {v : V}
    (hv : v ∈ S) (hsimp : ∀ a ∈ S, ∀ b ∈ S, G.Adj v a → G.Adj v b → a ≠ b → G.Adj a b)
    (F : G.MaxCliqueForest (S.erase v)) {C : Finset V}
    (hC : ∀ u, u ∈ C ↔ (u ∈ S.erase v ∧ G.Adj v u))
    (hCmax : ¬ G.IsMaximalCliqueOn (S.erase v) C) : Nonempty (G.MaxCliqueForest S) := by
  classical
  have hvS' : v ∉ S.erase v := Finset.notMem_erase v S
  have hvbag : ∀ i < F.size, v ∉ F.bag i := fun i hi hmem =>
    hvS' ((F.bag_maximal i hi).subset hmem)
  have hinsmax : G.IsMaximalCliqueOn S (insert v C) := isMaximalCliqueOn_insert hv hsimp hC
  have hCsub : C ⊆ S.erase v := fun u hu => ((hC u).1 hu).1
  obtain ⟨M, hCM, hMmax⟩ := exists_isMaximalCliqueOn hCsub (isClique_of_simplicial hsimp hC)
  obtain ⟨i₁, hi₁, hbagM⟩ := F.exists_bag M hMmax
  refine ⟨⟨F.size + 1, fun i => if i = F.size then insert v C else F.bag i,
    fun i => if i = F.size then some i₁ else F.parent i,
    fun u => if u = v then F.size else F.top u, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i j hi hp
    by_cases hii : i = F.size
    · rw [ite_eq_left hii] at hp
      have hj : j = i₁ := (Option.some_inj.1 hp).symm
      rw [hii, hj]
      exact hi₁
    · rw [ite_eq_right hii] at hp
      exact F.parent_lt (by omega) hp
  · intro i hi
    by_cases hii : i = F.size
    · rw [ite_eq_left hii]
      exact hinsmax
    · rw [ite_eq_right hii]
      refine isMaximalCliqueOn_of_erase hsimp hC (F.bag_maximal i (by omega)) ?_
      intro hEq
      exact hCmax (hEq ▸ F.bag_maximal i (by omega))
  · intro K hK
    by_cases hvK : v ∈ K
    · refine ⟨F.size, by omega, ?_⟩
      rw [ite_eq_left rfl]
      exact (eq_insert_of_isMaximalCliqueOn_of_mem hv hsimp hC hK hvK).symm
    · obtain ⟨i, hi, hbag⟩ := F.exists_bag K (isMaximalCliqueOn_erase_of_notMem hK hvK)
      refine ⟨i, by omega, ?_⟩
      rw [ite_eq_right (by omega : i ≠ F.size)]
      exact hbag
  · intro i hi j hj hEq
    by_cases hii : i = F.size <;> by_cases hjj : j = F.size
    · rw [hii, hjj]
    · rw [ite_eq_left hii, ite_eq_right hjj] at hEq
      exact absurd (hEq ▸ Finset.mem_insert_self v C) (hvbag j (by omega))
    · rw [ite_eq_right hii, ite_eq_left hjj] at hEq
      exact absurd (hEq.symm ▸ Finset.mem_insert_self v C) (hvbag i (by omega))
    · rw [ite_eq_right hii, ite_eq_right hjj] at hEq
      exact F.bag_inj i (by omega) j (by omega) hEq
  · intro u
    by_cases hu : u = v
    · rw [ite_eq_left hu]
      omega
    · rw [ite_eq_right hu]
      have := F.top_lt u
      omega
  · intro u hu
    by_cases huv : u = v
    · subst huv
      rw [ite_eq_left rfl, ite_eq_left rfl]
      exact Finset.mem_insert_self _ _
    · rw [ite_eq_right huv, ite_eq_right (Nat.ne_of_lt (F.top_lt u))]
      exact F.mem_bag_top u (Finset.mem_erase.2 ⟨huv, hu⟩)
  · intro i hi u hu hne
    by_cases hii : i = F.size
    · subst hii
      rw [ite_eq_left rfl] at hu
      rcases Finset.mem_insert.1 hu with rfl | huC
      · rw [ite_eq_left rfl] at hne
        exact absurd rfl hne
      · refine ⟨i₁, by rw [ite_eq_left rfl], ?_⟩
        rw [ite_eq_right (Nat.ne_of_lt hi₁), hbagM]
        exact hCM huC
    · have hi' : i < F.size := by omega
      rw [ite_eq_right hii] at hu
      have huv : u ≠ v := fun h => hvbag i hi' (h ▸ hu)
      rw [ite_eq_right huv] at hne
      obtain ⟨j, hj, huj⟩ := F.climb i hi' u hu hne
      have hjlt : j < F.size := lt_trans (F.parent_lt (i := i) hi' hj) hi'
      refine ⟨j, by rw [ite_eq_right hii]; exact hj, ?_⟩
      rw [ite_eq_right (Nat.ne_of_lt hjlt)]
      exact huj

omit [DecidableEq V] in
/-- **Simplicial elimination.** A finite chordal graph has a maximal-clique forest on every vertex
subset. -/
theorem exists_maxCliqueForest (hG : G.IsChordal) :
    ∀ (n : ℕ) (S : Finset V), S.card = n → Nonempty (G.MaxCliqueForest S) := by
  classical
  intro n
  induction n with
  | zero =>
      intro S hS
      rw [Finset.card_eq_zero] at hS
      subst hS
      exact nonempty_maxCliqueForest_empty
  | succ n ih =>
      intro S hS
      have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨z, hvS, hsimp⟩ := hG.exists_simplicial_in_finset S hSne
      obtain ⟨F⟩ := ih (S.erase (z : V))
        (by rw [Finset.card_erase_of_mem hvS, hS]; omega)
      have hC : ∀ u, u ∈ (S.erase (z : V)).filter (fun u => G.Adj (z : V) u) ↔
          (u ∈ S.erase (z : V) ∧ G.Adj (z : V) u) := by
        intro u
        simp
      by_cases hCmax : G.IsMaximalCliqueOn (S.erase (z : V))
          ((S.erase (z : V)).filter (fun u => G.Adj (z : V) u))
      · exact nonempty_maxCliqueForest_step_of_maximal hvS hsimp F hC hCmax
      · exact nonempty_maxCliqueForest_step_of_not_maximal hvS hsimp F hC hCmax

omit [DecidableEq V] in
/-- **The clique tree of maximal cliques.** A finite chordal graph carries a clique tree whose bags
are exactly its maximal cliques, each occurring exactly once. -/
theorem IsChordal.exists_maximalCliqueTree [Fintype V] (hG : G.IsChordal) :
    ∃ (n : ℕ) (T : CliqueTree G (Fin n)),
      (∀ i, G.IsMaximalCliqueOn Finset.univ (T.bag i)) ∧
      (∀ K, G.IsMaximalCliqueOn Finset.univ K → ∃ i, T.bag i = K) ∧
      Function.Injective T.bag := by
  classical
  obtain ⟨F⟩ := exists_maxCliqueForest hG (Finset.univ : Finset V).card Finset.univ rfl
  refine ⟨F.size, ⟨fun i => F.bag i,
      fun i => (F.parent (i : ℕ)).bind fun k => if h : k < F.size then some (⟨k, h⟩ : Fin F.size)
        else none,
      fun i => (i : ℕ), fun v => ⟨F.top v, F.top_lt v⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j hij
    exact Fin.ext hij
  · intro i j hij
    rcases hp : F.parent (i : ℕ) with - | k
    · rw [hp] at hij
      simp at hij
    · rw [hp] at hij
      by_cases hk : k < F.size
      · simp only [hk, dite_eq_left, Option.bind_some, Option.some_inj] at hij
        have hjk : (j : ℕ) = k := by rw [← hij]
        rw [hjk]
        exact F.parent_lt (i := (i : ℕ)) i.isLt hp
      · simp [hk] at hij
  · intro i
    exact (F.bag_maximal i i.isLt).isClique
  · intro v
    exact F.mem_bag_top v (Finset.mem_univ v)
  · intro u v hadj
    have hpair : G.IsClique (({u, v} : Finset V) : Set V) := by
      simp only [Finset.coe_insert, Finset.coe_singleton]
      rw [SimpleGraph.isClique_pair]
      exact fun _ => hadj
    obtain ⟨M, hsub, hM⟩ := exists_isMaximalCliqueOn (Finset.subset_univ _) hpair
    obtain ⟨i, hi, hbag⟩ := F.exists_bag M hM
    refine ⟨⟨i, hi⟩, ?_, ?_⟩
    · change u ∈ F.bag i
      rw [hbag]
      exact hsub (by simp)
    · change v ∈ F.bag i
      rw [hbag]
      exact hsub (by simp)
  · intro i v hv hne
    have hne' : (i : ℕ) ≠ F.top v := fun h => hne (Fin.ext h)
    obtain ⟨j, hj, hvj⟩ := F.climb (i : ℕ) i.isLt v hv hne'
    have hjlt : j < F.size := lt_trans (F.parent_lt (i := (i : ℕ)) i.isLt hj) i.isLt
    refine ⟨⟨j, hjlt⟩, ?_, hvj⟩
    rw [hj]
    simp [hjlt]
  · intro i
    exact F.bag_maximal i i.isLt
  · intro K hK
    obtain ⟨i, hi, hbag⟩ := F.exists_bag K hK
    exact ⟨⟨i, hi⟩, hbag⟩
  · intro i j hij
    exact Fin.ext (F.bag_inj i i.isLt j j.isLt hij)

/-- **No maximal clique is lost by removing redundant bags.** Along a perfect elimination order,
every maximal clique is the bag of its earliest vertex. -/
theorem IsPEO.exists_eq_peoBag_of_isMaximalCliqueOn [Fintype V] [DecidableRel G.Adj]
    {ord : V → ℕ} (h : G.IsPEO ord) {K : Finset V}
    (hK : G.IsMaximalCliqueOn Finset.univ K) (hne : K.Nonempty) :
    ∃ v ∈ K, K = peoBag G ord v := by
  obtain ⟨v, hvK, hvmin⟩ := Finset.exists_min_image K ord hne
  refine ⟨v, hvK, ?_⟩
  have hsub : K ⊆ peoBag G ord v := by
    intro u hu
    rcases eq_or_ne u v with rfl | hne'
    · exact self_mem_peoBag u
    · have hlt : ord v < ord u :=
        lt_of_le_of_ne (hvmin u hu) (fun heq => hne' (h.injective heq.symm))
      exact mem_peoBag.2 (Or.inr ⟨hlt,
        hK.isClique (by simpa using hvK) (by simpa using hu) (Ne.symm hne')⟩)
  exact (hK.eq_of_subset (Finset.subset_univ _) (h.peoBag_isClique v) hsub).symm

end SimpleGraph
