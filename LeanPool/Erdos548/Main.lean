/-
Copyright (c) 2026 Tom Adamczewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Adamczewski
-/

module

public import LeanPool.Erdos548.RootedTrees
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Erdős problem 548: the Erdős–Sós conjecture

*Reference:* [erdosproblems.com/548](https://www.erdosproblems.com/548)

Every graph on `n ≥ k + 1` vertices with at least `(k - 1) n / 2 + 1` edges contains every tree on
`k + 1` vertices (`erdos_548`).

## Proof outline

For each permutation word of the host vertices, distinguish its first vertex as a root image.
Count the prefixes of its remaining word which end at a neighbour of that root image and support
a rooted copy of the target tree.

Two reversible word operations provide the induction:
* Rotating the first qualifying prefix past the rest of a prefix gives the branch-gluing
  inequality (`marked_word_gluing_count`).
* Reversing both blocks at a cut moves the root to a newly attached leaf, losing at most one
  state per full word (`rooted_word_leaf_move_count`).

Splitting at a nonleaf root, or deleting a leaf root, then proves `rooted_word_tree_bound`: the
number of all adjacency-marked states is at most the rooted-copy count plus `(t - 2) * n!` for a
target of order `t ≥ 2`. The marked-state count is exactly `2 * |E(G)| * (n - 1)!`
(`full_word_base_count`). If the target is absent, cancellation yields `2 * |E(G)| ≤ (t - 2) * n`
(`tree_free_edge_bound`), contradicting the stated density. All counts and injections are finite
and exact.
-/

@[expose] public section

open SimpleGraph

namespace Erdos548

lemma full_word_base_count {V : Type*} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) (l₀ : List V) (hl : l₀.Nodup) (hall : ∀ b, b ∈ l₀) :
    fullWordCount l₀ G.Adj (fun _ _ => True) =
      (l₀.length - 1).factorial * (2 * G.edgeSet.ncard) := by
  classical
  cases nonempty_fintype V
  have hset : l₀.toFinset = Finset.univ := by
    ext b
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact hall b
  have hfiber : ∀ b ∈ l₀.toFinset,
      (goodWordCuts (permutationWords (l₀.erase b)) (l₀.length - 1) (G.Adj b)
        (fun _ => True)).card = (l₀.length - 1).factorial * G.degree b := by
    intro b hb
    have hlen : ∀ q ∈ permutationWords (l₀.erase b), q.length = l₀.length - 1 := by
      intro q hq
      rw [((mem_permutationWords _ _).mp hq).length_eq, List.length_erase_of_mem (hall b)]
    have hnodup : ∀ q ∈ permutationWords (l₀.erase b), q.Nodup := by
      intro q hq
      exact ((mem_permutationWords _ _).mp hq).nodup_iff.mpr (hl.erase b)
    rw [goodWordCuts_true_card _ _ _ hlen hnodup]
    have hterm : ∀ q ∈ permutationWords (l₀.erase b),
        (q.toFinset.filter (G.Adj b)).card = G.degree b := by
      intro q hq
      have hp : (b::q).Perm l₀ := List.cons_perm_iff_perm_erase.mpr
        ⟨hall b, (mem_permutationWords _ _).mp hq⟩
      have he : q.toFinset.filter (G.Adj b) = G.neighborFinset b := by
        ext v
        simp only [Finset.mem_filter, List.mem_toFinset, G.mem_neighborFinset]
        constructor
        · exact And.right
        · intro hv
          constructor
          · have hm : v ∈ b::q := hp.mem_iff.mpr (hall v)
            exact (List.mem_cons.mp hm).resolve_left (fun hh => hv.ne hh.symm)
          · exact hv
      rw [he, G.card_neighborFinset_eq_degree]
    rw [Finset.sum_congr rfl hterm]
    simp only [Finset.sum_const, nsmul_eq_mul, permutationWords_card _ (hl.erase b),
      List.length_erase_of_mem (hall b), Nat.cast_id]
  rw [fullWordCount_eq_sum, Finset.sum_congr rfl hfiber, ← Finset.mul_sum, hset,
    G.sum_degrees_eq_twice_card_edges]
  congr 2
  rw [edgeFinset_card, ← Nat.card_eq_fintype_card]
  rfl

lemma rooted_word_count_zero_of_not_contained {U V : Type*} [DecidableEq V]
    (T : SimpleGraph U) (r : U) (G : SimpleGraph V) (h : ¬T.IsContained G) (l₀ : List V) :
    rootedWordCount T r G l₀ = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨l, k⟩ hp
  obtain ⟨_, _, b, q, _, _, f, _, _⟩ := (mem_fullGoodWordCuts _ _ _ _ _).mp hp
  exact h ⟨f⟩

lemma tree_free_edge_bound {U V : Type} [Fintype U] [Fintype V]
    (T : SimpleGraph U) (hT : T.IsTree) (ht : 2 ≤ Fintype.card U)
    (G : SimpleGraph V) (hn : 0 < Fintype.card V) (hfree : ¬T.IsContained G) :
    2 * G.edgeSet.ncard ≤ (Fintype.card U - 2) * Fintype.card V := by
  classical
  let l₀ : List V := Finset.univ.toList
  have hl : l₀.Nodup := Finset.nodup_toList _
  have hlen : l₀.length = Fintype.card V := by
    simp only [l₀, Finset.length_toList, Finset.card_univ]
  have hne : l₀ ≠ [] := by
    intro he
    have : l₀.length = 0 := by rw [he]; rfl
    omega
  have hall : ∀ b, b ∈ l₀ := by intro b; simp only [l₀, Finset.mem_toList, Finset.mem_univ]
  obtain ⟨r⟩ := hT.connected.nonempty
  have hb := rooted_word_tree_bound T r hT ht G l₀ hl hne
  rw [rooted_word_count_zero_of_not_contained T r G hfree l₀, Nat.zero_add,
    full_word_base_count G l₀ hl hall, permutationWords_card l₀ hl, hlen] at hb
  have hfact : (Fintype.card V).factorial = Fintype.card V * (Fintype.card V - 1).factorial := by
    have he := Nat.factorial_succ (Fintype.card V - 1)
    simpa only [Nat.sub_add_cancel hn] using he
  rw [hfact] at hb
  apply Nat.le_of_mul_le_mul_right (c := (Fintype.card V - 1).factorial) _ (Nat.factorial_pos _)
  nlinarith only [hb]

/--
**Erdős problem #548 (the Erdős–Sós conjecture).** Let $n \geq k + 1$. Every graph on $n$ vertices
with at least $\frac{k-1}{2} n + 1$ edges contains every tree on $k + 1$ vertices, as a subgraph
(not necessarily induced). This is the statement of the FrontierMath Erdős benchmark, following
the phrasing on erdosproblems.com; the classical phrasing "more than $\frac{t-2}{2} n$ edges,
trees on $t$ vertices" (with $t = k + 1$) is recovered by `Erdos548.tree_free_edge_bound`.
-/
theorem erdos_548 :
    ∀ (n k : ℕ), k + 1 ≤ n → ∀ G : SimpleGraph (Fin n),
      ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ) →
        ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T.IsContained G := by
  intro n k hnk G hd T hT
  classical
  have hn : 0 < n := by omega
  by_cases hk : k = 0
  · subst k
    have : Subsingleton (Fin (0 + 1)) := by change Subsingleton (Fin 1); infer_instance
    let f : Fin (0 + 1) → Fin n := fun _ => ⟨0, hn⟩
    have hf : Function.Injective f := fun _ _ _ => Subsingleton.elim _ _
    have ha : ∀ {x y}, T.Adj x y → G.Adj (f x) (f y) := by
      intro x y hxy
      exact (hxy.ne (Subsingleton.elim _ _)).elim
    exact ⟨⟨⟨f, ha⟩, hf⟩⟩
  · by_contra hfree
    have hb := tree_free_edge_bound T hT (by simp only [Fintype.card_fin]; omega) G
      (by simpa only [Fintype.card_fin] using hn) hfree
    simp only [Fintype.card_fin] at hb
    have he : k + 1 - 2 = k - 1 := by omega
    rw [he] at hb
    have hbq : (2:ℚ) * G.edgeSet.ncard ≤ ((k:ℚ) - 1) * n := by
      have hh : (k:ℚ) - 1 = ((k - 1:ℕ):ℚ) := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [hh]
      exact_mod_cast hb
    nlinarith

end Erdos548
