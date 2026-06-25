/-
Copyright (c) 2026 Daniel Smania. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Smania
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Cases

/-!
# Rooted binary trees of disjoint Finset pairs and maximal laminar families

Source: url:https://github.com/SmaniaD/LaminarFamiliesMaximalBinaryTrees
Authors: Daniel Smania
Status: verified
Main declarations: `LaminarFamiliesMaximalBinaryTrees.BinaryTreeWithRootandTops`
Tags: combinatorics, laminar-families, binary-trees
MSC: 05C05
-/

/-!
# Binary trees of pairs of subsets associated with laminar families

This file formalizes `BinaryTreeWithRootandTops`, a rooted, ordered binary tree whose nodes
are pairs of disjoint, nonempty, finite subsets of a finite set of children, together with a
distinguished set of tops acting as the leaves of the tree. Such trees are the
tree-representations of maximal laminar families of subsets of the children set.

The main result, `exists_tree_childs_eq_C_and_all_childs_in_Tops_of_card_ge_two`, shows that any
finite set with at least two elements admits such a tree whose children set equals the whole set
and whose set of tops is the entire set (a maximal tree).
-/

open Finset Set

namespace LaminarFamiliesMaximalBinaryTrees


/-- For any `C` and `a`, we have `C ⊆ {a} ∪ (C \ {a})`. -/
lemma subset_singleton_union_sdiff [DecidableEq α] (C : Finset α) (a : α) :
    C ⊆ ({a} : Finset α) ∪ (C \ {a}) := by
  intro x hxC
  by_cases hxa : x = a
  · have : x ∈ ({a}:Finset α) := by
      simp [hxa, Finset.mem_singleton]
    simpa [Finset.mem_union] using Or.inl this
  · have hx_sdiff : x ∈ C \ {a} := by
      refine (Finset.mem_sdiff).mpr ?_
      exact ⟨hxC, by simp [Finset.mem_singleton, hxa]⟩
    exact Finset.mem_union_right _ hx_sdiff


lemma singleton_disjoint_sdiff [DecidableEq α] (C : Finset α) (a : α) :
    Disjoint ({a} : Finset α) (C \ {a}) := by
  -- `Disjoint s t ↔ ∀ x, x ∈ s → x ∈ t → False`
  refine (Finset.disjoint_left.2 ?_)
  intro x hx_left hx_right
  -- `hx_left : x ∈ {a}`  ⇒  `x = a`
  have hx_eq : x = a := by
    simpa [Finset.mem_singleton] using hx_left
  -- `hx_right : x ∈ C \ {a}`  ⇒  `x ≠ a`
  have hx_ne : x ≠ a := by
    -- `mem_sdiff.mp` dá `(x ∈ C) ∧ (x ∉ {a})`
    have h_not : x ∉ ({a} : Finset α) := (Finset.mem_sdiff.mp hx_right).2
    simpa [Finset.mem_singleton] using h_not
  -- Contradição entre `x = a` e `x ≠ a`
  exact (hx_ne hx_eq).elim


lemma union_sdiff_of_mem {α : Type _} [DecidableEq α] {C : Finset α} {a : α}
  (ha : a ∈ C) : {a} ∪ (C \ {a}) ⊆ C := by
  -- passo 1: provar igualdade de finsets pelo critério de extensão
  intro x hx
  -- passo 2: simplificar a condição de pertencimento usando `ha`
  rcases Finset.mem_union.mp hx with hxa | hC_hxa
  · -- x ∈ {a}
    rw [Finset.mem_singleton] at hxa
    rw [hxa]
    exact ha
  · -- x ∈ C \ {a}
    exact (Finset.mem_sdiff.mp hC_hxa).1



theorem embed_disj_tauto (a b c d e : Prop) :
  (a ∨ b ∨ c) → (a ∨ b ∨ c ∨ d ∨ e) := by
  intro h
  tauto


/-- `xor p q` is true iff **exactly one** of `p` and `q`
    holds. Equivalent to `(p ∧ ¬q) ∨ (¬p ∧ q)`. -/
def xor (p q : Prop) : Prop := (p ∧ ¬ q) ∨ (¬ p ∧ q)


/-- `pairToFinset (p1, p2)` is the two-element finset `{p1, p2}`. -/
noncomputable def pairToFinset {α : Type*} [DecidableEq α] : α × α → Finset α
| (p1, p2) => {p1, p2}

/-- The combinatorial support of a pair of finsets `p = (p.1, p.2)` is their union
`p.1 ∪ p.2`. -/
noncomputable def combinatorialSupport {α : Type*} [DecidableEq α] (p : Finset α × Finset α) :
    Finset α :=
p.1 ∪ p.2


/-- A `BinaryTreeWithRootandTops` over a type `α` models a rooted, ordered binary tree
whose nodes are pairs of disjoint, nonempty, finite subsets of a finite set of children,
together with a distinguished set of tops acting as the leaves of the tree. Such trees are
the tree-representations of maximal laminar families of subsets of the children set. -/
structure BinaryTreeWithRootandTops (α : Type*) [DecidableEq α] where
  /-- The root of the tree: the initial split of the children set into two finsets. -/
  Root : Finset α× Finset α
  /-- The ground finite set of atoms ("children"). -/
  Childs              : Finset α
  /-- All pairs of finsets describing the nodes (branches) of the tree. -/
  Branches            : Finset (Finset α × Finset α)
  /-- Both components of every branch are nonempty. -/
  NonemptyPairs:
    ∀ y ∈ Branches, y.1.Nonempty ∧ y.2.Nonempty
  /-- The distinguished set of leaves ("tops") of the tree. -/
  Tops: Finset α
  /-- The two components of every branch are disjoint. -/
  DisjointComponents:
    ∀ p ∈ Branches, Disjoint p.1 p.2
  /-- Distinct branches have disjoint two-element finsets of components. -/
  DistinctComponentsPairs:
    ∀ p ∈ Branches, ∀ q ∈ Branches, (p ≠ q)->Disjoint (pairToFinset p) (pairToFinset q)
  /-- The root is one of the branches. -/
  RootinBranches:
    Root ∈ Branches
  /-- Every child lies in the support of some branch. -/
  EveryChildinaBranch:
    ∀ a ∈ Childs,  ∃ p ∈ Branches, a ∈ combinatorialSupport p
  /-- The children set is contained in the support of the root. -/
  RootcontainsChilds:
   Childs ⊆  Root.1 ∪ Root.2
  /-- Both components of every branch are subsets of the children set. -/
  TreeStructureChilds:
    ∀ p ∈ Branches, p.1 ⊆ Childs ∧ p.2 ⊆ Childs
  /-- Every non-root branch has its support as a component of some other branch. -/
  TreeStructure:
    ∀ p ∈ Branches,    p ≠ Root → ∃ q ∈ Branches, p.1 ∪ p.2 ∈ pairToFinset q
  /-- Every top is a singleton component of some branch. -/
  TopsareTops:
    ∀ p ∈ Tops, ∃ q∈ Branches, {p}∈ pairToFinset q
  /-- Every singleton component of a branch is a top. -/
  SingletonsAreTops :
    ∀ p ∈ Branches,
       ∀ x, {x} ∈ pairToFinset p → (x ∈ Tops)
  /-- Both components of the root are nonempty. -/
  NonemptyRoot: Root.1.Nonempty ∧ Root.2.Nonempty
  /-- The children set is nonempty. -/
  NonemptyChilds: Childs.Nonempty
  /-- The two components of the root are disjoint. -/
  DisjointRoot: Disjoint Root.1 Root.2
  /-- Supports of distinct branches are disjoint or nested (laminar property). -/
  SupportProperty :
    ∀ p ∈ Branches,  ∀ q ∈ Branches, p ≠ q →
    (Disjoint (combinatorialSupport p) (combinatorialSupport q)∨
    combinatorialSupport p ⊆ q.1 ∨
    combinatorialSupport p ⊆ q.2 ∨
    combinatorialSupport q ⊆ p.1 ∨
    combinatorialSupport q ⊆ p.2)


lemma support_subset_root_support {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α}
  (hp : p ∈ T.Branches) :
  combinatorialSupport p ⊆ combinatorialSupport T.Root := by
  have hp_childs := T.TreeStructureChilds p hp
  dsimp [combinatorialSupport]
  exact (Finset.union_subset hp_childs.1 hp_childs.2).trans T.RootcontainsChilds

lemma child_support_card_lt_parent {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {p q : Finset α × Finset α}
  (hq : q ∈ T.Branches)
  (hparent : combinatorialSupport p = q.1 ∨ combinatorialSupport p = q.2) :
  (combinatorialSupport p).card < (combinatorialSupport q).card := by
  rcases hparent with hpq1 | hpq2
  · rw [hpq1]
    have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
    have hq2_pos : 0 < q.2.card := Finset.card_pos.mpr (T.NonemptyPairs q hq).2
    have hq_card : (combinatorialSupport q).card = q.1.card + q.2.card := by
      dsimp [combinatorialSupport]
      rw [Finset.card_union_of_disjoint hq_disj]
    calc
      q.1.card < q.1.card + q.2.card := Nat.lt_add_of_pos_right hq2_pos
      _ = (combinatorialSupport q).card := hq_card.symm
  · rw [hpq2]
    have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
    have hq1_pos : 0 < q.1.card := Finset.card_pos.mpr (T.NonemptyPairs q hq).1
    have hq_card : (combinatorialSupport q).card = q.1.card + q.2.card := by
      dsimp [combinatorialSupport]
      rw [Finset.card_union_of_disjoint hq_disj]
    calc
      q.2.card < q.1.card + q.2.card := Nat.lt_add_of_pos_left hq1_pos
      _ = (combinatorialSupport q).card := hq_card.symm

theorem exists_chain_from_root {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α}
  (hp : p ∈ T.Branches) :
  ∃ n : ℕ, ∃ chain : ℕ → (Finset α × Finset α),
    chain 0 = T.Root ∧
    chain n = p ∧
    (∀ i ≤ n, chain i ∈ T.Branches) ∧
    (∀ i < n,
      combinatorialSupport (chain (i + 1)) = (chain i).1 ∨
      combinatorialSupport (chain (i + 1)) = (chain i).2) := by
  by_cases hroot : p = T.Root
  · refine ⟨0, (fun _ => T.Root), ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [hroot]
    · intro i hi
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      simpa [hi0] using T.RootinBranches
    · intro i hi
      exact (Nat.not_lt_zero i hi).elim
  · obtain ⟨q, hq, hp_in_parent⟩ := T.TreeStructure p hp hroot
    have hparent : combinatorialSupport p = q.1 ∨ combinatorialSupport p = q.2 := by
      dsimp [pairToFinset] at hp_in_parent
      simpa [combinatorialSupport] using hp_in_parent
    rcases exists_chain_from_root (T := T) hq with ⟨k, hkrest⟩
    rcases hkrest with ⟨f, hf0, hfk, hfmem, hfstep⟩
    let g : ℕ → (Finset α × Finset α) :=
      fun i => if h : i ≤ k then f i else p
    refine ⟨k + 1, g, ?_, ?_, ?_, ?_⟩
    · have h0k : 0 ≤ k := Nat.zero_le k
      simp [g, h0k, hf0]
    · have hnot : ¬ (k + 1 ≤ k) := Nat.not_succ_le_self k
      simp [g, hnot]
    · intro idx hidx
      by_cases hidxk : idx ≤ k
      · simp [g, hidxk, hfmem idx hidxk]
      · have hidx_eq : idx = k + 1 := by omega
        subst hidx_eq
        have hnot : ¬ (k + 1 ≤ k) := Nat.not_succ_le_self k
        simp [g, hnot, hp]
    · intro idx hidx
      by_cases hidxk : idx < k
      · have hidxk_le : idx ≤ k := Nat.le_of_lt hidxk
        have hsucc_le : idx + 1 ≤ k := Nat.succ_le_of_lt hidxk
        have hstep := hfstep idx hidxk
        simpa [g, hidxk_le, hsucc_le] using hstep
      · have hidx_eq : idx = k := by omega
        have hg_k : g k = q := by
          simp [g, hfk]
        have hg_k1 : g (k + 1) = p := by
          have hnot : ¬ (k + 1 ≤ k) := Nat.not_succ_le_self k
          simp [g, hnot]
        have hg_idx : g idx = q := by simpa [hidx_eq] using hg_k
        have hg_idx1 : g (idx + 1) = p := by
          simpa [hidx_eq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hg_k1
        rw [hg_idx1, hg_idx]
        exact hparent
termination_by
  (combinatorialSupport T.Root).card - (combinatorialSupport p).card
decreasing_by
  have hparent :
      combinatorialSupport p = q.1 ∨ combinatorialSupport p = q.2 := by
    dsimp [pairToFinset] at hp_in_parent
    simpa [combinatorialSupport] using hp_in_parent
  have hcard_lt :
      (combinatorialSupport p).card < (combinatorialSupport q).card :=
    child_support_card_lt_parent (T := T) hq hparent
  have hq_le_root :
      (combinatorialSupport q).card ≤ (combinatorialSupport T.Root).card :=
    Finset.card_le_card (support_subset_root_support (T := T) hq)
  have hp_le_root :
      (combinatorialSupport p).card ≤ (combinatorialSupport T.Root).card :=
    Finset.card_le_card (support_subset_root_support (T := T) hp)
  omega




theorem exists_chain_from_root_to_top {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {t : α}
  (hp : t ∈ T.Tops) :
  ∃ n : ℕ, ∃ chain : ℕ → (Finset α × Finset α),
    chain 0 = T.Root ∧
    ({t}=(chain n).1 ∨ {t}=(chain n).2) ∧
    (∀ i ≤ n, chain i ∈ T.Branches) ∧
    (∀ i < n,
      combinatorialSupport (chain (i + 1)) = (chain i).1 ∨
      combinatorialSupport (chain (i + 1)) = (chain i).2) := by
  obtain ⟨q, hq, hqt⟩ := T.TopsareTops t hp
  rcases exists_chain_from_root (T := T) hq with ⟨n, chain, h0, hn, hmem, hstep⟩
  have hq_cases : ({t} : Finset α) = q.1 ∨ ({t} : Finset α) = q.2 := by
    dsimp [pairToFinset] at hqt
    simpa [Finset.mem_insert, Finset.mem_singleton] using hqt
  have hchain_top : ({t} : Finset α) = (chain n).1 ∨ ({t} : Finset α) = (chain n).2 := by
    simpa [hn] using hq_cases
  exact ⟨n, chain, h0, hchain_top, hmem, hstep⟩


/-- The branch containing a given component is unique: if the same finset belongs to
    `pairToFinset q` and `pairToFinset r` (both in `T.Branches`), then `q = r`. -/
lemma unique_parent {α : Type*} [DecidableEq α]
    {T : BinaryTreeWithRootandTops α} {s : Finset α}
    {q r : Finset α × Finset α}
    (hq : q ∈ T.Branches) (hr : r ∈ T.Branches)
    (hsq : s ∈ pairToFinset q) (hsr : s ∈ pairToFinset r) :
    q = r := by
  by_contra hne
  exact absurd hsr
    (Finset.disjoint_left.mp (T.DistinctComponentsPairs q hq r hr hne) hsq)

/-- Any two valid chains from `T.Root` to the same branch `p` have the same length
    and agree entry-by-entry. -/
theorem chain_from_root_unique {α : Type*} [DecidableEq α]
    {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α}
    (hp : p ∈ T.Branches)
    {n1 n2 : ℕ}
    {c1 c2 : ℕ → Finset α × Finset α}
    (h1_0 : c1 0 = T.Root) (h1_n : c1 n1 = p)
    (h1_mem : ∀ i ≤ n1, c1 i ∈ T.Branches)
    (h1_step : ∀ i < n1,
        combinatorialSupport (c1 (i + 1)) = (c1 i).1 ∨
        combinatorialSupport (c1 (i + 1)) = (c1 i).2)
    (h2_0 : c2 0 = T.Root) (h2_n : c2 n2 = p)
    (h2_mem : ∀ i ≤ n2, c2 i ∈ T.Branches)
    (h2_step : ∀ i < n2,
        combinatorialSupport (c2 (i + 1)) = (c2 i).1 ∨
        combinatorialSupport (c2 (i + 1)) = (c2 i).2) :
    n1 = n2 ∧ ∀ i ≤ n1, c1 i = c2 i := by
  -- ── Backward-agreement sub-lemma ─────────────────────────────────────────
  -- For every k ≤ n1 and k ≤ n2, the chains agree k steps from the end.
  have back : ∀ k, k ≤ n1 → k ≤ n2 → c1 (n1 - k) = c2 (n2 - k) := by
    intro k
    induction k with
    | zero => intros; simp [h1_n, h2_n]
    | succ k ih =>
      intro hsk1 hsk2
      have hk1 : k ≤ n1 := Nat.le_of_succ_le hsk1
      have hk2 : k ≤ n2 := Nat.le_of_succ_le hsk2
      have hklt1 : k < n1 := by omega
      have hklt2 : k < n2 := by omega
      have hk_eq := ih hk1 hk2
      -- Step conditions at index (n? - (k+1))
      have hst1 := h1_step (n1 - (k + 1)) (by omega)
      rw [show n1 - (k + 1) + 1 = n1 - k from by omega] at hst1
      have hst2 := h2_step (n2 - (k + 1)) (by omega)
      rw [show n2 - (k + 1) + 1 = n2 - k from by omega] at hst2
      -- Both step conditions now mention c1 (n1 - k) (via hk_eq)
      rw [← hk_eq] at hst2
      -- Convert to pairToFinset membership
      have hmem1 := h1_mem (n1 - (k + 1)) (by omega)
      have hmem2 := h2_mem (n2 - (k + 1)) (by omega)
      have hpq : combinatorialSupport (c1 (n1 - k)) ∈ pairToFinset (c1 (n1 - (k + 1))) := by
        dsimp [pairToFinset]; simpa [Finset.mem_insert, Finset.mem_singleton] using hst1
      have hpr : combinatorialSupport (c1 (n1 - k)) ∈ pairToFinset (c2 (n2 - (k + 1))) := by
        dsimp [pairToFinset]; simpa [Finset.mem_insert, Finset.mem_singleton] using hst2
      exact unique_parent hmem1 hmem2 hpq hpr
  -- ── Lengths are equal ────────────────────────────────────────────────────
  have hn_eq : n1 = n2 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · -- n1 < n2: backward-agree at distance n1 gives c2 (n2 - n1) = Root
      have hagree := back n1 le_rfl (by omega)
      simp only [Nat.sub_self, h1_0] at hagree
      -- hagree : c2 (n2 - n1) = T.Root
      -- But that means Root is a "child" branch at position n2-n1 > 0
      have hst2 := h2_step (n2 - n1 - 1) (by omega)
      rw [show n2 - n1 - 1 + 1 = n2 - n1 from by omega] at hst2
      rw [← hagree] at hst2
      have hmem2 := h2_mem (n2 - n1 - 1) (by omega)
      linarith [child_support_card_lt_parent (T := T) hmem2 hst2,
                Finset.card_le_card (support_subset_root_support (T := T) hmem2)]
    · -- n1 > n2: symmetric
      have hagree := back n2 (by omega) le_rfl
      simp only [Nat.sub_self, h2_0] at hagree
      -- hagree : c1 (n1 - n2) = T.Root
      have hst1 := h1_step (n1 - n2 - 1) (by omega)
      rw [show n1 - n2 - 1 + 1 = n1 - n2 from by omega] at hst1
      rw [hagree] at hst1
      have hmem1 := h1_mem (n1 - n2 - 1) (by omega)
      linarith [child_support_card_lt_parent (T := T) hmem1 hst1,
                Finset.card_le_card (support_subset_root_support (T := T) hmem1)]
  -- ── Pointwise agreement ───────────────────────────────────────────────────
  refine ⟨hn_eq, fun i hi => ?_⟩
  have hagree := back (n1 - i) (Nat.sub_le n1 i) (hn_eq ▸ Nat.sub_le n1 i)
  simp only [show n1 - (n1 - i) = i from by omega] at hagree
  -- After hn_eq ▸, n2 = n1 in hagree, so n2 - (n1 - i) = i as well
  convert hagree using 2
  omega

theorem chain_from_root_to_top_unique {α : Type*} [DecidableEq α]
    {T : BinaryTreeWithRootandTops α} {t : α}
    (_hp : t ∈ T.Tops)
    {n1 n2 : ℕ}
    {c1 c2 : ℕ → Finset α × Finset α}
    (h1_0 : c1 0 = T.Root) (h1_n : ({t} = (c1 n1).1 ∨ {t} = (c1 n1).2))
    (h1_mem : ∀ i ≤ n1, c1 i ∈ T.Branches)
    (h1_step : ∀ i < n1,
        combinatorialSupport (c1 (i + 1)) = (c1 i).1 ∨
        combinatorialSupport (c1 (i + 1)) = (c1 i).2)
    (h2_0 : c2 0 = T.Root) (h2_n : ({t} = (c2 n2).1 ∨ {t} = (c2 n2).2))
    (h2_mem : ∀ i ≤ n2, c2 i ∈ T.Branches)
    (h2_step : ∀ i < n2,
        combinatorialSupport (c2 (i + 1)) = (c2 i).1 ∨
        combinatorialSupport (c2 (i + 1)) = (c2 i).2) :
    n1 = n2 ∧ ∀ i ≤ n1, c1 i = c2 i := by
  -- {t} ∈ pairToFinset (c1 n1) and {t} ∈ pairToFinset (c2 n2),
  -- so unique_parent forces c1 n1 = c2 n2.
  have hmem1 := h1_mem n1 le_rfl
  have hmem2 := h2_mem n2 le_rfl
  have ht1 : ({t} : Finset α) ∈ pairToFinset (c1 n1) := by
    dsimp [pairToFinset]; simpa [Finset.mem_insert, Finset.mem_singleton] using h1_n
  have ht2 : ({t} : Finset α) ∈ pairToFinset (c2 n2) := by
    dsimp [pairToFinset]; simpa [Finset.mem_insert, Finset.mem_singleton] using h2_n
  have hend_eq : c1 n1 = c2 n2 := unique_parent hmem1 hmem2 ht1 ht2
  exact chain_from_root_unique hmem1 h1_0 rfl h1_mem h1_step h2_0 hend_eq.symm h2_mem h2_step

/-- The length of the unique chain from `T.Root` to branch `p`. -/
noncomputable def chainLength {α : Type*} [DecidableEq α]
    {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α}
    (hp : p ∈ T.Branches) : ℕ :=
  (exists_chain_from_root hp).choose




/-- The unique chain from `T.Root` to branch `p`. -/
noncomputable def ChainToRoot {α : Type*} [DecidableEq α]
    {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α}
    (hp : p ∈ T.Branches) : ℕ → Finset α × Finset α :=
  (exists_chain_from_root hp).choose_spec.choose

/-- The defining properties of `ChainToRoot`. -/
lemma ChainToRoot_spec {α : Type*} [DecidableEq α]
    {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α}
    (hp : p ∈ T.Branches) :
    ChainToRoot hp 0 = T.Root ∧
    ChainToRoot hp (chainLength hp) = p ∧
    (∀ i ≤ chainLength hp, ChainToRoot hp i ∈ T.Branches) ∧
    (∀ i < chainLength hp,
      combinatorialSupport (ChainToRoot hp (i + 1)) = (ChainToRoot hp i).1 ∨
      combinatorialSupport (ChainToRoot hp (i + 1)) = (ChainToRoot hp i).2) :=
  (exists_chain_from_root hp).choose_spec.choose_spec

lemma ChainToRoot_zero {α : Type*} [DecidableEq α]
    {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α}
    (hp : p ∈ T.Branches) : ChainToRoot hp 0 = T.Root :=
  (ChainToRoot_spec hp).1

lemma ChainToRoot_end {α : Type*} [DecidableEq α]
    {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α}
    (hp : p ∈ T.Branches) : ChainToRoot hp (chainLength hp) = p :=
  (ChainToRoot_spec hp).2.1

lemma ChainToRoot_mem {α : Type*} [DecidableEq α]
    {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α}
    (hp : p ∈ T.Branches) {i : ℕ} (hi : i ≤ chainLength hp) :
    ChainToRoot hp i ∈ T.Branches :=
  (ChainToRoot_spec hp).2.2.1 i hi

lemma ChainToRoot_step {α : Type*} [DecidableEq α]
    {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α}
    (hp : p ∈ T.Branches) {i : ℕ} (hi : i < chainLength hp) :
    combinatorialSupport (ChainToRoot hp (i + 1)) = (ChainToRoot hp i).1 ∨
    combinatorialSupport (ChainToRoot hp (i + 1)) = (ChainToRoot hp i).2 :=
  (ChainToRoot_spec hp).2.2.2 i hi

/-- Any chain with the same endpoint as `ChainToRoot hp` must agree with it. -/
lemma ChainToRoot_unique {α : Type*} [DecidableEq α]
    {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α}
    (hp : p ∈ T.Branches)
    {n : ℕ} {c : ℕ → Finset α × Finset α}
    (hc0 : c 0 = T.Root) (hcn : c n = p)
    (hcmem : ∀ i ≤ n, c i ∈ T.Branches)
    (hcstep : ∀ i < n,
        combinatorialSupport (c (i + 1)) = (c i).1 ∨
        combinatorialSupport (c (i + 1)) = (c i).2) :
    n = chainLength hp ∧ ∀ i ≤ n, c i = ChainToRoot hp i := by
  have := chain_from_root_unique hp hc0 hcn hcmem hcstep
      (ChainToRoot_zero hp) (ChainToRoot_end hp)
      (fun i hi => ChainToRoot_mem hp hi) (fun i hi => ChainToRoot_step hp hi)
  exact ⟨this.1, this.2⟩


lemma suppp_p_incl_q1_disjoint_pairfinset {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α} {q : Finset α × Finset α}
   (hq : q ∈ T.Branches) (hincl : combinatorialSupport p ⊆ q.1) (hdisj : Disjoint p.1 p.2)
   (hnempty : p.1.Nonempty ∧ p.2.Nonempty) :
    Disjoint (pairToFinset p) (pairToFinset q) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy
    dsimp [pairToFinset] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    cases hx with
    | inl hx_p1 => -- x = p.1
        cases hy with
        | inl hy_q1 => -- y = q.1
            rw [hx_p1, hy_q1]
            intro h_eq
            -- p.1 = q.1, but p.1 ⊆ combinatorialSupport p ⊆ q.1
            -- and p.1 is nonempty, so p.1 ⊂ q.1 (proper subset)
            -- Since p.1 = q.1 and combinatorialSupport p = p.1 ∪ p.2 = q.1 ∪ p.2
            -- but combinatorialSupport p ⊆ q.1, we get q.1 ∪ p.2 ⊆ q.1
            -- This implies p.2 ⊆ q.1, but p.1 = q.1 and p.1 ∩ p.2 = ∅
            -- So p.2 ∩ q.1 = ∅, contradicting p.2 ⊆ q.1 and p.2.Nonempty
            have hp1_eq_q1 : p.1 = q.1 := h_eq
            have hp2_sub_q1 : p.2 ⊆ q.1 := by
              have hp_support_sub : combinatorialSupport p ⊆ q.1 := hincl
              have hp2_sub_support : p.2 ⊆ combinatorialSupport p := Finset.subset_union_right
              exact hp2_sub_support.trans hp_support_sub
            have hp_disj : Disjoint p.1 p.2 := hdisj
            obtain ⟨y, hy⟩ := hnempty.2
            have hy_in_q1 : y ∈ q.1 := hp2_sub_q1 hy
            have hy_in_p1 : y ∈ p.1 := by rwa [hp1_eq_q1]
            exact Finset.disjoint_left.mp hp_disj hy_in_p1 hy
        | inr hy_q2 => -- y = q.2
            rw [hx_p1, hy_q2]
            intro h_eq
            -- p.1 = q.2, but combinatorialSupport p ⊆ q.1 and p.1 ⊆ combinatorialSupport p
            -- So p.1 ⊆ q.1, but also p.1 = q.2, and q.1 ∩ q.2 = ∅
            have hp1_sub_q1 : p.1 ⊆ q.1 := (Finset.subset_union_left).trans hincl
            have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
            obtain ⟨a, ha⟩ := hnempty.1
            have ha_in_q1 : a ∈ q.1 := hp1_sub_q1 ha
            have ha_in_q2 : a ∈ q.2 := by rw [← h_eq]; exact ha
            exact Finset.disjoint_left.mp hq_disj ha_in_q1 ha_in_q2
    | inr hx_p2 => -- x = p.2
        cases hy with
        | inl hy_q1 => -- y = q.1
            rw [hx_p2, hy_q1]
            intro h_eq
            -- p.2 = q.1, but we have hincl: combinatorialSupport p ⊆ q.1
            -- Since combinatorialSupport p = p.1 ∪ p.2, we get p.1 ∪ p.2 ⊆ q.1
            -- In particular, p.2 ⊆ q.1, but h_eq says p.2 = q.1
            -- However, p.1 is nonempty and disjoint from p.2, so p.1 ∪ p.2 ⊃ p.2
            -- This means q.1 = p.2 ⊂ p.1 ∪ p.2 ⊆ q.1, which is impossible
            have hp2_sub_support : p.2 ⊆ combinatorialSupport p := Finset.subset_union_right
            have hp2_sub_q1 : p.2 ⊆ q.1 := hp2_sub_support.trans hincl
            have hp2_eq_q1 : p.2 = q.1 := h_eq
            have hp1_sub_q1 : p.1 ⊆ q.1 := (Finset.subset_union_left).trans hincl
            -- Since p.1 and p.2 are disjoint and both nonempty, we have p.1 ∪ p.2 ⊃ p.2
            have hp1_nonempty : p.1.Nonempty := hnempty.1
            have hp_disj : Disjoint p.1 p.2 := hdisj
            obtain ⟨a, ha⟩ := hp1_nonempty
            have ha_in_q1 : a ∈ q.1 := hp1_sub_q1 ha
            have ha_in_p2 : a ∈ p.2 := by
              rw [hp2_eq_q1]
              exact ha_in_q1
            exact Finset.disjoint_left.mp hp_disj ha ha_in_p2
          | inr hy_q2 => -- y = q.2
            rw [hx_p2, hy_q2]
            intro h_eq
            -- p.2 = q.2, but p.2 ⊆ q.1 and q.1 ∩ q.2 = ∅
            have hp2_sub_q1 : p.2 ⊆ q.1 := (Finset.subset_union_right).trans hincl
            have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
            obtain ⟨a, ha⟩ := hnempty.2
            have ha_in_q1 : a ∈ q.1 := hp2_sub_q1 ha
            have ha_in_q2 : a ∈ q.2 := by rw [← h_eq]; exact ha
            exact Finset.disjoint_left.mp hq_disj ha_in_q1 ha_in_q2


lemma suppp_p_incl_q2_disjoint_pairfinset {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α} {q : Finset α × Finset α}
   (hq : q ∈ T.Branches) (hincl : combinatorialSupport p ⊆ q.2) (hdisj : Disjoint p.1 p.2)
   (hnempty : p.1.Nonempty ∧ p.2.Nonempty) :
    Disjoint (pairToFinset p) (pairToFinset q) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy
    dsimp [pairToFinset] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    cases hx with
    | inl hx_p1 => -- x = p.1
      cases hy with
      | inl hy_q1 => -- y = q.1
        rw [hx_p1, hy_q1]
        intro h_eq
        -- p.1 = q.1, but combinatorialSupport p ⊆ q.2 and p.1 ⊆ combinatorialSupport p
        -- So p.1 ⊆ q.2, but also p.1 = q.1, and q.1 ∩ q.2 = ∅
        have hp1_sub_q2 : p.1 ⊆ q.2 := (Finset.subset_union_left).trans hincl
        have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
        obtain ⟨a, ha⟩ := hnempty.1
        have ha_in_q2 : a ∈ q.2 := hp1_sub_q2 ha
        have ha_in_q1 : a ∈ q.1 := by rw [← h_eq]; exact ha
        exact Finset.disjoint_left.mp hq_disj ha_in_q1 ha_in_q2
      | inr hy_q2 => -- y = q.2
        rw [hx_p1, hy_q2]
        intro h_eq
        -- p.1 = q.2, but p.1 ⊆ combinatorialSupport p ⊆ q.2
        -- and p.1 is nonempty, so p.1 ⊂ q.2 (proper subset)
        -- Since p.1 = q.2 and combinatorialSupport p = p.1 ∪ p.2 = q.2 ∪ p.2
        -- but combinatorialSupport p ⊆ q.2, we get q.2 ∪ p.2 ⊆ q.2
        -- This implies p.2 ⊆ q.2, but p.1 = q.2 and p.1 ∩ p.2 = ∅
        -- So p.2 ∩ q.2 = ∅, contradicting p.2 ⊆ q.2 and p.2.Nonempty
        have hp1_eq_q2 : p.1 = q.2 := h_eq
        have hp2_sub_q2 : p.2 ⊆ q.2 := by
          have hp_support_sub : combinatorialSupport p ⊆ q.2 := hincl
          have hp2_sub_support : p.2 ⊆ combinatorialSupport p := Finset.subset_union_right
          exact hp2_sub_support.trans hp_support_sub
        have hp_disj : Disjoint p.1 p.2 := hdisj
        obtain ⟨y, hy⟩ := hnempty.2
        have hy_in_q2 : y ∈ q.2 := hp2_sub_q2 hy
        have hy_in_p1 : y ∈ p.1 := by rwa [hp1_eq_q2]
        exact Finset.disjoint_left.mp hp_disj hy_in_p1 hy
    | inr hx_p2 => -- x = p.2
      cases hy with
      | inl hy_q1 => -- y = q.1
        rw [hx_p2, hy_q1]
        intro h_eq
        -- p.2 = q.1, but p.2 ⊆ q.2 and q.1 ∩ q.2 = ∅
        have hp2_sub_q2 : p.2 ⊆ q.2 := (Finset.subset_union_right).trans hincl
        have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
        obtain ⟨a, ha⟩ := hnempty.2
        have ha_in_q2 : a ∈ q.2 := hp2_sub_q2 ha
        have ha_in_q1 : a ∈ q.1 := by rw [← h_eq]; exact ha
        exact Finset.disjoint_left.mp hq_disj ha_in_q1 ha_in_q2
        | inr hy_q2 => -- y = q.2
        rw [hx_p2, hy_q2]
        intro h_eq
        -- p.2 = q.2, but we have hincl: combinatorialSupport p ⊆ q.2
        -- Since combinatorialSupport p = p.1 ∪ p.2, we get p.1 ∪ p.2 ⊆ q.2
        -- In particular, p.2 ⊆ q.2, but h_eq says p.2 = q.2
        -- However, p.1 is nonempty and disjoint from p.2, so p.1 ∪ p.2 ⊃ p.2
        -- This means q.2 = p.2 ⊂ p.1 ∪ p.2 ⊆ q.2, which is impossible
        have hp2_sub_support : p.2 ⊆ combinatorialSupport p := Finset.subset_union_right
        have hp2_sub_q2 : p.2 ⊆ q.2 := hp2_sub_support.trans hincl
        have hp2_eq_q2 : p.2 = q.2 := h_eq
        have hp1_sub_q2 : p.1 ⊆ q.2 := (Finset.subset_union_left).trans hincl
        -- Since p.1 and p.2 are disjoint and both nonempty, we have p.1 ∪ p.2 ⊃ p.2
        have hp1_nonempty : p.1.Nonempty := hnempty.1
        have hp_disj : Disjoint p.1 p.2 := hdisj
        obtain ⟨a, ha⟩ := hp1_nonempty
        have ha_in_q2 : a ∈ q.2 := hp1_sub_q2 ha
        have ha_in_p2 : a ∈ p.2 := by
          rw [hp2_eq_q2]
          exact ha_in_q2
        exact Finset.disjoint_left.mp hp_disj ha ha_in_p2

lemma disjoint_suppport_pairfinset_disjoint {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α} {q : Finset α × Finset α} (hp : p ∈
      T.Branches) :
 Disjoint (combinatorialSupport p) (combinatorialSupport q) → Disjoint (pairToFinset p)
     (pairToFinset q) := by
  intro h_supp_disj
  rw [Finset.disjoint_iff_ne]
  intro x hx y hy
  dsimp [pairToFinset] at hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  cases hx with
  | inl hx_p1 => -- x = p.1
      cases hy with
      | inl hy_q1 => -- y = q.1
          rw [hx_p1, hy_q1]
          intro h_eq
          have hp1_nonempty : p.1.Nonempty := (T.NonemptyPairs p hp).1
          obtain ⟨a, ha⟩ := hp1_nonempty
          have ha_in_p : a ∈ combinatorialSupport p := Finset.mem_union_left p.2 ha
          have ha_in_q : a ∈ combinatorialSupport q := by
              dsimp [combinatorialSupport]
              rw [h_eq] at ha
              exact Finset.mem_union_left q.2 ha
          exact Finset.disjoint_left.mp h_supp_disj ha_in_p ha_in_q
      | inr hy_q2 => -- y = q.2
          rw [hx_p1, hy_q2]
          intro h_eq
          have hp1_nonempty : p.1.Nonempty := (T.NonemptyPairs p hp).1
          obtain ⟨a, ha⟩ := hp1_nonempty
          have ha_in_p : a ∈ combinatorialSupport p := Finset.mem_union_left p.2 ha
          have ha_in_q : a ∈ combinatorialSupport q := by
              dsimp [combinatorialSupport]
              rw [h_eq] at ha
              exact Finset.mem_union_right q.1 ha
          exact Finset.disjoint_left.mp h_supp_disj ha_in_p ha_in_q
  | inr hx_p2 => -- x = p.2
      cases hy with
      | inl hy_q1 => -- y = q.1
          rw [hx_p2, hy_q1]
          intro h_eq
          have hp2_nonempty : p.2.Nonempty := (T.NonemptyPairs p hp).2
          obtain ⟨a, ha⟩ := hp2_nonempty
          have ha_in_p : a ∈ combinatorialSupport p := Finset.mem_union_right p.1 ha
          have ha_in_q : a ∈ combinatorialSupport q := by
              dsimp [combinatorialSupport]
              rw [h_eq] at ha
              exact Finset.mem_union_left q.2 ha
          exact Finset.disjoint_left.mp h_supp_disj ha_in_p ha_in_q
      | inr hy_q2 => -- y = q.2
          rw [hx_p2, hy_q2]
          intro h_eq
          have hp2_nonempty : p.2.Nonempty := (T.NonemptyPairs p hp).2
          obtain ⟨a, ha⟩ := hp2_nonempty
          have ha_in_p : a ∈ combinatorialSupport p := Finset.mem_union_right p.1 ha
          have ha_in_q : a ∈ combinatorialSupport q := by
              dsimp [combinatorialSupport]
              rw [h_eq] at ha
              exact Finset.mem_union_right q.1 ha
          exact Finset.disjoint_left.mp h_supp_disj ha_in_p ha_in_q


lemma support_not_subset_components {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {q : Finset α × Finset α} (hq : q ∈ T.Branches) :
  ¬(combinatorialSupport q ⊆ q.1) ∧ ¬(combinatorialSupport q ⊆ q.2) := by
  constructor
  · -- ¬(combinatorialSupport q ⊆ q.1)
    intro h
    -- combinatorialSupport q = q.1 ∪ q.2, so if q.1 ∪ q.2 ⊆ q.1, then q.2 ⊆ q.1
    dsimp [combinatorialSupport] at h
    have hq2_sub : q.2 ⊆ q.1 := by
      intro x hx
      exact h (Finset.mem_union_right q.1 hx)
    -- But q.1 and q.2 are disjoint and q.2 is nonempty
    have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
    have hq2_nonempty : q.2.Nonempty := (T.NonemptyPairs q hq).2
    obtain ⟨y, hy⟩ := hq2_nonempty
    have hy_in_q1 : y ∈ q.1 := hq2_sub hy
    have hy_not_q1 : y ∉ q.1 := Finset.disjoint_right.mp hq_disj hy
    exact hy_not_q1 hy_in_q1
  · -- ¬(combinatorialSupport q ⊆ q.2)
    intro h
    dsimp [combinatorialSupport] at h
    have hq1_sub : q.1 ⊆ q.2 := by
      intro x hx
      exact h (Finset.mem_union_left q.2 hx)
    have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
    have hq1_nonempty : q.1.Nonempty := (T.NonemptyPairs q hq).1
    obtain ⟨y, hy⟩ := hq1_nonempty
    have hy_in_q2 : y ∈ q.2 := hq1_sub hy
    have hy_not_q2 : y ∉ q.2 := Finset.disjoint_left.mp hq_disj hy
    exact hy_not_q2 hy_in_q2


lemma inclusion_q1orq2 {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {r : Finset α × Finset α} {q : Finset α × Finset α} (hr : r ∈
      T.Branches) (hq : q ∈ T.Branches)
  (h2 : r ≠ q ∧ combinatorialSupport r ⊆ combinatorialSupport q) : combinatorialSupport r ⊆ q.1 ∨
      combinatorialSupport r ⊆ q.2  := by
  have h_support := T.SupportProperty r hr q hq h2.1
  cases h_support with
  | inl hdisj =>
      -- This case contradicts h2.2 since r and q have disjoint supports but r ⊆ q
      exfalso
      have hr_nonempty : (combinatorialSupport r).Nonempty := by
          dsimp [combinatorialSupport]
          exact Finset.Nonempty.inl (T.NonemptyPairs r hr).1
      obtain ⟨x, hx⟩ := hr_nonempty
      have hx_in_q : x ∈ combinatorialSupport q := h2.2 hx
      have hx_contra : x ∉ combinatorialSupport q := Finset.disjoint_left.mp hdisj hx
      exact hx_contra hx_in_q
  | inr hcases =>
      cases hcases with
      | inl hr_sub_q1 =>
          -- combinatorialSupport r ⊆ q.1 - this case should be possible
          left
          exact hr_sub_q1
      | inr hrest =>
          cases hrest with
          | inl hr_sub_q2 =>
              -- combinatorialSupport r ⊆ q.2 - this case should be possible
              right
              exact hr_sub_q2
          | inr hfinal =>
              cases hfinal with
              | inl hq_sub_r1 =>
                  -- combinatorialSupport q ⊆ r.1 - this case is impossible
                  exfalso
                  -- Since h2.2: combinatorialSupport r ⊆ combinatorialSupport q
                  -- and hq_sub_r1: combinatorialSupport q ⊆ r.1
                  -- We get combinatorialSupport r ⊆ combinatorialSupport q ⊆ r.1
                  -- But r.1 ⊆ combinatorialSupport r, so we have equality
                  -- This contradicts support_not_subset_components
                  have hr_sub_r1 : combinatorialSupport r ⊆ r.1 := h2.2.trans hq_sub_r1
                  have h_not_subset := support_not_subset_components hr
                  exact h_not_subset.1 hr_sub_r1
              | inr hq_sub_r2 =>
                  -- combinatorialSupport q ⊆ r.2 - this case is impossible
                  exfalso
                  -- Similar reasoning as above
                  have hr_sub_r2 : combinatorialSupport r ⊆ r.2 := h2.2.trans hq_sub_r2
                  have h_not_subset := support_not_subset_components hr
                  exact h_not_subset.2 hr_sub_r2



lemma eq_iff_eq_support {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α} {q : Finset α × Finset α} (h0 : p ∈
      T.Branches) (h1 : q ∈ T.Branches) : p=q ↔ combinatorialSupport p= combinatorialSupport q := by
  constructor
  · -- Forward direction: p = q → combinatorialSupport p = combinatorialSupport q
      intro h
      rw [h]
  · -- Reverse direction: combinatorialSupport p = combinatorialSupport q → p = q
      intro h_supp_eq
      by_cases h_eq : p = q
      · exact h_eq
      · -- Case p ≠ q: use SupportProperty to derive contradiction
          exfalso
          have h_support_cases := T.SupportProperty p h0 q h1 h_eq
          cases h_support_cases with
          | inl h_disj =>
              -- Case: supports are disjoint, but we have combinatorialSupport p =
              -- combinatorialSupport q
              have p_nonempty : (combinatorialSupport p).Nonempty := by
                  dsimp [combinatorialSupport]
                  exact Finset.Nonempty.inl (T.NonemptyPairs p h0).1
              rw [h_supp_eq] at h_disj
              have : ¬Disjoint (combinatorialSupport q) (combinatorialSupport q) :=
                  Finset.not_disjoint_iff_nonempty_inter.mpr (by simp [h_supp_eq ▸ p_nonempty])
              exact this h_disj
          | inr h_cases =>
              cases h_cases with
              | inl h_p_sub_q1 =>
                  -- combinatorialSupport p ⊆ q.1, but combinatorialSupport p =
                  -- combinatorialSupport q
                  rw [h_supp_eq] at h_p_sub_q1
                  have h_not_subset := support_not_subset_components h1
                  exact h_not_subset.1 h_p_sub_q1
              | inr h_rest =>
                  cases h_rest with
                  | inl h_p_sub_q2 =>
                      -- Similar contradiction for q.2
                      rw [h_supp_eq] at h_p_sub_q2
                      have h_not_subset := support_not_subset_components h1
                      exact h_not_subset.2 h_p_sub_q2
                  | inr h_final =>
                      cases h_final with
                      | inl h_q_sub_p1 =>
                          -- combinatorialSupport q ⊆ p.1, but they're equal
                          rw [← h_supp_eq] at h_q_sub_p1
                          have h_not_subset := support_not_subset_components h0
                          exact h_not_subset.1 h_q_sub_p1
                      | inr h_q_sub_p2 =>
                          -- combinatorialSupport q ⊆ p.2, but they're equal
                          rw [← h_supp_eq] at h_q_sub_p2
                          have h_not_subset := support_not_subset_components h0
                          exact h_not_subset.2 h_q_sub_p2



lemma inclusion_support {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α} {q : Finset α × Finset α} (h0 : p ∈
      T.Branches ∧ q ∈ T.Branches) (h : p.1 ⊆ combinatorialSupport q) :
  combinatorialSupport p ⊆ combinatorialSupport q ∨ p.1= combinatorialSupport q:= by
  by_cases hpq : p = q
  case pos =>
    -- Case: p = q
    simp [hpq]
  case neg =>
    -- Case: p ≠ q
    have hSup := T.SupportProperty p h0.1 q h0.2 hpq
    cases hSup with
    | inl hdisj =>
      -- Contradiction: if they're disjoint but p.1 or p.2 ⊆ combinatorialSupport q
      -- We have h : p.1 ⊆ combinatorialSupport q and hdisj : Disjoint (combinatorialSupport p)
      -- (combinatorialSupport q)
      -- This leads to a contradiction since p.1 ⊆ combinatorialSupport p
      have hp1_nonempty : p.1.Nonempty := (T.NonemptyPairs p h0.1).1
      obtain ⟨x, hx⟩ := hp1_nonempty
      have hx_in_p : x ∈ combinatorialSupport p := Finset.mem_union_left p.2 hx
      have hx_in_q : x ∈ combinatorialSupport q := by
        -- h : p.1 ⊆ combinatorialSupport q, so h hx directly gives x ∈ combinatorialSupport q
        exact h hx
      exact False.elim (Finset.disjoint_left.mp hdisj hx_in_p hx_in_q)
    | inr hrest =>
      cases hrest with
      | inl hp_sub_q1 =>
      dsimp [combinatorialSupport] at hp_sub_q1
      dsimp [combinatorialSupport]
      have h4: q.1⊆ q.1∪ q.2:= by
        exact Finset.subset_union_left
      exact Or.inl (hp_sub_q1.trans h4)
      | inr hrest2 =>
        cases hrest2 with
        | inl hp_sub_q2 =>
          dsimp [combinatorialSupport] at hp_sub_q2
          dsimp [combinatorialSupport]
          have h5: q.2⊆ q.1∪ q.2:= by
           exact Finset.subset_union_right
          exact Or.inl (Finset.Subset.trans hp_sub_q2 h5)
        | inr hrest3 =>
          cases hrest3 with
            | inl hq_sub_p1 =>
            -- This case: combinatorialSupport q ⊆ p.1
            -- Combined with h : p.1 ⊆ combinatorialSupport q
            -- This gives us p.1 = combinatorialSupport q
            have hp1_eq_q : p.1 = combinatorialSupport q := by
              exact Finset.Subset.antisymm h hq_sub_p1
            exact Or.inr hp1_eq_q
            | inr hq_sub_p2 =>
            -- This case is impossible: we have hq_sub_p2 : combinatorialSupport q ⊆ p.2
            -- and h : p.1 ⊆ combinatorialSupport q
            -- But p.1 and p.2 are disjoint, so this is a contradiction
              exfalso
              have hp_disj : Disjoint p.1 p.2 := T.DisjointComponents p h0.1
              have hp1_nonempty : p.1.Nonempty := (T.NonemptyPairs p h0.1).1
              obtain ⟨x, hx⟩ := hp1_nonempty
              have hx_in_q : x ∈ combinatorialSupport q := h hx
              have hx_in_p2 : x ∈ p.2 := hq_sub_p2 hx_in_q
              have hx_not_p2 : x ∉ p.2 := Finset.disjoint_left.mp hp_disj hx
              exact hx_not_p2 hx_in_p2

lemma inclusion_support_finner_1 {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α} {q : Finset α × Finset α} (h0 : p ∈
      T.Branches ∧ q ∈ T.Branches) (h : p.1 ⊆ q.1) :
  combinatorialSupport p ⊆ q.1 ∨ p=q:= by
  by_cases hpq : p = q
  · -- Case: p = q
    simp [hpq]
  · -- Case: p ≠ q
    have hSup := T.SupportProperty p h0.1 q h0.2 hpq
    cases hSup with
    | inl hdisj =>
      -- Contradiction: if they're disjoint but p.1 or p.2 ⊆ combinatorialSupport q
      -- We have h : p.1 ⊆ combinatorialSupport q and hdisj : Disjoint (combinatorialSupport p)
      -- (combinatorialSupport q)
      -- This leads to a contradiction since p.1 ⊆ combinatorialSupport p
      -- Contradiction: if p.1 ⊆ q.1 and the supports are disjoint, we have a contradiction
      -- Because p.1 is nonempty and p.1 ⊆ combinatorialSupport p
      have hp1_nonempty : p.1.Nonempty := (T.NonemptyPairs p h0.1).1
      obtain ⟨x, hx⟩ := hp1_nonempty
      have hx_in_p_support : x ∈ combinatorialSupport p := Finset.mem_union_left p.2 hx
      have hx_in_q1 : x ∈ q.1 := h hx
      have hx_in_q_support : x ∈ combinatorialSupport q := Finset.mem_union_left q.2 hx_in_q1
      exact False.elim (Finset.disjoint_left.mp hdisj hx_in_p_support hx_in_q_support)
    | inr hrest =>
      cases hrest with
      | inl hp_sub_q1 =>
        exact Or.inl hp_sub_q1
      | inr hrest2 =>
        cases hrest2 with
        | inl hp_sub_q2 =>
          -- This case is impossible: we have h : p.1 ⊆ q.1 and hp_sub_q2 : combinatorialSupport p
          -- ⊆ q.2
          -- But combinatorialSupport p = p.1 ∪ p.2, so p.1 ⊆ combinatorialSupport p ⊆ q.2
          -- This means p.1 ⊆ q.2, but we also have h : p.1 ⊆ q.1
          -- Since q.1 and q.2 are disjoint and p.1 is nonempty, this is a contradiction
          exfalso
          have hp1_sub_q2 : p.1 ⊆ q.2 := by
            have hp1_sub_support : p.1 ⊆ combinatorialSupport p := Finset.subset_union_left
            exact hp1_sub_support.trans hp_sub_q2
          have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q h0.2
          have hp1_nonempty : p.1.Nonempty := (T.NonemptyPairs p h0.1).1
          obtain ⟨x, hx⟩ := hp1_nonempty
          have hx_in_q1 : x ∈ q.1 := h hx
          have hx_in_q2 : x ∈ q.2 := hp1_sub_q2 hx
          exact Finset.disjoint_left.mp hq_disj hx_in_q1 hx_in_q2
        | inr hrest3 =>
          cases hrest3 with
            | inl hq_sub_p1 =>
            -- This case: combinatorialSupport q ⊆ p.1
            -- Combined with h : p.1 ⊆ q.1
            -- We have q.1 ⊆ combinatorialSupport q ⊆ p.1 ⊆ q.1
            -- This gives us q.1 = p.1, which implies p = q
            have hq1_sub_p1 : q.1 ⊆ p.1 := by
              have hq1_sub_support : q.1 ⊆ combinatorialSupport q := Finset.subset_union_left
              exact hq1_sub_support.trans hq_sub_p1
            have hp1_eq_q1 : p.1 = q.1 := Finset.Subset.antisymm h hq1_sub_p1
            -- Since p.1 = q.1 and both have the same structure, p = q
            have hp_eq_q : p = q := by
              -- Since p.1 = q.1, we need to show p = q
              -- We'll use DistinctComponentsPairs to get a contradiction if p ≠ q
              by_contra hp_neq_q
              -- If p ≠ q, then by DistinctComponentsPairs, pairToFinset p and pairToFinset q are
              -- disjoint
              have h_disjoint_pairs : Disjoint (pairToFinset p) (pairToFinset q) :=
                  T.DistinctComponentsPairs p h0.1 q h0.2 hpq
              -- But p.1 = q.1, so p.1 ∈ pairToFinset p ∩ pairToFinset q
              have hp1_in_p : p.1 ∈ pairToFinset p := by
                dsimp [pairToFinset]
                exact Finset.mem_insert_self p.1 {p.2}
              have hq1_in_q : q.1 ∈ pairToFinset q := by
                dsimp [pairToFinset]
                exact Finset.mem_insert_self q.1 {q.2}
              have h_not_disjoint : ¬Disjoint (pairToFinset p) (pairToFinset q) := by
                rw [Finset.not_disjoint_iff_nonempty_inter]
                use p.1
                rw [Finset.mem_inter]
                exact ⟨hp1_in_p, hp1_eq_q1 ▸ hq1_in_q⟩
              exact False.elim (h_not_disjoint h_disjoint_pairs)
            exact Or.inr hp_eq_q
            | inr hq_sub_p2 =>
             simp only [combinatorialSupport] at hq_sub_p2
             -- Este caso: combinatorialSupport q ⊆ p.2
             -- Mas também temos h : p.1 ⊆ q.1 do início
             -- E sabemos que combinatorialSupport q = q.1 ∪ q.2
             -- Então q.1 ⊆ combinatorialSupport q ⊆ p.2
             -- Por transitividade: p.1 ⊆ q.1 ⊆ p.2, logo p.1 ⊆ p.2
             -- Mas p.1 e p.2 são disjuntos por DisjointComponents, contradição
             exfalso
             have hq1_sub_p2 : q.1 ⊆ p.2 := by
               have hq1_sub_support : q.1 ⊆ combinatorialSupport q := Finset.subset_union_left
               exact hq1_sub_support.trans hq_sub_p2
             have hp1_sub_p2 : p.1 ⊆ p.2 := h.trans hq1_sub_p2
             have hp_disj : Disjoint p.1 p.2 := T.DisjointComponents p h0.1
             have hp1_nonempty : p.1.Nonempty := (T.NonemptyPairs p h0.1).1
             obtain ⟨x, hx⟩ := hp1_nonempty
             have hx_in_p2 : x ∈ p.2 := hp1_sub_p2 hx
             have hx_not_p2 : x ∉ p.2 := Finset.disjoint_left.mp hp_disj hx
             exact hx_not_p2 hx_in_p2

lemma inclusion_support_finner_2 {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α} {q : Finset α × Finset α} (h0 : p ∈
      T.Branches ∧ q ∈ T.Branches) (h : p.1 ⊆ q.2) :
  combinatorialSupport p ⊆ q.2 ∨ p=q:= by
  by_cases hpq : p = q
  · -- Case: p = q
    simp [hpq]
  · -- Case: p ≠ q
    have hSup := T.SupportProperty p h0.1 q h0.2 hpq
    cases hSup with
    | inl hdisj =>
      -- Contradiction: if p.1 ⊆ q.2 and the supports are disjoint, we have a contradiction
      -- Because p.1 is nonempty and p.1 ⊆ combinatorialSupport p
      have hp1_nonempty : p.1.Nonempty := (T.NonemptyPairs p h0.1).1
      obtain ⟨x, hx⟩ := hp1_nonempty
      have hx_in_p_support : x ∈ combinatorialSupport p := Finset.mem_union_left p.2 hx
      have hx_in_q2 : x ∈ q.2 := h hx
      have hx_in_q_support : x ∈ combinatorialSupport q := Finset.mem_union_right q.1 hx_in_q2
      exact False.elim (Finset.disjoint_left.mp hdisj hx_in_p_support hx_in_q_support)
    | inr hrest =>
      cases hrest with
      | inl hp_sub_q1 =>
        -- This case is impossible: we have h : p.1 ⊆ q.2 and hp_sub_q1 : combinatorialSupport p ⊆
        -- q.1
        -- But combinatorialSupport p = p.1 ∪ p.2, so p.1 ⊆ combinatorialSupport p ⊆ q.1
        -- This means p.1 ⊆ q.1, but we also have h : p.1 ⊆ q.2
        -- Since q.1 and q.2 are disjoint and p.1 is nonempty, this is a contradiction
        exfalso
        have hp1_sub_q1 : p.1 ⊆ q.1 := by
          have hp1_sub_support : p.1 ⊆ combinatorialSupport p := Finset.subset_union_left
          exact hp1_sub_support.trans hp_sub_q1
        have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q h0.2
        have hp1_nonempty : p.1.Nonempty := (T.NonemptyPairs p h0.1).1
        obtain ⟨x, hx⟩ := hp1_nonempty
        have hx_in_q1 : x ∈ q.1 := hp1_sub_q1 hx
        have hx_in_q2 : x ∈ q.2 := h hx
        exact Finset.disjoint_left.mp hq_disj hx_in_q1 hx_in_q2
      | inr hrest2 =>
        cases hrest2 with
        | inl hp_sub_q2 =>
          exact Or.inl hp_sub_q2
        | inr hrest3 =>
          cases hrest3 with
            | inl hq_sub_p1 =>
            -- This case: combinatorialSupport q ⊆ p.1
            -- Combined with h : p.1 ⊆ q.2
            -- We have q.2 ⊆ combinatorialSupport q ⊆ p.1 ⊆ q.2
            -- This gives us q.2 = p.1, which implies p = q
            have hq2_sub_p1 : q.2 ⊆ p.1 := by
              have hq2_sub_support : q.2 ⊆ combinatorialSupport q := Finset.subset_union_right
              exact hq2_sub_support.trans hq_sub_p1
            have hp1_eq_q2 : p.1 = q.2 := Finset.Subset.antisymm h hq2_sub_p1
            -- Since p.1 = q.2 and both have the same structure, p = q
            have hp_eq_q : p = q := by
              -- Since p.1 = q.2, we need to show p = q
              -- We'll use DistinctComponentsPairs to get a contradiction if p ≠ q
              by_contra hp_neq_q
              -- If p ≠ q, then by DistinctComponentsPairs, pairToFinset p and pairToFinset q are
              -- disjoint
              have h_disjoint_pairs : Disjoint (pairToFinset p) (pairToFinset q) :=
                T.DistinctComponentsPairs p h0.1 q h0.2 hp_neq_q
              -- But p.1 = q.2, so q.2 ∈ pairToFinset p ∩ pairToFinset q
              have hp1_in_p : p.1 ∈ pairToFinset p := by
                dsimp [pairToFinset]
                exact Finset.mem_insert_self p.1 {p.2}
              have hq2_in_q : q.2 ∈ pairToFinset q := by
                dsimp [pairToFinset]
                exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q.2)
              have h_not_disjoint : ¬Disjoint (pairToFinset p) (pairToFinset q) := by
                rw [Finset.not_disjoint_iff_nonempty_inter]
                use p.1
                rw [Finset.mem_inter]
                exact ⟨hp1_in_p, hp1_eq_q2 ▸ hq2_in_q⟩
              exact h_not_disjoint h_disjoint_pairs
            exact Or.inr hp_eq_q
            | inr hq_sub_p2 =>
             simp only [combinatorialSupport] at hq_sub_p2
             -- This case: combinatorialSupport q ⊆ p.2
             -- But we also have h : p.1 ⊆ q.2 from the beginning
             -- And we know that combinatorialSupport q = q.1 ∪ q.2
             -- So q.2 ⊆ combinatorialSupport q ⊆ p.2
             -- By transitivity: p.1 ⊆ q.2 ⊆ p.2, therefore p.1 ⊆ p.2
             -- But p.1 and p.2 are disjoint by DisjointComponents, contradiction
             exfalso
             have hq2_sub_p2 : q.2 ⊆ p.2 := by
               have hq2_sub_support : q.2 ⊆ combinatorialSupport q := Finset.subset_union_right
               exact hq2_sub_support.trans hq_sub_p2
             have hp1_sub_p2 : p.1 ⊆ p.2 := h.trans hq2_sub_p2
             have hp_disj : Disjoint p.1 p.2 := T.DisjointComponents p h0.1
             have hp1_nonempty : p.1.Nonempty := (T.NonemptyPairs p h0.1).1
             obtain ⟨x, hx⟩ := hp1_nonempty
             have hx_in_p2 : x ∈ p.2 := hp1_sub_p2 hx
             have hx_not_p2 : x ∉ p.2 := Finset.disjoint_left.mp hp_disj hx
             exact hx_not_p2 hx_in_p2

lemma inclusion_support_finner_3 {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α} {q : Finset α × Finset α} (h0 : p ∈
      T.Branches ∧ q ∈ T.Branches) (h : p.2 ⊆ q.1) :
  combinatorialSupport p ⊆ q.1 ∨ p=q:= by
  by_cases hpq : p = q
  · -- Case: p = q
    simp [hpq]
  · -- Case: p ≠ q
    have hSup := T.SupportProperty p h0.1 q h0.2 hpq
    cases hSup with
    | inl hdisj =>
      -- Contradiction: if p.2 ⊆ q.1 and the supports are disjoint, we have a contradiction
      -- Because p.2 is nonempty and p.2 ⊆ combinatorialSupport p
      have hp2_nonempty : p.2.Nonempty := (T.NonemptyPairs p h0.1).2
      obtain ⟨x, hx⟩ := hp2_nonempty
      have hx_in_p_support : x ∈ combinatorialSupport p := Finset.mem_union_right p.1 hx
      have hx_in_q1 : x ∈ q.1 := h hx
      have hx_in_q_support : x ∈ combinatorialSupport q := Finset.mem_union_left q.2 hx_in_q1
      exact False.elim (Finset.disjoint_left.mp hdisj hx_in_p_support hx_in_q_support)
    | inr hrest =>
      cases hrest with
      | inl hp_sub_q1 =>
        exact Or.inl hp_sub_q1
      | inr hrest2 =>
        cases hrest2 with
        | inl hp_sub_q2 =>
          -- This case is impossible: we have h : p.2 ⊆ q.1 and hp_sub_q2 : combinatorialSupport p
          -- ⊆ q.2
          -- But combinatorialSupport p = p.1 ∪ p.2, so p.2 ⊆ combinatorialSupport p ⊆ q.2
          -- This means p.2 ⊆ q.2, but we also have h : p.2 ⊆ q.1
          -- Since q.1 and q.2 are disjoint and p.2 is nonempty, this is a contradiction
          exfalso
          have hp2_sub_q2 : p.2 ⊆ q.2 := by
            have hp2_sub_support : p.2 ⊆ combinatorialSupport p := Finset.subset_union_right
            exact hp2_sub_support.trans hp_sub_q2
          have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q h0.2
          have hp2_nonempty : p.2.Nonempty := (T.NonemptyPairs p h0.1).2
          obtain ⟨x, hx⟩ := hp2_nonempty
          have hx_in_q1 : x ∈ q.1 := h hx
          have hx_in_q2 : x ∈ q.2 := hp2_sub_q2 hx
          exact Finset.disjoint_left.mp hq_disj hx_in_q1 hx_in_q2
        | inr hrest3 =>
          cases hrest3 with
            | inl hq_sub_p1 =>
            -- This case: combinatorialSupport q ⊆ p.1
            -- Combined with h : p.2 ⊆ q.1
            -- We have q.1 ⊆ combinatorialSupport q ⊆ p.1 and p.2 ⊆ q.1
            -- This gives us a contradiction since p.1 and p.2 are disjoint
            exfalso
            have hq1_sub_p1 : q.1 ⊆ p.1 := by
              have hq1_sub_support : q.1 ⊆ combinatorialSupport q := Finset.subset_union_left
              exact hq1_sub_support.trans hq_sub_p1
            have hp2_sub_p1 : p.2 ⊆ p.1 := Finset.Subset.trans h hq1_sub_p1
            have hp_disj : Disjoint p.1 p.2 := T.DisjointComponents p h0.1
            have hp2_nonempty : p.2.Nonempty := (T.NonemptyPairs p h0.1).2
            obtain ⟨x, hx⟩ := hp2_nonempty
            have hx_in_p1 : x ∈ p.1 := hp2_sub_p1 hx
            have hx_not_p1 : x ∉ p.1 := Finset.disjoint_right.mp hp_disj hx
            exact hx_not_p1 hx_in_p1
            | inr hq_sub_p2 =>
             simp only [combinatorialSupport] at hq_sub_p2
             -- This case: combinatorialSupport q ⊆ p.2
             -- But we also have h : p.2 ⊆ q.1 from the beginning
             -- And we know that combinatorialSupport q = q.1 ∪ q.2
             -- So q.1 ⊆ combinatorialSupport q ⊆ p.2
             -- By transitivity: p.2 ⊆ q.1 ⊆ p.2, therefore p.2 = q.1
             -- And also q.2 ⊆ combinatorialSupport q ⊆ p.2
             -- But p.1 and p.2 are disjoint, and also q.1 and q.2 are disjoint
             -- This would lead to contradictions with the disjunction properties
             exfalso
             have hq1_sub_p2 : q.1 ⊆ p.2 := by
               have hq1_sub_support : q.1 ⊆ combinatorialSupport q := Finset.subset_union_left
               exact hq1_sub_support.trans hq_sub_p2
             have hp2_eq_q1 : p.2 = q.1 := Finset.Subset.antisymm h hq1_sub_p2
             have hq2_sub_p2 : q.2 ⊆ p.2 := by
               have hq2_sub_support : q.2 ⊆ combinatorialSupport q := Finset.subset_union_right
               exact hq2_sub_support.trans hq_sub_p2
             -- Now we have q.1 ⊆ p.2 and q.2 ⊆ p.2, but q.1 and q.2 are disjoint and both nonempty
             -- Also p.2 = q.1, so q.2 ⊆ q.1, which contradicts that q.1 and q.2 are disjoint
             have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q h0.2
             have hq2_nonempty : q.2.Nonempty := (T.NonemptyPairs q h0.2).2
             obtain ⟨x, hx⟩ := hq2_nonempty
             have hx_in_q1 : x ∈ q.1 := by
               rw [← hp2_eq_q1]
               exact hq2_sub_p2 hx
             have hx_not_q1 : x ∉ q.1 := Finset.disjoint_right.mp hq_disj hx
             exact hx_not_q1 hx_in_q1

lemma inclusion_support_finner_4 {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α} {q : Finset α × Finset α} (h0 : p ∈
      T.Branches ∧ q ∈ T.Branches) (h : p.2 ⊆ q.2) :
  combinatorialSupport p ⊆ q.2 ∨ p=q:= by
  by_cases hpq : p = q
  · -- Case: p = q
    simp [hpq]
  · -- Case: p ≠ q
    have hSup := T.SupportProperty p h0.1 q h0.2 hpq
    cases hSup with
    | inl hdisj =>
      -- Contradiction: if they're disjoint but p.1 or p.2 ⊆ combinatorialSupport q
      -- We have h : p.1 ⊆ combinatorialSupport q and hdisj : Disjoint (combinatorialSupport p)
      -- (combinatorialSupport q)
      -- This leads to a contradiction since p.1 ⊆ combinatorialSupport p
      -- Contradiction: if p.1 ⊆ q.1 and the supports are disjoint, we have a contradiction
      -- Because p.1 is nonempty and p.1 ⊆ combinatorialSupport p
      have hp2_nonempty : p.2.Nonempty := (T.NonemptyPairs p h0.1).2
      obtain ⟨y, hy⟩ := hp2_nonempty
      have hy_in_p_support : y ∈ combinatorialSupport p := Finset.mem_union_right p.1 hy
      have hy_in_q2 : y ∈ q.2 := h hy
      have hy_in_q_support : y ∈ combinatorialSupport q := Finset.mem_union_right q.1 hy_in_q2
      exact False.elim (Finset.disjoint_left.mp hdisj hy_in_p_support hy_in_q_support)
    | inr hrest =>
      cases hrest with
      | inl hp_sub_q1 =>
          exfalso
          have hp2_sub_q1 : p.2 ⊆ q.1 := by
            have hp2_sub_support : p.2 ⊆ combinatorialSupport p := Finset.subset_union_right
            exact hp2_sub_support.trans hp_sub_q1
          have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q h0.2
          have hp2_nonempty : p.2.Nonempty := (T.NonemptyPairs p h0.1).2
          obtain ⟨y, hy⟩ := hp2_nonempty
          have hy_in_q2 : y ∈ q.2 := h hy
          have hy_in_q1 : y ∈ q.1 := hp2_sub_q1 hy
          exact Finset.disjoint_left.mp hq_disj hy_in_q1 hy_in_q2
      | inr hrest2 =>
        cases hrest2 with
        | inl hp_sub_q2 =>
          exact Or.inl hp_sub_q2
        | inr hrest3 =>
          cases hrest3 with
            | inl hq_sub_p1 =>
             simp only [combinatorialSupport] at hq_sub_p1
             -- Este caso: combinatorialSupport q ⊆ p.2
             -- Mas também temos h : p.1 ⊆ q.1 do início
             -- E sabemos que combinatorialSupport q = q.1 ∪ q.2
             -- Então q.1 ⊆ combinatorialSupport q ⊆ p.2
             -- Por transitividade: p.1 ⊆ q.1 ⊆ p.2, logo p.1 ⊆ p.2
             -- Mas p.1 e p.2 são disjuntos por DisjointComponents, contradição
             exfalso
             have hq2_sub_p1 : q.2 ⊆ p.1 := by
               have hq2_sub_support : q.2 ⊆ combinatorialSupport q := Finset.subset_union_right
               exact hq2_sub_support.trans hq_sub_p1
             have hp2_sub_p1 : p.2 ⊆ p.1 := h.trans hq2_sub_p1
             have hp_disj : Disjoint p.1 p.2 := T.DisjointComponents p h0.1
             have hp2_nonempty : p.2.Nonempty := (T.NonemptyPairs p h0.1).2
             obtain ⟨x, hx⟩ := hp2_nonempty
             have hx_in_p1 : x ∈ p.1 := hp2_sub_p1 hx
             have hx_not_p1 : x ∉ p.1 := Finset.disjoint_right.mp hp_disj hx
             exact hx_not_p1 hx_in_p1
            | inr hq_sub_p2 =>
             -- This case: combinatorialSupport q ⊆ p.1
            -- Combined with h : p.1 ⊆ q.1
            -- We have q.1 ⊆ combinatorialSupport q ⊆ p.1 ⊆ q.1
            -- This gives us q.1 = p.1, which implies p = q
            have hq2_sub_p2 : q.2 ⊆ p.2 := by
              have hq2_sub_support : q.2 ⊆ combinatorialSupport q := Finset.subset_union_right
              exact hq2_sub_support.trans hq_sub_p2
            have hp2_eq_q2 : p.2 = q.2 := Finset.Subset.antisymm h hq2_sub_p2
            -- Since p.1 = q.1 and both have the same structure, p = q
            have hp_eq_q : p = q := by
              -- Since p.1 = q.1, we need to show p = q
              -- We'll use DistinctComponentsPairs to get a contradiction if p ≠ q
              by_contra hp_neq_q
              -- If p ≠ q, then by DistinctComponentsPairs, pairToFinset p and pairToFinset q are
              -- disjoint
              have h_disjoint_pairs : Disjoint (pairToFinset p) (pairToFinset q) :=
                  T.DistinctComponentsPairs p h0.1 q h0.2 hpq
              -- But p.1 = q.1, so p.1 ∈ pairToFinset p ∩ pairToFinset q
              have hp2_in_p : p.2 ∈ pairToFinset p := by
                dsimp [pairToFinset]
                exact Finset.mem_insert_of_mem (Finset.mem_singleton_self p.2)
              have hq2_in_q : q.2 ∈ pairToFinset q := by
                dsimp [pairToFinset]
                exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q.2)
              have h_not_disjoint : ¬Disjoint (pairToFinset p) (pairToFinset q) := by
                rw [Finset.not_disjoint_iff_nonempty_inter]
                use p.2
                rw [Finset.mem_inter]
                exact ⟨hp2_in_p, hp2_eq_q2 ▸ hq2_in_q⟩
              exact False.elim (h_not_disjoint h_disjoint_pairs)
            exact Or.inr hp_eq_q


/-- Along a valid chain, the support of the endpoint is contained in the
    support of every branch appearing earlier in the chain. -/
lemma chain_endpoint_support_subset {α : Type*} [DecidableEq α]
    {p : Finset α × Finset α}
    {n : ℕ} {c : ℕ → Finset α × Finset α}
    (hcn : c n = p)
    (hstep : ∀ i < n,
        combinatorialSupport (c (i + 1)) = (c i).1 ∨
        combinatorialSupport (c (i + 1)) = (c i).2) :
    ∀ i ≤ n, combinatorialSupport p ⊆ combinatorialSupport (c i) := by
  induction n generalizing p c with
  | zero =>
    intro i hi
    have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
    subst hi0
    simp [hcn]
  | succ n ih =>
    intro i hi
    by_cases hin : i = n + 1
    · subst hin
      simp [hcn]
    · have hi_prefix : i ≤ n := by omega
      have hlast := hstep n (Nat.lt_succ_self n)
      have hp_subset_parent :
          combinatorialSupport p ⊆ combinatorialSupport (c n) := by
        rcases hlast with hleft | hright
        · intro x hx
          have hx_child : x ∈ combinatorialSupport (c (n + 1)) := by
            simpa [hcn] using hx
          dsimp [combinatorialSupport]
          exact Finset.mem_union_left (c n).2 (by simpa [hleft] using hx_child)
        · intro x hx
          have hx_child : x ∈ combinatorialSupport (c (n + 1)) := by
            simpa [hcn] using hx
          dsimp [combinatorialSupport]
          exact Finset.mem_union_right (c n).1 (by simpa [hright] using hx_child)
      have hprefix_step :
          ∀ j < n,
            combinatorialSupport (c (j + 1)) = (c j).1 ∨
            combinatorialSupport (c (j + 1)) = (c j).2 := by
        intro j hj
        exact hstep j (by omega)
      have hparent_subset_i :
          combinatorialSupport (c n) ⊆ combinatorialSupport (c i) :=
        ih (p := c n) (c := c) rfl hprefix_step i hi_prefix
      exact hp_subset_parent.trans hparent_subset_i

/-- If `q` contains the support of the child endpoint of a chain step, then
    either `q` is that endpoint, or it also contains the support of the parent. -/
lemma chain_step_parent_support_subset_or_eq {α : Type*} [DecidableEq α]
    {T : BinaryTreeWithRootandTops α} {parent child q : Finset α × Finset α}
    (hparent : parent ∈ T.Branches) (hchild : child ∈ T.Branches)
    (hq : q ∈ T.Branches)
    (hstep :
      combinatorialSupport child = parent.1 ∨
      combinatorialSupport child = parent.2)
    (hsub : combinatorialSupport child ⊆ combinatorialSupport q) :
    child = q ∨ combinatorialSupport parent ⊆ combinatorialSupport q := by
  by_cases hcq : child = q
  · exact Or.inl hcq
  · have hchild_sub_q_component :
        combinatorialSupport child ⊆ q.1 ∨
        combinatorialSupport child ⊆ q.2 :=
      inclusion_q1orq2 hchild hq ⟨hcq, hsub⟩
    right
    rcases hstep with hleft | hright
    · rcases hchild_sub_q_component with hsubq1 | hsubq2
      · have hparent1_sub_q1 : parent.1 ⊆ q.1 := by
          intro x hx
          exact hsubq1 (by simpa [hleft] using hx)
        rcases inclusion_support_finner_1 ⟨hparent, hq⟩ hparent1_sub_q1 with hs | hpq
        · exact hs.trans Finset.subset_union_left
        · subst hpq
          exact subset_rfl
      · have hparent1_sub_q2 : parent.1 ⊆ q.2 := by
          intro x hx
          exact hsubq2 (by simpa [hleft] using hx)
        rcases inclusion_support_finner_2 ⟨hparent, hq⟩ hparent1_sub_q2 with hs | hpq
        · exact hs.trans Finset.subset_union_right
        · subst hpq
          exact subset_rfl
    · rcases hchild_sub_q_component with hsubq1 | hsubq2
      · have hparent2_sub_q1 : parent.2 ⊆ q.1 := by
          intro x hx
          exact hsubq1 (by simpa [hright] using hx)
        rcases inclusion_support_finner_3 ⟨hparent, hq⟩ hparent2_sub_q1 with hs | hpq
        · exact hs.trans Finset.subset_union_left
        · subst hpq
          exact subset_rfl
      · have hparent2_sub_q2 : parent.2 ⊆ q.2 := by
          intro x hx
          exact hsubq2 (by simpa [hright] using hx)
        rcases inclusion_support_finner_4 ⟨hparent, hq⟩ hparent2_sub_q2 with hs | hpq
        · exact hs.trans Finset.subset_union_right
        · subst hpq
          exact subset_rfl

/-- For any valid chain from `T.Root` to `p`, the entries of the chain are exactly
    the branches whose support contains the support of `p`. -/
theorem chain_from_root_exactly_support_containers {α : Type*} [DecidableEq α]
    {T : BinaryTreeWithRootandTops α} {p q : Finset α × Finset α}
    (hp : p ∈ T.Branches) (hq : q ∈ T.Branches)
    {n : ℕ} {c : ℕ → Finset α × Finset α}
    (hc0 : c 0 = T.Root) (hcn : c n = p)
    (hcmem : ∀ i ≤ n, c i ∈ T.Branches)
    (hcstep : ∀ i < n,
        combinatorialSupport (c (i + 1)) = (c i).1 ∨
        combinatorialSupport (c (i + 1)) = (c i).2) :
    (∃ i ≤ n, c i = q) ↔
      combinatorialSupport p ⊆ combinatorialSupport q := by
  constructor
  · rintro ⟨i, hi, hiq⟩
    simpa [hiq] using chain_endpoint_support_subset hcn hcstep i hi
  · intro hsub
    induction n generalizing p c hp hc0 hsub with
    | zero =>
      have hp_root : p = T.Root := by simpa [hc0] using hcn.symm
      have hq_support_eq_root :
          combinatorialSupport q = combinatorialSupport T.Root := by
        apply Finset.Subset.antisymm
        · exact support_subset_root_support (T := T) hq
        · simpa [hp_root] using hsub
      have hq_root : q = T.Root :=
        (eq_iff_eq_support hq T.RootinBranches).mpr hq_support_eq_root
      exact ⟨0, le_rfl, by simp [hc0, hq_root]⟩
    | succ n ih =>
      by_cases hpq : p = q
      · exact ⟨n + 1, le_rfl, by simp [hcn, hpq]⟩
      · let parent := c n
        have hparent_mem : parent ∈ T.Branches := hcmem n (by omega)
        have hchild_mem : c (n + 1) ∈ T.Branches := hcmem (n + 1) le_rfl
        have hstep_last := hcstep n (Nat.lt_succ_self n)
        have hparent_sub :
            combinatorialSupport parent ⊆ combinatorialSupport q := by
          have hstep_p :
              combinatorialSupport p = parent.1 ∨
              combinatorialSupport p = parent.2 := by
            simpa [parent, hcn] using hstep_last
          have hres := chain_step_parent_support_subset_or_eq
              (T := T) hparent_mem hp hq hstep_p hsub
          rcases hres with hpq' | hparent_sub
          · exact (hpq hpq').elim
          · exact hparent_sub
        have hprefix_mem : ∀ i ≤ n, c i ∈ T.Branches := by
          intro i hi
          exact hcmem i (by omega)
        have hprefix_step :
            ∀ i < n,
              combinatorialSupport (c (i + 1)) = (c i).1 ∨
              combinatorialSupport (c (i + 1)) = (c i).2 := by
          intro i hi
          exact hcstep i (by omega)
        have happ := ih (p := parent) (c := c)
          hparent_mem hc0 rfl hprefix_mem hprefix_step hparent_sub
        rcases happ with ⟨i, hi, hiq⟩
        exact ⟨i, by omega, hiq⟩

/-- The canonical chain `ChainToRoot hp` lists exactly the branches whose support
    contains the support of `p`. -/
theorem ChainToRoot_exactly_support_containers {α : Type*} [DecidableEq α]
    {T : BinaryTreeWithRootandTops α} {p q : Finset α × Finset α}
    (hp : p ∈ T.Branches) (hq : q ∈ T.Branches) :
    (∃ i ≤ chainLength hp, ChainToRoot hp i = q) ↔
      combinatorialSupport p ⊆ combinatorialSupport q := by
  exact chain_from_root_exactly_support_containers hp hq
    (ChainToRoot_zero hp) (ChainToRoot_end hp)
    (fun i hi => ChainToRoot_mem hp hi) (fun i hi => ChainToRoot_step hp hi)


lemma maximal_compact_inside_p1 {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α} (h1 : p ∈ T.Branches)
  (h_ex : ∃ q ∈ T.Branches, combinatorialSupport q ⊆ p.1) :
  ∃ r ∈ T.Branches, combinatorialSupport r = p.1 := by
  -- Find q with the largest support among those satisfying h_ex
  let S := T.Branches.filter (fun b => combinatorialSupport b ⊆ p.1)
  have hS_nonempty : S.Nonempty := by
    rcases h_ex with ⟨q, hq, hq_sub⟩
    use q
    exact Finset.mem_filter.mpr ⟨hq, hq_sub⟩
  obtain ⟨q, hq_in_S, hq_maximal⟩ := S.exists_max_image (fun b => (combinatorialSupport b).card)
      hS_nonempty
  have hq_in_branches : q ∈ T.Branches := (Finset.mem_filter.mp hq_in_S).1
  have hq_sub : combinatorialSupport q ⊆ p.1 := (Finset.mem_filter.mp hq_in_S).2
  use q, hq_in_branches
  -- Use TreeStructure to show equality
  by_cases hq_root : q = T.Root
  case pos =>
    -- If q is the root, this is absurd because the support of root contains
    -- the support of any pair in branches due to RootcontainsChilds,
    -- but this is impossible since the support of p is not contained in the support of q
    exfalso
    -- q = Root and combinatorialSupport q ⊆ p.1
    -- But Root contains all Childs, so p.1 ⊆ Root.1 ∪ Root.2 = combinatorialSupport Root
    -- This would mean combinatorialSupport q ⊆ p.1 ⊆ combinatorialSupport q
    -- So p.1 = combinatorialSupport q, contradicting that p is a proper subset
    have hp_sub_root : combinatorialSupport p ⊆ combinatorialSupport T.Root := by
      dsimp [combinatorialSupport]
      have hp_in_childs := T.TreeStructureChilds p h1
      have hp_union_sub : p.1 ∪ p.2 ⊆ T.Childs := Finset.union_subset hp_in_childs.1 hp_in_childs.2
      exact hp_union_sub.trans T.RootcontainsChilds
    -- Since combinatorialSupport q ⊆ p.1 and p ∈ T.Branches,
    -- by SupportProperty, either they are disjoint or one is contained in the other
    -- But since q = Root and p ≠ Root (p is a proper branch),
    -- and hp_sub_root shows combinatorialSupport p ⊆ combinatorialSupport q,
    -- combined with hq_sub: combinatorialSupport q ⊆ p.1,
    -- we get combinatorialSupport q ⊆ p.1 ⊆ combinatorialSupport p ⊆ combinatorialSupport q
    -- This forces equality, contradicting that p should be distinct from q
    have hp_neq_q : p ≠ q := by
      rw [hq_root]
      intro h_eq
      -- If p = Root, then we have combinatorialSupport Root ⊆ p.1
      -- But p = Root means p.1 = Root.1, so we need Root.1 ∪ Root.2 ⊆ Root.1
      -- This would imply Root.2 ⊆ Root.1, contradicting DisjointRoot and NonemptyRoot
      rw [h_eq] at hq_sub
      -- hq_sub : combinatorialSupport Root ⊆ Root.1
      -- But combinatorialSupport Root = Root.1 ∪ Root.2
      dsimp [combinatorialSupport] at hq_sub
      -- So we have Root.1 ∪ Root.2 ⊆ Root.1
      -- This implies Root.2 ⊆ Root.1
      have h_subset : T.Root.2 ⊆ T.Root.1 := by
        intro x hx
        rw [hq_root] at hq_sub
        exact hq_sub (Finset.mem_union_right T.Root.1 hx)
      -- But T.Root.2 is nonempty and disjoint from T.Root.1
      have h_nonempty := T.NonemptyRoot.2
      have h_disjoint := T.DisjointRoot
      -- Get an element from Root.2
      obtain ⟨y, hy⟩ := h_nonempty
      -- y ∈ Root.2 and by h_subset, y ∈ Root.1
      have hy_in_1 : y ∈ T.Root.1 := h_subset hy
      -- But this contradicts disjointness
      have : y ∉ T.Root.1 := Finset.disjoint_right.mp h_disjoint hy
      exact this hy_in_1
    -- Now we use SupportProperty between p and q
    have h_support := T.SupportProperty p h1 q hq_in_branches hp_neq_q
    -- We have both hp_sub_root : combinatorialSupport p ⊆ combinatorialSupport q
    -- and hq_sub : combinatorialSupport q ⊆ p.1
    -- Since p.1 ⊆ combinatorialSupport p, this gives us a cycle of inclusions
    have hp1_sub : p.1 ⊆ combinatorialSupport p := Finset.subset_union_left
    have hp_sub_q : combinatorialSupport p ⊆ combinatorialSupport q := by
      rw [hq_root]; exact hp_sub_root
    have h_cycle : combinatorialSupport q ⊆ combinatorialSupport p ∧
                   combinatorialSupport p ⊆ combinatorialSupport q :=
      ⟨hq_sub.trans hp1_sub, hp_sub_q⟩
    -- This forces equality, but then by SupportProperty, p and q must be disjoint or
    -- one contained in the other, contradicting the equality
    have h_eq_support : combinatorialSupport p = combinatorialSupport q :=
      Finset.Subset.antisymm h_cycle.2 h_cycle.1
    -- This contradicts the distinctness required by the tree structure
    have hp_eq_q : p = q := by
      -- We have h_eq_support : combinatorialSupport p = combinatorialSupport q
      -- and we know q ≠ p (since hp_neq_q)
      -- But the SupportProperty says that for distinct branches p and q,
      -- either they are disjoint or one is contained in a component of the other
      have h_support_prop := T.SupportProperty p h1 q hq_in_branches hp_neq_q
      rw [h_eq_support] at h_support_prop
      -- Now h_support_prop becomes: either combinatorialSupport q is disjoint with itself,
      -- or combinatorialSupport q ⊆ p.1, or combinatorialSupport q ⊆ p.2, etc.
      -- The disjoint case is impossible, so we have containment
      cases h_support_prop with
      | inl hdisj =>
        -- Disjoint (combinatorialSupport q) (combinatorialSupport q) is impossible
        have hq_nonempty : (combinatorialSupport q).Nonempty := by
          dsimp [combinatorialSupport]
          have h1 : q.1.Nonempty := (T.NonemptyPairs q hq_in_branches).1
          exact Finset.Nonempty.inl h1
        have : ¬Disjoint (combinatorialSupport q) (combinatorialSupport q) :=
          Finset.not_disjoint_iff_nonempty_inter.mpr (by simp [hq_nonempty])
        exact False.elim (this hdisj)
      | inr hcases =>
        cases hcases with
    | inl hq_sub_p1 =>
      -- This case is impossible by support_not_subset_components
      exfalso
      have h_not_subset := support_not_subset_components hq_in_branches
      exact h_not_subset.1 hq_sub_p1
    | inr hrest =>
      -- Similar contradictions for the other cases
      cases hrest with
      | inl hq_sub_p2 =>
        -- This case is impossible by support_not_subset_components
        exfalso
        have h_not_subset := support_not_subset_components hq_in_branches
        exact h_not_subset.2 hq_sub_p2
      | inr hfinal =>
        -- The remaining cases involve q being contained in components of p,
        -- but since combinatorialSupport p = combinatorialSupport q,
        -- this leads to similar contradictions
        cases hfinal with
    | inl hp_sub_q1 =>
      rw [← h_eq_support] at hp_sub_q1
      exfalso
      have h_not_subset := support_not_subset_components h1
      exact h_not_subset.1 hp_sub_q1
    | inr hp_sub_q2 =>
      rw [← h_eq_support] at hp_sub_q2
      exfalso
      have h_not_subset := support_not_subset_components h1
      exact h_not_subset.2 hp_sub_q2
    exact hp_neq_q hp_eq_q
  case neg =>
    -- If q ≠ Root, use TreeStructure
    obtain ⟨r, hr, hr_contains⟩ := T.TreeStructure q hq_in_branches hq_root
    -- r is a parent of q, so q.1 ∪ q.2 ∈ pairToFinset r
    -- This means q.1 ∪ q.2 = r.1 or q.1 ∪ q.2 = r.2
    -- We have r is a parent of q, so combinatorialSupport q ∈ pairToFinset r
    -- This means either combinatorialSupport q = r.1 or combinatorialSupport q = r.2
    have hq_union_in_r : combinatorialSupport q ∈ pairToFinset r := by
      exact hr_contains
    -- From pairToFinset definition, this gives us the cases
    have hq_cases : combinatorialSupport q = r.1 ∨ combinatorialSupport q = r.2 := by
      dsimp [pairToFinset] at hq_union_in_r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq_union_in_r
      exact hq_union_in_r
    cases hq_cases with
    | inl hq_eq_r1 =>
      -- Case: combinatorialSupport q = r.1
      -- Since combinatorialSupport q ⊆ p.1 and combinatorialSupport q = r.1, we have r.1 ⊆ p.1
      have hr1_sub : r.1 ⊆ p.1 := by
        rw [← hq_eq_r1]
        exact hq_sub
      -- Use inclusion_support_finner with r.1 ⊆ combinatorialSupport q = r.1 to get r = p or
      -- combinatorialSupport r ⊆ p.1
      have hr_result := inclusion_support_finner_1 ⟨hr, h1⟩ hr1_sub
      cases hr_result with
      | inl hr_sub_p1 =>
        -- Case: combinatorialSupport r ⊆ p.1
        -- This contradicts the maximality of q among branches with support ⊆ p.1
        exfalso
        -- But we also have combinatorialSupport q = r.1, so q.1 ∪ q.2 = r.1
        -- Since r.1 ⊆ combinatorialSupport r, this gives us a contradiction with maximality
        have hr1_sub_support : r.1 ⊆ combinatorialSupport r := Finset.subset_union_left
        have hq_eq_r1_card : (combinatorialSupport q).card = r.1.card := by
          rw [hq_eq_r1]
        have hr1_card_le : r.1.card <  (combinatorialSupport r).card := by
          have hr2_nonempty : r.2.Nonempty := (T.NonemptyPairs r hr).2
          have hr2_sub_support : r.2 ⊆ combinatorialSupport r := Finset.subset_union_right
          have hr2_card_pos : r.2.card > 0 := Finset.card_pos.mpr hr2_nonempty
          have : r.1.card + r.2.card = (combinatorialSupport r).card := by
            rw [← Finset.card_union_of_disjoint (T.DisjointComponents r hr)]
            simp [combinatorialSupport]
          linarith [hr2_card_pos, this]
        have cardpr: (combinatorialSupport q).card < (combinatorialSupport r).card := by
          -- Since r.1 ⊂ combinatorialSupport r (r.2 is nonempty and disjoint from r.1)
          rw [hq_eq_r1]
          exact hr1_card_le
        -- This contradicts the maximality of q since r has a larger support but contains the same
        -- element c
        have hr_in_S : r ∈ S := Finset.mem_filter.mpr ⟨hr, hr_sub_p1⟩
        -- But we showed that (combinatorialSupport q).card < (combinatorialSupport r).card
        -- This contradicts maximality since hq_maximal should give us the opposite inequality
        have hr_card_le : (combinatorialSupport r).card ≤ (combinatorialSupport q).card :=
          hq_maximal r hr_in_S
        exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hr_card_le cardpr)
      | inr hr_eq_p =>
        -- Case: r = p
        -- This gives us r.1 = p.1, so combinatorialSupport q = r.1 = p.1
        rw [hr_eq_p] at hq_eq_r1
        exact hq_eq_r1
    | inr hq_eq_r2 =>
      -- Case: combinatorialSupport q = r.2
      -- Since combinatorialSupport q ⊆ p.1 and combinatorialSupport q = r.2, we have r.2 ⊆ p.1
      have hr2_sub : r.2 ⊆ p.1 := by
        rw [← hq_eq_r2]
        exact hq_sub
      -- Use inclusion_support_finner_2 with r.2 ⊆ p.1 to get r = p or combinatorialSupport r ⊆ p.1
      have hr_result := inclusion_support_finner_3 ⟨hr, h1⟩ hr2_sub
      cases hr_result with
      | inl hr_sub_p2 =>
        -- Case: combinatorialSupport r ⊆ p.1
        -- This contradicts the maximality of q among branches with support ⊆ p.1
        exfalso
        -- But we also have combinatorialSupport q = r.1, so q.1 ∪ q.2 = r.1
        -- Since r.1 ⊆ combinatorialSupport r, this gives us a contradiction with maximality
        have hr1_sub_support : r.1 ⊆ combinatorialSupport r := Finset.subset_union_left
        have hq_eq_r2card : (combinatorialSupport q).card = r.2.card := by
          rw [hq_eq_r2]
        have hr1_card_le : r.2.card <  (combinatorialSupport r).card := by
          have hr1_nonempty : r.1.Nonempty := (T.NonemptyPairs r hr).1
          have hr1_sub_support : r.1 ⊆ combinatorialSupport r := Finset.subset_union_left
          have hr1_card_pos : r.1.card > 0 := Finset.card_pos.mpr hr1_nonempty
          have : r.1.card + r.2.card = (combinatorialSupport r).card := by
            rw [← Finset.card_union_of_disjoint (T.DisjointComponents r hr)]
            simp [combinatorialSupport]
          linarith [hr1_card_pos, this]
        have cardpr: (combinatorialSupport q).card < (combinatorialSupport r).card := by
          -- Since r.1 ⊂ combinatorialSupport r (r.2 is nonempty and disjoint from r.1)
          rw [hq_eq_r2]
          exact hr1_card_le
        -- This contradicts the maximality of q since r has a larger support but contains the same
        -- element c
        have hr_in_S : r ∈ S := Finset.mem_filter.mpr ⟨hr, hr_sub_p2⟩
        -- But we showed that (combinatorialSupport q).card < (combinatorialSupport r).card
        -- This contradicts maximality since hq_maximal should give us the opposite inequality
        have hr_card_le : (combinatorialSupport r).card ≤ (combinatorialSupport q).card :=
          hq_maximal r hr_in_S
        exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hr_card_le cardpr)
      | inr hr_eq_p =>
        -- Case: r = p
        -- This gives us r.2 = p.2, so combinatorialSupport q = r.2 = p.2
        rw [hr_eq_p] at hq_eq_r2
        exfalso
        -- We have hq_eq_r2 : combinatorialSupport q = r.2 = p.2
        -- But we also have hq_sub : combinatorialSupport q ⊆ p.1
        -- Since combinatorialSupport q = p.2 and p.2 ⊆ p.1, and p.1 and p.2 are disjoint
        -- and p.2 is nonempty, this is a contradiction
        have hp2_sub_p1 : p.2 ⊆ p.1 := by
          rw [← hq_eq_r2]
          exact hq_sub
        have hp_disj : Disjoint p.1 p.2 := T.DisjointComponents p h1
        have hp2_nonempty : p.2.Nonempty := (T.NonemptyPairs p h1).2
        obtain ⟨y, hy⟩ := hp2_nonempty
        have hy_in_p1 : y ∈ p.1 := hp2_sub_p1 hy
        have hy_not_p1 : y ∉ p.1 := Finset.disjoint_right.mp hp_disj hy
        exact hy_not_p1 hy_in_p1

lemma maximal_compact_inside_p2 {α : Type*} [DecidableEq α]
  {T : BinaryTreeWithRootandTops α} {p : Finset α × Finset α} (h1 : p ∈ T.Branches)
  (h_ex : ∃ q ∈ T.Branches, combinatorialSupport q ⊆ p.2) :
  ∃ r ∈ T.Branches, combinatorialSupport r = p.2 := by
  -- Find q with the largest support among those satisfying h_ex
  let S := T.Branches.filter (fun b => combinatorialSupport b ⊆ p.2)
  have hS_nonempty : S.Nonempty := by
    rcases h_ex with ⟨q, hq, hq_sub⟩
    use q
    exact Finset.mem_filter.mpr ⟨hq, hq_sub⟩
  obtain ⟨q, hq_in_S, hq_maximal⟩ := S.exists_max_image (fun b => (combinatorialSupport b).card)
      hS_nonempty
  have hq_in_branches : q ∈ T.Branches := (Finset.mem_filter.mp hq_in_S).1
  have hq_sub : combinatorialSupport q ⊆ p.2 := (Finset.mem_filter.mp hq_in_S).2
  use q, hq_in_branches
  -- Use TreeStructure to show equality
  by_cases hq_root : q = T.Root
  case pos =>
    -- If q is the root, this is absurd because the support of root contains
    -- the support of any pair in branches due to RootcontainsChilds,
    -- but this is impossible since the support of p is not contained in the support of q
    exfalso
    -- q = Root and combinatorialSupport q ⊆ p.1
    -- But Root contains all Childs, so p.1 ⊆ Root.1 ∪ Root.2 = combinatorialSupport Root
    -- This would mean combinatorialSupport q ⊆ p.1 ⊆ combinatorialSupport q
    -- So p.1 = combinatorialSupport q, contradicting that p is a proper subset
    have hp_sub_root : combinatorialSupport p ⊆ combinatorialSupport T.Root := by
      dsimp [combinatorialSupport]
      have hp_in_childs := T.TreeStructureChilds p h1
      have hp_union_sub : p.1 ∪ p.2 ⊆ T.Childs := Finset.union_subset hp_in_childs.1 hp_in_childs.2
      exact hp_union_sub.trans T.RootcontainsChilds
    -- Since combinatorialSupport q ⊆ p.1 and p ∈ T.Branches,
    -- by SupportProperty, either they are disjoint or one is contained in the other
    -- But since q = Root and p ≠ Root (p is a proper branch),
    -- and hp_sub_root shows combinatorialSupport p ⊆ combinatorialSupport q,
    -- combined with hq_sub: combinatorialSupport q ⊆ p.1,
    -- we get combinatorialSupport q ⊆ p.1 ⊆ combinatorialSupport p ⊆ combinatorialSupport q
    -- This forces equality, contradicting that p should be distinct from q
    have hp_neq_q : p ≠ q := by
      rw [hq_root]
      intro h_eq
      -- If p = Root, then we have combinatorialSupport Root ⊆ p.1
      -- But p = Root means p.1 = Root.1, so we need Root.1 ∪ Root.2 ⊆ Root.1
      -- This would imply Root.2 ⊆ Root.1, contradicting DisjointRoot and NonemptyRoot
      rw [h_eq] at hq_sub
      -- hq_sub : combinatorialSupport Root ⊆ Root.1
      -- But combinatorialSupport Root = Root.1 ∪ Root.2
      dsimp [combinatorialSupport] at hq_sub
      -- So we have Root.1 ∪ Root.2 ⊆ Root.1
      -- This implies Root.2 ⊆ Root.1
      have h_subset : T.Root.1 ⊆ T.Root.2 := by
        intro x hx
        rw [hq_root] at hq_sub
        exact hq_sub (Finset.mem_union_left T.Root.2 hx)
      -- But T.Root.2 is nonempty and disjoint from T.Root.1
      have h_nonempty := T.NonemptyRoot.1
      have h_disjoint := T.DisjointRoot
      -- Get an element from Root.2
      obtain ⟨x, hx⟩ := h_nonempty
      -- y ∈ Root.2 and by h_subset, y ∈ Root.1
      have hx_in_2 : x ∈ T.Root.2 := h_subset hx
      -- But this contradicts disjointness
      have : x ∉ T.Root.2 := Finset.disjoint_left.mp h_disjoint hx
      exact this hx_in_2
    -- Now we use SupportProperty between p and q
    have h_support := T.SupportProperty p h1 q hq_in_branches hp_neq_q
    -- We have both hp_sub_root : combinatorialSupport p ⊆ combinatorialSupport q
    -- and hq_sub : combinatorialSupport q ⊆ p.1
    -- Since p.1 ⊆ combinatorialSupport p, this gives us a cycle of inclusions
    have hp2_sub : p.2 ⊆ combinatorialSupport p := Finset.subset_union_right
    have hp_sub_q : combinatorialSupport p ⊆ combinatorialSupport q := by
      rw [hq_root]; exact hp_sub_root
    have h_cycle : combinatorialSupport q ⊆ combinatorialSupport p ∧
                   combinatorialSupport p ⊆ combinatorialSupport q :=
      ⟨hq_sub.trans hp2_sub, hp_sub_q⟩
    -- This forces equality, but then by SupportProperty, p and q must be disjoint or
    -- one contained in the other, contradicting the equality
    have h_eq_support : combinatorialSupport p = combinatorialSupport q :=
      Finset.Subset.antisymm h_cycle.2 h_cycle.1
    -- This contradicts the distinctness required by the tree structure
    have hp_eq_q : p = q := by
      -- We have h_eq_support : combinatorialSupport p = combinatorialSupport q
      -- and we know q ≠ p (since hp_neq_q)
      -- But the SupportProperty says that for distinct branches p and q,
      -- either they are disjoint or one is contained in a component of the other
      have h_support_prop := T.SupportProperty p h1 q hq_in_branches hp_neq_q
      rw [h_eq_support] at h_support_prop
      -- Now h_support_prop becomes: either combinatorialSupport q is disjoint with itself,
      -- or combinatorialSupport q ⊆ p.1, or combinatorialSupport q ⊆ p.2, etc.
      -- The disjoint case is impossible, so we have containment
      cases h_support_prop with
      | inl hdisj =>
        -- Disjoint (combinatorialSupport q) (combinatorialSupport q) is impossible
        have hq_nonempty : (combinatorialSupport q).Nonempty := by
          dsimp [combinatorialSupport]
          have h1 : q.1.Nonempty := (T.NonemptyPairs q hq_in_branches).1
          exact Finset.Nonempty.inl h1
        have : ¬Disjoint (combinatorialSupport q) (combinatorialSupport q) :=
          Finset.not_disjoint_iff_nonempty_inter.mpr (by simp [hq_nonempty])
        exact False.elim (this hdisj)
      | inr hcases =>
        cases hcases with
    | inl hq_sub_p1 =>
      -- This case is impossible by support_not_subset_components
      exfalso
      have h_not_subset := support_not_subset_components hq_in_branches
      exact h_not_subset.1 hq_sub_p1
    | inr hrest =>
      -- Similar contradictions for the other cases
      cases hrest with
      | inl hq_sub_p2 =>
        -- This case is impossible by support_not_subset_components
        exfalso
        have h_not_subset := support_not_subset_components hq_in_branches
        exact h_not_subset.2 hq_sub_p2
      | inr hfinal =>
        -- The remaining cases involve q being contained in components of p,
        -- but since combinatorialSupport p = combinatorialSupport q,
        -- this leads to similar contradictions
        cases hfinal with
    | inl hp_sub_q1 =>
      rw [← h_eq_support] at hp_sub_q1
      exfalso
      have h_not_subset := support_not_subset_components h1
      exact h_not_subset.1 hp_sub_q1
    | inr hp_sub_q2 =>
      rw [← h_eq_support] at hp_sub_q2
      exfalso
      have h_not_subset := support_not_subset_components h1
      exact h_not_subset.2 hp_sub_q2
    exact hp_neq_q hp_eq_q
  case neg =>
    -- If q ≠ Root, use TreeStructure
    obtain ⟨r, hr, hr_contains⟩ := T.TreeStructure q hq_in_branches hq_root
    -- r is a parent of q, so q.1 ∪ q.2 ∈ pairToFinset r
    -- This means q.1 ∪ q.2 = r.1 or q.1 ∪ q.2 = r.2
    -- We have r is a parent of q, so combinatorialSupport q ∈ pairToFinset r
    -- This means either combinatorialSupport q = r.1 or combinatorialSupport q = r.2
    have hq_union_in_r : combinatorialSupport q ∈ pairToFinset r := by
      exact hr_contains
    -- From pairToFinset definition, this gives us the cases
    have hq_cases : combinatorialSupport q = r.1 ∨ combinatorialSupport q = r.2 := by
      dsimp [pairToFinset] at hq_union_in_r
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq_union_in_r
      exact hq_union_in_r
    cases hq_cases with
    | inl hq_eq_r1 =>
      -- Case: combinatorialSupport q = r.1
      -- Since combinatorialSupport q ⊆ p.1 and combinatorialSupport q = r.1, we have r.1 ⊆ p.1
      have hr1_sub : r.1 ⊆ p.2 := by
        rw [← hq_eq_r1]
        exact hq_sub
      -- Use inclusion_support_finner with r.1 ⊆ combinatorialSupport q = r.1 to get r = p or
      -- combinatorialSupport r ⊆ p.1
      have hr_result := inclusion_support_finner_2 ⟨hr, h1⟩ hr1_sub
      cases hr_result with
      | inl hr_sub_p1 =>
        -- Case: combinatorialSupport r ⊆ p.1
        -- This contradicts the maximality of q among branches with support ⊆ p.1
        exfalso
        -- But we also have combinatorialSupport q = r.1, so q.1 ∪ q.2 = r.1
        -- Since r.1 ⊆ combinatorialSupport r, this gives us a contradiction with maximality
        have hr1_sub_support : r.1 ⊆ combinatorialSupport r := Finset.subset_union_left
        have hq_eq_r1_card : (combinatorialSupport q).card = r.1.card := by
          rw [hq_eq_r1]
        have hr1_card_le : r.1.card <  (combinatorialSupport r).card := by
          have hr2_nonempty : r.2.Nonempty := (T.NonemptyPairs r hr).2
          have hr2_sub_support : r.2 ⊆ combinatorialSupport r := Finset.subset_union_right
          have hr2_card_pos : r.2.card > 0 := Finset.card_pos.mpr hr2_nonempty
          have : r.1.card + r.2.card = (combinatorialSupport r).card := by
            rw [← Finset.card_union_of_disjoint (T.DisjointComponents r hr)]
            simp [combinatorialSupport]
          linarith [hr2_card_pos, this]
        have cardpr: (combinatorialSupport q).card < (combinatorialSupport r).card := by
          -- Since r.1 ⊂ combinatorialSupport r (r.2 is nonempty and disjoint from r.1)
          rw [hq_eq_r1]
          exact hr1_card_le
        -- This contradicts the maximality of q since r has a larger support but contains the same
        -- element c
        have hr_in_S : r ∈ S := Finset.mem_filter.mpr ⟨hr, hr_sub_p1⟩
        -- But we showed that (combinatorialSupport q).card < (combinatorialSupport r).card
        -- This contradicts maximality since hq_maximal should give us the opposite inequality
        have hr_card_le : (combinatorialSupport r).card ≤ (combinatorialSupport q).card :=
          hq_maximal r hr_in_S
        exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hr_card_le cardpr)
      | inr hr_eq_p =>
        -- Case: r = p
        -- This gives us r.1 = p.1, so combinatorialSupport q = r.1 = p.1
        rw [hr_eq_p] at hq_eq_r1
        exfalso
        -- We have hq_eq_r1 : combinatorialSupport q = r.1
        -- and hr_eq_p : r = p
        -- So combinatorialSupport q = p.1
        -- But we also have hq_sub : combinatorialSupport q ⊆ p.2
        -- This means p.1 ⊆ p.2, which contradicts that p.1 and p.2 are disjoint
        have hp1_eq_q : p.1 = combinatorialSupport q := by
          exact hq_eq_r1.symm
        have hp1_sub_p2 : p.1 ⊆ p.2 := by
          rw [hp1_eq_q]
          exact hq_sub
        have hp_disj : Disjoint p.1 p.2 := T.DisjointComponents p h1
        have hp1_nonempty : p.1.Nonempty := (T.NonemptyPairs p h1).1
        obtain ⟨x, hx⟩ := hp1_nonempty
        have hx_in_p2 : x ∈ p.2 := hp1_sub_p2 hx
        have hx_not_p2 : x ∉ p.2 := Finset.disjoint_left.mp hp_disj hx
        exact hx_not_p2 hx_in_p2
    | inr hq_eq_r2 =>
      -- Case: combinatorialSupport q = r.2
      -- Since combinatorialSupport q ⊆ p.1 and combinatorialSupport q = r.2, we have r.2 ⊆ p.1
      have hr2_sub : r.2 ⊆ p.2 := by
        rw [← hq_eq_r2]
        exact hq_sub
      -- Use inclusion_support_finner_2 with r.2 ⊆ p.1 to get r = p or combinatorialSupport r ⊆ p.1
      have hr_result := inclusion_support_finner_4 ⟨hr, h1⟩ hr2_sub
      cases hr_result with
      | inl hr_sub_p2 =>
        -- Case: combinatorialSupport r ⊆ p.1
        -- This contradicts the maximality of q among branches with support ⊆ p.1
        exfalso
        -- But we also have combinatorialSupport q = r.1, so q.1 ∪ q.2 = r.1
        -- Since r.1 ⊆ combinatorialSupport r, this gives us a contradiction with maximality
        have hr1_sub_support : r.1 ⊆ combinatorialSupport r := Finset.subset_union_left
        have hq_eq_r2card : (combinatorialSupport q).card = r.2.card := by
          rw [hq_eq_r2]
        have hr1_card_le : r.2.card <  (combinatorialSupport r).card := by
          have hr1_nonempty : r.1.Nonempty := (T.NonemptyPairs r hr).1
          have hr1_sub_support : r.1 ⊆ combinatorialSupport r := Finset.subset_union_left
          have hr1_card_pos : r.1.card > 0 := Finset.card_pos.mpr hr1_nonempty
          have : r.1.card + r.2.card = (combinatorialSupport r).card := by
            rw [← Finset.card_union_of_disjoint (T.DisjointComponents r hr)]
            simp [combinatorialSupport]
          linarith [hr1_card_pos, this]
        have cardpr: (combinatorialSupport q).card < (combinatorialSupport r).card := by
          -- Since r.1 ⊂ combinatorialSupport r (r.2 is nonempty and disjoint from r.1)
          rw [hq_eq_r2]
          exact hr1_card_le
        -- This contradicts the maximality of q since r has a larger support but contains the same
        -- element c
        have hr_in_S : r ∈ S := Finset.mem_filter.mpr ⟨hr, hr_sub_p2⟩
        -- But we showed that (combinatorialSupport q).card < (combinatorialSupport r).card
        -- This contradicts maximality since hq_maximal should give us the opposite inequality
        have hr_card_le : (combinatorialSupport r).card ≤ (combinatorialSupport q).card :=
          hq_maximal r hr_in_S
        exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hr_card_le cardpr)
      | inr hr_eq_p =>
        -- Case: r = p
        -- This gives us r.2 = p.2, so combinatorialSupport q = r.2 = p.2
        rw [hr_eq_p] at hq_eq_r2
        exact hq_eq_r2


lemma all_have_property_insert_general {α : Type*} [DecidableEq α] {P : α → Prop} {x : α} {S :
    Finset α}
(hx : P x) (hS : ∀ y ∈ S, P y) : ∀ y ∈ insert x S, P y := by
  intro y hy
  rcases Finset.mem_insert.mp hy with (rfl | h_in)
  · exact hx
  · exact hS y h_in

lemma all_members_property_insert_general {α : Type*} [DecidableEq α] {P : α → Prop} {A : Finset α}
    {S : Finset α}
  (hA : ∀ y ∈ A, P y) (hS : ∀ y ∈ S, P y) :
      ∀ y ∈ A ∪S, P y := by
  intro y hy
  rcases Finset.mem_union.mp hy with (hA' | hS')
  · exact hA y hA'
  · exact hS y hS'

lemma new_pairs_in_childs [DecidableEq α] {pairs : Finset (Finset α × Finset α)} (T :
    BinaryTreeWithRootandTops α)
  (h3 : ∀ p ∈ pairs, ∃ q ∈ T.Branches, p.1 ∪ p.2 ∈ pairToFinset q) :
  ∀ p ∈ pairs, p.1 ⊆ T.Childs ∧ p.2 ⊆ T.Childs := by
  intro p hp
  -- use h3 to find q ∈ T.Branches and the equality of unions
  rcases h3 p hp with ⟨q, hq, hq_eq⟩
  -- split on whether p.1 ∪ p.2 = q.1 or = q.2
  -- pairToFinset q = {q.1, q.2}, so p.1 ∪ p.2 ∈ {q.1, q.2}
  have hmem : p.1 ∪ p.2 = q.1 ∨ p.1 ∪ p.2 = q.2 :=
    by
      simp only [pairToFinset] at hq_eq
      rw [Finset.mem_insert, Finset.mem_singleton] at hq_eq
      exact hq_eq
  cases hmem
  case inl h1 =>
    -- case p.1 ∪ p.2 = q.1
    have hq_subs := T.TreeStructureChilds q hq
    refine ⟨
      fun x hx => hq_subs.1 (by rw [←h1]; exact Finset.mem_union_left _ hx),
      fun x hx => hq_subs.1 (by rw [←h1]; exact Finset.mem_union_right _ hx)
    ⟩
  case inr h2 =>
    -- case p.1 ∪ p.2 = q.2
    have hq_subs := T.TreeStructureChilds q hq
    refine ⟨
      fun x hx => hq_subs.2 (by rw [←h2]; exact Finset.mem_union_left _ hx),
      fun x hx => hq_subs.2 (by rw [←h2]; exact Finset.mem_union_right _ hx)
    ⟩

  -- 1) Primeiro, um lema auxiliar que mora a disjunção {x}=p.1 ∨ {x}=p.2
lemma singleton_in_pairToFinset {α : Type*} [DecidableEq α]
  (p : Finset α × Finset α) {x : α} :
  {x} ∈ pairToFinset p → x∈  p.1 ∨ x∈ p.2 := by
  -- by definition pairToFinset p = insert p.1 {p.2}
  dsimp [pairToFinset]
  -- simplifica mem_insert e mem_singleton
  simp only [Finset.mem_insert, Finset.mem_singleton]
  intro h
  cases h
  case inl h1 =>
    left
    rw [h1.symm]
    exact Finset.mem_singleton_self x
  case inr h2 =>
    right
    rw [h2.symm]
    exact Finset.mem_singleton_self x

lemma singleton_in_support {α : Type*} [DecidableEq α]
  (p : Finset α × Finset α) {x : α} :
  {x} ∈ pairToFinset p → x ∈ p.1 ∪ p.2 := by
  -- by definition pairToFinset p = insert p.1 {p.2}
  dsimp [pairToFinset]
  -- simplifica mem_insert e mem_singleton
  simp only [Finset.mem_insert, Finset.mem_singleton]
  intro h
  cases h
  case inl h1 =>
    rw [h1.symm]
    exact Finset.mem_union_left _ (Finset.mem_singleton_self x)
  case inr h2 =>
    rw [h2.symm]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self x)


lemma mem_of_eq_singleton_of_subset {α : Type*}
  {x : α} {A T : Finset α}
  (hA : A = {x}) (hA_sub : A ⊆ T) :
  x ∈ T := by
    -- rewrite `A` to `{x}` in the subset proof
    rw [hA] at hA_sub
    -- now `hA_sub : {x} ⊆ T`, so
    exact Finset.mem_of_subset hA_sub (Finset.mem_singleton_self x)

lemma Compare_Supports [DecidableEq α]
  {p : Finset α × Finset α}
  (T : BinaryTreeWithRootandTops α)
  (h3 :
    ∃ q ∈ T.Branches,
      -- q é um ancestral imediato de p, e minimal
      p.1 ∪ p.2 ∈ pairToFinset q ∧
      ¬ ∃ r ∈ T.Branches, r ≠ q ∧
        combinatorialSupport r ⊆ combinatorialSupport q ∧ combinatorialSupport r ∩ (p.1 ∪ p.2) ≠ ∅)
            :
  ∀ w ∈ T.Branches,
    ((Disjoint (combinatorialSupport p) (combinatorialSupport w))∨
    (combinatorialSupport p ⊆ w.1) ∨
    (combinatorialSupport p ⊆ w.2)):= by
  -- 1) extrair q, hq, h₁ (p está em q) e h_min (não há r≠q com sup r ⊆ sup q)
  rcases h3 with ⟨q, hq, ⟨hp_in, h_min⟩⟩
  -- 2) como hp_in : (p.1 ∪ p.2) ∈ pairToFinset q, temos
  --    pairToFinset q = {q.1, q.2}, então
  have hcase : p.1 ∪ p.2 = q.1 ∨ p.1 ∪ p.2 = q.2 := by
    dsimp [pairToFinset] at hp_in
    -- simplifica mem_insert e mem_singleton
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp_in
    exact hp_in
  -- 3) para todo w em Branches
  intro w hw
  -- 4) tratamos os dois casos de hcase
  cases hcase
  case inl hq1 =>
    -- caso 𝚙.1 ∪ 𝚙.2 = q.1
    have hpsup : combinatorialSupport p = q.1 := by
      dsimp [combinatorialSupport]; rw [hq1]
    -- (a) se w = q, sobra mostrar p.support ⊆ w.support
    by_cases hwq : w = q
    case pos =>
      rw [hwq]
      right
      left
      -- combinatorialSupport p = q.1, so the inclusion is p.1 ∪ p.2 ⊆ q.1
      dsimp [combinatorialSupport]
      exact Finset.subset_of_eq hq1
    case neg =>
      -- Caso w ≠ q: pelo h_min, não existe r ≠ q com combinatorialSupport r ⊆ combinatorialSupport
      -- q
      -- Mas w ≠ q, então não pode ser combinatorialSupport w ⊆ combinatorialSupport q
      -- Então, pelo SupportPorperty de T, ou os suportes são disjuntos, ou combinatorialSupport q
      -- ⊆ combinatorialSupport w
      have hT := T.SupportProperty w hw q hq hwq
      cases hT with
      | inl hdisj =>
        left
        -- Disjoint (combinatorialSupport w) (combinatorialSupport q), mas combinatorialSupport p ⊆
        -- combinatorialSupport q
        -- Então também disjoint de combinatorialSupport p
        have hpq : combinatorialSupport p⊆ combinatorialSupport q := by
          dsimp [combinatorialSupport]
          rw [hq1]
          exact Finset.subset_union_left
        have hpr : Disjoint (combinatorialSupport p)  (combinatorialSupport w) := by
           exact  Finset.disjoint_of_subset_left hpq hdisj.symm
        exact hpr
      | inr hcases =>
        cases hcases with
        | inl hqsubw =>
          -- Este caso é impossível devido à minimalidade de q em h3: se combinatorialSupport q ⊆
          -- combinatorialSupport w, então pela propriedade de h3, q = w, contradizendo hwq.
          exfalso
          have hg: combinatorialSupport w ⊆ combinatorialSupport q ∧ (combinatorialSupport w ∩
              (p.1∪ p.2)≠ ∅) :=
            by
              dsimp [combinatorialSupport]
              have hq11 : q.1⊆  q.1 ∪ q.2:= by exact Finset.subset_union_left
              have hswsq: combinatorialSupport w ⊆ combinatorialSupport q:= hqsubw.trans (by
                dsimp [combinatorialSupport]
                exact Finset.subset_union_left)
              have hswp1p2: combinatorialSupport w ∩ (p.1∪ p.2)≠ ∅ :=
                by
                  have : p.1 ∪ p.2 ⊆ q.1 := by
                    rw [hq1]
                  have hw_sub_p1p2 :  combinatorialSupport w ⊆ p.1 ∪ p.2 := by
                    rw [hq1]
                    exact hqsubw
                  -- Since combinatorialSupport w ⊆ p.1 ∪ p.2 and w is nonempty, the intersection
                  -- is nonempty
                  have hw_nonempty : (combinatorialSupport w).Nonempty := by
                    dsimp [combinatorialSupport]
                    have h1 : w.1.Nonempty := (T.NonemptyPairs w hw).1
                    exact Finset.Nonempty.inl h1
                  obtain ⟨x, hx⟩ := hw_nonempty
                  have hx_in_inter : x ∈ combinatorialSupport w ∩ (p.1 ∪ p.2) :=
                    Finset.mem_inter.mpr ⟨hx, hw_sub_p1p2 hx⟩
                  exact Finset.ne_empty_of_mem hx_in_inter
              exact ⟨hswsq, hswp1p2⟩
          have : w=q :=
            by
              -- Pela minimalidade de q, se existe w ≠ q com combinatorialSupport q ⊆
              -- combinatorialSupport w, isso contradiz h_min
              by_contra hneq
              have contra := h_min ⟨w, hw, ⟨hneq, hg⟩⟩
              exact contra
          exact hwq this
        | inr hrest =>
          -- Os outros casos são inclusões de suportes de q em componentes de w, mas como q ≠ w,
          -- isso não pode acontecer por minimalidade de q
          -- Mas formalmente, como combinatorialSupport q ⊆ w.1 ou w.2, e combinatorialSupport p =
          -- q.1 ⊆ combinatorialSupport q, então combinatorialSupport p ⊆ w.1 ou w.2
          --rw [hpsup]
          cases hrest with
            | inl hqsubw1 =>
              have hf: p.1 ∪ p.2 ⊆ q.1 := by
                    rw [hq1]
              left
              simp only [combinatorialSupport] at hqsubw1
              simp only [combinatorialSupport]
              -- We have hqsubw1 : combinatorialSupport q ⊆ w.1
              -- This means q.1 ∪ q.2 ⊆ w.1
              -- Since w.1 and w.2 are disjoint, and q.1 ∪ q.2 ⊆ w.1, we have Disjoint (q.1 ∪ q.2)
              -- w.2
              have hq_disj_w1w2 : Disjoint q.1  (w.1∪w.2) := by
                -- Since w.1 ∪ w.2 ⊆ q.2 and q.1 and q.2 are disjoint, q.1 is disjoint from w.1 ∪
                -- w.2
                have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
                exact Finset.disjoint_of_subset_right hqsubw1 hq_disj
              have hp_disj_w2 : Disjoint (p.1 ∪ p.2) (w.1∪ w.2) := by
                have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
                exact Finset.disjoint_of_subset_left hf hq_disj_w1w2
              exact hp_disj_w2
            | inr hqsubw2 =>
               cases hqsubw2 with
                | inl hqsubw21 =>
                    dsimp [combinatorialSupport]
                    right
                    left
                    dsimp [combinatorialSupport] at hqsubw21
                    have hg: p.1∪p.2⊆ q.1∪q.2 := by
                      have hq2 : q.1⊆  q.1 ∪ q.2 := by exact Finset.subset_union_left
                      exact hq1 ▸ hq2
                    exact hg.trans hqsubw21
                | inr hqsubw22 =>
                  dsimp [combinatorialSupport]
                  right
                  right
                  dsimp [combinatorialSupport] at hqsubw22
                  have hg: p.1∪p.2⊆ q.1∪q.2 :=
                    by
                    have hq2 : q.1⊆  q.1 ∪ q.2 := by exact Finset.subset_union_left
                    exact hq1 ▸ hq2
                  exact hg.trans hqsubw22
  case inr hq2 =>
    -- case 𝚙.1 ∪ 𝚙.2 = q.2
    have hpsup : combinatorialSupport p = q.2 := by
      dsimp [combinatorialSupport]; rw [hq2]
    -- (a) if  w = q, it remains to show p.support ⊆ w.support
    by_cases hwq : w = q
    case pos =>
      rw [hwq]
      right
      right
      dsimp [combinatorialSupport]
      exact Finset.subset_of_eq hq2
    case neg =>
    -- Case w ≠ q: by h_min, there doesn't exist r ≠ q with combinatorialSupport r ⊆
    -- combinatorialSupport q
    -- But w ≠ q, so it cannot be that combinatorialSupport w ⊆ combinatorialSupport q
    -- Then, by SupportProperty of T, either the supports are disjoint, or combinatorialSupport q ⊆
    -- combinatorialSupport w
      have hT := T.SupportProperty w hw q hq hwq
      cases hT with
      | inl hdisj =>
        left
        have hpq : combinatorialSupport p⊆ combinatorialSupport q := by
          dsimp [combinatorialSupport]
          rw [hq2]
          exact Finset.subset_union_right
        have hpr : Disjoint (combinatorialSupport p)  (combinatorialSupport w) := by
           exact  Finset.disjoint_of_subset_left hpq hdisj.symm
        exact hpr
      | inr hcases =>
        cases hcases with
        | inl hqsubw =>
          have hf: p.1 ∪ p.2 ⊆ q.2 := by
                    rw [hq2]
          left
          simp only [combinatorialSupport] at hqsubw
          simp only [combinatorialSupport]
              -- We have hqsubw1 : combinatorialSupport q ⊆ w.1
              -- This means q.1 ∪ q.2 ⊆ w.1
              -- Since w.1 and w.2 are disjoint, and q.1 ∪ q.2 ⊆ w.1, we have Disjoint (q.1 ∪ q.2)
              -- w.2
          have hq_disj_w1w2 : Disjoint q.2  (w.1∪w.2) := by
          -- Since w.1 ∪ w.2 ⊆ q.2 and q.1 and q.2 are disjoint, q.1 is disjoint from w.1 ∪ w.2
                have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
                exact Finset.disjoint_of_subset_right hqsubw hq_disj.symm
          have hp_disj_w2 : Disjoint (p.1 ∪ p.2) (w.1∪ w.2) := by
                have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
                exact Finset.disjoint_of_subset_left hf hq_disj_w1w2
          exact hp_disj_w2
        | inr hrest =>
          cases hrest with
            | inl hqsubw1 =>
              -- Este caso é impossível devido à minimalidade de q em h3: se combinatorialSupport q
              -- ⊆ combinatorialSupport w, então pela propriedade de h3, q = w, contradizendo hwq.
              exfalso
              have hg: combinatorialSupport w ⊆ combinatorialSupport q ∧ (combinatorialSupport w ∩
                  (p.1∪ p.2)≠ ∅) :=
                by
                  dsimp [combinatorialSupport]
                  have hq11 : q.2⊆  q.1 ∪ q.2:= by exact Finset.subset_union_right
                  have hswsq: combinatorialSupport w ⊆ combinatorialSupport q:= hqsubw1.trans (by
                    dsimp [combinatorialSupport]
                    exact Finset.subset_union_right)
                  have hswp1p2: combinatorialSupport w ∩ (p.1∪ p.2)≠ ∅ :=
                    by
                      have : p.1 ∪ p.2 ⊆ q.2 := by
                        rw [hq2]
                      have hw_sub_p1p2 :  combinatorialSupport w ⊆ p.1 ∪ p.2 := by
                        rw [hq2]
                        exact hqsubw1
                      -- Since combinatorialSupport w ⊆ p.1 ∪ p.2 and w is nonempty, the
                      -- intersection is nonempty
                      have hw_nonempty : (combinatorialSupport w).Nonempty := by
                        dsimp [combinatorialSupport]
                        have h1 : w.1.Nonempty := (T.NonemptyPairs w hw).1
                        exact Finset.Nonempty.inl h1
                      obtain ⟨x, hx⟩ := hw_nonempty
                      have hx_in_inter : x ∈ combinatorialSupport w ∩ (p.1 ∪ p.2) :=
                        Finset.mem_inter.mpr ⟨hx, hw_sub_p1p2 hx⟩
                      exact Finset.ne_empty_of_mem hx_in_inter
                  exact ⟨hswsq, hswp1p2⟩
              have : w=q :=
                by
                  -- By the minimality of q, if there exists w ≠ q with
                  -- combinatorialSupport q ⊆ combinatorialSupport w, this contradicts h_min
                  by_contra hneq
                  have contra := h_min ⟨w, hw, ⟨hneq, hg⟩⟩
                  exact contra
              exact hwq this
            | inr hqsubw2 =>
               cases hqsubw2 with
                | inl hqsubw21 =>
                    dsimp [combinatorialSupport]
                    right
                    left
                    dsimp [combinatorialSupport] at hqsubw21
                    have hg: p.1∪p.2⊆ q.1∪q.2 :=
                      by
                      have hq2e : q.2⊆  q.1 ∪ q.2 := by exact Finset.subset_union_right
                      exact hq2 ▸ hq2e
                    exact hg.trans hqsubw21
                | inr hqsubw22 =>
                  dsimp [combinatorialSupport]
                  right
                  right
                  dsimp [combinatorialSupport] at hqsubw22
                  have hg: p.1∪p.2⊆ q.1∪q.2 :=
                    by
                    have hq2e : q.2⊆  q.1 ∪ q.2 := by exact Finset.subset_union_right
                    exact hq2 ▸ hq2e
                  exact hg.trans hqsubw22





lemma create_new_tree {α : Type*} [DecidableEq α]
    (T : BinaryTreeWithRootandTops α)
    (pairs : Finset (Finset α × Finset α))
    (h0 : ∀ a ∈ pairs, ∀ b ∈ T.Branches, Disjoint (pairToFinset a) (pairToFinset b))
    (h1 : ∀ p ∈ pairs, ∀ q ∈ pairs, (p ≠ q) → Disjoint (pairToFinset p) (pairToFinset q))
    (h3 : ∀ p ∈ pairs, ∃ q ∈ T.Branches, (p.1 ∪ p.2 ∈ pairToFinset q) ∧
        (¬ ∃ r ∈ T.Branches, (r ≠ q) ∧
        combinatorialSupport r ⊆ combinatorialSupport q ∧ combinatorialSupport r ∩ (p.1 ∪ p.2) ≠
        ∅))
    (h4 : ∀ p ∈ pairs, Disjoint p.1 p.2)
    (h6 : ∀ p ∈ pairs, p.1.Nonempty ∧ p.2.Nonempty)
    (h8 : ∀ p ∈ pairs, ∀ q ∈ pairs, p ≠ q →
    (Disjoint (combinatorialSupport p) (combinatorialSupport q) ∨
    combinatorialSupport p ⊆ q.1 ∨
    combinatorialSupport p ⊆ q.2 ∨
    combinatorialSupport q ⊆ p.1 ∨
    combinatorialSupport q ⊆ p.2)) :
∃ New_T : BinaryTreeWithRootandTops α, (New_T.Childs = T.Childs) ∧ (T.Branches ⊆
    New_T.Branches) ∧ (pairs ⊆ New_T.Branches) ∧ (T.Tops ⊆ New_T.Tops) :=
    let tops := T.Childs.filter (fun x => ∃ q ∈ pairs, {x} ∈ pairToFinset q)
    let h5 : ∀ x ∈ tops, ∃ p ∈ pairs, {x} ∈ pairToFinset p := by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hx1, hx2⟩
      rcases hx2 with ⟨p, hp, hpx⟩
      exact ⟨p, hp, hpx⟩
    let h7 : ∀ p ∈ pairs, ∀ x, {x} ∈ pairToFinset p → x ∈ tops := by
      intros p hp x hx
      -- 1) reduzimos `{x} ∈ pairToFinset p` à disjunção `{x} = p.1 ∨ {x} = p.2`
      have h_cases := singleton_in_pairToFinset p hx
      cases h_cases
      case inl h₁ =>
        -- caso `{x} = p.1`
        -- 2) obtemos p.1 ⊆ T.Childs
        let ⟨sub₁, _⟩ := (new_pairs_in_childs T (fun p hp => let ⟨q, hq, hq_and⟩ := h3 p hp; ⟨q,
            hq, hq_and.1⟩)) p hp
        -- 3) daí x ∈ T.Childs
        have x_in_C : x ∈ T.Childs :=  sub₁ h₁
        -- 4) e finalmente x ∈ tops = T.Childs.filter …
        apply Finset.mem_filter.mpr
        constructor
        · exact x_in_C
        · -- witness: p ∈ pairs e `{x} ∈ pairToFinset p`
          exact ⟨p, hp, hx⟩
      case inr h₂ =>
        -- caso `{x} = p.2`
        -- 2) obtemos p.1 ⊆ T.Childs
        let ⟨_,sub₁⟩ := (new_pairs_in_childs T (fun p hp => let ⟨q, hq, hq_and⟩ := h3 p hp; ⟨q, hq,
            hq_and.1⟩)) p hp
        -- 3) daí x ∈ T.Childs
        have x_in_C : x ∈ T.Childs :=  sub₁ h₂
        -- 4) e finalmente x ∈ tops = T.Childs.filter …
        apply Finset.mem_filter.mpr
        constructor
        · exact x_in_C
        · -- witness: p ∈ pairs e `{x} ∈ pairToFinset p`
          exact ⟨p, hp, hx⟩
    let New_T : BinaryTreeWithRootandTops α :=
        {T with
        Branches := T.Branches ∪ pairs,
        Tops := T.Tops ∪ tops,
        NonemptyPairs := all_members_property_insert_general
                T.NonemptyPairs
                h6,
        DisjointComponents := all_members_property_insert_general
                T.DisjointComponents
                h4,
        -- TODO: Provide a correct implementation for DistinctComponentsPairs
        -- DistinctComponentsPairs :=  all_members_property_insert_general ...,
        EveryChildinaBranch:= by
            intro a ha
            have ⟨p, hp, hpx⟩ := T.EveryChildinaBranch a ha
            exact ⟨p, Finset.mem_union_left _ hp, hpx⟩

        RootinBranches := by
          -- Root ∈ T.Branches ⊆ T.Branches ∪ pairs
          exact Finset.mem_union_left _ T.RootinBranches,
        TreeStructureChilds :=
          all_members_property_insert_general
            T.TreeStructureChilds
            (new_pairs_in_childs T (fun p hp => let ⟨q, hq, hq_and⟩ := h3 p hp; ⟨q, hq, hq_and.1⟩)),
        DistinctComponentsPairs :=
            fun p hp q hq hneq =>
              match Finset.mem_union.mp hp, Finset.mem_union.mp hq with
              | .inl hpT, .inl hqT =>
              T.DistinctComponentsPairs p hpT q hqT hneq
              | .inl hpT, .inr hqP =>
              h0 q hqP p hpT |> Disjoint.symm
              | .inr hpP, .inl hqT =>
              h0 p hpP q hqT
              | .inr hpP, .inr hqP =>
              h1 p hpP q hqP hneq,
        TreeStructure :=
          all_members_property_insert_general
            (fun p hp hne =>
            -- caso p ∈ T.Branches
            let ⟨q, hq, hq_eq⟩ := T.TreeStructure p hp hne
            ⟨q, Finset.mem_union_left _ hq, hq_eq⟩)
            (fun p hp _ =>
            -- caso p ∈ pairs
            let ⟨q, hq, hq_eq⟩ := h3 p hp
            ⟨q, Finset.mem_union_left _ hq, hq_eq.1⟩),
        TopsareTops := by
              intro y hy
              rcases Finset.mem_union.mp hy with (hT.Tops' | hTops')
              · -- T.Branches ⊆ T.Branches ∪ pairs, so lift the witness
                rcases T.TopsareTops y hT.Tops' with ⟨q, hq, hq_mem⟩
                exact ⟨q, Finset.mem_union_left _ hq, hq_mem⟩
              · rcases h5 y hTops' with ⟨q, hq, hq_mem⟩
                exact ⟨q, Finset.mem_union_right _ hq, hq_mem⟩
        SingletonsAreTops :=
              fun q hq x hx =>
              by
                rcases mem_union.mp hq with (h_branch | h_new)
                case inl =>
                  -- caso q ∈ T.Branches
                  have : x ∈ T.Tops :=
                    T.SingletonsAreTops q h_branch x hx
                  exact Finset.mem_union_left _ this  -- x ∈ T.Tops ⊆ T.Tops ∪ tops
                case inr =>
                  -- caso q ∈ pairs
                  have : x ∈ tops :=
                    h7 q h_new x (by exact hx)
                  exact Finset.mem_union_right _ this,  -- x ∈ tops ⊆ T.Tops ∪ tops
        SupportProperty := by
          intros p hp q hq hneq
          cases Finset.mem_union.1 hp
          case  inl hpT =>
            cases Finset.mem_union.1 hq
            case inl hqT =>
              exact T.SupportProperty p hpT q hqT hneq
            case inr hqP =>
              have h3p := h3 q hqP
              have hht: Disjoint (combinatorialSupport q) (combinatorialSupport p)
               ∨ combinatorialSupport q ⊆ p.1
               ∨ combinatorialSupport q ⊆ p.2 := by exact Compare_Supports T h3p p hpT
              -- Extend the 3-way disjunction to the required 5-way disjunction
              cases hht with
              | inl hdisj => exact Or.inl hdisj.symm
              | inr hcases =>
                right; right;right
                exact hcases
          case inr hpP =>
            cases Finset.mem_union.1 hq
            case inl hqT =>
              have h3p := h3 p hpP
              have hht: Disjoint (combinatorialSupport p) (combinatorialSupport q)
               ∨ combinatorialSupport p ⊆ q.1
               ∨ combinatorialSupport p ⊆ q.2 := by exact Compare_Supports T h3p q hqT
              -- Extend the 3-way disjunction to the required 5-way disjunction
              cases hht with
              | inl hdisj => exact Or.inl hdisj
              | inr hcases =>
                cases hcases with
                | inl hsub1 => exact Or.inr (Or.inl hsub1)
                | inr hsub2 => exact Or.inr (Or.inr (Or.inl hsub2))
            case inr hqP =>
              exact h8 p hpP q hqP hneq
        }
    ⟨New_T, rfl, Finset.subset_union_left, Finset.subset_union_right, Finset.subset_union_left⟩

lemma exists_binary_tree_with_childs_eq_C {α : Type*} [DecidableEq α] {C : Finset α} (hC : C.card ≥
    2) :
∃ T : BinaryTreeWithRootandTops α, (T.Childs = C) := by
  have hC_nonempty : C.Nonempty := Finset.card_pos.mp (Nat.lt_of_lt_of_le zero_lt_two hC)
  -- Pick two distinct elements from C
  obtain ⟨a, ha⟩ := hC_nonempty
  have hC2 : ∃ b, b ≠ a ∧ b ∈ C := by
    have hErase : 0 < (C.erase a).card := by
      rw [Finset.card_erase_of_mem ha]
      exact Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hC)
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hErase
    have hb' : b ≠ a ∧ b ∈ C := Finset.mem_erase.mp hb
    exact ⟨b, hb'.1, hb'.2⟩
  obtain ⟨b, hba, hb⟩ := hC2
  let p : Finset α × Finset α := ({a}, C \ {a})
  have anempty: ({a} : Finset α).Nonempty := Finset.singleton_nonempty a
  have cmanempty: (C \ {a}).Nonempty := by
    -- b ∈ C and b ≠ a, so b ∈ C \ {a}
    have hbaa: b ∉ ({a} : Finset α) := by
      intro h
      exact hba (Finset.mem_singleton.mp h)
    have t: b ∈ C\{a}:= Finset.mem_sdiff.mpr ⟨hb, hbaa⟩
    exact  ⟨b, t⟩
  have pnempty : p.1.Nonempty ∧ p.2.Nonempty :=by
   dsimp [p]
   exact ⟨anempty, cmanempty⟩
  -- {a} é não vazio pois contém a
  have p1p2C: p.1 ∪ p.2 ⊆  C := by
    dsimp [p]
    exact union_sdiff_of_mem ha
  have dp: Disjoint p.1 p.2 := by
    dsimp [p]
    exact singleton_disjoint_sdiff C a
  have p1p2Cb: p.1 ⊆ C ∧  p.2 ⊆  C := by
    dsimp [p]
    constructor
    · exact Finset.singleton_subset_iff.mpr ha
    · intros x hx
      exact (Finset.mem_sdiff.mp hx).1
  have dp: Disjoint p.1 p.2 := by
    dsimp [p]
    exact singleton_disjoint_sdiff C a
  let branches : Finset (Finset α × Finset α) := {p}
  have childsinabranch : ∀ b ∈ C, ∃ q ∈ branches, b ∈ combinatorialSupport q := by
    intros c hc
    -- Como branches = {p}, então p é o único elemento de branches
    use p, Finset.mem_singleton_self p
    -- combinatorialSupport p = p.1 ∪ p.2 = {a} ∪ (C \ {a}) = C
    dsimp [combinatorialSupport, p]
    have : {a} ∪ (C \ {a}) = C := by
        apply Finset.Subset.antisymm
        · exact union_sdiff_of_mem ha
        · exact subset_singleton_union_sdiff C a
    have hc' : c ∈ ({a} ∪ (C \ {a})) := by
      rw [this]
      exact hc
    exact hc'
  have branches_singleton : branches = {p} := rfl
  let tops := C.filter (fun x => {x} ∈ pairToFinset p)
  have tops_property : ∀ x ∈ tops, ∃ q ∈ branches, {x} ∈ pairToFinset q := by
      -- Como tops = C.filter (λ x => {x} ∈ pairToFinset p) e branches = {p}, basta testemunhar p ∈
      -- branches
      intros x hx
      use p
      exact ⟨Finset.mem_singleton_self p, (Finset.mem_filter.mp hx).2⟩
  have singleton_are_tops :∀ q ∈ branches,
       ∀ x, {x} ∈ pairToFinset q → (x ∈ tops):= by
    intros q hq x hx
    -- Como branches = {p}, só existe q = p
    rw [branches_singleton] at hq
    rw [Finset.mem_singleton] at hq
    subst hq
    -- Agora q = p
    have hC: x∈ C := by
      -- Como p.1 = {a}, p.2 = C \ {a}, então x ∈ C
      -- Como {x} ∈ pairToFinset p, então x ∈ p.1 ∪ p.2, e p.1 ∪ p.2 ⊆ C
      have x_in_p : x ∈ p.1 ∪ p.2 := singleton_in_support p hx
      exact Finset.mem_of_subset p1p2C x_in_p
    -- Como x ∈ C e {x} ∈ pairToFinset p, então x ∈ tops = C.filter (λ x => {x} ∈ pairToFinset p)
    exact Finset.mem_filter.mpr ⟨hC, hx⟩
  have nonempty_pairs : ∀ q ∈ branches, q.1.Nonempty ∧ q.2.Nonempty := by
    intros q hq
    -- branches = {p}, então q = p
    rw [branches_singleton] at hq
    rw [Finset.mem_singleton] at hq
    rw [hq]
    exact ⟨anempty, cmanempty⟩
    -- p.1 = {a}, p.2 = C \ {a}
  have disjoint_components : ∀ p ∈ branches, Disjoint p.1 p.2 := by
    intros y hy
    have : y = p := by simpa [branches] using hy
    rw [this]
    exact dp
  -- Como `branches` só tem um elemento, não existem `p ≠ q` com `p, q ∈ branches`
  have distinct_components_pairs:  ∀ p ∈ branches, ∀ q ∈ branches, (p ≠ q)->Disjoint (pairToFinset
      p) (pairToFinset q) := by
    intros p hp q hq hneq
    -- Como branches é singleton, q = p
    rw [branches_singleton] at hp hq
    rw [Finset.mem_singleton] at hp hq
    subst hp
    subst hq
    exact False.elim (hneq rfl)
  have root_in_branches : p ∈ branches := Finset.mem_singleton_self p
  have root_contains_childs : C ⊆ p.1 ∪ p.2 := by
    simp only [p]
    exact subset_singleton_union_sdiff C a
  have tree_structure_childs : ∀ q ∈ branches, q.1 ⊆ C ∧ q.2 ⊆ C := by
    intros y hy
    -- branches = {p}, então y = p
    rw [branches_singleton] at hy
    rw [Finset.mem_singleton] at hy
    subst hy
    -- Agora a meta é p.1 ⊆ C ∧ p.2 ⊆ C
    -- Sabemos que p = ({a}, C \ {a})
    dsimp [p]
    exact p1p2Cb
  have tree_structure : ∀ p_1 ∈ branches, p_1 ≠ p → ∃ q ∈ branches, p_1.1 ∪ p_1.2 ∈ pairToFinset q
      := by
    intros p_1 hp_1 h
    -- Since branches = {p}, we have p_1 = p
    rw [branches_singleton] at hp_1
    rw [Finset.mem_singleton] at hp_1
    rw [hp_1] at h
    -- Now h is asserting p ≠ p, which is a contradiction
    exfalso; exact h rfl
  have tops_are_tops := tops_property
  have singletons_are_tops : ∀ q ∈ branches, ∀ x, {x} ∈ pairToFinset q → x ∈ tops := by
    intros _ hp x hx
    rw [branches_singleton] at hp
    rw [Finset.mem_singleton] at hp
    rw [hp] at hx
    have hww: x∈ C:= by
      exact Finset.mem_of_subset p1p2C (singleton_in_support p hx)
    exact Finset.mem_filter.mpr ⟨hww, hx⟩
  have nonempty_root : p.1.Nonempty ∧ p.2.Nonempty :=
    by
      dsimp [p]
      constructor
      · exact anempty
      · exact cmanempty
  have nonempty_childs : C.Nonempty := by
    -- C é não vazio pois contém a
    exact ⟨a, ha⟩
  have disjoint_root : Disjoint p.1 p.2 := dp
  have support_property : ∀ p ∈ branches, ∀ q ∈ branches, p ≠ q →
    (Disjoint (combinatorialSupport p) (combinatorialSupport q) ∨
    combinatorialSupport p ⊆ q.1 ∨
    combinatorialSupport p ⊆ q.2 ∨
    combinatorialSupport q ⊆ p.1 ∨
    combinatorialSupport q ⊆ p.2) := by
    intros p hp q hq hneq
    rw [branches_singleton] at hp hq
    simp only [Finset.mem_singleton] at hp hq
    subst p; subst q
    exfalso; exact hneq rfl
  exact ⟨BinaryTreeWithRootandTops.mk
    p
    C
    branches
    nonempty_pairs
    tops
    disjoint_components
    distinct_components_pairs
    root_in_branches
    childsinabranch
    root_contains_childs
    tree_structure_childs
    tree_structure
    tops_are_tops
    singletons_are_tops
    nonempty_root
    nonempty_childs
    disjoint_root
    support_property, rfl⟩


/-- The two-element finset of the freshly split pair is disjoint from the finset of every
existing branch. -/
lemma newPairLeft_disjoint {α : Type*} [DecidableEq α]
    {T : BinaryTreeWithRootandTops α} {q : Finset α × Finset α} (hq : q ∈ T.Branches)
    {c : α}
    (hc_in_q1 : c ∈ q.1)
    (hq1_card_ge_2 : q.1.card ≥ 2)
    (hq_minimal : ¬∃ r ∈ T.Branches, r ≠ q ∧ c ∈ combinatorialSupport r ∧
      combinatorialSupport r ⊆ combinatorialSupport q) :
    ∀ b ∈ T.Branches, Disjoint (pairToFinset ((q.1 \ {c}, {c}) : Finset α × Finset α))
      (pairToFinset b) := by
  let p : Finset α × Finset α := (q.1 \ {c}, {c})
  intro b hb
  by_cases hqb : q = b
  case pos =>
    -- Case q = b: this contradicts the fact that {p.1, p.2} is disjoint from {q.1, q.2}
    rw[hqb.symm]
    simp only [pairToFinset, Finset.disjoint_insert_right,
Finset.disjoint_singleton_right, Finset.mem_insert, Finset.mem_singleton, not_or]
    -- We have p.1 ∪ p.2 = q.1, so pairToFinset p contains q.1
    -- But pairToFinset b = pairToFinset q contains q.1 as well
    -- This means pairToFinset p and pairToFinset b are not disjoint
    have hp_union : p.1 ∪ p.2 = q.1 := by
     dsimp [p]
     rw [Finset.sdiff_union_of_subset]
     exact Finset.singleton_subset_iff.mpr hc_in_q1
    have hp1dq1: ¬ p.1= q.1 := by
      dsimp [p]
      intro h_eq
      -- We have p.1 = q.1 \ {c} and h_eq says q.1 \ {c} = q.1
      -- This would mean c ∉ q.1, contradicting hc_in_q1
      have hc_not_in_q1 : c ∉ q.1 := by
        rw [← h_eq]
        simp [Finset.mem_sdiff, Finset.mem_singleton]
      exact hc_not_in_q1 hc_in_q1
    have hp2dq1: ¬ p.2= q.1 := by
      dsimp [p]
      intro h_eq
      -- We have p.2 = {c} and h_eq says {c} = q.1
      -- This would mean q.1 = {c}, which contradicts hq1_card_ge_2
      rw [← h_eq] at hq1_card_ge_2
      simp only [Finset.card_singleton] at hq1_card_ge_2
      linarith
    have hp1dq2: ¬ p.1= q.2 := by
      dsimp [p]
      intro h_eq
      -- We have p.1 = q.1 \ {c} and h_eq says q.1 \ {c} = q.2
      -- Since q.1 and q.2 are disjoint and q.2 is nonempty, we get a contradiction
      have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
      have hq2_nonempty : q.2.Nonempty := (T.NonemptyPairs q hq).2
      obtain ⟨x, hx⟩ := hq2_nonempty
      -- x ∈ q.2, but by h_eq, q.2 = q.1 \ {c} ⊆ q.1
      have hx_in_q1 : x ∈ q.1 := by
        rw [← h_eq] at hx
        exact Finset.mem_of_subset Finset.sdiff_subset hx
      -- This contradicts disjointness since x ∈ q.1 ∩ q.2
      exact Finset.disjoint_left.mp hq_disj hx_in_q1 hx
    have hp2dq2: ¬ p.2= q.2 := by
      intro h_eq
      -- We have p.2 = {c} and h_eq says {c} = q.2
      -- Since c ∈ q.1 and q.1 and q.2 are disjoint, we have c ∉ q.2
      have hc_not_in_q2 : c ∉ q.2 := by
        have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
        exact Finset.disjoint_left.mp hq_disj hc_in_q1
      -- But h_eq would imply c ∈ q.2
      have hc_in_q2 : c ∈ q.2 := by
        rw [← h_eq]
        exact Finset.mem_singleton_self c
      exact hc_not_in_q2 hc_in_q2
    have hne : (¬ q.1 = p.1 ∧ ¬ q.1 = p.2) ∧ ¬ q.2 = p.1 ∧ ¬ q.2 = p.2 := by
     refine ⟨⟨mt Eq.symm hp1dq1, mt Eq.symm hp2dq1⟩, mt Eq.symm hp1dq2, mt Eq.symm hp2dq2⟩
    exact hne
  case neg =>
    -- Case q ≠ b: use SupportProperty between q and b
    have h_support := T.SupportProperty q hq b hb hqb
    cases h_support with
    | inl hdisj =>
      -- Case: Disjoint (combinatorialSupport q) (combinatorialSupport b)
      -- Since combinatorialSupport p ⊆ combinatorialSupport q (as p.1 ∪ p.2 = q.1)
      -- and Disjoint (combinatorialSupport q) (combinatorialSupport b)
      -- we get Disjoint (combinatorialSupport p) (combinatorialSupport b)
      have hp_subset_q : combinatorialSupport p ⊆ combinatorialSupport q := by
        dsimp [combinatorialSupport, p]
        have h_union : (q.1 \ {c}) ∪ {c} = q.1 := by
          rw [Finset.sdiff_union_of_subset]
          exact Finset.singleton_subset_iff.mpr hc_in_q1
        rw [h_union]
        exact Finset.subset_union_left
      have hp_disj_b : Disjoint  (combinatorialSupport b) (combinatorialSupport p):=
        Finset.disjoint_of_subset_right hp_subset_q hdisj.symm
      have h_disj : Disjoint (pairToFinset b) (pairToFinset p) := by
        exact disjoint_suppport_pairfinset_disjoint hb hp_disj_b
      exact  h_disj.symm
    | inr hcases =>
      have disjp1p2: Disjoint p.1 p.2:= by
        dsimp [p]
        exact (singleton_disjoint_sdiff q.1 c).symm
      cases hcases with
      | inl hq_sub_b1 =>
        -- Case: combinatorialSupport q ⊆ b.1
        have hcpcb1: combinatorialSupport p ⊆ b.1 := by
          dsimp [combinatorialSupport, p]
          have h_union : (q.1 \ {c}) ∪ {c} = q.1 := by
            rw [Finset.sdiff_union_of_subset]
            exact Finset.singleton_subset_iff.mpr hc_in_q1
          rw [h_union]
          -- Now we need q.1 ⊆ b.1, which follows from hq_sub_b1
          dsimp [combinatorialSupport] at hq_sub_b1
          exact Finset.subset_union_left.trans hq_sub_b1
        have hnempty: p.1.Nonempty ∧ p.2.Nonempty := by
          constructor
          · -- q.1 \ {c} is nonempty since q.1.card ≥ 2
            dsimp [p]
            have : (q.1 \ {c}).card = q.1.card - 1 := by
                rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr
                    hc_in_q1)]
                simp
            have card_pos : (q.1 \ {c}).card > 0 := by
              rw [this]
              have := hq1_card_ge_2
              omega
            exact Finset.card_pos.mp card_pos
          · exact Finset.singleton_nonempty c
        have h_disj : Disjoint (pairToFinset p) (pairToFinset b) := by
          apply suppp_p_incl_q1_disjoint_pairfinset hb hcpcb1 disjp1p2 hnempty
        exact h_disj
      | inr hrest =>
        cases hrest with
        | inl hq_sub_b2 =>
          -- Case: combinatorialSupport q ⊆ b.2
        have hcpcb2: combinatorialSupport p ⊆ b.2 := by
          dsimp [combinatorialSupport, p]
          have h_union : (q.1 \ {c}) ∪ {c} = q.1 := by
            rw [Finset.sdiff_union_of_subset]
            exact Finset.singleton_subset_iff.mpr hc_in_q1
          rw [h_union]
          -- Now we need q.1 ⊆ b.2, which follows from hq_sub_b2
          dsimp [combinatorialSupport] at hq_sub_b2
          exact Finset.subset_union_left.trans hq_sub_b2
        have hnempty: p.1.Nonempty ∧ p.2.Nonempty := by
          constructor
          · -- q.1 \ {c} is nonempty since q.1.card ≥ 2
            dsimp [p]
            have : (q.1 \ {c}).card = q.1.card - 1 := by
                rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr
                    hc_in_q1)]
                simp
            have card_pos : (q.1 \ {c}).card > 0 := by
              rw [this]
              have : q.1.card ≥ 2 := hq1_card_ge_2
              have : q.1.card - 1 ≥ 1 := Nat.sub_le_sub_right this 1
              simp at this
              linarith
            exact Finset.card_pos.mp card_pos
          · exact Finset.singleton_nonempty c
        have h_disj : Disjoint (pairToFinset p) (pairToFinset b) := by
          apply suppp_p_incl_q2_disjoint_pairfinset hb hcpcb2 disjp1p2 hnempty
        exact h_disj
        | inr hfinal =>
          cases hfinal with
          | inl hb_sub_q1 =>
            -- Case: combinatorialSupport b ⊆ q.1
            -- maximal_compact_inside_p1
            exfalso
            have hr_exists : ∃ s ∈ T.Branches, combinatorialSupport s = q.1 := by
              apply maximal_compact_inside_p1 hq
              exact ⟨b, hb, hb_sub_q1⟩
            obtain ⟨s, hs, hs_eq⟩ := hr_exists
            -- Now s has support exactly q.1, but q also has q.1 in its support
            -- This should lead to a contradiction with the tree structure
            -- Since s has support exactly q.1 and c ∈ q.1, we have c ∈
            -- combinatorialSupport s
            have hc_in_s : c ∈ combinatorialSupport s := by
              rw [hs_eq]
              exact hc_in_q1
            -- But s ≠ q since they have different supports
            have hs_neq_q : s ≠ q := by
              intro h_eq
              rw [h_eq] at hs_eq
              -- This would mean combinatorialSupport q = q.1, contradicting
              -- support_not_subset_components
              have h_not_subset := support_not_subset_components hq
              exact h_not_subset.1 (Finset.subset_of_eq hs_eq)
            -- This contradicts the minimality of q
            have : combinatorialSupport s ⊆ combinatorialSupport q := by
              rw [hs_eq]
              dsimp [combinatorialSupport]
              exact Finset.subset_union_left
            exact hq_minimal ⟨s, hs, hs_neq_q, hc_in_s, this⟩
          | inr hb_sub_q2 =>
            -- Case: combinatorialSupport b ⊆ q.2
            have spsbdisj:   Disjoint (combinatorialSupport p)  (combinatorialSupport b)
                := by
              have hp_eq_q1 : combinatorialSupport p = q.1 := by
                dsimp [combinatorialSupport, p]
                rw [Finset.sdiff_union_of_subset]
                exact Finset.singleton_subset_iff.mpr hc_in_q1
              rw [hp_eq_q1]
              have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
              exact Finset.disjoint_of_subset_right hb_sub_q2 hq_disj
            have h_disj : Disjoint  (pairToFinset b) (pairToFinset p) := by
             apply disjoint_suppport_pairfinset_disjoint hb spsbdisj.symm
            exact h_disj.symm

/-- Descent helper: builds a measure-decreasing tree when the chosen child lies in the
left component of the minimal branch. -/
lemma exists_tree_succ_measure_inLeft {α : Type*} [DecidableEq α] {C : Finset α} {n : ℕ}
    {T : BinaryTreeWithRootandTops α} (hT_eq : T.Childs = C)
    (hT_measure : (C \ T.Tops).card ≤ n + 1)
    {c : α} (hc : c ∈ C \ T.Tops) (hc_not_tops : c ∉ T.Tops) (_hc_in_childs : c ∈ T.Childs)
    {q : Finset α × Finset α} (hq : q ∈ T.Branches) (_hc_in_q : c ∈ combinatorialSupport q)
    (hq_minimal : ¬∃ r ∈ T.Branches, r ≠ q ∧ c ∈ combinatorialSupport r ∧
      combinatorialSupport r ⊆ combinatorialSupport q)
    (_h_eq : ¬T.Tops = C)
    (hc_in_q1 : c ∈ q.1) :
    ∃ S : BinaryTreeWithRootandTops α, ∃ _ : S.Childs = C, (C \ S.Tops).card ≤ n := by
  classical
  -- Case: c ∈ q.1
  -- q.1 must have at least 2 elements since c is not a top
  have hq1_card_ge_2 : q.1.card ≥ 2 := by
    by_contra h_not
    push Not at h_not
    have hq1_card_lt_2 : q.1.card < 2 := h_not
    interval_cases h : (q.1.card)
    · -- q.1.card = 0, contradicts nonempty
      have hq1_nonempty : q.1.Nonempty := (T.NonemptyPairs q hq).1
      rw [Finset.card_eq_zero] at h
      rw [h] at hq1_nonempty
      exact Finset.not_nonempty_empty hq1_nonempty
    · -- q.1.card = 1, so q.1 = {c}
      have hq1_singleton : q.1 = {c} := by
        have hc_only : ∀ x ∈ q.1, x = c := by
          intro x hx
          have : q.1.card = 1 := h
          rw [Finset.card_eq_one] at this
          obtain ⟨y, hy⟩ := this
          rw [hy] at hx hc_in_q1
          exact (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hc_in_q1).symm
        exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hc_in_q1, hc_only⟩
      -- But then {c} ∈ pairToFinset q, so c ∈ T.Tops by SingletonsAreTops
      have hc_in_tops : c ∈ T.Tops := by
        apply T.SingletonsAreTops q hq c
        dsimp [pairToFinset]
        rw [hq1_singleton]
        exact Finset.mem_insert_self {c} {q.2}
      exact hc_not_tops hc_in_tops
  -- Since q.1.card ≥ 2, we can create a new pair p = (q.1 \ {c}, {c})
  let p : Finset α × Finset α := (q.1 \ {c}, {c})
  let pairs : Finset (Finset α × Finset α) := {p}
  -- Verify all conditions for create_new_tree
  have h0 : ∀ a ∈ pairs, ∀ b ∈ T.Branches, Disjoint (pairToFinset a) (pairToFinset b) := by
    intro a ha b hb
    rw [Finset.eq_of_mem_singleton ha]
    exact newPairLeft_disjoint hq hc_in_q1 hq1_card_ge_2 hq_minimal b hb
  have h1 : ∀ p_1 ∈ pairs, ∀ q_1 ∈ pairs, (p_1 ≠ q_1) → Disjoint (pairToFinset p_1)
      (pairToFinset q_1) := by
    intro p_1 hp_1 q_1 hq_1 hneq
    -- Since pairs = {p}, both p_1 and q_1 equal p
    have hp_1_eq : p_1 = p := Finset.eq_of_mem_singleton hp_1
    have hq_1_eq : q_1 = p := Finset.eq_of_mem_singleton hq_1
    rw [hp_1_eq, hq_1_eq] at hneq
    exact False.elim (hneq rfl)
  have h3 : ∀ p_elem ∈ pairs, ∃ q_elem ∈ T.Branches, (p_elem.1 ∪ p_elem.2 ∈ pairToFinset
      q_elem) ∧ (¬ ∃ r ∈ T.Branches, (r ≠ q_elem) ∧ combinatorialSupport r ⊆
      combinatorialSupport q_elem∧ combinatorialSupport r ∩ (p_elem.1 ∪ p_elem.2) ≠ ∅) := by
    intro p_elem hp_elem
    have hp_elem_eq : p_elem = p := Finset.eq_of_mem_singleton hp_elem
    rw [hp_elem_eq]
    -- Now we need to show there exists q_elem ∈ T.Branches such that p.1 ∪ p.2 ∈
    -- pairToFinset q_elem
    -- and q_elem is minimal
    -- We have p = (q.1 \ {c}, {c}), so p.1 ∪ p.2 = (q.1 \ {c}) ∪ {c} = q.1
    use q, hq
    have hfinal: ¬∃ r ∈ T.Branches, r ≠ q ∧ c ∈ combinatorialSupport r ∧
        combinatorialSupport r ⊆  combinatorialSupport q :=by
      intro h
      obtain ⟨r, hr, hr_neq, hc_in_r, hr_subset⟩ := h
      -- Since r ≠ q and c ∈ combinatorialSupport r, we have r ≠ q
      have hr_contra: combinatorialSupport r ∩  (p.1 ∪ p.2)≠ ∅:= by
          have : c ∈ p.1 ∪ p.2 := by
            dsimp [p]
            exact Finset.mem_union_right (q.1 \ {c}) (Finset.mem_singleton_self c)
          have : c ∈ combinatorialSupport r ∩ (p.1 ∪ p.2) :=
            Finset.mem_inter.mpr ⟨hc_in_r, this⟩
          exact Finset.ne_empty_of_mem this
      exact hq_minimal ⟨r, hr, hr_neq, hc_in_r, hr_subset⟩
    have hfinal2: ¬∃ r ∈ T.Branches, r ≠ q ∧ combinatorialSupport r ⊆  combinatorialSupport
        q∧ combinatorialSupport r ∩(p.1 ∪ p.2)≠  ∅:= by
      intro ⟨r, hr, hr_neq, hr_subset, hr_intersect⟩
      -- Case analysis: either c ∈ combinatorialSupport r or c ∉ combinatorialSupport r
      by_cases hc_r : c ∈ combinatorialSupport r
      · -- Case: c ∈ combinatorialSupport r
        -- We need to show combinatorialSupport r ⊂ combinatorialSupport q
        exact hfinal ⟨r, hr, hr_neq, hc_r, hr_subset⟩
      · -- Case: c ∉ combinatorialSupport r
        -- Since hr_intersect: combinatorialSupport r ∩ (p.1 ∪ p.2) ≠ ∅
        -- and p.1 ∪ p.2 = (q.1 \ {c}) ∪ {c} = q.1
        -- we have combinatorialSupport r ∩ q.1 ≠ ∅
        -- Since c ∉ combinatorialSupport r and c ∈ q.1,
        -- there must be some element in combinatorialSupport r ∩ (q.1 \ {c})
        -- This means combinatorialSupport r ⊆ q.1 and combinatorialSupport r ≠ {c}
        have hr_subset_q : combinatorialSupport r ⊆ combinatorialSupport q := hr_subset
        have hr_intersect_q1 : combinatorialSupport r ∩ q.1 ≠ ∅ := by
          have p_union_eq : p.1 ∪ p.2 = q.1 := by
            dsimp [p]
            rw [Finset.sdiff_union_of_subset]
            exact Finset.singleton_subset_iff.mpr hc_in_q1
          rwa [← p_union_eq]
        -- Use inclusion_q1orq2 to get either combinatorialSupport r ⊆ q.1 or r = q
        have hr_cases := inclusion_q1orq2 hr hq ⟨hr_neq, hr_subset⟩
        cases hr_cases with
        | inl hr_sub_q1 =>
          -- Case: combinatorialSupport r ⊆ q.1
          have hr_exists : ∃ s ∈ T.Branches, combinatorialSupport s = q.1 := by
            apply maximal_compact_inside_p1 hq
            exact ⟨r, hr, hr_sub_q1⟩
          obtain ⟨s, hs, hs_eq⟩ := hr_exists
          -- Now s has support exactly q.1, but q also has q.1 in its support
          -- This should lead to a contradiction with the tree structure
          -- Since s has support exactly q.1 and c ∈ q.1, we have c ∈ combinatorialSupport s
          have hc_in_s : c ∈ combinatorialSupport s := by
            rw [hs_eq]
            exact hc_in_q1
          -- But s ≠ q since they have different supports
          have hs_neq_q : s ≠ q := by
            intro h_eq
            rw [h_eq] at hs_eq
            -- This would mean combinatorialSupport q = q.1, contradicting
            -- support_not_subset_components
            have h_not_subset := support_not_subset_components hq
            exact h_not_subset.1 (Finset.subset_of_eq hs_eq)
          -- This contradicts the minimality of q
          have : combinatorialSupport s ⊆ combinatorialSupport q := by
            rw [hs_eq]
            dsimp [combinatorialSupport]
            exact Finset.subset_union_left
          exact hq_minimal ⟨s, hs, hs_neq_q, hc_in_s, this⟩
        | inr hr_sub_q2 =>
          -- Case: combinatorialSupport r ⊆ q.2
          -- Since c ∉ combinatorialSupport r and c ∈ q.1, we have combinatorialSupport r ⊆
          -- q.2
          -- But p.1 = q.1 \ {c} and p.2 = {c}, so combinatorialSupport r is disjoint from
          -- both p.1 and p.2
          -- This contradicts the fact that combinatorialSupport r ∩ (p.1 ∪ p.2) ≠ ∅
          exfalso
          have hr_disjoint_p2 : Disjoint (combinatorialSupport r) p.2 := by
            dsimp [p]
            -- Since c ∉ combinatorialSupport r and p.2 = {c}
            exact Finset.disjoint_singleton_right.mpr hc_r
          have hr_disjoint_p1 : Disjoint (combinatorialSupport r) p.1 := by
            dsimp [p]
            -- Since combinatorialSupport r ⊆ q.2 and p.1 = q.1 \ {c} ⊆ q.1,
            -- and q.1 and q.2 are disjoint, we have disjointness
            have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
            have hp1_sub_q1 : p.1 ⊆ q.1 := Finset.sdiff_subset
            exact Finset.disjoint_of_subset_left hr_sub_q2 (Finset.disjoint_of_subset_right
                hp1_sub_q1 hq_disj.symm)
          have hr_intersect_empty : combinatorialSupport r ∩ (p.1 ∪ p.2) = ∅ := by
            rw [Finset.inter_union_distrib_left]
            rw [Finset.disjoint_iff_inter_eq_empty.mp hr_disjoint_p1]
            rw [Finset.disjoint_iff_inter_eq_empty.mp hr_disjoint_p2]
            simp
          exact hr_intersect hr_intersect_empty
    have p1p2q:  p.1 ∪ p.2 ∈ pairToFinset q := by
      dsimp [pairToFinset, p]
      have h_union : (q.1 \ {c}) ∪ {c} = q.1 := by
        rw [Finset.sdiff_union_of_subset]
        exact Finset.singleton_subset_iff.mpr hc_in_q1
      rw [h_union]
      exact Finset.mem_insert_self q.1 {q.2}
    exact ⟨p1p2q, hfinal2⟩
  have h4 : ∀ p_elem ∈ pairs, Disjoint p_elem.1 p_elem.2 := by
    intro p_elem hp_elem_membership
    have hp_elem_eq : p_elem = p := Finset.eq_of_mem_singleton hp_elem_membership
    rw [hp_elem_eq]
    -- The goal is now to prove Disjoint p.1 p.2
    -- We know p := (q.1 \ {c}, {c})
    -- So the goal is Disjoint (q.1 \ {c}) {c}
    dsimp [p]
    exact (singleton_disjoint_sdiff q.1 c).symm
  have h6 : ∀ p_elem ∈ pairs, p_elem.1.Nonempty ∧ p_elem.2.Nonempty := by
    intro p_elem hp_elem_membership
    have hp_elem_eq : p_elem = p := Finset.eq_of_mem_singleton hp_elem_membership
    rw [hp_elem_eq]
    constructor
    · -- q.1 \ {c} is nonempty since q.1.card ≥ 2
      dsimp [p] -- Unfold p.1 to q.1 \ {c}
      have : (q.1 \ {c}).card = q.1.card - 1 := by
        rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hc_in_q1)]
        simp
      have card_pos : (q.1 \ {c}).card > 0 := by
        rw [this]
        have : q.1.card ≥ 2 := hq1_card_ge_2
        have : q.1.card - 1 ≥ 1 := Nat.sub_le_sub_right this 1
        simp at this
        linarith
      exact Finset.card_pos.mp card_pos
    · exact Finset.singleton_nonempty c
  have h8 : ∀ p_1 ∈ pairs, ∀ q_1 ∈ pairs, p_1 ≠ q_1 →
    (Disjoint (combinatorialSupport p_1) (combinatorialSupport q_1) ∨
    combinatorialSupport p_1 ⊆ q_1.1 ∨
    combinatorialSupport p_1 ⊆ q_1.2 ∨
    combinatorialSupport q_1 ⊆ p_1.1 ∨
    combinatorialSupport q_1 ⊆ p_1.2) := by
    intro p_1 hp_1 q_1 hq_1 hneq
    -- Since pairs = {p}, both p_1 and q_1 equal p
    have hp_1_eq : p_1 = p := Finset.eq_of_mem_singleton hp_1
    have hq_1_eq : q_1 = p := Finset.eq_of_mem_singleton hq_1
    rw [hp_1_eq, hq_1_eq] at hneq
    exact False.elim (hneq rfl)
  -- Apply create_new_tree
  obtain ⟨New_T, hNew_eq, hT_subset, hpairs_subset, hTops_subset⟩ :=
    create_new_tree T pairs h0 h1 h3 h4 h6 h8
  -- The new tree has measure strictly less than T
  use New_T, (hNew_eq.trans hT_eq)
  -- Show that (C \ New_T.Tops).card ≤ n
  have h_measure_decrease : (C \ New_T.Tops).card < (C \ T.Tops).card := by
    -- c ∈ New_T.Tops but c ∉ T.Tops
    have hc_in_new_tops : c ∈ New_T.Tops := by
      -- c appears as a singleton in the new pair p
      apply New_T.SingletonsAreTops p (hpairs_subset (Finset.mem_singleton_self p)) c
      dsimp [pairToFinset, p]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self {c})
    -- We have c ∈ C \ T.Tops (from hc) and c ∈ New_T.Tops (just proven)
    -- This means c ∈ C \ T.Tops but c ∉ C \ New_T.Tops
    -- So C \ New_T.Tops ⊂ C \ T.Tops (proper subset)
    have hc_not_in_new_diff : c ∉ C \ New_T.Tops := by
      intro h_contra
      have hc_not_in_new_tops : c ∉ New_T.Tops := (Finset.mem_sdiff.mp h_contra).2
      exact hc_not_in_new_tops hc_in_new_tops
    have hc_in_old_diff : c ∈ C \ T.Tops := hc
    -- Since c ∈ C \ T.Tops but c ∉ C \ New_T.Tops, we have a proper subset
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · -- C \ New_T.Tops ⊆ C \ T.Tops
      intro x hx_new
      have hx_in_C : x ∈ C := (Finset.mem_sdiff.mp hx_new).1
      have hx_not_new_tops : x ∉ New_T.Tops := (Finset.mem_sdiff.mp hx_new).2
      -- Since New_T.Tops = T.Tops ∪ tops and x ∉ New_T.Tops, we have x ∉ T.Tops
      have hx_not_old_tops : x ∉ T.Tops := by
        intro h_contra
        have hx_in_new_tops : x ∈ New_T.Tops := hTops_subset h_contra
        exact hx_not_new_tops hx_in_new_tops
      exact Finset.mem_sdiff.mpr ⟨hx_in_C, hx_not_old_tops⟩
    · -- C \ New_T.Tops ≠ C \ T.Tops
      intro h_eq
      have : c ∈ C \ New_T.Tops := by
        rw [h_eq]
        exact hc_in_old_diff
      exact hc_not_in_new_diff this
  have : (C \ New_T.Tops).card ≤ n := by
    have : (C \ New_T.Tops).card < (C \ T.Tops).card := h_measure_decrease
    have : (C \ T.Tops).card ≤ n + 1 := hT_measure
    linarith
  exact this

/-- The two-element finset of the freshly split pair is disjoint from the finset of every
existing branch. -/
lemma newPairRight_disjoint {α : Type*} [DecidableEq α]
    {T : BinaryTreeWithRootandTops α} {q : Finset α × Finset α} (hq : q ∈ T.Branches)
    {c : α}
    (hc_in_q2 : c ∈ q.2)
    (hq2_card_ge_2 : q.2.card ≥ 2)
    (hq_minimal : ¬∃ r ∈ T.Branches, r ≠ q ∧ c ∈ combinatorialSupport r ∧
      combinatorialSupport r ⊆ combinatorialSupport q) :
    ∀ b ∈ T.Branches, Disjoint (pairToFinset (({c}, q.2 \ {c}) : Finset α × Finset α))
      (pairToFinset b) := by
  let p : Finset α × Finset α := ({c}, q.2 \ {c})
  intro b hb
  by_cases hqb : q = b
  case pos =>
    -- Case q = b: this contradicts the fact that {p.1, p.2} is disjoint from {q.1, q.2}
    rw[hqb.symm]
    simp only [pairToFinset, Finset.disjoint_insert_right,
Finset.disjoint_singleton_right, Finset.mem_insert, Finset.mem_singleton, not_or]
    -- We have p.1 ∪ p.2 = q.2, so pairToFinset p contains q.2
    -- But pairToFinset b = pairToFinset q contains q.2 as well
    -- This means pairToFinset p and pairToFinset b are not disjoint
    have hp_union : p.1 ∪ p.2 = q.2 := by
     dsimp [p]
     simp [hc_in_q2]
    have hp1dq1: ¬ p.1= q.1 := by
      dsimp [p]
      intro h_eq
      -- We have p.1 = {c} and h_eq says {c} = q.1
      -- This would mean q.1 = {c}, but we know c ∈ q.2 and q.1 and q.2 are disjoint
      have hc_not_in_q1 : c ∉ q.1 := by
        have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
        exact Finset.disjoint_right.mp hq_disj hc_in_q2
      have hc_in_q1 : c ∈ q.1 := by
        rw [← h_eq]
        exact Finset.mem_singleton_self c
      exact hc_not_in_q1 hc_in_q1
    have hp2dq1: ¬ p.2= q.1 := by
      dsimp [p]
      intro h_eq
      -- We have p.2 = q.2 \ {c} and h_eq says q.2 \ {c} = q.1
      -- Since q.1 and q.2 are disjoint and q.1 is nonempty, we get a contradiction
      have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
      have hq1_nonempty : q.1.Nonempty := (T.NonemptyPairs q hq).1
      obtain ⟨x, hx⟩ := hq1_nonempty
      -- x ∈ q.1, but by h_eq, q.1 = q.2 \ {c} ⊆ q.2
      have hx_in_q2 : x ∈ q.2 := by
        rw [← h_eq] at hx
        exact Finset.mem_of_subset Finset.sdiff_subset hx
      -- This contradicts disjointness since x ∈ q.1 ∩ q.2
      exact Finset.disjoint_left.mp hq_disj hx hx_in_q2
    have hp1dq2: ¬ p.1= q.2 := by
      intro h_eq
      -- We have p.1 = {c} and h_eq says {c} = q.2
      -- This would mean q.2 = {c}, which contradicts hq2_card_ge_2
      rw [← h_eq] at hq2_card_ge_2
      have p1c: p.1={c} := by
        dsimp [p]
      rw [p1c] at hq2_card_ge_2
      simp only [Finset.card_singleton] at hq2_card_ge_2
      linarith
    have hp2dq2: ¬ p.2= q.2 := by
      dsimp [p]
      intro h_eq
      -- We have p.2 = q.2 \ {c} and h_eq says q.2 \ {c} = q.2
      -- This would mean c ∉ q.2, contradicting hc_in_q2
      have hc_not_in_q2 : c ∉ q.2 := by
        rw [← h_eq]
        simp [Finset.mem_sdiff]
      exact hc_not_in_q2 hc_in_q2
    have hne : (¬ q.1 = p.1 ∧ ¬ q.1 = p.2) ∧ ¬ q.2 = p.1 ∧ ¬ q.2 = p.2 := by
     refine ⟨⟨mt Eq.symm hp1dq1, mt Eq.symm hp2dq1⟩, mt Eq.symm hp1dq2, mt Eq.symm hp2dq2⟩
    exact hne
  case neg =>
    -- Case q ≠ b: use SupportProperty between q and b
    have h_support := T.SupportProperty q hq b hb hqb
    cases h_support with
    | inl hdisj =>
      -- Case: Disjoint (combinatorialSupport q) (combinatorialSupport b)
      -- Since combinatorialSupport p ⊆ combinatorialSupport q (as p.1 ∪ p.2 = q.2)
      -- and Disjoint (combinatorialSupport q) (combinatorialSupport b)
      -- we get Disjoint (combinatorialSupport p) (combinatorialSupport b)
      have hp_subset_q : combinatorialSupport p ⊆ combinatorialSupport q := by
        dsimp [combinatorialSupport, p]
        have h_union : {c} ∪ (q.2 \ {c}) = q.2 := by
          rw [Finset.union_sdiff_of_subset]
          exact Finset.singleton_subset_iff.mpr hc_in_q2
        simp only [Finset.insert_eq]
        rw [h_union]
        exact Finset.subset_union_right
      have hp_disj_b : Disjoint  (combinatorialSupport b) (combinatorialSupport p):=
        Finset.disjoint_of_subset_right hp_subset_q hdisj.symm
      have h_disj : Disjoint (pairToFinset b) (pairToFinset p) := by
        exact disjoint_suppport_pairfinset_disjoint hb hp_disj_b
      exact  h_disj.symm
    | inr hcases =>
      have disjp1p2: Disjoint p.1 p.2:= by
        dsimp [p]
        exact singleton_disjoint_sdiff q.2 c
      cases hcases with
      | inl hq_sub_b1 =>
        -- Case: combinatorialSupport q ⊆ b.1
        have hcpcb1: combinatorialSupport p ⊆ b.1 := by
          dsimp [combinatorialSupport, p]
          have h_union : {c} ∪ (q.2 \ {c}) = q.2 := by
            rw [Finset.union_sdiff_of_subset]
            exact Finset.singleton_subset_iff.mpr hc_in_q2
          simp only [Finset.insert_eq]
          rw [h_union]
          -- Now we need q.2 ⊆ b.1, which follows from hq_sub_b1
          dsimp [combinatorialSupport] at hq_sub_b1
          exact Finset.subset_union_right.trans hq_sub_b1
        have hnempty: p.1.Nonempty ∧ p.2.Nonempty := by
          constructor
          · exact Finset.singleton_nonempty c
          · -- q.2 \ {c} is nonempty since q.2.card ≥ 2
            dsimp [p]
            have : (q.2 \ {c}).card = q.2.card - 1 := by
               rw [Finset.card_sdiff]
               simp [hc_in_q2]
            have card_pos : (q.2 \ {c}).card > 0 := by
              rw [this]
              have : q.2.card ≥ 2 := hq2_card_ge_2
              have : q.2.card - 1 ≥ 1 := Nat.sub_le_sub_right this 1
              simp at this
              linarith
            exact Finset.card_pos.mp card_pos
        have h_disj : Disjoint (pairToFinset p) (pairToFinset b) := by
          apply suppp_p_incl_q1_disjoint_pairfinset hb hcpcb1 disjp1p2 hnempty
        exact h_disj
      | inr hrest =>
        cases hrest with
        | inl hq_sub_b2 =>
          -- Case: combinatorialSupport q ⊆ b.2
          have hcpcb2 : combinatorialSupport p ⊆ b.2 := by
              dsimp [combinatorialSupport, p]
              have h_union : {c} ∪ (q.2 \ {c}) = q.2 := by
                rw [Finset.union_sdiff_of_subset]
                exact Finset.singleton_subset_iff.mpr hc_in_q2
              dsimp [combinatorialSupport] at hq_sub_b2
              simpa [h_union, hc_in_q2] using
                ((Finset.subset_union_right : q.2 ⊆ q.1 ∪ q.2).trans hq_sub_b2)
          have hnempty: p.1.Nonempty ∧ p.2.Nonempty := by
            constructor
            · exact Finset.singleton_nonempty c
            · -- q.2 \ {c} is nonempty since q.2.card ≥ 2
              dsimp [p]
              have : (q.2 \ {c}).card = q.2.card - 1 := by
                rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr
                    hc_in_q2)]
                simp [Finset.card_singleton]
              have card_pos : (q.2 \ {c}).card > 0 := by
                rw [this]
                have : q.2.card ≥ 2 := hq2_card_ge_2
                have : q.2.card - 1 ≥ 1 := Nat.sub_le_sub_right this 1
                simp at this
                linarith
              exact Finset.card_pos.mp card_pos
          have h_disj : Disjoint (pairToFinset p) (pairToFinset b) := by
            apply suppp_p_incl_q2_disjoint_pairfinset hb hcpcb2 disjp1p2 hnempty
          exact h_disj
        | inr hfinal =>
          cases hfinal with
          | inl hb_sub_q1 =>
            -- Case: combinatorialSupport b ⊆ q.1
            have spsbdisj:   Disjoint (combinatorialSupport p)  (combinatorialSupport b)
                := by
              have hp_eq_q2 : combinatorialSupport p = q.2 := by
                 dsimp [combinatorialSupport, p]
                 simp [hc_in_q2]
              rw [hp_eq_q2]
              have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
              exact Finset.disjoint_of_subset_right hb_sub_q1 hq_disj.symm
            have h_disj : Disjoint  (pairToFinset b) (pairToFinset p) := by
             apply disjoint_suppport_pairfinset_disjoint hb spsbdisj.symm
            exact h_disj.symm
          | inr hb_sub_q2 =>
            -- Case: combinatorialSupport b ⊆ q.2
            -- maximal_compact_inside_p2
            exfalso
            have hr_exists : ∃ s ∈ T.Branches, combinatorialSupport s = q.2 := by
              apply maximal_compact_inside_p2 hq
              exact ⟨b, hb, hb_sub_q2⟩
            obtain ⟨s, hs, hs_eq⟩ := hr_exists
            -- Now s has support exactly q.2, but q also has q.2 in its support
            -- This should lead to a contradiction with the tree structure
            -- Since s has support exactly q.2 and c ∈ q.2, we have c ∈
            -- combinatorialSupport s
            have hc_in_s : c ∈ combinatorialSupport s := by
              rw [hs_eq]
              exact hc_in_q2
            -- But s ≠ q since they have different supports
            have hs_neq_q : s ≠ q := by
              intro h_eq
              rw [h_eq] at hs_eq
              -- This would mean combinatorialSupport q = q.2, contradicting
              -- support_not_subset_components
              have h_not_subset := support_not_subset_components hq
              exact h_not_subset.2 (Finset.subset_of_eq hs_eq)
            -- This contradicts the minimality of q
            have : combinatorialSupport s ⊆ combinatorialSupport q := by
              rw [hs_eq]
              dsimp [combinatorialSupport]
              exact Finset.subset_union_right
            exact hq_minimal ⟨s, hs, hs_neq_q, hc_in_s, this⟩

/-- Descent helper: builds a measure-decreasing tree when the chosen child lies in the
right component of the minimal branch. -/
lemma exists_tree_succ_measure_inRight {α : Type*} [DecidableEq α] {C : Finset α} {n : ℕ}
    {T : BinaryTreeWithRootandTops α} (hT_eq : T.Childs = C)
    (hT_measure : (C \ T.Tops).card ≤ n + 1)
    {c : α} (hc : c ∈ C \ T.Tops) (hc_not_tops : c ∉ T.Tops) (_hc_in_childs : c ∈ T.Childs)
    {q : Finset α × Finset α} (hq : q ∈ T.Branches) (_hc_in_q : c ∈ combinatorialSupport q)
    (hq_minimal : ¬∃ r ∈ T.Branches, r ≠ q ∧ c ∈ combinatorialSupport r ∧
      combinatorialSupport r ⊆ combinatorialSupport q)
    (_h_eq : ¬T.Tops = C)
    (hc_in_q2 : c ∈ q.2) :
    ∃ S : BinaryTreeWithRootandTops α, ∃ _ : S.Childs = C, (C \ S.Tops).card ≤ n := by
  classical
  -- Case: c ∈ q.2
  -- q.2 must have at least 2 elements since c is not a top
  have hq2_card_ge_2 : q.2.card ≥ 2 := by
    by_contra h_not
    push Not at h_not
    have hq2_card_lt_2 : q.2.card < 2 := h_not
    interval_cases h : (q.2.card)
    · -- q.2.card = 0, contradicts nonempty
      have hq2_nonempty : q.2.Nonempty := (T.NonemptyPairs q hq).2
      rw [Finset.card_eq_zero] at h
      rw [h] at hq2_nonempty
      exact Finset.not_nonempty_empty hq2_nonempty
    · -- q.2.card = 1, so q.2 = {c}
      have hq2_singleton : q.2 = {c} := by
        have hc_only : ∀ x ∈ q.2, x = c := by
          intro x hx
          have : q.2.card = 1 := h
          rw [Finset.card_eq_one] at this
          obtain ⟨y, hy⟩ := this
          rw [hy] at hx hc_in_q2
          exact (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hc_in_q2).symm
        exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hc_in_q2, hc_only⟩
      -- But then {c} ∈ pairToFinset q, so c ∈ T.Tops by SingletonsAreTops
      have hc_in_tops : c ∈ T.Tops := by
        apply T.SingletonsAreTops q hq c
        dsimp [pairToFinset]
        rw [hq2_singleton]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self {c})
      exact hc_not_tops hc_in_tops
  -- Since q.2.card ≥ 2, we can create a new pair p = (q.2 \ {c}, {c})
  let p : Finset α × Finset α := ({c}, q.2 \ {c})
  let pairs : Finset (Finset α × Finset α) := {p}
  -- Verify all conditions for create_new_tree
  have h0 : ∀ a ∈ pairs, ∀ b ∈ T.Branches, Disjoint (pairToFinset a) (pairToFinset b) := by
    intro a ha b hb
    rw [Finset.eq_of_mem_singleton ha]
    exact newPairRight_disjoint hq hc_in_q2 hq2_card_ge_2 hq_minimal b hb
  have h1 : ∀ p_1 ∈ pairs, ∀ q_1 ∈ pairs, (p_1 ≠ q_1) → Disjoint (pairToFinset p_1)
      (pairToFinset q_1) := by
    intro p_1 hp_1 q_1 hq_1 hneq
    -- Since pairs = {p}, both p_1 and q_1 equal p
    have hp_1_eq : p_1 = p := Finset.eq_of_mem_singleton hp_1
    have hq_1_eq : q_1 = p := Finset.eq_of_mem_singleton hq_1
    rw [hp_1_eq, hq_1_eq] at hneq
    exact False.elim (hneq rfl)
  have h3 : ∀ p_elem ∈ pairs, ∃ q_elem ∈ T.Branches, (p_elem.1 ∪ p_elem.2 ∈ pairToFinset
      q_elem) ∧ (¬ ∃ r ∈ T.Branches, (r ≠ q_elem) ∧ combinatorialSupport r ⊆
      combinatorialSupport q_elem∧ combinatorialSupport r ∩ (p_elem.1 ∪ p_elem.2) ≠ ∅) := by
    intro p_elem hp_elem
    have hp_elem_eq : p_elem = p := Finset.eq_of_mem_singleton hp_elem
    rw [hp_elem_eq]
    -- Now we need to show there exists q_elem ∈ T.Branches such that p.1 ∪ p.2 ∈
    -- pairToFinset q_elem
    -- and q_elem is minimal
    -- We have p = ({c}, q.2 \ {c}), so p.1 ∪ p.2 = {c} ∪ (q.2 \ {c}) = q.2
    use q, hq
    have hfinal: ¬∃ r ∈ T.Branches, r ≠ q ∧ c ∈ combinatorialSupport r ∧
        combinatorialSupport r ⊆  combinatorialSupport q :=by
      intro h
      obtain ⟨r, hr, hr_neq, hc_in_r, hr_subset⟩ := h
      -- Since r ≠ q and c ∈ combinatorialSupport r, we have r ≠ q
      have hr_contra: combinatorialSupport r ∩  (p.1 ∪ p.2)≠ ∅:= by
          have : c ∈ p.1 ∪ p.2 := by
            dsimp [p]
            exact Finset.mem_union_left (q.2 \ {c}) (Finset.mem_singleton_self c)
          have : c ∈ combinatorialSupport r ∩ (p.1 ∪ p.2) :=
            Finset.mem_inter.mpr ⟨hc_in_r, this⟩
          exact Finset.ne_empty_of_mem this
      exact hq_minimal ⟨r, hr, hr_neq, hc_in_r, hr_subset⟩
    have hfinal2: ¬∃ r ∈ T.Branches, r ≠ q ∧ combinatorialSupport r ⊆  combinatorialSupport
        q∧ combinatorialSupport r ∩(p.1 ∪ p.2)≠  ∅:= by
      intro ⟨r, hr, hr_neq, hr_subset, hr_intersect⟩
      -- Case analysis: either c ∈ combinatorialSupport r or c ∉ combinatorialSupport r
      by_cases hc_r : c ∈ combinatorialSupport r
      · -- Case: c ∈ combinatorialSupport r
        -- We need to show combinatorialSupport r ⊂ combinatorialSupport q
        exact hfinal ⟨r, hr, hr_neq, hc_r, hr_subset⟩
      · -- Case: c ∉ combinatorialSupport r
        -- Since hr_intersect: combinatorialSupport r ∩ (p.1 ∪ p.2) ≠ ∅
        -- and p.1 ∪ p.2 = {c} ∪ (q.2 \ {c}) = q.2
        -- we have combinatorialSupport r ∩ q.2 ≠ ∅
        -- Since c ∉ combinatorialSupport r and c ∈ q.2,
        -- there must be some element in combinatorialSupport r ∩ (q.2 \ {c})
        -- This means combinatorialSupport r ⊆ q.2 and combinatorialSupport r ≠ {c}
        have hr_subset_q : combinatorialSupport r ⊆ combinatorialSupport q := hr_subset
        have hr_intersect_q2 : combinatorialSupport r ∩ q.2 ≠ ∅ := by
          have p_union_eq : p.1 ∪ p.2 = q.2 := by
            dsimp [p]
            simp [hc_in_q2]
          rwa [← p_union_eq]
        -- Use inclusion_q1orq2 to get either combinatorialSupport r ⊆ q.1 or
        -- combinatorialSupport r ⊆ q.2
        have hr_cases := inclusion_q1orq2 hr hq ⟨hr_neq, hr_subset⟩
        cases hr_cases with
        | inl hr_sub_q1 =>
          -- Case: combinatorialSupport r ⊆ q.1
          -- Since c ∉ combinatorialSupport r and c ∈ q.2, we have combinatorialSupport r ⊆
          -- q.1
          -- But p.1 = {c} and p.2 = q.2 \ {c}, so combinatorialSupport r is disjoint from
          -- both p.1 and p.2
          -- This contradicts the fact that combinatorialSupport r ∩ (p.1 ∪ p.2) ≠ ∅
          exfalso
          have hr_disjoint_p1 : Disjoint (combinatorialSupport r) p.1 := by
            dsimp [p]
            -- Since c ∉ combinatorialSupport r and p.1 = {c}
            exact Finset.disjoint_singleton_right.mpr hc_r
          have hr_disjoint_p2 : Disjoint (combinatorialSupport r) p.2 := by
            dsimp [p]
            -- Since combinatorialSupport r ⊆ q.1 and p.2 = q.2 \ {c} ⊆ q.2,
            -- and q.1 and q.2 are disjoint, we have disjointness
            have hq_disj : Disjoint q.1 q.2 := T.DisjointComponents q hq
            have hp2_sub_q2 : p.2 ⊆ q.2 := Finset.sdiff_subset
            exact Finset.disjoint_of_subset_left hr_sub_q1 (Finset.disjoint_of_subset_right
                hp2_sub_q2 hq_disj)
          have hr_intersect_empty : combinatorialSupport r ∩ (p.1 ∪ p.2) = ∅ := by
            rw [Finset.inter_union_distrib_left]
            rw [Finset.disjoint_iff_inter_eq_empty.mp hr_disjoint_p1]
            rw [Finset.disjoint_iff_inter_eq_empty.mp hr_disjoint_p2]
            simp
          exact hr_intersect hr_intersect_empty
        | inr hr_sub_q2 =>
          -- Case: combinatorialSupport r ⊆ q.2
          have hr_exists : ∃ s ∈ T.Branches, combinatorialSupport s = q.2 := by
            apply maximal_compact_inside_p2 hq
            exact ⟨r, hr, hr_sub_q2⟩
          obtain ⟨s, hs, hs_eq⟩ := hr_exists
          -- Now s has support exactly q.2, but q also has q.2 in its support
          -- This should lead to a contradiction with the tree structure
          -- Since s has support exactly q.2 and c ∈ q.2, we have c ∈ combinatorialSupport s
          have hc_in_s : c ∈ combinatorialSupport s := by
            rw [hs_eq]
            exact hc_in_q2
          -- But s ≠ q since they have different supports
          have hs_neq_q : s ≠ q := by
            intro h_eq
            rw [h_eq] at hs_eq
            -- This would mean combinatorialSupport q = q.2, contradicting
            -- support_not_subset_components
            have h_not_subset := support_not_subset_components hq
            exact h_not_subset.2 (Finset.subset_of_eq hs_eq)
          -- This contradicts the minimality of q
          have : combinatorialSupport s ⊆ combinatorialSupport q := by
            rw [hs_eq]
            dsimp [combinatorialSupport]
            exact Finset.subset_union_right
          exact hq_minimal ⟨s, hs, hs_neq_q, hc_in_s, this⟩
    have p1p2q:  p.1 ∪ p.2 ∈ pairToFinset q := by
      dsimp [pairToFinset, p]
      rw [Finset.sdiff_singleton_eq_erase]
      rw [Finset.insert_erase hc_in_q2]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q.2)
    exact ⟨p1p2q, hfinal2⟩
  have h4 : ∀ p_elem ∈ pairs, Disjoint p_elem.1 p_elem.2 := by
    intro p_elem hp_elem_membership
    have hp_elem_eq : p_elem = p := Finset.eq_of_mem_singleton hp_elem_membership
    rw [hp_elem_eq]
    -- The goal is now to prove Disjoint p.1 p.2
    -- We know p := ({c}, q.2 \ {c})
    -- So the goal is Disjoint {c} (q.2 \ {c})
    dsimp [p]
    exact singleton_disjoint_sdiff q.2 c
  have h6 : ∀ p_elem ∈ pairs, p_elem.1.Nonempty ∧ p_elem.2.Nonempty := by
    intro p_elem hp_elem_membership
    have hp_elem_eq : p_elem = p := Finset.eq_of_mem_singleton hp_elem_membership
    rw [hp_elem_eq]
    constructor
    · exact Finset.singleton_nonempty c
    · -- q.2 \ {c} is nonempty since q.2.card ≥ 2
      dsimp [p] -- Unfold p.2 to q.2 \ {c}
      have : (q.2 \ {c}).card = q.2.card - 1 := by
        have hsubset : ({c} : Finset _) ⊆ q.2 :=
          Finset.singleton_subset_iff.mpr hc_in_q2
        have hcard : (q.2 \ {c}).card = q.2.card - ({c} : Finset _).card :=
            Finset.card_sdiff_of_subset hsubset
        simpa using hcard
      have card_pos : (q.2 \ {c}).card > 0 := by
        rw [this]
        have : q.2.card ≥ 2 := hq2_card_ge_2
        have : q.2.card - 1 ≥ 1 := Nat.sub_le_sub_right this 1
        simp at this
        linarith
      exact Finset.card_pos.mp card_pos
  have h8 : ∀ p_1 ∈ pairs, ∀ q_1 ∈ pairs, p_1 ≠ q_1 →
    (Disjoint (combinatorialSupport p_1) (combinatorialSupport q_1) ∨
    combinatorialSupport p_1 ⊆ q_1.1 ∨
    combinatorialSupport p_1 ⊆ q_1.2 ∨
    combinatorialSupport q_1 ⊆ p_1.1 ∨
    combinatorialSupport q_1 ⊆ p_1.2) := by
    intro p_1 hp_1 q_1 hq_1 hneq
    -- Since pairs = {p}, both p_1 and q_1 equal p
    have hp_1_eq : p_1 = p := Finset.eq_of_mem_singleton hp_1
    have hq_1_eq : q_1 = p := Finset.eq_of_mem_singleton hq_1
    rw [hp_1_eq, hq_1_eq] at hneq
    exact False.elim (hneq rfl)
  -- Apply create_new_tree
  obtain ⟨New_T, hNew_eq, hT_subset, hpairs_subset, hTops_subset⟩ :=
    create_new_tree T pairs h0 h1 h3 h4 h6 h8
  -- The new tree has measure strictly less than T
  use New_T, (hNew_eq.trans hT_eq)
  -- Show that (C \ New_T.Tops).card ≤ n
  have h_measure_decrease : (C \ New_T.Tops).card < (C \ T.Tops).card := by
    -- c ∈ New_T.Tops but c ∉ T.Tops
    have hc_in_new_tops : c ∈ New_T.Tops := by
      -- c appears as a singleton in the new pair p
      apply New_T.SingletonsAreTops p (hpairs_subset (Finset.mem_singleton_self p)) c
      dsimp [pairToFinset, p]
      exact Finset.mem_insert_self {c} {q.2 \ {c}}
    -- We have c ∈ C \ T.Tops (from hc) and c ∈ New_T.Tops (just proven)
    -- This means c ∈ C \ T.Tops but c ∉ C \ New_T.Tops
    -- So C \ New_T.Tops ⊂ C \ T.Tops (proper subset)
    have hc_not_in_new_diff : c ∉ C \ New_T.Tops := by
      intro h_contra
      have hc_not_in_new_tops : c ∉ New_T.Tops := (Finset.mem_sdiff.mp h_contra).2
      exact hc_not_in_new_tops hc_in_new_tops
    have hc_in_old_diff : c ∈ C \ T.Tops := hc
    -- Since c ∈ C \ T.Tops but c ∉ C \ New_T.Tops, we have a proper subset
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · -- C \ New_T.Tops ⊆ C \ T.Tops
      intro x hx_new
      have hx_in_C : x ∈ C := (Finset.mem_sdiff.mp hx_new).1
      have hx_not_new_tops : x ∉ New_T.Tops := (Finset.mem_sdiff.mp hx_new).2
      -- Since New_T.Tops = T.Tops ∪ tops and x ∉ New_T.Tops, we have x ∉ T.Tops
      have hx_not_old_tops : x ∉ T.Tops := by
        intro h_contra
        have hx_in_new_tops : x ∈ New_T.Tops := hTops_subset h_contra
        exact hx_not_new_tops hx_in_new_tops
      exact Finset.mem_sdiff.mpr ⟨hx_in_C, hx_not_old_tops⟩
    · -- C \ New_T.Tops ≠ C \ T.Tops
      intro h_eq
      have : c ∈ C \ New_T.Tops := by
        rw [h_eq]
        exact hc_in_old_diff
      exact hc_not_in_new_diff this
  have : (C \ New_T.Tops).card ≤ n := by
    have : (C \ New_T.Tops).card < (C \ T.Tops).card := h_measure_decrease
    have : (C \ T.Tops).card ≤ n + 1 := hT_measure
    linarith
  exact this


/-- Descent step: from a tree whose set of non-top children has cardinality at most `n + 1`,
build one whose non-top children set has cardinality at most `n`, by adjoining a new branch. -/
lemma exists_tree_succ_measure {α : Type*} [DecidableEq α] {C : Finset α}
    (n : ℕ)
    (h_n_plus_1 :
      ∃ S : BinaryTreeWithRootandTops α, ∃ _ : S.Childs = C, (C \ S.Tops).card ≤ n + 1) :
    ∃ S : BinaryTreeWithRootandTops α, ∃ _ : S.Childs = C, (C \ S.Tops).card ≤ n := by
  classical
  -- Obtain T from P(n+1)
  obtain ⟨T, hT_eq, hT_measure⟩ := h_n_plus_1
  -- Case analysis: if T.Tops = C, we're done
  by_cases h_eq : T.Tops = C
  case pos =>
    -- If T.Tops = C, then C \ T.Tops = ∅, so measure = 0 ≤ n
    use T, hT_eq
    rw [h_eq, Finset.sdiff_self, Finset.card_empty]
    exact Nat.zero_le n
  case neg =>
    -- If T.Tops ≠ C, we can create a new tree with a smaller measure
    -- Choose c ∈ C \ T.Tops
    have h_nonempty : (C \ T.Tops).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h_empty
      have h_subset : C ⊆ T.Tops := Finset.sdiff_eq_empty_iff_subset.mp h_empty
      -- We need T.Tops ⊆ C to get equality
      have h_tops_subset : T.Tops ⊆ C := by
        intro x hx
        -- All tops are elements that appear as singletons in some branch
        obtain ⟨q, hq, hq_singleton⟩ := T.TopsareTops x hx
        -- Since x appears as a singleton in branch q, and branches have support contained in
        -- Childs
        have x_in_support : x ∈ combinatorialSupport q := singleton_in_support q hq_singleton
        -- Every element in the support of a branch is in Childs
        have q_support_subset : combinatorialSupport q ⊆ T.Childs := by
          dsimp [combinatorialSupport]
          apply Finset.union_subset
          · exact (T.TreeStructureChilds q hq).1
          · exact (T.TreeStructureChilds q hq).2
        obtain ⟨r, hr, hr_support⟩ := T.EveryChildinaBranch x (q_support_subset x_in_support)
        have x_in_childs : x ∈ T.Childs := q_support_subset x_in_support
        rwa [hT_eq] at x_in_childs
      have : C = T.Tops := Finset.Subset.antisymm h_subset h_tops_subset
      exact h_eq this.symm
    obtain ⟨c, hc⟩ := h_nonempty
    -- c ∈ C \ T.Tops, so c ∈ C and c ∉ T.Tops
    have hc_in_C : c ∈ C := (Finset.mem_sdiff.mp hc).1
    have hc_not_tops : c ∉ T.Tops := (Finset.mem_sdiff.mp hc).2
    -- Since c ∈ C = T.Childs, there exists a branch containing c
    have hc_in_childs : c ∈ T.Childs := by rwa [hT_eq]
    obtain ⟨p, hp, hc_in_p⟩ := T.EveryChildinaBranch c hc_in_childs
    -- Find a minimal branch containing c (one with no proper subset branch also containing c)
    have h_exists_minimal : ∃ q ∈ T.Branches, c ∈ combinatorialSupport q ∧
    ¬∃ r ∈ T.Branches, r ≠ q ∧ c ∈ combinatorialSupport r ∧
    combinatorialSupport r ⊆  combinatorialSupport q := by
      -- Start with any branch containing c
      let S := T.Branches.filter (fun b => c ∈ combinatorialSupport b)
      have hS_nonempty : S.Nonempty := by
        use p
        exact Finset.mem_filter.mpr ⟨hp, hc_in_p⟩
      -- Find a branch with minimal support among those containing c
      obtain ⟨q, hq_in_S, hq_minimal⟩ := S.exists_min_image (fun b => (combinatorialSupport
          b).card) hS_nonempty
      have hq_in_branches : q ∈ T.Branches := (Finset.mem_filter.mp hq_in_S).1
      have hc_in_q : c ∈ combinatorialSupport q := (Finset.mem_filter.mp hq_in_S).2
      use q, hq_in_branches
      constructor
      · exact hc_in_q
      · intro ⟨r, hr_in_branches, hr_neq, hc_in_r, hr_subset⟩
        have hr_in_S : r ∈ S := Finset.mem_filter.mpr ⟨hr_in_branches, hc_in_r⟩
        have hr_card_ge : (combinatorialSupport q).card ≤ (combinatorialSupport r).card :=
          hq_minimal r hr_in_S
        have hr_card_lt : (combinatorialSupport r).card < (combinatorialSupport q).card := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_subset_ne]
          exact ⟨hr_subset, fun h => hr_neq (eq_iff_eq_support hr_in_branches hq_in_branches
              |>.mpr h)⟩
        exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hr_card_ge hr_card_lt)
    obtain ⟨q, hq, hc_in_q, hq_minimal⟩ := h_exists_minimal
    -- Case analysis: is c ∈ q.1 or c ∈ q.2?
    have hc_in_q_cases : c ∈ q.1 ∨ c ∈ q.2 := by
        dsimp [combinatorialSupport] at hc_in_q
        exact Finset.mem_union.mp hc_in_q
    cases hc_in_q_cases with
      | inl hc_in_q1 =>
        exact exists_tree_succ_measure_inLeft hT_eq hT_measure hc hc_not_tops hc_in_childs
          hq hc_in_q hq_minimal h_eq hc_in_q1
      | inr hc_in_q2 =>
        exact exists_tree_succ_measure_inRight hT_eq hT_measure hc hc_not_tops hc_in_childs
          hq hc_in_q hq_minimal h_eq hc_in_q2
theorem exists_tree_childs_eq_C_and_all_childs_in_Tops_of_card_ge_two
{α : Type*} [DecidableEq α] {C : Finset α} (hC : C.card ≥ 2) :
∃ T : BinaryTreeWithRootandTops α, T.Childs = C ∧ C = T.Tops := by
  classical
  let measure (S : BinaryTreeWithRootandTops α) (hT : S.Childs = C) := (C \ S.Tops).card
  /- Propriedade que queremos para cada `n` ≤ `S.card`. -/
  let P : ℕ → Prop := fun j ↦ ∃ S : BinaryTreeWithRootandTops α, ∃ hT : S.Childs = C, (C \
      S.Tops).card ≤  j
  /- Passo inicial da indução: `n = S.card` — basta o próprio `S`. -/
  have h_top : ∀ j ≥ C.card, P j := by
    intro j hj
    -- Primeiro obtemos uma árvore T com T.Childs = C
    obtain ⟨T, hT_eq⟩ := exists_binary_tree_with_childs_eq_C hC
    -- Para esta árvore, measure T hT_eq = (C \ T.Tops).card ≤ C.card ≤ j
    use T, hT_eq
    -- T.Tops ⊆ C porque todos os tops são elementos de Childs
    have gh: (C \ T.Tops) ⊆ C := Finset.sdiff_subset
    have h_card_le_C : (C \ T.Tops).card ≤ C.card := Finset.card_le_card gh
    exact Nat.le_trans h_card_le_C hj
  /- Passo recursivo: -/
  have h_step : ∀ n, (P (n + 1)) → P n := fun n h => exists_tree_succ_measure n h
  have h_zero : P 0 := by
    -- The set of all natural numbers where P n holds is nonempty
    have h_set_nonempty : ∃ n, P n := by
      -- By h_top, P n holds for all n ≥ C.card
      -- In particular, P C.card holds
      use C.card
      exact h_top C.card (le_refl C.card)
    -- Find the minimum m such that P m using Nat.find
    let m := Nat.find h_set_nonempty
    have hm_property : P m := Nat.find_spec h_set_nonempty
    have hm_minimal : ∀ k < m, ¬P k := fun k hk => Nat.find_min h_set_nonempty hk
    have hm: m=0:= by
      -- If m > 0, then P m would imply P 0 by the induction hypothesis
      -- But we have hm_minimal which says no k < m satisfies P k
      -- So m must be 0
      by_contra h_not_zero
      push Not at h_not_zero
      have h_m_gt_0 : m > 0 := Nat.lt_of_le_of_ne (Nat.zero_le m) h_not_zero.symm
      -- Since m > 0, we have m = (m-1) + 1
      have h_m_eq : m = (m - 1) + 1 := by
        rw [Nat.sub_add_cancel h_m_gt_0]
      -- Apply h_step to get P (m-1) from P m
      have h_pred : P (m - 1) := h_step (m - 1) (by
        rw [← h_m_eq]
        exact hm_property)
      -- This contradicts minimality since m-1 < m
      have h_lt : m - 1 < m := Nat.sub_lt h_m_gt_0 (by norm_num)
      exact hm_minimal (m - 1) h_lt h_pred
    rw [hm] at hm_property
    exact hm_property
  -- Use h_zero to conclude the goal
  obtain ⟨T, hT_eq, hT_measure⟩ := h_zero
  -- Since P 0 holds, we have a tree T with T.Childs = C and (C \ T.Tops).card ≤ 0
  -- This means (C \ T.Tops).card = 0, so C \ T.Tops = ∅
  have h_empty : C \ T.Tops = ∅ := by
    rw [← Finset.card_eq_zero]
    exact Nat.eq_zero_of_le_zero hT_measure
  -- Therefore C ⊆ T.Tops
  have h_subset : C ⊆ T.Tops := Finset.sdiff_eq_empty_iff_subset.mp h_empty
  -- We also need T.Tops ⊆ C
  have h_tops_subset : T.Tops ⊆ C := by
    intro x hx
    -- All tops are elements that appear as singletons in some branch
    obtain ⟨q, hq, hq_singleton⟩ := T.TopsareTops x hx
    -- Since x appears as a singleton in branch q, and branches have support contained in Childs
    have x_in_support : x ∈ combinatorialSupport q := singleton_in_support q hq_singleton
    -- Every element in the support of a branch is in Childs
    have q_support_subset : combinatorialSupport q ⊆ T.Childs := by
      dsimp [combinatorialSupport]
      apply Finset.union_subset
      · exact (T.TreeStructureChilds q hq).1
      · exact (T.TreeStructureChilds q hq).2
    have x_in_childs : x ∈ T.Childs := q_support_subset x_in_support
    rwa [hT_eq] at x_in_childs
  -- Therefore C = T.Tops
  have h_eq : C = T.Tops := Finset.Subset.antisymm h_subset h_tops_subset
  exact ⟨T, hT_eq, h_eq⟩




lemma exists_branch_support_eq_left_of_two_le_card
    {T : BinaryTreeWithRootandTops (Set α)}
    {p : Finset (Set α) × Finset (Set α)}
    (hp : p ∈ T.Branches)
    (hcard : 2 ≤ p.1.card)
    (childs_eq_tops : T.Childs = T.Tops) :
    ∃ q ∈ T.Branches, combinatorialSupport q = p.1 := by
  have hp1_pos : 0 < p.1.card := lt_of_lt_of_le (by decide : 0 < 2) hcard
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hp1_pos
  have hx_childs : x ∈ T.Childs := (T.TreeStructureChilds p hp).1 hx
  have hx_tops : x ∈ T.Tops := by simpa [childs_eq_tops] using hx_childs
  obtain ⟨q, hq, hx_singleton⟩ := T.TopsareTops x hx_tops
  have hx_in_qsupport : x ∈ combinatorialSupport q := singleton_in_support q hx_singleton
  have hq_ne_p : q ≠ p := by
    intro hqp
    subst hqp
    -- After `subst hqp` (hqp : q = p), p is replaced by q everywhere in context
    have hx_cases : ({x} : Finset (Set α)) = q.1 ∨ ({x} : Finset (Set α)) = q.2 := by
      dsimp [pairToFinset] at hx_singleton
      simpa [Finset.mem_insert, Finset.mem_singleton] using hx_singleton
    cases hx_cases with
    | inl hleft =>
        have hq1_card_one : q.1.card = 1 := by rw [← hleft]; simp
        linarith
    | inr hright =>
        have hx_in_q2 : x ∈ q.2 := by
          rw [← hright]
          exact Finset.mem_singleton_self x
        exact (Finset.disjoint_left.mp (T.DisjointComponents q hq) hx hx_in_q2).elim
  have hq_sub_p1 : combinatorialSupport q ⊆ p.1 := by
    have hcases := T.SupportProperty q hq p hp hq_ne_p
    cases hcases with
    | inl hdisj =>
        exfalso
        have hx_in_psupport : x ∈ combinatorialSupport p := Finset.mem_union_left p.2 hx
        exact Finset.disjoint_left.mp hdisj hx_in_qsupport hx_in_psupport
    | inr hrest =>
        cases hrest with
        | inl hq_sub_p1 =>
            exact hq_sub_p1
        | inr hrest2 =>
            cases hrest2 with
            | inl hq_sub_p2 =>
                exfalso
                have hx_in_p2 : x ∈ p.2 := hq_sub_p2 hx_in_qsupport
                exact Finset.disjoint_left.mp (T.DisjointComponents p hp) hx hx_in_p2
            | inr hrest3 =>
                cases hrest3 with
                | inl hp_sub_q1 =>
                    exfalso
                    have hx_in_psup : x ∈ combinatorialSupport p := Finset.mem_union_left p.2 hx
                    have hx_in_q1 : x ∈ q.1 := hp_sub_q1 hx_in_psup
                    have hx_cases2 : ({x} : Finset (Set α)) = q.1 ∨ ({x} : Finset (Set α)) = q.2 :=
                        by
                      dsimp [pairToFinset] at hx_singleton
                      simpa [Finset.mem_insert, Finset.mem_singleton] using hx_singleton
                    cases hx_cases2 with
                    | inl hxeqq1 =>
                        have hcard_q1 : q.1.card = 1 := by rw [← hxeqq1]; simp
                        have : p.1.card ≤ q.1.card :=
                          Finset.card_le_card (Finset.subset_union_left.trans hp_sub_q1)
                        linarith
                    | inr hxeqq2 =>
                        have hx_in_q2 : x ∈ q.2 := hxeqq2 ▸ Finset.mem_singleton_self x
                        exact absurd hx_in_q2 (Finset.disjoint_left.mp (T.DisjointComponents q hq)
                            hx_in_q1)
                | inr hp_sub_q2 =>
                    exfalso
                    have hx_in_psup : x ∈ combinatorialSupport p := Finset.mem_union_left p.2 hx
                    have hx_in_q2 : x ∈ q.2 := hp_sub_q2 hx_in_psup
                    have hx_cases2 : ({x} : Finset (Set α)) = q.1 ∨ ({x} : Finset (Set α)) = q.2 :=
                        by
                      dsimp [pairToFinset] at hx_singleton
                      simpa [Finset.mem_insert, Finset.mem_singleton] using hx_singleton
                    cases hx_cases2 with
                    | inl hxeqq1 =>
                        have hx_in_q1 : x ∈ q.1 := hxeqq1 ▸ Finset.mem_singleton_self x
                        exact absurd hx_in_q2 (Finset.disjoint_left.mp (T.DisjointComponents q hq)
                            hx_in_q1)
                    | inr hxeqq2 =>
                        have hcard_q2 : q.2.card = 1 := by rw [← hxeqq2]; simp
                        have : p.1.card ≤ q.2.card :=
                          Finset.card_le_card (Finset.subset_union_left.trans hp_sub_q2)
                        linarith
  exact maximal_compact_inside_p1 hp ⟨q, hq, hq_sub_p1⟩


lemma exists_branch_support_eq_right_of_two_le_card
    {T : BinaryTreeWithRootandTops (Set α)}
    {p : Finset (Set α) × Finset (Set α)}
    (hp : p ∈ T.Branches)
    (hcard : 2 ≤ p.2.card)
    (childs_eq_tops : T.Childs = T.Tops) :
    ∃ q ∈ T.Branches, combinatorialSupport q = p.2 := by
  have hp2_pos : 0 < p.2.card := lt_of_lt_of_le (by decide : 0 < 2) hcard
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hp2_pos
  have hx_childs : x ∈ T.Childs := (T.TreeStructureChilds p hp).2 hx
  have hx_tops : x ∈ T.Tops := by simpa [childs_eq_tops] using hx_childs
  obtain ⟨q, hq, hx_singleton⟩ := T.TopsareTops x hx_tops
  have hx_in_qsupport : x ∈ combinatorialSupport q := singleton_in_support q hx_singleton
  have hq_ne_p : q ≠ p := by
    intro hqp
    subst hqp
    have hx_cases : ({x} : Finset (Set α)) = q.1 ∨ ({x} : Finset (Set α)) = q.2 := by
      dsimp [pairToFinset] at hx_singleton
      simpa [Finset.mem_insert, Finset.mem_singleton] using hx_singleton
    cases hx_cases with
    | inl hleft =>
        have hx_in_q1 : x ∈ q.1 := hleft ▸ Finset.mem_singleton_self x
        exact absurd hx (Finset.disjoint_left.mp (T.DisjointComponents q hq) hx_in_q1)
    | inr hright =>
        have hq2_card_one : q.2.card = 1 := by rw [← hright]; simp
        linarith
  have hq_sub_p2 : combinatorialSupport q ⊆ p.2 := by
    have hcases := T.SupportProperty q hq p hp hq_ne_p
    cases hcases with
    | inl hdisj =>
        exfalso
        have hx_in_psupport : x ∈ combinatorialSupport p := Finset.mem_union_right p.1 hx
        exact Finset.disjoint_left.mp hdisj hx_in_qsupport hx_in_psupport
    | inr hrest =>
        cases hrest with
        | inl hq_sub_p1 =>
            exfalso
            have hx_in_p1 : x ∈ p.1 := hq_sub_p1 hx_in_qsupport
            exact absurd hx (Finset.disjoint_left.mp (T.DisjointComponents p hp) hx_in_p1)
        | inr hrest2 =>
            cases hrest2 with
            | inl hq_sub_p2 =>
                exact hq_sub_p2
            | inr hrest3 =>
                cases hrest3 with
                | inl hp_sub_q1 =>
                    exfalso
                    have hx_in_psup : x ∈ combinatorialSupport p := Finset.mem_union_right p.1 hx
                    have hx_in_q1 : x ∈ q.1 := hp_sub_q1 hx_in_psup
                    have hx_cases2 : ({x} : Finset (Set α)) = q.1 ∨ ({x} : Finset (Set α)) = q.2 :=
                        by
                      dsimp [pairToFinset] at hx_singleton
                      simpa [Finset.mem_insert, Finset.mem_singleton] using hx_singleton
                    cases hx_cases2 with
                    | inl hxeqq1 =>
                        have hcard_q1 : q.1.card = 1 := by rw [← hxeqq1]; simp
                        have : p.2.card ≤ q.1.card :=
                          Finset.card_le_card (Finset.subset_union_right.trans hp_sub_q1)
                        linarith
                    | inr hxeqq2 =>
                        have hx_in_q2 : x ∈ q.2 := hxeqq2 ▸ Finset.mem_singleton_self x
                        exact absurd hx_in_q2 (Finset.disjoint_left.mp (T.DisjointComponents q hq)
                            hx_in_q1)
                | inr hp_sub_q2 =>
                    exfalso
                    have hx_in_psup : x ∈ combinatorialSupport p := Finset.mem_union_right p.1 hx
                    have hx_in_q2 : x ∈ q.2 := hp_sub_q2 hx_in_psup
                    have hx_cases2 : ({x} : Finset (Set α)) = q.1 ∨ ({x} : Finset (Set α)) = q.2 :=
                        by
                      dsimp [pairToFinset] at hx_singleton
                      simpa [Finset.mem_insert, Finset.mem_singleton] using hx_singleton
                    cases hx_cases2 with
                    | inl hxeqq1 =>
                        have hx_in_q1 : x ∈ q.1 := hxeqq1 ▸ Finset.mem_singleton_self x
                        exact absurd hx_in_q2 (Finset.disjoint_left.mp (T.DisjointComponents q hq)
                            hx_in_q1)
                    | inr hxeqq2 =>
                        have hcard_q2 : q.2.card = 1 := by rw [← hxeqq2]; simp
                        have : p.2.card ≤ q.2.card :=
                          Finset.card_le_card (Finset.subset_union_right.trans hp_sub_q2)
                        linarith
  exact maximal_compact_inside_p2 hp ⟨q, hq, hq_sub_p2⟩

end LaminarFamiliesMaximalBinaryTrees
