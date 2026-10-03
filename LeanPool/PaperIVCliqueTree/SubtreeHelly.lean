/-
Copyright (c) 2026 Juan Pablo Traverso Giannini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Giannini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Helly for connected vertex sets of a finite tree

The proof removes a leaf. Unless one member is that singleton, every member
survives removal; two members meeting only at the leaf also contain its neighbour.
-/

public section

namespace SimpleGraph

variable {N : Type*} {T : SimpleGraph N}

/-- Remove a vertex from a set, viewed in the remaining induced graph. -/
def prunedSet (S : Set N) (leaf : N) : Set ({leaf}ᶜ : Set N) :=
  {x | x.val ∈ S}

/-- A connected set containing a leaf and another vertex contains its neighbour. -/
theorem leaf_neighbor_mem {leaf neighbour : N}
    (hunique : ∀ x, T.Adj leaf x → x = neighbour)
    {S : Set N} (hS : (T.induce S).Connected) (hleaf : leaf ∈ S)
    (hother : ∃ x ∈ S, x ≠ leaf) : neighbour ∈ S := by
  obtain ⟨x, hx, hne⟩ := hother
  obtain ⟨p⟩ := hS.preconnected ⟨leaf, hleaf⟩ ⟨x, hx⟩
  have hp : ¬ p.Nil := p.not_nil_of_ne (by exact fun h => hne (Subtype.ext_iff.mp h).symm)
  have he : T.Adj leaf p.snd.val := p.adj_snd hp
  exact hunique _ he ▸ p.snd.property

/-- Removing a leaf preserves connectedness of every subtree that has another vertex. -/
theorem connected_prunedSet [Finite N] {leaf neighbour : N}
    (hadj : T.Adj leaf neighbour)
    (hunique : ∀ x, T.Adj leaf x → x = neighbour)
    {S : Set N} (hS : (T.induce S).Connected)
    (hother : ∃ x ∈ S, x ≠ leaf) :
    ((T.induce ({leaf}ᶜ : Set N)).induce (prunedSet S leaf)).Connected := by
  classical
  let _ := Fintype.ofFinite N
  by_cases hl : leaf ∈ S
  · have hn : neighbour ∈ S := leaf_neighbor_mem hunique hS hl hother
    have hd : (T.induce S).degree ⟨leaf, hl⟩ = 1 := by
      rw [degree_eq_one_iff_existsUnique_adj]
      exact ⟨⟨neighbour, hn⟩, hadj, fun x hx => Subtype.ext (hunique x.val hx)⟩
    have hc := hS.induce_compl_singleton_of_degree_eq_one hd
    let f : ((T.induce S).induce ({(⟨leaf, hl⟩ : S)}ᶜ : Set S)) →g
        ((T.induce ({leaf}ᶜ : Set N)).induce (prunedSet S leaf)) := {
      toFun := fun x => ⟨⟨x.val.val, by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Subtype.ext_iff] using x.property⟩,
        x.val.property⟩
      map_rel' := fun h => h }
    exact hc.map f (by
      rintro ⟨⟨x, hx⟩, hs⟩
      refine ⟨⟨⟨x, hs⟩, ?_⟩, rfl⟩
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Subtype.ext_iff] using hx)
  · let f : (T.induce S) →g
        ((T.induce ({leaf}ᶜ : Set N)).induce (prunedSet S leaf)) := {
      toFun := fun x => ⟨⟨x.val, by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact fun h => hl (h ▸ x.property)⟩, x.property⟩
      map_rel' := fun h => h }
    exact hS.map f (by rintro ⟨⟨x, hx⟩, hs⟩; exact ⟨⟨x, hs⟩, rfl⟩)

/-- Pruning a leaf preserves intersection when both subtrees have another vertex. -/
theorem prunedSet_inter_nonempty_iff {leaf neighbour : N}
    (hadj : T.Adj leaf neighbour) (hunique : ∀ x, T.Adj leaf x → x = neighbour)
    {S R : Set N} (hS : (T.induce S).Connected) (hR : (T.induce R).Connected)
    (hSother : ∃ x ∈ S, x ≠ leaf) (hRother : ∃ x ∈ R, x ≠ leaf) :
    (prunedSet S leaf ∩ prunedSet R leaf).Nonempty ↔ (S ∩ R).Nonempty := by
  constructor
  · rintro ⟨x, hxS, hxR⟩
    exact ⟨x.val, hxS, hxR⟩
  · rintro ⟨x, hxS, hxR⟩
    by_cases hx : x = leaf
    · subst x
      refine ⟨⟨neighbour, ?_⟩, leaf_neighbor_mem hunique hS hxS hSother,
        leaf_neighbor_mem hunique hR hxR hRother⟩
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hadj.ne.symm
    · exact ⟨⟨x, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx⟩,
        hxS, hxR⟩

/-- A set with no vertex other than the designated leaf is contained in that singleton. -/
theorem eq_leaf_of_no_other {S : Set N} {leaf x : N}
    (hother : ¬ ∃ y ∈ S, y ≠ leaf) (hx : x ∈ S) : x = leaf := by
  by_contra hne
  exact hother ⟨x, hx, hne⟩

/-- The common smaller-host step: pruning preserves the tree, subtrees and intersections. -/
theorem IsTree.prune_subtree_family [Fintype N] [DecidableEq N] (hT : T.IsTree)
    {leaf neighbour : N} (hadj : T.Adj leaf neighbour)
    (hunique : ∀ x, T.Adj leaf x → x = neighbour)
    {I : Type*} (F : Finset I) (S : I → Set N)
    (hc : ∀ i ∈ F, (T.induce (S i)).Connected)
    (hother : ∀ i ∈ F, ∃ x ∈ S i, x ≠ leaf) :
    Fintype.card ({leaf}ᶜ : Set N) < Fintype.card N ∧
      (T.induce ({leaf}ᶜ : Set N)).IsTree ∧
      (∀ i ∈ F, ((T.induce ({leaf}ᶜ : Set N)).induce (prunedSet (S i) leaf)).Connected) ∧
      (∀ i ∈ F, ∀ j ∈ F,
        (prunedSet (S i) leaf ∩ prunedSet (S j) leaf).Nonempty ↔
          (S i ∩ S j).Nonempty) := by
  classical
  have hd : T.degree leaf = 1 :=
    degree_eq_one_iff_existsUnique_adj.mpr ⟨neighbour, hadj, hunique⟩
  refine ⟨Fintype.card_subtype_lt (by simp : leaf ∉ ({leaf}ᶜ : Set N)),
    ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hd, hT.isAcyclic.induce _⟩,
    fun i hi => connected_prunedSet hadj hunique (hc i hi) (hother i hi), ?_⟩
  intro i hi j hj
  exact prunedSet_inter_nonempty_iff hadj hunique (hc i hi) (hc j hj)
    (hother i hi) (hother j hj)

private theorem subtree_helly_of_singleton {I : Type*} {F : Finset I}
    {S : I → Set N} {leaf : N}
    (hsingle : ∃ i ∈ F, ¬ ∃ x ∈ S i, x ≠ leaf)
    (hinter : ∀ i ∈ F, ∀ j ∈ F, (S i ∩ S j).Nonempty) :
    ∀ j ∈ F, leaf ∈ S j := by
  obtain ⟨i, hi, hs⟩ := hsingle
  intro j hj
  obtain ⟨x, hxi, hxj⟩ := hinter i hi j hj
  exact eq_leaf_of_no_other hs hxi ▸ hxj

private theorem subtree_helly_aux : ∀ n : ℕ,
    ∀ {N : Type*} [Fintype N] (T : SimpleGraph N), Fintype.card N = n → T.IsTree →
    ∀ {I : Type*} (F : Finset I) (S : I → Set N),
      (∀ i ∈ F, (T.induce (S i)).Connected) →
      (∀ i ∈ F, ∀ j ∈ F, (S i ∩ S j).Nonempty) →
      ∃ x, ∀ i ∈ F, x ∈ S i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N _ T hcard hT I F S hconnected hinter
    classical
    rcases subsingleton_or_nontrivial N with hsmall | hlarge
    · let _ := hsmall
      obtain ⟨x⟩ := hT.connected.nonempty
      refine ⟨x, fun i hi => ?_⟩
      obtain ⟨y⟩ := (hconnected i hi).nonempty
      exact Subsingleton.elim y.val x ▸ y.property
    · let _ := hlarge
      obtain ⟨leaf, hdegree⟩ := hT.exists_vert_degree_one_of_nontrivial
      obtain ⟨neighbour, hadj, hunique⟩ := degree_eq_one_iff_existsUnique_adj.mp hdegree
      by_cases hsingle : ∃ i ∈ F, ¬ ∃ x ∈ S i, x ≠ leaf
      · exact ⟨leaf, subtree_helly_of_singleton hsingle hinter⟩
      · have hother : ∀ i ∈ F, ∃ x ∈ S i, x ≠ leaf := by
          intro i hi
          by_contra h
          exact hsingle ⟨i, hi, h⟩
        obtain ⟨hlt, ht, hc, hp⟩ :=
          hT.prune_subtree_family hadj hunique F S hconnected hother
        obtain ⟨x, hx⟩ := ih _ (hlt.trans_eq hcard) (T.induce ({leaf}ᶜ : Set N)) rfl ht F
          (fun i => prunedSet (S i) leaf) hc
          (fun i hi j hj => (hp i hi j hj).mpr (hinter i hi j hj))
        exact ⟨x.val, hx⟩

/-- A finite pairwise-intersecting family of nonempty subtrees has a common vertex. -/
theorem IsTree.finite_subtree_helly [Finite N] (hT : T.IsTree)
    {I : Type*} (F : Finset I) (S : I → Set N)
    (hconnected : ∀ i ∈ F, (T.induce (S i)).Connected)
    (hinter : ∀ i ∈ F, ∀ j ∈ F, (S i ∩ S j).Nonempty) :
    ∃ x, ∀ i ∈ F, x ∈ S i := by
  let _ := Fintype.ofFinite N
  exact subtree_helly_aux (Fintype.card N) T rfl hT F S hconnected hinter

end SimpleGraph
