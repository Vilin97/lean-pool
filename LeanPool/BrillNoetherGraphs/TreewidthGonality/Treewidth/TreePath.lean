/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.PartialDecomposition

/-!
# Paths to a fixed node of a tree

Bellenbaum--Diestel's Lemma 1 is stated for an edge `t₁t₂` of the decomposition
tree and the two components of `T − t₁t₂`.  The Seymour--Thomas proof uses it
only in one shape: a node `t` lying on the tree path from a home node `t_x` to a
distinguished node `s`.  This module supplies exactly that shape, and nothing
else — in particular no edge deletion, no bridges, and no direct use of
acyclicity.

The cut argument follows from

  `Anc s a ⊆ (support of any walk a ⟶ b) ∪ Anc s b`,

which in turn is just uniqueness of paths in a tree applied to the concatenation
`(a ⟶ b) ++ (b ⟶ s)`.

`Anc hT s n` is the paper's `n T s`, the set of nodes on the tree path from `n`
to `s`.  The name is short for "ancestors": thinking of `s` as the root, it is
the set of ancestors of `n`, and `Below hT s t = {n | t ∈ Anc hT s n}` is the
subtree hanging below `t`.
-/

@[expose] public section

namespace Utilities.Treewidth

open SimpleGraph

universe v

variable {N : Type v} {T : SimpleGraph N}

/-- The unique path from `n` to `s` in a tree. -/
noncomputable def treePath (hT : T.IsTree) (n s : N) : T.Walk n s :=
  (hT.existsUnique_path n s).choose

theorem treePath_isPath (hT : T.IsTree) (n s : N) : (treePath hT n s).IsPath :=
  (hT.existsUnique_path n s).choose_spec.1

/-- Any path from `n` to `s` in a tree *is* `treePath`. -/
theorem eq_treePath (hT : T.IsTree) {n s : N} (p : T.Walk n s) (hp : p.IsPath) :
    p = treePath hT n s :=
  (hT.existsUnique_path n s).choose_spec.2 p hp

/-- **The paper's `n T s`**: the set of nodes on the tree path from `n` to `s`.
With `s` thought of as a root, this is the set of ancestors of `n`. -/
def Anc (hT : T.IsTree) (s n : N) : Set N :=
  {u | u ∈ (treePath hT n s).support}

/-- With `s` thought of as a root, the subtree hanging below `t`. -/
def Below (hT : T.IsTree) (s t : N) : Set N :=
  {n | t ∈ Anc hT s n}

theorem self_mem_anc (hT : T.IsTree) (s n : N) : n ∈ Anc hT s n :=
  (treePath hT n s).start_mem_support

theorem root_mem_anc (hT : T.IsTree) (s n : N) : s ∈ Anc hT s n :=
  (treePath hT n s).end_mem_support

/-- The path from the root to itself is trivial. -/
theorem anc_root (hT : T.IsTree) (s : N) : Anc hT s s = {s} := by
  have h : (SimpleGraph.Walk.nil : T.Walk s s) = treePath hT s s :=
    eq_treePath hT _ SimpleGraph.Walk.IsPath.nil
  ext u
  simp [Anc, ← h]

/-- Membership in `Below` is membership of the root's path set. -/
theorem mem_below_iff (hT : T.IsTree) (s t n : N) :
    n ∈ Below hT s t ↔ t ∈ Anc hT s n := Iff.rfl

/-- The root is below nothing but itself. -/
theorem root_notMem_below (hT : T.IsTree) {s t : N} (h : t ≠ s) :
    s ∉ Below hT s t := by
  intro hs
  have : t ∈ ({s} : Set N) := by rwa [← anc_root hT s]
  exact h this

/-- `Anc hT s n` is connected in the tree: it is the support of a walk. -/
theorem anc_connected (hT : T.IsTree) (s n : N) :
    (T.induce (Anc hT s n)).Connected :=
  (treePath hT n s).connected_induce_support

/-- **The cut inequality.**  The path from `a` to the root is contained in the
union of (the support of) any walk from `a` to `b` with the path from `b` to the
root.

Discharge plan: `(p.append (treePath hT b s)).toPath` is a path from `a` to `s`,
hence equals `treePath hT a s` by `eq_treePath`; then
`Walk.support_toPath_subset_support` and `Walk.support_append`. -/
theorem anc_subset_of_walk (hT : T.IsTree) (s : N) {a b : N} (p : T.Walk a b) :
    Anc hT s a ⊆ {x | x ∈ p.support} ∪ Anc hT s b := by
  classical
  intro u hu
  have hq : (((p.append (treePath hT b s)).toPath : T.Path a s) : T.Walk a s)
      = treePath hT a s :=
    eq_treePath hT _ (p.append (treePath hT b s)).toPath.2
  have hsub : (treePath hT a s).support ⊆ (p.append (treePath hT b s)).support := by
    rw [← hq]
    exact SimpleGraph.Walk.support_toPath_subset_support _
  have hmem := hsub hu
  rw [SimpleGraph.Walk.support_append, List.mem_append] at hmem
  rcases hmem with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_of_mem_tail h)

/-- **The cut lemma, in the only form the proof uses.**  A connected node set
meeting both `Below hT s t` and its complement contains `t`.

This replaces Bellenbaum--Diestel's "let `T₁` and `T₂` be the components of
`T − t₁t₂`" entirely.

Discharge plan: `hS.preconnected` gives a walk inside `S` from `a` to `b`; push
it down to `T` along `SimpleGraph.Embedding.induce`; apply
`anc_subset_of_walk`. -/
theorem mem_of_connected_cross (hT : T.IsTree) {s t : N} {S : Set N}
    (hS : (T.induce S).Connected) {a b : N} (ha : a ∈ S) (hb : b ∈ S)
    (hta : t ∈ Anc hT s a) (htb : t ∉ Anc hT s b) : t ∈ S := by
  classical
  obtain ⟨q⟩ := hS.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  have key : ∀ (u v : ↥S) (r : (T.induce S).Walk u v),
      ∀ x ∈ (r.map (SimpleGraph.Embedding.induce S).toHom).support, x ∈ S := by
    intro u v r x hx
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2
  rcases anc_subset_of_walk hT s
      (q.map (SimpleGraph.Embedding.induce S).toHom) hta with h | h
  · exact key _ _ q _ h
  · exact absurd h htb

/-- The dichotomy actually consumed by the separation lemma: a connected set of
nodes avoiding `t` lies entirely below `t` or entirely outside. -/
theorem subset_below_or_disjoint (hT : T.IsTree) {s t : N} {S : Set N}
    (hS : (T.induce S).Connected) (ht : t ∉ S) :
    S ⊆ Below hT s t ∨ Disjoint S (Below hT s t) := by
  by_cases h : ∃ a ∈ S, a ∈ Below hT s t
  · refine Or.inl fun b hbS => ?_
    obtain ⟨a, haS, haB⟩ := h
    by_contra hb
    exact ht (mem_of_connected_cross hT hS haS hbS haB hb)
  · refine Or.inr ?_
    push Not at h
    rw [Set.disjoint_left]
    exact h

end Utilities.Treewidth
