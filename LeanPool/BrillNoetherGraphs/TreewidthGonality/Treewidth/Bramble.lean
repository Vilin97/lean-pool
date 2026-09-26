/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.TreeDecomposition

/-!
# Brambles and the bramble number

A **bramble** of a simple graph `H` is a collection of connected vertex sets
that pairwise *touch*: any two of them have connected union.  A **hitting set**
meets every member, and the **order** of the bramble is the least size of a
hitting set.  Seymour--Thomas duality says the largest order of a bramble is
`treewidth H + 1`; the half of that used here is proved in
`TreewidthGonality/Treewidth/SeymourThomas.lean`.

## Conventions

Connectivity of a vertex set is `(H.induce (↑S : Set V)).Connected`, as fixed in
the module docstring of `TreewidthGonality/Treewidth/TreeDecomposition.lean`.  Since
`SimpleGraph.Connected` bundles `Nonempty`, the `connected_mem` field already
forces every member of a bramble to be nonempty (`Bramble.nonempty_of_mem`), so
there is no separate nonemptiness field.

`order` is an `sInf` over `ℕ`; `hittingSetCards_nonempty` (all of `V` is a
hitting set) is what makes it meaningful rather than the `sInf ∅ = 0` default.
-/

@[expose] public section

namespace Utilities.Treewidth

open Finset

universe u

variable {V : Type u} [DecidableEq V] {H : SimpleGraph V}

/-- **First-crossing lemma.**  A walk that starts inside `S` and ends outside it
uses an edge from `S` to its complement.  This is the same induction as the
`private` `walk_has_edge_across_cut` of
`Utilities/Foundations/UnderlyingSimpleGraph.lean`, restated here (that one is
not exported) and used both by `Bramble.exists_inter_or_adj` and by
`TreewidthGonality/Gonality/BrambleGonality.lean`. -/
theorem exists_adj_across_of_walk {W : Type*} {K : SimpleGraph W} {a b : W}
    (S : Set W) (p : K.Walk a b) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ v ∈ S, ∃ w ∉ S, K.Adj v w := by
  induction p with
  | nil => exact (hb ha).elim
  | @cons u v w huv p ih =>
      by_cases hv : v ∈ S
      · exact ih hv hb
      · exact ⟨u, ha, v, hv, huv⟩

/-- A **bramble** of `H`: a finite family of vertex sets, each inducing a
connected subgraph, any two of which have connected union ("they touch").

Taking `B = B'` in `touching` recovers `connected_mem`, so the latter is
redundant; it is kept because it is the field consumers use and because it makes
the definition read the way the literature states it. -/
structure Bramble (H : SimpleGraph V) where
  /-- The members of the bramble. -/
  members : Finset (Finset V)
  /-- Each member induces a connected subgraph (in particular is nonempty). -/
  connected_mem : ∀ B ∈ members, (H.induce (↑B : Set V)).Connected
  /-- Any two members touch: their union induces a connected subgraph. -/
  touching : ∀ B ∈ members, ∀ B' ∈ members,
    (H.induce (↑(B ∪ B') : Set V)).Connected

namespace Bramble

variable (𝔅 : Bramble H)

/-- Members of a bramble are nonempty: `SimpleGraph.Connected` bundles
`Nonempty`. -/
theorem nonempty_of_mem {B : Finset V} (hB : B ∈ 𝔅.members) : B.Nonempty := by
  have h : Nonempty ↥(↑B : Set V) := (𝔅.connected_mem B hB).nonempty
  rw [Set.nonempty_coe_sort] at h
  exact Finset.coe_nonempty.mp h

/-- A **hitting set** of a bramble meets every member. -/
def IsHittingSet (S : Finset V) : Prop :=
  ∀ B ∈ 𝔅.members, (B ∩ S).Nonempty

/-- The sizes of the hitting sets of `𝔅`. -/
def hittingSetCards : Set ℕ :=
  {n : ℕ | ∃ S : Finset V, 𝔅.IsHittingSet S ∧ S.card = n}

/-- The **order** of a bramble: the least size of a hitting set. -/
noncomputable def order : ℕ :=
  sInf 𝔅.hittingSetCards

/-- Any hitting set bounds the order. -/
theorem order_le_card_of_isHittingSet {S : Finset V} (hS : 𝔅.IsHittingSet S) :
    𝔅.order ≤ S.card :=
  Nat.sInf_le ⟨S, hS, rfl⟩

/-- Restricting a bramble to a subfamily of its members is again a bramble. -/
def restrict (M : Finset (Finset V)) (hM : M ⊆ 𝔅.members) : Bramble H where
  members := M
  connected_mem := fun B hB => 𝔅.connected_mem B (hM hB)
  touching := fun B hB B' hB' => 𝔅.touching B (hM hB) B' (hM hB')

@[simp] theorem restrict_members (M : Finset (Finset V)) (hM : M ⊆ 𝔅.members) :
    (𝔅.restrict M hM).members = M := rfl

/-- Two members of a bramble either share a vertex or are joined by an edge.

This is the combinatorial content of `touching` and is what
`TreewidthGonality/Gonality/BrambleGonality.lean` consumes when it builds a hitting set
out of a cut.

Proved (2026-08-25): `touching B hB B' hB'` gives a walk inside `↑(B ∪ B')` from
a vertex of `B` to a vertex of `B'` (both are nonempty).  If `B ∩ B' = ∅` the
endpoint of that walk is outside the subtype-level set `{x | ↑x ∈ B}`, so
`exists_adj_across_of_walk` produces an edge of the induced graph with one end in
`B` and the other in `(B ∪ B') ∖ B = B' ∖ B`; `SimpleGraph.comap_adj` pushes it
back down to an edge of `H`. -/
theorem exists_inter_or_adj {B B' : Finset V} (hB : B ∈ 𝔅.members)
    (hB' : B' ∈ 𝔅.members) :
    (B ∩ B').Nonempty ∨ ∃ x ∈ B, ∃ y ∈ B', H.Adj x y := by
  classical
  by_cases hinter : (B ∩ B').Nonempty
  · exact Or.inl hinter
  refine Or.inr ?_
  rw [Finset.not_nonempty_iff_eq_empty] at hinter
  have hdisj : ∀ x : V, x ∈ B → x ∈ B' → False := by
    intro x hx hx'
    have hmem : x ∈ B ∩ B' := Finset.mem_inter.mpr ⟨hx, hx'⟩
    rw [hinter] at hmem
    exact absurd hmem (Finset.notMem_empty x)
  obtain ⟨b, hb⟩ := 𝔅.nonempty_of_mem hB
  obtain ⟨b', hb'⟩ := 𝔅.nonempty_of_mem hB'
  have hbs : b ∈ (↑(B ∪ B') : Set V) := by
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
    exact Or.inl hb
  have hb's : b' ∈ (↑(B ∪ B') : Set V) := by
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
    exact Or.inr hb'
  obtain ⟨p⟩ := (𝔅.touching B hB B' hB').preconnected ⟨b, hbs⟩ ⟨b', hb's⟩
  obtain ⟨x, hx, y, hy, hadj⟩ :=
    exists_adj_across_of_walk
      (S := {z : ↥(↑(B ∪ B') : Set V) | (↑z : V) ∈ B}) p
      (show b ∈ B from hb) (fun h => hdisj b' h hb')
  refine ⟨(↑x : V), hx, (↑y : V), ?_, hadj⟩
  have hyU : (↑y : V) ∈ B ∪ B' := by
    have hy2 := y.2
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hy2
    exact Finset.mem_union.mpr hy2
  rcases Finset.mem_union.mp hyU with h | h
  · exact absurd h hy
  · exact h

variable [Fintype V]

/-- All of `V` is a hitting set, because members are nonempty. -/
theorem isHittingSet_univ : 𝔅.IsHittingSet (Finset.univ : Finset V) := by
  intro B hB
  obtain ⟨x, hx⟩ := 𝔅.nonempty_of_mem hB
  exact ⟨x, Finset.mem_inter.mpr ⟨hx, Finset.mem_univ x⟩⟩

/-- Hitting sets exist, so `order` is an infimum over a nonempty set. -/
theorem hittingSetCards_nonempty : 𝔅.hittingSetCards.Nonempty :=
  ⟨(Finset.univ : Finset V).card, Finset.univ, 𝔅.isHittingSet_univ, rfl⟩

/-- The order is realized by an actual hitting set. -/
theorem exists_isHittingSet_card_eq_order :
    ∃ S : Finset V, 𝔅.IsHittingSet S ∧ S.card = 𝔅.order :=
  Nat.sInf_mem 𝔅.hittingSetCards_nonempty

/-- `order 𝔅 ≤ |V|`. -/
theorem order_le_card : 𝔅.order ≤ Fintype.card V := by
  simpa [Finset.card_univ] using 𝔅.order_le_card_of_isHittingSet 𝔅.isHittingSet_univ

omit [Fintype V] in
/-- **The form the main proof uses**: a set too small to be a hitting set misses
some member outright. -/
theorem exists_disjoint_of_card_lt_order {S : Finset V} (hS : S.card < 𝔅.order) :
    ∃ B ∈ 𝔅.members, B ∩ S = ∅ := by
  by_contra hcon
  push Not at hcon
  exact absurd (𝔅.order_le_card_of_isHittingSet hcon) (not_le.mpr hS)

/-- A bramble with at least one member has positive order. -/
theorem one_le_order (h : 𝔅.members.Nonempty) : 1 ≤ 𝔅.order := by
  obtain ⟨B, hB⟩ := h
  rcases Nat.eq_zero_or_pos 𝔅.order with h0 | hpos
  · obtain ⟨S, hS, hcard⟩ := 𝔅.exists_isHittingSet_card_eq_order
    rw [h0] at hcard
    obtain ⟨x, hx⟩ := hS B hB
    rw [Finset.card_eq_zero.mp hcard] at hx
    simp at hx
  · exact hpos

/-- **Monotonicity of the order under passing to a subfamily**: fewer members are
easier to hit. -/
theorem order_restrict_le (M : Finset (Finset V)) (hM : M ⊆ 𝔅.members) :
    (𝔅.restrict M hM).order ≤ 𝔅.order := by
  obtain ⟨S, hS, hcard⟩ := 𝔅.exists_isHittingSet_card_eq_order
  refine le_trans (order_le_card_of_isHittingSet _ ?_) (le_of_eq hcard)
  intro B hB
  exact hS B (hM hB)

end Bramble

end Utilities.Treewidth
