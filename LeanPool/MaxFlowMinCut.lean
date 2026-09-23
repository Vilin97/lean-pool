/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Chain
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Finite max-flow / min-cut

Source: url:https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/b3423f3e8c8db7c2d1b279673293ef3079faf903/preprints/PAPER_III/05_formalization/lean_v1.4_freeze/Contrib/MaxFlowMinCut.lean
Authors: Juan Pablo Traverso Gianini, Aristotle
Status: verified
Main declarations: `Contrib.MaxFlowMinCut.maxflow_eq_mincut`
Tags: combinatorial-optimization, graph-theory, network-flows
MSC: 05C21, 90C35
-/

/-!
# Finite max-flow / min-cut

A self-contained, Mathlib-only development of the finite max-flow / min-cut theorem for a
network with real, nonnegative capacities on a finite node type.

Contents:

* `Network`, `Flow`, `Flow.value`, `Cut`, `Cut.capacity` — the basic objects.
* `Flow.value_eq_flow_across` — the cut-flow identity.
* `value_le_capacity` — weak duality: every flow value is at most every cut capacity.
* `exists_nodup_chain` — from a reflexive-transitive-closure path between distinct points one can
  extract a duplicate-free chain (simple path).
* `pairs`, `pairs_antisymm`, `pairs_rel`, `degree_balance` — edge-set combinatorics of a simple
  path: no 2-cycles, consecutive nodes are related, and the unit degree balance.
* `max_flow_exists` — a maximum-value flow exists (the flow polytope is compact and `value` is
  continuous).
* `augEdges_exists`, `t_not_reachable_of_max` — the augmenting-path step.
* `maxflow_eq_mincut` — strong duality: there is a flow and an s–t cut of equal value.

The development is `sorry`-free and uses only the standard axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/

@[expose] public section

namespace Contrib.MaxFlowMinCut

/-! ## Duplicate-free chains from reflexive-transitive-closure paths -/

section NodupChain

open List

/-- If `x` occurs at least twice in `l`, split `l` around the two occurrences. -/
private theorem dup_decomp {α : Type*} {x : α} {l : List α}
    (h : List.Duplicate x l) : ∃ A B C, l = A ++ x :: (B ++ x :: C) := by
  induction h with
  | @cons_mem l hx =>
      obtain ⟨B, C, rfl⟩ := List.append_of_mem hx
      exact ⟨[], B, C, rfl⟩
  | @cons_duplicate y l hd ih =>
      obtain ⟨A, B, C, rfl⟩ := ih
      exact ⟨y :: A, B, C, rfl⟩

/-- Splicing out the loop between two occurrences of `x` preserves the chain property. -/
private theorem chain_splice {α : Type*} {R : α → α → Prop} {x : α} {A B C : List α}
    (h : List.IsChain R (A ++ x :: (B ++ x :: C))) : List.IsChain R (A ++ x :: C) := by
  rw [isChain_split] at h ⊢
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rw [← cons_append, isChain_split] at h2
  exact h2.2

/-- Core strong-induction lemma: any nonempty chain list has a `Nodup` chain sublist with the
same first and last elements. -/
private theorem nodup_chain_core {α : Type*} {R : α → α → Prop} :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → l ≠ [] → l.IsChain R →
      ∃ l', l' ≠ [] ∧ l'.IsChain R ∧ l'.head? = l.head? ∧ l'.getLast? = l.getLast? ∧ l'.Nodup := by
  intro n
  induction n with
  | zero =>
      intro l hlen hne _
      exact absurd (List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)) hne
  | succ n ih =>
      intro l hlen hne hchain
      by_cases hnd : l.Nodup
      · exact ⟨l, hne, hchain, rfl, rfl, hnd⟩
      · obtain ⟨x, hx⟩ := (exists_duplicate_iff_not_nodup).mpr hnd
        obtain ⟨A, B, C, rfl⟩ := dup_decomp hx
        -- The spliced list `A ++ x :: C`.
        have hchain' : List.IsChain R (A ++ x :: C) := chain_splice hchain
        have hne' : (A ++ x :: C) ≠ [] := by cases A <;> simp
        -- head? is preserved.
        have hhead : (A ++ x :: C).head? = (A ++ x :: (B ++ x :: C)).head? := by
          cases A <;> rfl
        -- getLast? is preserved: both equal `getLast? (x :: C)`.
        have hlast : (A ++ x :: C).getLast? = (A ++ x :: (B ++ x :: C)).getLast? := by
          have e1 : (A ++ x :: C).getLast? = (x :: C).getLast? := getLast?_append_cons A x C
          have e2 : (A ++ x :: (B ++ x :: C)).getLast? = (x :: C).getLast? := by
            rw [getLast?_append_cons]
            rw [show (x :: (B ++ x :: C)) = (x :: B) ++ x :: C from by rw [cons_append]]
            rw [getLast?_append_cons]
          rw [e1, e2]
        -- length strictly decreased, so ≤ n.
        have hlen' : (A ++ x :: C).length ≤ n := by
          simp only [List.length_append, List.length_cons] at hlen ⊢
          omega
        obtain ⟨l', hl'ne, hl'chain, hl'head, hl'last, hl'nodup⟩ := ih _ hlen' hne' hchain'
        exact ⟨l', hl'ne, hl'chain, hl'head.trans hhead, hl'last.trans hlast, hl'nodup⟩

/-- From a reflexive-transitive-closure path between two DISTINCT points, extract a simple
(duplicate-free) chain list from `s` to `t`. -/
theorem exists_nodup_chain {α : Type*} {R : α → α → Prop} {s t : α}
    (h : Relation.ReflTransGen R s t) (_hst : s ≠ t) :
    ∃ l : List α, l.IsChain R ∧ l.head? = some s ∧ l.getLast? = some t ∧ l.Nodup := by
  obtain ⟨l, hlne, hlchain, hlhead, hllast⟩ :=
    List.exists_isChain_ne_nil_of_relationReflTransGen h
  obtain ⟨l', _, hl'chain, hl'head, hl'last, hl'nodup⟩ :=
    nodup_chain_core l.length l le_rfl hlne hlchain
  refine ⟨l', hl'chain, ?_, ?_, hl'nodup⟩
  · rw [hl'head, List.head?_eq_some_head hlne, hlhead]
  · rw [hl'last, List.getLast?_eq_some_getLast hlne, hllast]

end NodupChain

/-! ## Edge sets of simple paths and their degree balance -/

section PathBalance

open Finset

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The set of consecutive directed pairs (edges) of a list. -/
def pairs (l : List N) : Finset (N × N) := (l.zip l.tail).toFinset

omit [Fintype N] in
/-- Master characterization of edge membership via `getElem?` indices. -/
private theorem mem_pairs_iff' (l : List N) {u v : N} :
    (u, v) ∈ pairs l ↔ ∃ i : ℕ, l[i]? = some u ∧ l[i + 1]? = some v := by
  unfold pairs
  rw [List.mem_toFinset, List.mem_iff_getElem?]
  constructor
  · rintro ⟨i, hi⟩
    rw [List.getElem?_zip_eq_some] at hi
    obtain ⟨h1, h2⟩ := hi
    exact ⟨i, h1, by rw [List.getElem?_tail] at h2; exact h2⟩
  · rintro ⟨i, h1, h2⟩
    refine ⟨i, ?_⟩
    rw [List.getElem?_zip_eq_some]
    exact ⟨h1, by rw [List.getElem?_tail]; exact h2⟩

omit [Fintype N] in
/-- Membership in `pairs` means the two nodes are consecutive. -/
theorem mem_pairs_iff (l : List N) {u v : N} :
    (u, v) ∈ pairs l ↔ (u, v) ∈ l.zip l.tail := by
  unfold pairs
  rw [List.mem_toFinset]

omit [Fintype N] in
/-- In a duplicate-free list, no directed edge and its reverse both occur (no 2-cycle). -/
theorem pairs_antisymm (l : List N) (hnd : l.Nodup) {u v : N}
    (h : (u, v) ∈ pairs l) : (v, u) ∉ pairs l := by
  rw [mem_pairs_iff'] at h
  rw [mem_pairs_iff']
  rintro ⟨j, hj1, hj2⟩
  obtain ⟨i, hi1, hi2⟩ := h
  rw [List.getElem?_eq_some_iff] at hi1 hi2 hj1 hj2
  obtain ⟨hib, hie⟩ := hi1
  obtain ⟨hib2, hie2⟩ := hi2
  obtain ⟨hjb, hje⟩ := hj1
  obtain ⟨hjb2, hje2⟩ := hj2
  -- l[i] = u, l[i+1] = v, l[j] = v, l[j+1] = u
  -- from l[i+1] = v = l[j]: i+1 = j; from l[j+1] = u = l[i]: j+1 = i
  have e1 : i + 1 = j := hnd.getElem_inj_iff.mp (by rw [hie2, hje])
  have e2 : j + 1 = i := hnd.getElem_inj_iff.mp (by rw [hje2, hie])
  omega

omit [Fintype N] in
/-- An edge of `pairs l` relates its endpoints under any relation the list is a chain for. -/
theorem pairs_rel {R : N → N → Prop} (l : List N) (hc : l.IsChain R)
    {u v : N} (h : (u, v) ∈ pairs l) : R u v := by
  rw [mem_pairs_iff'] at h
  obtain ⟨i, h1, h2⟩ := h
  rw [List.getElem?_eq_some_iff] at h1 h2
  obtain ⟨hib, hie⟩ := h1
  obtain ⟨hib2, hie2⟩ := h2
  have := List.isChain_iff_getElem.mp hc i hib2
  rw [hie, hie2] at this
  exact this

/-- Out-neighbour predicate: `u` sits at a non-final position. -/
def POut (l : List N) (u : N) : Prop := ∃ i : ℕ, i + 1 < l.length ∧ l[i]? = some u
/-- In-neighbour predicate: `u` sits at a non-initial position. -/
def PIn (l : List N) (u : N) : Prop := ∃ i : ℕ, i + 1 < l.length ∧ l[i + 1]? = some u

instance (l : List N) (u : N) : Decidable (POut l u) :=
  decidable_of_iff (∃ i ∈ Finset.range l.length, i + 1 < l.length ∧ l[i]? = some u) (by
    unfold POut; simp only [Finset.mem_range]
    exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h1, h2⟩ => ⟨i, by omega, h1, h2⟩⟩)
instance (l : List N) (u : N) : Decidable (PIn l u) :=
  decidable_of_iff (∃ i ∈ Finset.range l.length, i + 1 < l.length ∧ l[i + 1]? = some u) (by
    unfold PIn; simp only [Finset.mem_range]
    exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h1, h2⟩ => ⟨i, by omega, h1, h2⟩⟩)

private theorem out_card (l : List N) (hnd : l.Nodup) (u : N) :
    (univ.filter (fun v => (u, v) ∈ pairs l)).card = if POut l u then 1 else 0 := by
  by_cases hP : POut l u
  · rw [ite_eq_left hP]
    obtain ⟨i, hilt, hiu⟩ := hP
    have hi1 : i + 1 < l.length := hilt
    -- successor value
    set v0 := l[i + 1] with hv0
    rw [Finset.card_eq_one]
    refine ⟨v0, ?_⟩
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [mem_pairs_iff']
      exact ⟨i, hiu, by rw [List.getElem?_eq_some_iff]; exact ⟨hi1, rfl⟩⟩
    · intro v hv
      rw [Finset.mem_filter, mem_pairs_iff'] at hv
      obtain ⟨_, j, hj1, hj2⟩ := hv
      rw [List.getElem?_eq_some_iff] at hiu hj1
      obtain ⟨hib, hie⟩ := hiu
      obtain ⟨hjb, hje⟩ := hj1
      have : j = i := hnd.getElem_inj_iff.mp (by rw [hje, hie])
      subst this
      rw [List.getElem?_eq_some_iff] at hj2
      obtain ⟨_, hjv⟩ := hj2
      rw [hv0, ← hjv]
  · rw [ite_eq_right hP]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _
    rw [mem_pairs_iff']
    rintro ⟨i, hiu, hiv⟩
    apply hP
    rw [List.getElem?_eq_some_iff] at hiv
    obtain ⟨hib, _⟩ := hiv
    exact ⟨i, hib, hiu⟩

private theorem in_card (l : List N) (hnd : l.Nodup) (u : N) :
    (univ.filter (fun v => (v, u) ∈ pairs l)).card = if PIn l u then 1 else 0 := by
  by_cases hP : PIn l u
  · rw [ite_eq_left hP]
    obtain ⟨i, hilt, hiu⟩ := hP
    have hi0 : i < l.length := by omega
    set v0 := l[i] with hv0
    rw [Finset.card_eq_one]
    refine ⟨v0, ?_⟩
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [mem_pairs_iff']
      exact ⟨i, by rw [List.getElem?_eq_some_iff]; exact ⟨hi0, rfl⟩, hiu⟩
    · intro v hv
      rw [Finset.mem_filter, mem_pairs_iff'] at hv
      obtain ⟨_, j, hj1, hj2⟩ := hv
      rw [List.getElem?_eq_some_iff] at hiu hj2
      obtain ⟨hib, hie⟩ := hiu
      obtain ⟨hjb, hje⟩ := hj2
      have : j + 1 = i + 1 := hnd.getElem_inj_iff.mp (by rw [hje, hie])
      have hji : j = i := by omega
      subst hji
      rw [List.getElem?_eq_some_iff] at hj1
      obtain ⟨_, hjv⟩ := hj1
      rw [hv0, ← hjv]
  · rw [ite_eq_right hP]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _
    rw [mem_pairs_iff']
    rintro ⟨i, hiv, hiu⟩
    apply hP
    obtain ⟨hi1, _⟩ := List.getElem?_eq_some_iff.mp hiu
    exact ⟨i, hi1, hiu⟩

omit [Fintype N] [DecidableEq N] in
/-- `POut` is equivalent to: `u` occurs and is not the last element. -/
private theorem pout_iff (l : List N) (hnd : l.Nodup) (u : N) :
    POut l u ↔ (u ∈ l ∧ l.getLast? ≠ some u) := by
  constructor
  · rintro ⟨i, hilt, hiu⟩
    have hmem : u ∈ l := List.mem_iff_getElem?.mpr ⟨i, hiu⟩
    refine ⟨hmem, ?_⟩
    intro hlast
    rw [List.getLast?_eq_getElem?] at hlast
    rw [List.getElem?_eq_some_iff] at hiu hlast
    obtain ⟨hib, hie⟩ := hiu
    obtain ⟨hlb, hle⟩ := hlast
    have : i = l.length - 1 := hnd.getElem_inj_iff.mp (by rw [hie, hle])
    omega
  · rintro ⟨hmem, hlast⟩
    rw [List.mem_iff_getElem?] at hmem
    obtain ⟨i, hiu⟩ := hmem
    rw [List.getElem?_eq_some_iff] at hiu
    obtain ⟨hib, hie⟩ := hiu
    refine ⟨i, ?_, by rw [List.getElem?_eq_some_iff]; exact ⟨hib, hie⟩⟩
    -- i ≠ length-1 since otherwise it's the last element
    by_contra hcon
    push Not at hcon
    have hi : i = l.length - 1 := by omega
    apply hlast
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_some_iff]
    subst hi
    exact ⟨by omega, hie⟩

omit [Fintype N] [DecidableEq N] in
/-- `PIn` is equivalent to: `u` occurs and is not the first element. -/
private theorem pin_iff (l : List N) (hnd : l.Nodup) (u : N) :
    PIn l u ↔ (u ∈ l ∧ l.head? ≠ some u) := by
  constructor
  · rintro ⟨i, hilt, hiu⟩
    have hmem : u ∈ l := List.mem_iff_getElem?.mpr ⟨i + 1, hiu⟩
    refine ⟨hmem, ?_⟩
    intro hhead
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_some_iff] at hiu hhead
    obtain ⟨hib, hie⟩ := hiu
    obtain ⟨hhb, hhe⟩ := hhead
    have : i + 1 = 0 := hnd.getElem_inj_iff.mp (by rw [hie, hhe])
    omega
  · rintro ⟨hmem, hhead⟩
    rw [List.mem_iff_getElem?] at hmem
    obtain ⟨j, hju⟩ := hmem
    rw [List.getElem?_eq_some_iff] at hju
    obtain ⟨hjb, hje⟩ := hju
    -- j ≠ 0
    have hj0 : j ≠ 0 := by
      intro h0
      apply hhead
      rw [List.head?_eq_getElem?, List.getElem?_eq_some_iff]
      subst h0
      exact ⟨by omega, hje⟩
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact ⟨i, by omega, by rw [List.getElem?_eq_some_iff]; exact ⟨hjb, hje⟩⟩

/-- Degree balance: along a duplicate-free list, every node has out-degree minus in-degree equal
to `1` at the head, `-1` at the last element, and `0` elsewhere. -/
theorem degree_balance (l : List N) (hnd : l.Nodup) (u : N) :
    (∑ v, (if (u, v) ∈ pairs l then (1 : ℝ) else 0))
      - (∑ v, if (v, u) ∈ pairs l then (1 : ℝ) else 0)
    = (if l.head? = some u then (1 : ℝ) else 0) - (if l.getLast? = some u then (1 : ℝ) else 0) := by
  rw [Finset.sum_boole, Finset.sum_boole]
  rw [out_card l hnd u, in_card l hnd u]
  simp only [pout_iff l hnd u, pin_iff l hnd u]
  -- Now everything is in terms of membership and head?/getLast?
  by_cases hmem : u ∈ l
  · -- u ∈ l
    have hne : l ≠ [] := by rintro rfl; simp at hmem
    by_cases hhead : l.head? = some u <;> by_cases hlast : l.getLast? = some u <;>
      simp [hmem, hhead, hlast]
  · -- u ∉ l : head? and getLast? cannot be some u
    have h1 : l.head? ≠ some u := by
      intro h; exact hmem (List.mem_of_mem_head? h)
    have h2 : l.getLast? ≠ some u := by
      intro h; exact hmem (List.mem_of_mem_getLast? h)
    simp [hmem, h1, h2]

end PathBalance

/-! ## Networks, flows, cuts and weak duality -/

section Network

open Finset

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- A finite s–t network: capacities (assumed nonnegative) with distinct source and sink. -/
structure Network (N : Type*) [Fintype N] [DecidableEq N] where
  /-- The capacity assigned to each ordered pair of vertices. -/
  cap : N → N → ℝ
  capNonneg : ∀ u v, 0 ≤ cap u v
  /-- The source vertex. -/
  s : N
  /-- The sink vertex. -/
  t : N
  st : s ≠ t

/-- A feasible flow on a network. -/
structure Flow (Net : Network N) where
  /-- The signed flow on each ordered pair of vertices. -/
  f : N → N → ℝ
  skew : ∀ u v, f u v = - f v u
  capacitated : ∀ u v, f u v ≤ Net.cap u v
  conserved : ∀ u, u ≠ Net.s → u ≠ Net.t → ∑ v, f u v = 0

/-- The value of a flow: net flow out of the source. -/
def Flow.value {Net : Network N} (F : Flow Net) : ℝ := ∑ v, F.f Net.s v

/-- An s–t cut: a set of nodes containing the source but not the sink. -/
structure Cut (Net : Network N) where
  /-- The source side of the cut. -/
  S : Finset N
  hs : Net.s ∈ S
  ht : Net.t ∉ S

/-- The capacity of a cut: total capacity of edges leaving `S`. -/
def Cut.capacity {Net : Network N} (C : Cut Net) : ℝ :=
  ∑ u ∈ C.S, ∑ v ∈ (Finset.univ \ C.S), Net.cap u v

/-- The flow across a cut equals the value of the flow. -/
lemma Flow.value_eq_flow_across {Net : Network N} (F : Flow Net) (C : Cut Net) :
    F.value = ∑ u ∈ C.S, ∑ v ∈ (Finset.univ \ C.S), F.f u v := by
  -- Σ_{u∈S} Σ_{v∈univ} f u v  =  value (only s contributes; internal nodes conserved, t∉S)
  have hfull : ∑ u ∈ C.S, ∑ v, F.f u v = F.value := by
    rw [Finset.sum_eq_single Net.s]
    · rfl
    · intro u huS hune
      exact F.conserved u hune (by rintro rfl; exact C.ht huS)
    · intro h; exact absurd C.hs h
  -- split the inner full sum over v into v∈S and v∉S
  have hsplit : ∀ u, ∑ v, F.f u v
      = (∑ v ∈ C.S, F.f u v) + ∑ v ∈ (Finset.univ \ C.S), F.f u v := by
    intro u
    rw [← Finset.sum_add_sum_compl C.S (F.f u), Finset.compl_eq_univ_sdiff]
  -- the S×S block vanishes by skew symmetry: D = -D ⇒ D = 0
  have hdiag : ∑ u ∈ C.S, ∑ v ∈ C.S, F.f u v = 0 := by
    have e1 : ∑ u ∈ C.S, ∑ v ∈ C.S, F.f u v
            = ∑ u ∈ C.S, ∑ v ∈ C.S, (- F.f v u) := by
      apply Finset.sum_congr rfl; intro u _
      apply Finset.sum_congr rfl; intro v _
      exact F.skew u v
    have e2 : ∑ u ∈ C.S, ∑ v ∈ C.S, (- F.f v u)
            = - ∑ u ∈ C.S, ∑ v ∈ C.S, F.f v u := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro u _
      rw [Finset.sum_neg_distrib]
    have e3 : ∑ u ∈ C.S, ∑ v ∈ C.S, F.f v u
            = ∑ u ∈ C.S, ∑ v ∈ C.S, F.f u v := Finset.sum_comm
    linarith [e1, e2, e3]
  calc F.value = ∑ u ∈ C.S, ∑ v, F.f u v := hfull.symm
    _ = ∑ u ∈ C.S, ((∑ v ∈ C.S, F.f u v) + ∑ v ∈ (Finset.univ \ C.S), F.f u v) := by
          apply Finset.sum_congr rfl; intro u _; rw [hsplit u]
    _ = (∑ u ∈ C.S, ∑ v ∈ C.S, F.f u v)
          + ∑ u ∈ C.S, ∑ v ∈ (Finset.univ \ C.S), F.f u v := by rw [Finset.sum_add_distrib]
    _ = ∑ u ∈ C.S, ∑ v ∈ (Finset.univ \ C.S), F.f u v := by rw [hdiag]; ring

/-- **Weak duality.** Every flow value is bounded by every cut capacity. -/
theorem value_le_capacity {Net : Network N} (F : Flow Net) (C : Cut Net) :
    F.value ≤ C.capacity := by
  rw [F.value_eq_flow_across C]
  unfold Cut.capacity
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  exact F.capacitated u v

/-! ## Residual reachability -/

/-- Residual step: there is spare capacity on the (skew) edge `u → v`. -/
def ResStep (Net : Network N) (F : Flow Net) (u v : N) : Prop :=
  0 < Net.cap u v - F.f u v

/-- Residual reachability from the source. -/
def Reaches (Net : Network N) (F : Flow Net) (v : N) : Prop :=
  Relation.ReflTransGen (ResStep Net F) Net.s v

open scoped Classical in
/-- The set of nodes reachable from `s` in the residual graph. -/
noncomputable def reachableSet {Net : Network N} (F : Flow Net) : Finset N :=
  {v | Reaches Net F v}.toFinset

open scoped Classical in
@[simp] lemma mem_reachableSet {Net : Network N} (F : Flow Net) (v : N) :
    v ∈ reachableSet F ↔ Reaches Net F v := by
  unfold reachableSet; rw [Set.mem_toFinset]; rfl

/-- **Saturated-cut value.** If every edge leaving `S` is saturated, then the flow
value equals the cut capacity. No augmenting paths — pure flow/cut accounting. -/
lemma saturated_cut_value {Net : Network N} (F : Flow Net) (S : Finset N)
    (hs : Net.s ∈ S) (ht : Net.t ∉ S)
    (hsat : ∀ u ∈ S, ∀ v ∉ S, F.f u v = Net.cap u v) :
    F.value = (⟨S, hs, ht⟩ : Cut Net).capacity := by
  rw [F.value_eq_flow_across ⟨S, hs, ht⟩]
  unfold Cut.capacity
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.mem_sdiff] at hv
  exact hsat u hu v hv.2

/-- **The residual-reachable set saturates its outgoing edges.** If a node `u` is
reachable and `v` is not, the edge `u → v` has no residual capacity, hence is saturated. -/
lemma reachable_saturates {Net : Network N} (F : Flow Net)
    {u v : N} (hu : u ∈ reachableSet F) (hv : v ∉ reachableSet F) :
    F.f u v = Net.cap u v := by
  have hnres : ¬ ResStep Net F u v := by
    intro hres
    apply hv
    rw [mem_reachableSet] at hu ⊢
    exact Relation.ReflTransGen.tail hu hres
  -- ¬ (0 < cap - f)  ⇒  cap ≤ f; with f ≤ cap ⇒ f = cap
  unfold ResStep at hnres
  have h1 : Net.cap u v - F.f u v ≤ 0 := not_lt.mp hnres
  have h2 : F.f u v ≤ Net.cap u v := F.capacitated u v
  linarith

/-! ## Existence of a maximum flow -/

/-- The underlying set of feasible flow-functions of a network. -/
def FlowSet (Net : Network N) : Set (N → N → ℝ) :=
  {g | (∀ u v, g u v = - g v u) ∧ (∀ u v, g u v ≤ Net.cap u v) ∧
       (∀ u, u ≠ Net.s → u ≠ Net.t → ∑ v, g u v = 0)}

lemma flowSet_isClosed (Net : Network N) : IsClosed (FlowSet Net) := by
  unfold FlowSet
  have hskew : IsClosed {g : N → N → ℝ | ∀ u v, g u v = - g v u} := by
    rw [Set.ofPred_forall]; refine isClosed_iInter (fun u => ?_)
    rw [Set.ofPred_forall]; refine isClosed_iInter (fun v => ?_)
    exact isClosed_eq (by continuity) (by continuity)
  have hcap : IsClosed {g : N → N → ℝ | ∀ u v, g u v ≤ Net.cap u v} := by
    rw [Set.ofPred_forall]; refine isClosed_iInter (fun u => ?_)
    rw [Set.ofPred_forall]; refine isClosed_iInter (fun v => ?_)
    exact isClosed_le (by continuity) continuous_const
  have hcons : IsClosed {g : N → N → ℝ | ∀ u, u ≠ Net.s → u ≠ Net.t → ∑ v, g u v = 0} := by
    rw [Set.ofPred_forall]; refine isClosed_iInter (fun u => ?_)
    by_cases hu : u ≠ Net.s ∧ u ≠ Net.t
    · have : {g : N → N → ℝ | u ≠ Net.s → u ≠ Net.t → ∑ v, g u v = 0}
            = {g : N → N → ℝ | ∑ v, g u v = 0} := by
        ext g; simp [hu.1, hu.2]
      rw [this]
      refine isClosed_eq ?_ continuous_const
      exact continuous_finsetSum Finset.univ fun v _ =>
        (continuous_apply v).comp (continuous_apply u)
    · have : {g : N → N → ℝ | u ≠ Net.s → u ≠ Net.t → ∑ v, g u v = 0} = Set.univ := by
        ext g; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        intro h1 h2; exact absurd ⟨h1, h2⟩ hu
      rw [this]; exact isClosed_univ
  exact (hskew.inter (hcap.inter hcons))

lemma flowSet_isBounded (Net : Network N) : Bornology.IsBounded (FlowSet Net) := by
  -- every coordinate is pinned in [-cap v u, cap u v]; bound by the max capacity
  obtain ⟨M, hM⟩ := (Set.finite_range (fun p : N × N => Net.cap p.1 p.2)).bddAbove
  refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨M ⊔ 0, ?_⟩
  intro g hg
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [pi_norm_le_iff_of_nonneg (le_sup_right)]
  intro u
  rw [pi_norm_le_iff_of_nonneg (le_sup_right)]
  intro v
  rw [Real.norm_eq_abs, abs_le]
  have hup : g u v ≤ Net.cap u v := hg.2.1 u v
  have hlo : - g u v = g v u := (hg.1 u v).symm ▸ (neg_neg _)
  have hup2 : g v u ≤ Net.cap v u := hg.2.1 v u
  have hMuv : Net.cap u v ≤ M := hM ⟨(u, v), rfl⟩
  have hMvu : Net.cap v u ≤ M := hM ⟨(v, u), rfl⟩
  constructor
  · have : - g u v ≤ M := by rw [hlo]; linarith
    linarith [le_sup_left (a := M) (b := (0:ℝ))]
  · linarith [le_sup_left (a := M) (b := (0:ℝ))]

/-- **A maximum-value flow exists.** The flow polytope is compact (closed + bounded
in the finite-dimensional space `N → N → ℝ`) and `value` is continuous, so it is attained. -/
theorem max_flow_exists (Net : Network N) :
    ∃ F : Flow Net, ∀ F' : Flow Net, F'.value ≤ F.value := by
  have hcompact : IsCompact (FlowSet Net) :=
    Metric.isCompact_of_isClosed_isBounded (flowSet_isClosed Net) (flowSet_isBounded Net)
  have hne : (FlowSet Net).Nonempty := by
    refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩
    · intro u v; simp
    · intro u v; simpa using Net.capNonneg u v
    · intro u _ _; simp
  have hcont : ContinuousOn (fun g : N → N → ℝ => ∑ v, g Net.s v) (FlowSet Net) :=
    (continuous_finsetSum Finset.univ fun v _ =>
      (continuous_apply v).comp (continuous_apply Net.s)).continuousOn
  obtain ⟨g, hg, hmax⟩ := hcompact.exists_isMaxOn hne hcont
  refine ⟨⟨g, hg.1, hg.2.1, hg.2.2⟩, ?_⟩
  intro F'
  exact hmax (show F'.f ∈ FlowSet Net from ⟨F'.skew, F'.capacitated, F'.conserved⟩)

/-! ## Augmenting paths -/

/-- **Augmenting edge-set kernel.** If the sink is residual-reachable, a
simple residual `s→t` path yields a finite set `P` of directed residual edges with a uniform slack
`δ > 0`, no 2-cycles, and unit `s`-to-`t` degree balance (source has net out-degree `+1`, sink
`−1`, every other node balanced). This is pure path combinatorics — no flow content. -/
theorem augEdges_exists {Net : Network N} (F : Flow Net) (hreach : Reaches Net F Net.t) :
    ∃ (P : Finset (N × N)) (δ : ℝ), 0 < δ ∧
      (∀ p ∈ P, δ ≤ Net.cap p.1 p.2 - F.f p.1 p.2) ∧
      (∀ u v, (u, v) ∈ P → (v, u) ∉ P) ∧
      (∀ u, (∑ v, (if (u, v) ∈ P then (1 : ℝ) else 0))
              - (∑ v, if (v, u) ∈ P then (1 : ℝ) else 0)
            = (if u = Net.s then 1 else 0) - (if u = Net.t then 1 else 0)) := by
  -- (A) simple residual s→t path
  obtain ⟨l, hchain, hhead, hlast, hnd⟩ := exists_nodup_chain hreach Net.st
  set P := pairs l with hP
  -- l has ≥ 2 elements, so P is nonempty
  have hl2 : l.zip l.tail ≠ [] := by
    intro he
    -- zip empty ⇒ l.tail = [] ⇒ l = [] or singleton ⇒ head = last ⇒ s = t
    have htail : l.tail = [] := by
      cases l with
      | nil => simp_all
      | cons a t =>
        cases t with
        | nil => rfl
        | cons b t' => simp [List.zip_cons_cons] at he
    have : l.length ≤ 1 := by
      cases l with
      | nil => simp
      | cons a t => simp only [List.tail_cons] at htail; simp [htail]
    interval_cases h : l.length
    · exact absurd (List.length_eq_zero_iff.mp h ▸ hhead) (by simp)
    · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h
      simp only [List.head?_cons, List.getLast?_singleton] at hhead hlast
      exact Net.st (by rw [← Option.some_inj.mp hhead, ← Option.some_inj.mp hlast])
  have hPne : P.Nonempty := by
    rw [hP, pairs]
    obtain ⟨e, es, hz⟩ := List.exists_cons_of_ne_nil hl2
    rw [hz]; exact ⟨e, by simp⟩
  -- every edge of P is a residual edge
  have hpos : ∀ p ∈ P, 0 < Net.cap p.1 p.2 - F.f p.1 p.2 := by
    intro p hp
    have hr : ResStep Net F p.1 p.2 :=
      pairs_rel l hchain (u := p.1) (v := p.2) (by rw [← hP]; simpa using hp)
    exact hr
  refine ⟨P, P.inf' hPne (fun p => Net.cap p.1 p.2 - F.f p.1 p.2), ?_, ?_, ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]; exact hpos
  · intro p hp; exact Finset.inf'_le _ hp
  · intro u v huv; exact pairs_antisymm l hnd huv
  · intro u
    have hb := degree_balance l hnd u
    rw [hP, hb, hhead, hlast]
    simp only [Option.some.injEq, eq_comm]

/-- **Maximality ⇒ sink unreachable.** Given the augmenting edge-set,
the pushed flow `F' = F + δ·(P − Pᵀ)` is feasible with value `F.value + δ > F.value`,
contradicting maximality. -/
theorem t_not_reachable_of_max {Net : Network N} (F : Flow Net)
    (hmax : ∀ F' : Flow Net, F'.value ≤ F.value) :
    Net.t ∉ reachableSet F := by
  rw [mem_reachableSet]
  intro hreach
  obtain ⟨P, δ, hδ, hres, hanti, hbal⟩ := augEdges_exists F hreach
  -- the augmenting push, skew by construction
  set push : N → N → ℝ :=
    fun u v => δ * ((if (u, v) ∈ P then 1 else 0) - (if (v, u) ∈ P then 1 else 0)) with hpush
  have push_skew : ∀ u v, push u v = - push v u := by
    intro u v; simp only [hpush]; ring
  -- row sums of the push follow the degree balance
  have hrowsum : ∀ u, ∑ v, push u v
      = δ * ((if u = Net.s then 1 else 0) - (if u = Net.t then 1 else 0)) := by
    intro u
    simp only [hpush]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_sub_distrib]
    exact hbal u
  -- the augmented flow
  have cap' : ∀ u v, F.f u v + push u v ≤ Net.cap u v := by
    intro u v
    simp only [hpush]
    by_cases huv : (u, v) ∈ P
    · have hvu : (v, u) ∉ P := hanti u v huv
      simp only [huv, hvu, ite_true, ite_false]
      have := hres (u, v) huv
      simp only at this
      linarith
    · have hle : F.f u v ≤ Net.cap u v := F.capacitated u v
      by_cases hvu : (v, u) ∈ P
      · simp only [huv, hvu, ite_true, ite_false]; nlinarith [hδ]
      · simp only [huv, hvu, ite_false]; linarith
  have cons' : ∀ u, u ≠ Net.s → u ≠ Net.t → ∑ v, (F.f u v + push u v) = 0 := by
    intro u hus hut
    rw [Finset.sum_add_distrib, F.conserved u hus hut, hrowsum u]
    simp [hus, hut]
  let F' : Flow Net :=
    { f := fun u v => F.f u v + push u v
      skew := by intro u v; rw [F.skew u v, push_skew u v]; ring
      capacitated := cap'
      conserved := cons' }
  -- value strictly increases by δ
  have hval : F'.value = F.value + δ := by
    change ∑ v, (F.f Net.s v + push Net.s v) = F.value + δ
    rw [Finset.sum_add_distrib, hrowsum Net.s, ite_eq_left rfl, ite_eq_right Net.st]
    simp only [Flow.value]
    ring
  have := hmax F'
  rw [hval] at this
  linarith

/-- **Max-flow / min-cut.** There is a flow and an s–t cut with equal value.
Combined with weak duality (`value_le_capacity`), this flow is of maximum value and this cut is
of minimum capacity. -/
theorem maxflow_eq_mincut (Net : Network N) :
    ∃ (F : Flow Net) (C : Cut Net), F.value = C.capacity := by
  obtain ⟨F, hmax⟩ := max_flow_exists Net
  have ht : Net.t ∉ reachableSet F := t_not_reachable_of_max F hmax
  have hs : Net.s ∈ reachableSet F := by
    rw [mem_reachableSet]; exact Relation.ReflTransGen.refl
  refine ⟨F, ⟨reachableSet F, hs, ht⟩, ?_⟩
  exact saturated_cut_value F (reachableSet F) hs ht
    (fun u hu v hv => reachable_saturates F hu hv)

end Network

end Contrib.MaxFlowMinCut
