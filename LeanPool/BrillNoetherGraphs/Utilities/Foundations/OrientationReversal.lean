/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.AcyclicOrientation
public import Mathlib.Data.List.TakeWhile
public import Mathlib.Data.List.GetD

/-!
# The orientation reversal calculus

This file develops reversal of sets of edges of a `CFOrientation`, the two
fundamental moves given by directed cycles and directed cuts, and Gioan's
theorem relating reversal classes to linear equivalence of orientation
divisors.

## Contents

1. `reverseOn` — reverse every edge whose directed pair satisfies a predicate, with the
   `flow` and `indeg` bookkeeping (`flow_reverseOn`, `indeg_reverseOn`). This is the *coarse*
   move: a predicate on vertex pairs can only turn a whole parallel class at once.
2. `DirectedCycle`, and the two cycle reversals.
   * `reverseCycle` (coarse) turns the whole parallel class at each step.
     `indeg_reverseCycle_vert` and `indeg_reverseCycle_of_notMem` are its exact bookkeeping;
     `ordiv_reverseCycle` gives *equality* of `ordiv` only under a balance hypothesis, and
     `ordiv_reverseCycle_of_simple` discharges that hypothesis for simple graphs.
   * `reverseCycleOne` (fine) turns exactly one edge at each step — the classical move. It
     preserves every in-degree unconditionally (`indeg_reverseCycleOne`), hence `ordiv`
     (`ordiv_reverseCycleOne`).
   `DirectedCycle.reversed` / `.reversedOne` say the reversed cycle is again a directed
   cycle, so "has a directed cycle" survives either reversal.
3. `eq_of_indeg_eq_of_isAcyclic` — the strengthened uniqueness: if `O` is acyclic and
   `indeg O = indeg O'` pointwise then `O = O'`. `isAcyclic_iff_unique_of_indeg` packages
   it as "an orientation is acyclic iff it is the *unique* orientation with its indegree
   function", where the `←` direction assumes only that `O` has no directed `2`-cycle.
4. `isAcyclic_reverseCut` — reversing a directed cut takes acyclic orientations to acyclic
   ones.
5. `ReversalStep` / `ReversalEquiv`, `isAcyclic_of_reversalEquiv`, and
   `gioan_reversalEquiv_of_linear_equiv` — **Gioan's theorem, proved**. Its two halves are
   `reversalEquiv_of_indeg_eq` (the fine cycle move handles a difference of divergence zero)
   and `reversalEquiv_of_potential` (the cut move handles the rest); `diffFlow` is the signed
   difference vector both of them read, and `isDirectedCut_compl_of_min` is the one real
   idea — see the header of "Step 2" below.
6. `winnable_ordiv_of_not_isAcyclic` and `isAcyclic_iff_not_winnable_ordiv`,
   derived from 2+4+5 and `unwinnable_iff_exists_acyclic_ordiv`.

The path combinatorics is confined to `exists_isChain_of_backward_step`: a nonempty set of
vertices each of which is the head of an edge from another member forces arbitrarily long
chains, hence a repeat. It is used three times, for 2, for 3, and for 5.

## The edge-level orientation model

`CFOrientation` used to carry a field `no_bidirectional` forbidding two parallel edges to
point in opposite directions, so an orientation in that model turned each parallel class as a
block. Dependency pin `4f06d84` removed it; `CFOrientation` is now an arbitrary edge-level
orientation, i.e. any flow-count vector satisfying `count_preserving`. Three consequences,
all of them realised in this file:

* **`DirectedCycle` now allows two vertices** (`Fin (len + 2)`, not `Fin (len + 3)`): a
  parallel class with one edge each way *is* a directed `2`-cycle. Only looplessness rules
  out one-vertex cycles. Both `reverseCycle_ne` and `reverseCycleOne_ne` consequently need
  `1 ≤ C.len`: on a `2`-cycle the coarse move swaps the two flow counts and the fine move
  removes and restores one unit each way, so both can return `O` itself.
* **The fine cycle reversal exists**, and it is what makes `ordiv` preservation
  unconditional. The old "multi-edge caveat" — cycle reversal changes indegrees by the class
  multiplicity, so `ordiv_reverseCycle` needs a balance hypothesis — applies to the coarse
  move only, and the coarse move is now a curiosity rather than the only option.
* **`isAcyclic_iff_unique_of_indeg` no longer needs simplicity**, only the absence of a
  directed `2`-cycle; see its docstring for why that residue is not removable.

-/

@[expose] public section

namespace Utilities

open Multiset Finset

variable {G : CFGraph}

/-! ## 0. Helpers re-derived from `Orientation.lean`

`Orientation.lean` keeps `eq_orient`, `opp_flow`, `indeg_eq_sum_flow` and
`count_of_multiset_of_count` `private`, so the four facts are re-proved here (same proofs,
public names). They are the whole interface this file needs to the flow model. -/

/-- `multisetOfCount f` has count function `f`. Public re-proof of the `private`
`count_of_multiset_of_count` of `Orientation.lean`. -/
lemma count_multiset_of_count {T : Type*} [DecidableEq T] [Fintype T] (f : T → ℕ) (e : T) :
    Multiset.count e (multisetOfCount f) = f e := by
  rw [← Multiset.toDFinsupp_apply]
  calc
    (Multiset.toDFinsupp (multisetOfCount f)) e = (DFinsupp.equivFunOnFintype.symm f) e := by
      simp only [multisetOfCount, DFinsupp.toMultiset_toDFinsupp]
    _ = f e := by
      simpa only [DFinsupp.equivFunOnFintype_apply]
        using congrFun (Equiv.apply_symm_apply DFinsupp.equivFunOnFintype f) e

/-- The flow of `orientationFromFlow f _` is `f`. -/
lemma flow_orientation_from_flow (f : G.V × G.V → ℕ)
    (h₁ : ∀ v w : G.V, f (v, w) + f (w, v) = numEdges G v w) (u v : G.V) :
    flow (orientationFromFlow f h₁) u v = f (u, v) :=
  count_multiset_of_count f (u, v)

/-- Two orientations agreeing on every flow are equal. Public re-proof of the `private`
`eq_orient` of `Orientation.lean`. -/
lemma orientation_ext {O₁ O₂ : CFOrientation G} (h : ∀ u v : G.V, flow O₁ u v = flow O₂ u v) :
    O₁ = O₂ := by
  have hd : O₁.directedEdges = O₂.directedEdges := by
    refine Multiset.ext.mpr ?_
    rintro ⟨u, v⟩
    exact h u v
  cases O₁
  cases O₂
  cases hd
  rfl

/-- The two flows on an undirected edge add up to its multiplicity. Public re-proof of the
`private` `opp_flow` of `Orientation.lean`. -/
lemma flow_add_flow_rev (O : CFOrientation G) (u v : G.V) :
    flow O u v + flow O v u = numEdges G u v :=
  (O.count_preserving u v).symm

/-- The in-degree is the total flow into the vertex. Public re-proof of the `private`
`indeg_eq_sum_flow` of `Orientation.lean`, by a shorter route (count the filtered multiset
pairwise rather than by induction). -/
lemma indeg_eq_sum_flow (O : CFOrientation G) (v : G.V) :
    indeg G O v = ∑ w : G.V, flow O w v := by
  classical
  have hmem : ∀ e ∈ O.directedEdges.filter (fun e => e.snd = v),
      e ∈ (Finset.univ : Finset (G.V × G.V)) := fun e _ => Finset.mem_univ e
  rw [indeg, ← Multiset.sum_count_eq_card hmem, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [Multiset.count_filter, flow, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- A directed edge is exactly a pair carrying positive flow. -/
lemma directed_edge_iff_flow_pos (O : CFOrientation G) (u v : G.V) :
    directedEdge G O u v ↔ 0 < flow O u v :=
  Multiset.count_pos.symm

/-- **No directed loop**: `G` is loopless, so `numEdges G v v = 0` and no orientation can
carry an edge from `v` to itself. This is what rules out one-vertex directed cycles. -/
lemma not_directed_edge_self (O : CFOrientation G) (v : G.V) : ¬ directedEdge G O v v := by
  have h := flow_add_flow_rev O v v
  rw [num_edges_self_zero] at h
  rw [directed_edge_iff_flow_pos]
  omega

/-- **A directed 2-cycle**: `O` sends an edge from `u` to `v` and another back from `v` to
`u`. Since the removal of `CFOrientation.no_bidirectional` from the dependency this is a
legal configuration on a parallel class, and it is exactly what the two-vertex directed
cycles are. -/
def HasDirectedTwoCycle (O : CFOrientation G) : Prop :=
  ∃ u v : G.V, directedEdge G O u v ∧ directedEdge G O v u

/-! ## 1. Reversing a set of edges

`reverseOn O S` reverses every edge of `O` whose directed pair `(u, v)` satisfies `S u v`.
This is the *coarse* move: it turns a whole parallel class at once, since `S` can only see
the vertex pair. `reverseCycleOne` below is the fine move that turns a single edge of each
class; see the module docstring for which one is load-bearing where. -/

/-- The flow function of `reverseOn O S`: the edges of the class `(u,v)` survive unless
`S u v`, and the class `(v,u)` is added in when `S v u`. -/
def reverseFlow (O : CFOrientation G) (S : G.V → G.V → Prop) [DecidableRel S] :
    G.V × G.V → ℕ :=
  fun e => (if S e.1 e.2 then 0 else flow O e.1 e.2) + (if S e.2 e.1 then flow O e.2 e.1 else 0)

/-- `reverseFlow` still saturates every edge multiplicity: each parallel class contributes
its full count to exactly one of the two directions. -/
lemma reverseFlow_count_preserving (O : CFOrientation G) (S : G.V → G.V → Prop)
    [DecidableRel S] (u v : G.V) :
    reverseFlow O S (u, v) + reverseFlow O S (v, u) = numEdges G u v := by
  have h := flow_add_flow_rev O u v
  simp only [reverseFlow]
  split_ifs <;> omega

/-- **Reversing an edge set.** `reverseOn O S` is `O` with every edge whose directed pair
satisfies `S` turned around. -/
def reverseOn (O : CFOrientation G) (S : G.V → G.V → Prop) [DecidableRel S] :
    CFOrientation G :=
  orientationFromFlow (reverseFlow O S) (reverseFlow_count_preserving O S)

/-- The defining flow identity for `reverseOn`. -/
lemma flow_reverseOn (O : CFOrientation G) (S : G.V → G.V → Prop) [DecidableRel S]
    (u v : G.V) :
    flow (reverseOn O S) u v =
      (if S u v then 0 else flow O u v) + (if S v u then flow O v u else 0) :=
  flow_orientation_from_flow _ _ u v

/-- Reversing nothing changes nothing. -/
lemma reverseOn_bot (O : CFOrientation G) :
    reverseOn O (fun _ _ => False) = O := by
  refine orientation_ext fun u v => ?_
  simp [flow_reverseOn]

/-- **The `indeg` bookkeeping for a reversal.** The in-degree of `v` loses the reversed
edges pointing into `v` and gains the reversed edges pointing out of `v`. -/
lemma indeg_reverseOn (O : CFOrientation G) (S : G.V → G.V → Prop) [DecidableRel S]
    (v : G.V) :
    (indeg G (reverseOn O S) v : ℤ) =
      (indeg G O v : ℤ) - ∑ w : G.V, (if S w v then (flow O w v : ℤ) else 0)
        + ∑ w : G.V, (if S v w then (flow O v w : ℤ) else 0) := by
  have key : ∀ w : G.V, (flow (reverseOn O S) w v : ℤ) =
      (flow O w v : ℤ) - (if S w v then (flow O w v : ℤ) else 0)
        + (if S v w then (flow O v w : ℤ) else 0) := by
    intro w
    rw [flow_reverseOn]
    split_ifs <;> push_cast <;> ring
  rw [indeg_eq_sum_flow (reverseOn O S) v, indeg_eq_sum_flow O v]
  push_cast
  rw [Finset.sum_congr rfl fun w (_ : w ∈ Finset.univ) => key w, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]


/-- **Walking backwards produces arbitrarily long chains.** If every member of `P` is the
head of an `R`-edge from another member, then `R`-chains of every length exist, each headed
by a member of `P`.

This is the one piece of path combinatorics the file needs, and it is used three times: to
see that a directed cycle obstructs acyclicity (`not_isAcyclic_of_backward_step`), in
`eq_of_indeg_eq_of_isAcyclic` (with `P` the set of tails of edges where two orientations
disagree), and in `nonempty_relCycle_of_backward_step`, which is what turns the walk into an
actual cycle. -/
lemma exists_isChain_of_backward_step {V : Type*} {R : V → V → Prop} {P : V → Prop}
    (step : ∀ v, P v → ∃ u, P u ∧ R u v) {v₀ : V} (h₀ : P v₀) (k : ℕ) :
    ∃ l : List V, l.length = k + 1 ∧ List.IsChain R l ∧ ∃ a, l.head? = some a ∧ P a := by
  induction k with
  | zero => exact ⟨[v₀], rfl, List.isChain_singleton _, v₀, rfl, h₀⟩
  | succ k ih =>
    obtain ⟨l, hlen, hchain, a, hhead, ha⟩ := ih
    obtain ⟨u, hu, hedge⟩ := step a ha
    refine ⟨u :: l, by simp only [List.length_cons, hlen], ?_, u, rfl, hu⟩
    refine List.isChain_cons.mpr ⟨fun y hy => ?_, hchain⟩
    simp only [Option.mem_def, hhead, Option.some.injEq] at hy
    exact hy ▸ hedge

/-- **The walk-backwards criterion for a directed cycle.** If a nonempty set `P` of vertices
has the property that every member is the head of a directed edge from another member, then
`O` is not acyclic: walking backwards produces directed paths of every length, and a path
longer than `Fintype.card G.V` cannot be non-repeating. -/
lemma not_isAcyclic_of_backward_step {O : CFOrientation G} {P : G.V → Prop}
    (step : ∀ v, P v → ∃ u, P u ∧ directedEdge G O u v) {v₀ : G.V} (h₀ : P v₀) :
    ¬ isAcyclic G O := by
  intro hacyc
  obtain ⟨l, hlen, hchain, -⟩ := exists_isChain_of_backward_step step h₀ (Fintype.card G.V)
  have hnodup : l.Nodup := hacyc ⟨l, by omega, hchain⟩
  have hle := List.Nodup.length_le_card hnodup
  omega

/-! ## 2. Cycle reversal -/

/-- A **directed cycle** of `O`: `len + 2` distinct vertices, indexed cyclically by
`Fin (len + 2)`, with a directed edge from each to its successor.

Requiring at least *two* vertices is no restriction: `G` is loopless, so no directed cycle
has one vertex. Two-vertex cycles (`len = 0`) are genuine and must be allowed — a parallel
class with one edge each way is a directed 2-cycle, which the `CFOrientation` model
represents since `no_bidirectional` was removed from the dependency. The bound was `+ 3`
while that field existed. -/
structure DirectedCycle {G : CFGraph} (O : CFOrientation G) where
  /-- The cycle has `len + 2` vertices. -/
  len : ℕ
  /-- The vertices of the cycle, indexed cyclically. -/
  vert : Fin (len + 2) → G.V
  /-- The vertices are distinct. -/
  vert_inj : Function.Injective vert
  /-- Consecutive vertices carry a directed edge of `O`. -/
  edge : ∀ i : Fin (len + 2), directedEdge G O (vert i) (vert (i + 1))

/-- Cyclic index arithmetic: `Fin (n)` is an additive group when `n ≠ 0`. -/
private lemma fin_sub_add_one {n : ℕ} [NeZero n] (i : Fin n) : i - 1 + 1 = i := by abel

/-- Cyclic index arithmetic, the other way round: the successor in `Fin (n + 2)` is the
numerical successor except at the top, where it wraps to `0`. -/
private lemma fin_val_succ {n : ℕ} (i : Fin (n + 2)) :
    ((i + 1 : Fin (n + 2)) : ℕ) = if i.val + 1 = n + 2 then 0 else i.val + 1 := by
  have hone : ((1 : Fin (n + 2)) : ℕ) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have hi := i.isLt
  rw [Fin.val_add_eq_ite, hone]
  split_ifs <;> omega

/-- Two steps forward from `0` in `Fin (n + 2)` is *not* `0` once `n ≥ 1`, i.e. once the
cycle has at least three vertices. -/
private lemma fin_succ_succ_zero_ne {n : ℕ} (hn : 1 ≤ n) :
    ((0 : Fin (n + 2)) + 1 + 1) ≠ (0 : Fin (n + 2)) := by
  have h1 : (((0 : Fin (n + 2)) + 1 : Fin (n + 2)) : ℕ) = 1 := by
    rw [fin_val_succ, Fin.val_zero, ite_eq_right (by omega)]
  have h2 : (((0 : Fin (n + 2)) + 1 + 1 : Fin (n + 2)) : ℕ) = 2 := by
    rw [fin_val_succ, h1, ite_eq_right (by omega)]
  intro h
  rw [h, Fin.val_zero] at h2
  omega

/-- Two steps forward from `0` in `Fin (0 + 2)` *is* `0`: a `len = 0` cycle closes up after
two vertices. -/
private lemma fin_succ_succ_zero_eq {n : ℕ} (hn : n = 0) :
    ((0 : Fin (n + 2)) + 1 + 1) = (0 : Fin (n + 2)) := by
  have h1 : (((0 : Fin (n + 2)) + 1 : Fin (n + 2)) : ℕ) = 1 := by
    rw [fin_val_succ, Fin.val_zero, ite_eq_right (by omega)]
  refine Fin.ext ?_
  rw [fin_val_succ, h1, ite_eq_left (by omega), Fin.val_zero]

namespace DirectedCycle

/-- The set of directed pairs traversed by a directed cycle. -/
def pred {O : CFOrientation G} (C : DirectedCycle O) : G.V → G.V → Prop :=
  fun u v => ∃ i : Fin (C.len + 2), u = C.vert i ∧ v = C.vert (i + 1)

instance {O : CFOrientation G} (C : DirectedCycle O) : DecidableRel C.pred := fun u v =>
  inferInstanceAs (Decidable (∃ i : Fin (C.len + 2), u = C.vert i ∧ v = C.vert (i + 1)))

/-- The predecessor of a cycle vertex along the cycle. -/
lemma edge_pred {O : CFOrientation G} (C : DirectedCycle O) (i : Fin (C.len + 2)) :
    directedEdge G O (C.vert (i - 1)) (C.vert i) := by
  simpa only [fin_sub_add_one] using C.edge (i - 1)

/-- The pairs of `C` ending at a cycle vertex: only the predecessor edge. -/
lemma pred_into {O : CFOrientation G} (C : DirectedCycle O) (w : G.V)
    (j : Fin (C.len + 2)) : C.pred w (C.vert j) ↔ w = C.vert (j - 1) := by
  constructor
  · rintro ⟨i, rfl, hj⟩
    have hij : j = i + 1 := C.vert_inj hj
    subst hij
    congr 1
    abel
  · rintro rfl
    exact ⟨j - 1, rfl, by rw [fin_sub_add_one]⟩

/-- The pairs of `C` starting at a cycle vertex: only the successor edge. -/
lemma pred_outOf {O : CFOrientation G} (C : DirectedCycle O) (w : G.V)
    (j : Fin (C.len + 2)) : C.pred (C.vert j) w ↔ w = C.vert (j + 1) := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [C.vert_inj hi]
  · rintro rfl
    exact ⟨j, rfl, rfl⟩

/-- A vertex off the cycle meets none of the cycle's pairs. -/
lemma not_pred_of_notMem {O : CFOrientation G} (C : DirectedCycle O) {v : G.V}
    (hv : ∀ i, v ≠ C.vert i) (w : G.V) : ¬ C.pred w v ∧ ¬ C.pred v w := by
  constructor
  · rintro ⟨i, -, hv'⟩
    exact hv (i + 1) hv'
  · rintro ⟨i, hv', -⟩
    exact hv i hv'

/-- Every pair traversed by the cycle carries positive flow. -/
lemma flow_pos_of_pred {O : CFOrientation G} (C : DirectedCycle O) {u v : G.V}
    (h : C.pred u v) : 0 < flow O u v := by
  obtain ⟨i, rfl, rfl⟩ := h
  exact (directed_edge_iff_flow_pos O _ _).mp (C.edge i)

/-- On a cycle of at least three vertices the first step is not also traversed backwards.
This is what fails for a `len = 0` cycle, where the two steps are each other's reverse. -/
lemma not_pred_succ_zero {O : CFOrientation G} (C : DirectedCycle O) (hlen : 1 ≤ C.len) :
    ¬ C.pred (C.vert (0 + 1)) (C.vert 0) := fun h =>
  fin_succ_succ_zero_ne hlen (C.vert_inj ((C.pred_outOf _ (0 + 1)).mp h)).symm

/-- A cycle with `len = 0` has exactly two vertices, and its two steps are a directed
2-cycle of `O`. -/
lemma hasDirectedTwoCycle_of_len_eq_zero {O : CFOrientation G} (C : DirectedCycle O)
    (h : C.len = 0) : HasDirectedTwoCycle O :=
  ⟨C.vert 0, C.vert (0 + 1), C.edge 0, by
    have hE := C.edge (0 + 1)
    rwa [fin_succ_succ_zero_eq h] at hE⟩

end DirectedCycle

/-- An orientation carrying a directed cycle is not acyclic. -/
theorem not_isAcyclic_of_directedCycle (O : CFOrientation G) (C : DirectedCycle O) :
    ¬ isAcyclic G O :=
  not_isAcyclic_of_backward_step (P := fun v => ∃ i, v = C.vert i)
    (fun _ hv => by
      obtain ⟨i, rfl⟩ := hv
      exact ⟨C.vert (i - 1), ⟨i - 1, rfl⟩, C.edge_pred i⟩)
    ⟨0, rfl⟩

/-! ### Cycles of an arbitrary relation

`DirectedCycle O` is the case `R = directedEdge G O` of `RelCycle R`. The generality is
needed exactly once, and it is essential there: `reversalEquiv_of_indeg_eq` finds its cycle
in the relation "`O₁` carries strictly more flow than `O₂`", which is *smaller* than
`directedEdge G O₁`, and the extra information — that every step of the cycle is a step
where the two orientations disagree — is what makes the flow bookkeeping close. -/

/-- A **cycle of a relation** `R`: `len + 2` distinct vertices, indexed cyclically, with
`R` holding from each to its successor. `DirectedCycle O` is `RelCycle (directedEdge G O)`
with a bespoke name. -/
structure RelCycle {V : Type*} (R : V → V → Prop) where
  /-- The cycle has `len + 2` vertices. -/
  len : ℕ
  /-- The vertices of the cycle, indexed cyclically. -/
  vert : Fin (len + 2) → V
  /-- The vertices are distinct. -/
  vert_inj : Function.Injective vert
  /-- Consecutive vertices are `R`-related. -/
  edge : ∀ i : Fin (len + 2), R (vert i) (vert (i + 1))

/-- A cycle of the opposite relation, read backwards, is a cycle of `R`. -/
def RelCycle.op {V : Type*} {R : V → V → Prop} (C : RelCycle (fun u v => R v u)) :
    RelCycle R where
  len := C.len
  vert := fun j => C.vert (-j)
  vert_inj := C.vert_inj.comp neg_injective
  edge := fun j => by
    have h : (-(j + 1) : Fin (C.len + 2)) = -j - 1 := by abel
    rw [h]
    simpa only [fin_sub_add_one] using C.edge (-j - 1)

/-- A cycle of a relation refining `directedEdge G O` is a directed cycle of `O`. -/
def RelCycle.toDirectedCycle {O : CFOrientation G} {R : G.V → G.V → Prop} (C : RelCycle R)
    (h : ∀ u v : G.V, R u v → directedEdge G O u v) : DirectedCycle O where
  len := C.len
  vert := C.vert
  vert_inj := C.vert_inj
  edge := fun i => h _ _ (C.edge i)

/-- **A repeated vertex in an `R`-chain produces an `R`-cycle.**

The whole construction, with no modular arithmetic beyond `fin_val_succ`: index the chain by
`f i = l.getD i v₀` and pick, by `Nat.find`, the *shortest* gap `m + 1` over all repeats
`f c = f (c + (m + 1))` of the chain. Minimality makes `f c, …, f (c + m)` pairwise distinct —
a shorter repeat inside that window would be a shorter gap — so they are the vertices of a
cycle, closed up by `f (c + (m + 1)) = f c`. The gap is at least `2`, because irreflexivity
of `R` kills gap `1` — and that is the only exclusion needed, since `RelCycle` (like
`DirectedCycle`) allows two-vertex cycles.

The construction extracts a finite cycle directly from the repeated segment
of the chain. -/
theorem nonempty_relCycle_of_repeat {V : Type*} [Nonempty V] {R : V → V → Prop}
    (hirr : ∀ v : V, ¬ R v v) (l : List V)
    (hchain : List.IsChain R l) (a b : ℕ) (hab : a < b)
    (hb : b < l.length) (heq : l[a]'(by omega) = l[b]) :
    Nonempty (RelCycle R) := by
  classical
  obtain ⟨v₀⟩ := ‹Nonempty V›
  set f : ℕ → V := fun i => l.getD i v₀ with hfdef
  have hgi : ∀ (i : ℕ) (hi : i < l.length), f i = l[i] := fun i hi =>
    List.getD_eq_getElem l v₀ hi
  have hstep : ∀ i : ℕ, i + 1 < l.length → R (f i) (f (i + 1)) := by
    intro i hi
    rw [hgi i (by omega), hgi (i + 1) hi]
    exact List.isChain_iff_getElem.mp hchain i hi
  -- The set of gaps at which the chain repeats is nonempty, so it has a least element.
  have hQ : ∃ d : ℕ, ∃ c : ℕ, c + (d + 1) < l.length ∧ f c = f (c + (d + 1)) := by
    refine ⟨b - a - 1, a, by omega, ?_⟩
    rw [show a + (b - a - 1 + 1) = b by omega, hgi a (by omega), hgi b hb]
    exact heq
  have hmin : ∀ k, k < Nat.find hQ → ∀ c' : ℕ, c' + (k + 1) < l.length →
      f c' ≠ f (c' + (k + 1)) := fun k hk c' h₁ h₂ => Nat.find_min hQ hk ⟨c', h₁, h₂⟩
  obtain ⟨c, hclen, hfc⟩ := Nat.find_spec hQ
  set m := Nat.find hQ with hmdef
  -- Gap `1` is impossible: it would be an `R`-loop, and `R` is irreflexive.
  have hm2 : 1 ≤ m := by
    by_contra hcon
    rw [show c + (m + 1) = c + 1 by omega] at hclen hfc
    have hd := hstep c hclen
    rw [← hfc] at hd
    exact hirr (f c) hd
  -- The window `f c, …, f (c + m)` is the cycle.
  refine ⟨{ len := m - 1, vert := fun i => f (c + i.val), vert_inj := ?_, edge := ?_ }⟩
  · -- Injectivity is exactly the minimality of `m`.
    have key : ∀ x y : Fin (m - 1 + 2), x.val < y.val → f (c + x.val) ≠ f (c + y.val) := by
      intro x y hxy hfxy
      have hylt := y.isLt
      refine hmin (y.val - x.val - 1) (by omega) (c + x.val) (by omega) ?_
      rw [show c + x.val + (y.val - x.val - 1 + 1) = c + y.val by omega]
      exact hfxy
    intro x y hxy
    rcases Nat.lt_trichotomy x.val y.val with h | h | h
    · exact absurd hxy (key x y h)
    · exact Fin.ext h
    · exact absurd hxy.symm (key y x h)
  · -- Each step is a chain step, and the last one closes up by `hfc`.
    intro i
    have hilt := i.isLt
    have hnext : f (c + ((i + 1 : Fin (m - 1 + 2)) : ℕ)) = f (c + i.val + 1) := by
      rw [fin_val_succ]
      split_ifs with hlast
      · rw [Nat.add_zero, show c + i.val + 1 = c + (m + 1) by omega]
        exact hfc
      · rw [Nat.add_assoc]
    rw [hnext]
    exact hstep _ (by omega)

/-- The `directedEdge` case of `nonempty_relCycle_of_repeat`; the irreflexivity hypothesis
is `not_directed_edge_self`, i.e. looplessness of `G`. -/
private theorem nonempty_directedCycle_of_repeat (O : CFOrientation G) (l : List G.V)
    (hchain : List.IsChain (directedEdge G O) l) (a b : ℕ) (hab : a < b)
    (hb : b < l.length) (heq : l[a]'(by omega) = l[b]) :
    Nonempty (DirectedCycle O) :=
  (nonempty_relCycle_of_repeat (not_directed_edge_self O) l hchain a b hab hb heq).map
    fun C => C.toDirectedCycle fun _ _ h => h

/-- **Walking backwards inside a finite set produces a cycle.** Combine
`exists_isChain_of_backward_step` — which makes an `R`-chain longer than `Fintype.card V` —
with `nonempty_relCycle_of_repeat`, which turns its unavoidable repeat into a cycle. -/
theorem nonempty_relCycle_of_backward_step {V : Type*} [Fintype V] {R : V → V → Prop}
    (hirr : ∀ v : V, ¬ R v v) {P : V → Prop} (step : ∀ v, P v → ∃ u, P u ∧ R u v)
    {v₀ : V} (h₀ : P v₀) : Nonempty (RelCycle R) := by
  classical
  have : Nonempty V := ⟨v₀⟩
  obtain ⟨l, hlen, hchain, -⟩ := exists_isChain_of_backward_step step h₀ (Fintype.card V)
  have hnd : ¬ l.Nodup := fun hnd => by
    have := List.Nodup.length_le_card hnd
    omega
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp
    (fun hinj => hnd (List.nodup_iff_injective_getElem.mpr hinj))
  rcases lt_or_gt_of_ne (fun hv : x.val = y.val => hne (Fin.ext hv)) with hlt | hlt
  · exact nonempty_relCycle_of_repeat hirr l hchain x.val y.val hlt y.isLt hxy
  · exact nonempty_relCycle_of_repeat hirr l hchain y.val x.val hlt x.isLt hxy.symm

/-- **Walking forwards inside a finite set produces a cycle**, the mirror image of
`nonempty_relCycle_of_backward_step` obtained by running it on the opposite relation and
reading the resulting cycle backwards (`RelCycle.op`). -/
theorem nonempty_relCycle_of_forward_step {V : Type*} [Fintype V] {R : V → V → Prop}
    (hirr : ∀ v : V, ¬ R v v) {P : V → Prop} (step : ∀ v, P v → ∃ w, P w ∧ R v w)
    {v₀ : V} (h₀ : P v₀) : Nonempty (RelCycle R) :=
  (nonempty_relCycle_of_backward_step (R := fun u v => R v u) hirr step h₀).map RelCycle.op

/-- **Every non-acyclic orientation carries a directed cycle**, the converse of
`not_isAcyclic_of_directedCycle`. Failure of acyclicity hands over a directed path with a
repeated vertex; `nonempty_directedCycle_of_repeat` turns the shortest such repeat into a
cycle, whose length is at least two because `G` is loopless. -/
theorem nonempty_directedCycle_of_not_isAcyclic (O : CFOrientation G)
    (h : ¬ isAcyclic G O) : Nonempty (DirectedCycle O) := by
  classical
  simp only [isAcyclic, not_forall] at h
  obtain ⟨q, hq⟩ := h
  simp only [nonRepeating] at hq
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp
    (fun hinj => hq (List.nodup_iff_injective_getElem.mpr hinj))
  rcases lt_or_gt_of_ne (fun hv : x.val = y.val => hne (Fin.ext hv)) with hlt | hlt
  · exact nonempty_directedCycle_of_repeat O q.vertices q.valid_edges x.val y.val hlt y.isLt hxy
  · exact nonempty_directedCycle_of_repeat O q.vertices q.valid_edges y.val x.val hlt x.isLt
      hxy.symm

/-- **Cycle reversal.** Reverse every edge traversed by the directed cycle `C`. -/
def reverseCycle (O : CFOrientation G) (C : DirectedCycle O) : CFOrientation G :=
  reverseOn O C.pred

namespace DirectedCycle

/-- **The reversed cycle is again a directed cycle**, now of `reverseCycle O C`. Hence
"has a directed cycle" is preserved by cycle reversal — which is what makes the reversal
class of an acyclic orientation consist of acyclic orientations. -/
def reversed {O : CFOrientation G} (C : DirectedCycle O) :
    DirectedCycle (reverseCycle O C) where
  len := C.len
  vert := fun j => C.vert (-j)
  vert_inj := C.vert_inj.comp neg_injective
  edge := by
    intro j
    have hstep : C.pred (C.vert (-j - 1)) (C.vert (-j)) :=
      (C.pred_into _ (-j)).mpr rfl
    have hpos : 0 < flow O (C.vert (-j - 1)) (C.vert (-j)) :=
      (directed_edge_iff_flow_pos O _ _).mp (C.edge_pred (-j))
    have hneg : (-(j + 1) : Fin (C.len + 2)) = -j - 1 := by abel
    rw [hneg]
    refine (directed_edge_iff_flow_pos _ _ _).mpr ?_
    rw [reverseCycle, flow_reverseOn, ite_eq_left hstep]
    omega

end DirectedCycle

/-- The `indeg` bookkeeping at a vertex *on* the cycle: it loses the predecessor edge class
and gains the successor edge class. -/
lemma indeg_reverseCycle_vert (O : CFOrientation G) (C : DirectedCycle O)
    (j : Fin (C.len + 2)) :
    (indeg G (reverseCycle O C) (C.vert j) : ℤ) =
      (indeg G O (C.vert j) : ℤ) - (flow O (C.vert (j - 1)) (C.vert j) : ℤ)
        + (flow O (C.vert j) (C.vert (j + 1)) : ℤ) := by
  have hin : ∑ w : G.V, (if C.pred w (C.vert j) then (flow O w (C.vert j) : ℤ) else 0)
      = (flow O (C.vert (j - 1)) (C.vert j) : ℤ) := by
    refine (Finset.sum_eq_single (C.vert (j - 1)) (fun b _ hb => ?_)
      (fun hb => absurd (Finset.mem_univ _) hb)).trans ?_
    · exact ite_eq_right fun hc => hb ((C.pred_into b j).mp hc)
    · exact ite_eq_left ((C.pred_into _ j).mpr rfl)
  have hout : ∑ w : G.V, (if C.pred (C.vert j) w then (flow O (C.vert j) w : ℤ) else 0)
      = (flow O (C.vert j) (C.vert (j + 1)) : ℤ) := by
    refine (Finset.sum_eq_single (C.vert (j + 1)) (fun b _ hb => ?_)
      (fun hb => absurd (Finset.mem_univ _) hb)).trans ?_
    · exact ite_eq_right fun hc => hb ((C.pred_outOf b j).mp hc)
    · exact ite_eq_left ((C.pred_outOf _ j).mpr rfl)
  rw [reverseCycle, indeg_reverseOn, hin, hout]

/-- The `indeg` bookkeeping at a vertex *off* the cycle: nothing changes. -/
lemma indeg_reverseCycle_of_notMem (O : CFOrientation G) (C : DirectedCycle O) {v : G.V}
    (hv : ∀ i, v ≠ C.vert i) : indeg G (reverseCycle O C) v = indeg G O v := by
  have h : (indeg G (reverseCycle O C) v : ℤ) = (indeg G O v : ℤ) := by
    rw [reverseCycle, indeg_reverseOn,
      Finset.sum_eq_zero fun w _ => ite_eq_right (C.not_pred_of_notMem hv w).1,
      Finset.sum_eq_zero fun w _ => ite_eq_right (C.not_pred_of_notMem hv w).2]
    ring
  exact_mod_cast h

/-- **Cycle reversal preserves `ordiv` exactly**, under the balance hypothesis that the
edge multiplicity is constant around the cycle.

The hypothesis is an artefact of the *coarse* move, which reverses a whole parallel class at
each step: the indegree at a cycle vertex then moves by the class multiplicity rather than by
one. It holds whenever `G` is simple (`ordiv_reverseCycle_of_simple`), and it is vacuous for
the fine move, which preserves `ordiv` outright (`ordiv_reverseCycleOne`). -/
theorem ordiv_reverseCycle (O : CFOrientation G) (C : DirectedCycle O)
    (hbal : ∀ i : Fin (C.len + 2),
      flow O (C.vert (i - 1)) (C.vert i) = flow O (C.vert i) (C.vert (i + 1))) :
    ordiv G (reverseCycle O C) = ordiv G O := by
  funext v
  by_cases hv : ∃ i, v = C.vert i
  · obtain ⟨j, rfl⟩ := hv
    have h := indeg_reverseCycle_vert O C j
    have hb := hbal j
    simp only [ordiv]
    rw [h, hb]
    ring
  · simp only [not_exists] at hv
    simp only [ordiv, indeg_reverseCycle_of_notMem O C hv]

/-- On a simple graph the balance hypothesis of `ordiv_reverseCycle` is automatic: every
edge class traversed by the cycle has multiplicity exactly one. -/
theorem ordiv_reverseCycle_of_simple (O : CFOrientation G) (C : DirectedCycle O)
    (hsimple : ∀ u v : G.V, numEdges G u v ≤ 1) :
    ordiv G (reverseCycle O C) = ordiv G O := by
  refine ordiv_reverseCycle O C fun i => ?_
  have h₁ : flow O (C.vert (i - 1)) (C.vert i) = 1 := by
    have hpos : 0 < flow O (C.vert (i - 1)) (C.vert i) :=
      (directed_edge_iff_flow_pos O _ _).mp (C.edge_pred i)
    have hle := flow_add_flow_rev O (C.vert (i - 1)) (C.vert i)
    have hs := hsimple (C.vert (i - 1)) (C.vert i)
    omega
  have h₂ : flow O (C.vert i) (C.vert (i + 1)) = 1 := by
    have hpos : 0 < flow O (C.vert i) (C.vert (i + 1)) :=
      (directed_edge_iff_flow_pos O _ _).mp (C.edge i)
    have hle := flow_add_flow_rev O (C.vert i) (C.vert (i + 1))
    have hs := hsimple (C.vert i) (C.vert (i + 1))
    omega
  rw [h₁, h₂]

/-- A cycle reversal genuinely changes the orientation — **provided the cycle has at least
three vertices** (`1 ≤ C.len`).

The restriction is not removable, and it is the price of the widened `CFOrientation` model.
A `len = 0` cycle is a parallel class `u ⇄ v` carrying flow in both directions; `reverseCycle`
turns the whole class each way at once, i.e. it *swaps* `flow O u v` with `flow O v u`, so on
a `2`-banana oriented one edge each way it gives back exactly `O`. With three or more
vertices the first step's reverse is not itself a step of the cycle
(`DirectedCycle.not_pred_succ_zero`), so its flow really does drop to zero. -/
lemma reverseCycle_ne (O : CFOrientation G) (C : DirectedCycle O) (hlen : 1 ≤ C.len) :
    reverseCycle O C ≠ O := by
  intro heq
  have hpos : 0 < flow O (C.vert 0) (C.vert (0 + 1)) :=
    (directed_edge_iff_flow_pos O _ _).mp (C.edge 0)
  have hzero : flow (reverseCycle O C) (C.vert 0) (C.vert (0 + 1)) = 0 := by
    rw [reverseCycle, flow_reverseOn, ite_eq_left ⟨0, rfl, rfl⟩,
      ite_eq_right (C.not_pred_succ_zero hlen), add_zero]
  rw [heq] at hzero
  omega

/-! ### The fine cycle reversal

`reverseCycle` turns a whole parallel class at every step of the cycle, because `reverseOn`
sees only the vertex pair. `reverseCycleOne` turns exactly **one** edge at every step, which
is the classical cycle-reversal move of the orientation calculus. It became representable
only when `no_bidirectional` was removed from `CFOrientation`: splitting a parallel class is
precisely what that field forbade. Unlike the coarse move it preserves `indeg`, and hence
`ordiv`, with no hypothesis at all. -/

/-- The flow function of the fine cycle reversal: move one unit of flow backwards along every
step of `C`. -/
def reverseCycleOneFlow (O : CFOrientation G) (C : DirectedCycle O) : G.V × G.V → ℕ :=
  fun e =>
    flow O e.1 e.2 - (if C.pred e.1 e.2 then 1 else 0) + (if C.pred e.2 e.1 then 1 else 0)

/-- `reverseCycleOneFlow` still saturates every edge multiplicity: a step of the cycle moves
one unit from one direction to the other, and a pair traversed in *both* directions (only
possible for a `len = 0` cycle) loses and regains the same unit. -/
lemma reverseCycleOneFlow_count_preserving (O : CFOrientation G) (C : DirectedCycle O)
    (u v : G.V) :
    reverseCycleOneFlow O C (u, v) + reverseCycleOneFlow O C (v, u) = numEdges G u v := by
  have hsum := flow_add_flow_rev O u v
  by_cases h₁ : C.pred u v <;> by_cases h₂ : C.pred v u
  · have hp := C.flow_pos_of_pred h₁
    have hq := C.flow_pos_of_pred h₂
    simp only [reverseCycleOneFlow, ite_eq_left h₁, ite_eq_left h₂]
    omega
  · have hp := C.flow_pos_of_pred h₁
    simp only [reverseCycleOneFlow, ite_eq_left h₁, ite_eq_right h₂]
    omega
  · have hq := C.flow_pos_of_pred h₂
    simp only [reverseCycleOneFlow, ite_eq_left h₂, ite_eq_right h₁]
    omega
  · simp only [reverseCycleOneFlow, ite_eq_right h₁, ite_eq_right h₂]
    omega

/-- **Fine cycle reversal.** Turn one edge of each parallel class traversed by `C`. -/
def reverseCycleOne (O : CFOrientation G) (C : DirectedCycle O) : CFOrientation G :=
  orientationFromFlow (reverseCycleOneFlow O C) (reverseCycleOneFlow_count_preserving O C)

/-- The defining flow identity for `reverseCycleOne`. -/
lemma flow_reverseCycleOne (O : CFOrientation G) (C : DirectedCycle O) (u v : G.V) :
    flow (reverseCycleOne O C) u v =
      flow O u v - (if C.pred u v then 1 else 0) + (if C.pred v u then 1 else 0) :=
  flow_orientation_from_flow _ _ u v

namespace DirectedCycle

/-- **The reversed cycle is again a directed cycle**, now of `reverseCycleOne O C`. The fine
analogue of `DirectedCycle.reversed`. -/
def reversedOne {O : CFOrientation G} (C : DirectedCycle O) :
    DirectedCycle (reverseCycleOne O C) where
  len := C.len
  vert := fun j => C.vert (-j)
  vert_inj := C.vert_inj.comp neg_injective
  edge := by
    intro j
    have hstep : C.pred (C.vert (-j - 1)) (C.vert (-j)) := (C.pred_into _ (-j)).mpr rfl
    have hneg : (-(j + 1) : Fin (C.len + 2)) = -j - 1 := by abel
    rw [hneg]
    refine (directed_edge_iff_flow_pos _ _ _).mpr ?_
    rw [flow_reverseCycleOne, ite_eq_left hstep]
    split_ifs with hback
    · have := C.flow_pos_of_pred hback
      omega
    · omega

end DirectedCycle

/-- **The fine cycle reversal preserves every in-degree.** At a cycle vertex it removes one
unit of flow on the incoming step and adds one on the outgoing step; off the cycle nothing
moves. No balance hypothesis is needed, in contrast to `ordiv_reverseCycle`. -/
lemma indeg_reverseCycleOne (O : CFOrientation G) (C : DirectedCycle O) (v : G.V) :
    indeg G (reverseCycleOne O C) v = indeg G O v := by
  have key : ∀ w : G.V, (flow (reverseCycleOne O C) w v : ℤ) =
      (flow O w v : ℤ) - (if C.pred w v then 1 else 0) + (if C.pred v w then 1 else 0) := by
    intro w
    rw [flow_reverseCycleOne]
    split_ifs with h₁ h₂ h₂
    · have := C.flow_pos_of_pred h₁; omega
    · have := C.flow_pos_of_pred h₁; omega
    · omega
    · omega
  have hbal : (∑ w : G.V, (if C.pred w v then (1 : ℤ) else 0))
      = ∑ w : G.V, (if C.pred v w then (1 : ℤ) else 0) := by
    by_cases hv : ∃ i, v = C.vert i
    · obtain ⟨j, rfl⟩ := hv
      have hin : (∑ w : G.V, (if C.pred w (C.vert j) then (1 : ℤ) else 0)) = 1 :=
        (Finset.sum_eq_single (C.vert (j - 1))
          (fun b _ hb => ite_eq_right fun hc => hb ((C.pred_into b j).mp hc))
          (fun hb => absurd (Finset.mem_univ _) hb)).trans (ite_eq_left ((C.pred_into _ j).mpr rfl))
      have hout : (∑ w : G.V, (if C.pred (C.vert j) w then (1 : ℤ) else 0)) = 1 :=
        (Finset.sum_eq_single (C.vert (j + 1))
          (fun b _ hb => ite_eq_right fun hc => hb ((C.pred_outOf b j).mp hc))
          (fun hb => absurd (Finset.mem_univ _) hb)).trans
            (ite_eq_left ((C.pred_outOf _ j).mpr rfl))
      rw [hin, hout]
    · simp only [not_exists] at hv
      rw [Finset.sum_eq_zero fun w _ => ite_eq_right (C.not_pred_of_notMem hv w).1,
        Finset.sum_eq_zero fun w _ => ite_eq_right (C.not_pred_of_notMem hv w).2]
  have h : (indeg G (reverseCycleOne O C) v : ℤ) = (indeg G O v : ℤ) := by
    rw [indeg_eq_sum_flow (reverseCycleOne O C) v, indeg_eq_sum_flow O v]
    push_cast
    rw [Finset.sum_congr rfl fun w (_ : w ∈ Finset.univ) => key w, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, hbal]
    ring
  exact_mod_cast h

/-- **The fine cycle reversal preserves `ordiv` exactly, unconditionally.** This is what the
coarse `ordiv_reverseCycle` needs a balance hypothesis for. -/
theorem ordiv_reverseCycleOne (O : CFOrientation G) (C : DirectedCycle O) :
    ordiv G (reverseCycleOne O C) = ordiv G O := by
  funext v
  simp only [ordiv, indeg_reverseCycleOne]

/-- A fine cycle reversal genuinely changes the orientation, again provided the cycle has at
least three vertices. For a `len = 0` cycle the move takes one edge out of each of the two
directions of a parallel class and puts one back, so it is the identity. -/
lemma reverseCycleOne_ne (O : CFOrientation G) (C : DirectedCycle O) (hlen : 1 ≤ C.len) :
    reverseCycleOne O C ≠ O := by
  intro heq
  have hpos : 0 < flow O (C.vert 0) (C.vert (0 + 1)) :=
    (directed_edge_iff_flow_pos O _ _).mp (C.edge 0)
  have hstep : C.pred (C.vert 0) (C.vert (0 + 1)) := ⟨0, rfl, rfl⟩
  have hlt : flow (reverseCycleOne O C) (C.vert 0) (C.vert (0 + 1))
      < flow O (C.vert 0) (C.vert (0 + 1)) := by
    rw [flow_reverseCycleOne, ite_eq_left hstep, ite_eq_right (C.not_pred_succ_zero hlen)]
    omega
  rw [heq] at hlt
  omega

/-! ## 3. Acyclicity as uniqueness of the indegree function

`orientation_determined_by_indegrees` in the dependency requires *both* orientations to be
acyclic. Only one of them is really needed, and the proof of the dependency's lemma in fact
never uses the second hypothesis — but the hypothesis is in its statement, so the stronger
form is re-proved here from `not_isAcyclic_of_backward_step`.

The mathematical content: the signed set of edges on which `O` and `O'` disagree is a
circulation (it preserves every indegree), so following disagreements backwards never
terminates, which an acyclic `O` forbids. -/

/-- **Acyclic orientations are determined by their indegree function**, with acyclicity
assumed of only one of the two orientations. Strengthens
`orientation_determined_by_indegrees` (`Orientation.lean`), which assumes both. -/
theorem eq_of_indeg_eq_of_isAcyclic {O O' : CFOrientation G} (hO : isAcyclic G O)
    (h : ∀ v : G.V, indeg G O v = indeg G O' v) : O = O' := by
  -- Every pair where `O` beats `O'` has a predecessor pair where `O` beats `O'`.
  have going_up : ∀ u v : G.V, flow O' u v < flow O u v →
      ∃ w : G.V, flow O' w u < flow O w u := by
    intro u v huv
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have hstrict : ∃ w : G.V, flow O w u < flow O' w u := by
      refine ⟨v, ?_⟩
      have h1 := flow_add_flow_rev O u v
      have h2 := flow_add_flow_rev O' u v
      omega
    have hsum : indeg G O u < indeg G O' u := by
      rw [indeg_eq_sum_flow, indeg_eq_sum_flow]
      obtain ⟨w, hw⟩ := hstrict
      exact Finset.sum_lt_sum (fun i _ => hcon i) ⟨w, Finset.mem_univ w, hw⟩
    have := h u
    omega
  -- Hence there is no such pair at all: otherwise `O` has an infinite backward walk.
  have hle : ∀ u v : G.V, flow O u v ≤ flow O' u v := by
    by_contra hcon
    simp only [not_forall, not_le] at hcon
    obtain ⟨u, v, huv⟩ := hcon
    refine not_isAcyclic_of_backward_step (O := O)
      (P := fun x => ∃ y : G.V, flow O' x y < flow O x y) (fun x hx => ?_) ⟨v, huv⟩ hO
    obtain ⟨y, hy⟩ := hx
    obtain ⟨w, hw⟩ := going_up x y hy
    exact ⟨w, ⟨x, hw⟩, (directed_edge_iff_flow_pos O w x).mpr (by omega)⟩
  -- Domination in one direction plus equal indegrees forces equality.
  refine orientation_ext fun u v => ?_
  by_contra hne
  have hlt : flow O u v < flow O' u v := lt_of_le_of_ne (hle u v) hne
  have hsum : indeg G O v < indeg G O' v := by
    rw [indeg_eq_sum_flow, indeg_eq_sum_flow]
    exact Finset.sum_lt_sum (fun i _ => hle i v) ⟨u, Finset.mem_univ u, hlt⟩
  have := h v
  omega

/-- **An orientation is acyclic iff it is the unique orientation with its indegree
function** — the clean restatement of `eq_of_indeg_eq_of_isAcyclic`.

`→` is unconditional. `←` needs a hypothesis, and the hypothesis is exactly **"`O` has no
directed 2-cycle"** — strictly weaker than the simplicity hypothesis this theorem used to
carry, and not removable:

* it is *sufficient* because a non-acyclic `O` then carries a directed cycle on at least
  three vertices, and the fine cycle reversal `reverseCycleOne` produces a different
  orientation with the same in-degrees (`indeg_reverseCycleOne`, `reverseCycleOne_ne`);
* it is *necessary* because on the `3`-banana the orientation with two edges `u → v` and one
  edge `v → u` has in-degrees `(1, 2)`, and no other orientation of that graph does — the
  three edges must split `(2, 1)` — yet it is cyclic. Note that both cycle reversals are
  useless here: reversing the `2`-cycle finely takes one edge out of each direction and puts
  one back, and coarsely swaps the two counts, which changes the in-degrees.

Simplicity was the right hypothesis only while `CFOrientation.no_bidirectional` forced cycle
reversal to turn whole parallel classes; with that field gone the fine move is available and
the only obstruction left is the degenerate `2`-cycle. -/
theorem isAcyclic_iff_unique_of_indeg (O : CFOrientation G) (hno2 : ¬ HasDirectedTwoCycle O) :
    isAcyclic G O ↔ ∀ O' : CFOrientation G, (∀ v : G.V, indeg G O v = indeg G O' v) → O = O' := by
  constructor
  · intro hO O' h
    exact eq_of_indeg_eq_of_isAcyclic hO h
  · intro huniq
    by_contra hO
    obtain ⟨C⟩ := nonempty_directedCycle_of_not_isAcyclic O hO
    have hlen : 1 ≤ C.len := by
      rcases Nat.eq_zero_or_pos C.len with h | h
      · exact absurd (C.hasDirectedTwoCycle_of_len_eq_zero h) hno2
      · exact h
    exact reverseCycleOne_ne O C hlen
      (huniq (reverseCycleOne O C) fun v => (indeg_reverseCycleOne O C v).symm).symm

/-! ## 4. Cocycle (directed cut) reversal -/

/-- `W` is a **directed cut** of `O` when every edge between `W` and its complement leaves
`W`: there is no flow from outside `W` into `W`. -/
def IsDirectedCut (O : CFOrientation G) (W : Finset G.V) : Prop :=
  ∀ u v : G.V, u ∉ W → v ∈ W → flow O u v = 0

/-- **Cocycle reversal.** Turn every edge from `W` to its complement. -/
def reverseCut (O : CFOrientation G) (W : Finset G.V) : CFOrientation G :=
  reverseOn O (fun u v => u ∈ W ∧ v ∉ W)

/-- After the reversal no edge leaves `W`. -/
lemma flow_reverseCut_out (O : CFOrientation G) (W : Finset G.V) {u v : G.V}
    (hu : u ∈ W) (hv : v ∉ W) : flow (reverseCut O W) u v = 0 := by
  rw [reverseCut, flow_reverseOn, ite_eq_left ⟨hu, hv⟩, ite_eq_right fun hh => hv hh.1, add_zero]

/-- The edges that used to leave `W` now enter it. -/
lemma flow_reverseCut_in (O : CFOrientation G) (W : Finset G.V) (hcut : IsDirectedCut O W)
    {u v : G.V} (hu : u ∉ W) (hv : v ∈ W) :
    flow (reverseCut O W) u v = flow O v u := by
  rw [reverseCut, flow_reverseOn, ite_eq_right fun hh => hu hh.1, ite_eq_left ⟨hv, hu⟩,
    hcut u v hu hv, zero_add]

/-- Edges with both ends on the same side of the cut are untouched. -/
lemma flow_reverseCut_same (O : CFOrientation G) (W : Finset G.V) {u v : G.V}
    (h : u ∈ W ↔ v ∈ W) : flow (reverseCut O W) u v = flow O u v := by
  rw [reverseCut, flow_reverseOn, ite_eq_right fun hh => hh.2 (h.mp hh.1),
    ite_eq_right fun hh => hh.2 (h.mpr hh.1), add_zero]

/-- After reversing the directed cut at `W`, the complement of `W` is a directed cut. -/
lemma isDirectedCut_reverseCut (O : CFOrientation G) (W : Finset G.V) :
    IsDirectedCut (reverseCut O W) Wᶜ := by
  intro u v hu hv
  rw [Finset.mem_compl] at hv
  simp only [Finset.mem_compl, not_not] at hu
  exact flow_reverseCut_out O W hu hv

/-- Cocycle reversal is undone by reversing the complementary cut, so the move is
symmetric. -/
lemma reverseCut_reverseCut (O : CFOrientation G) (W : Finset G.V) (hcut : IsDirectedCut O W) :
    reverseCut (reverseCut O W) Wᶜ = O := by
  refine orientation_ext fun u v => ?_
  by_cases hu : u ∈ W <;> by_cases hv : v ∈ W
  · rw [flow_reverseCut_same _ _ (by simp [Finset.mem_compl, hu, hv]),
      flow_reverseCut_same _ _ (by simp [hu, hv])]
  · rw [flow_reverseCut_in _ _ (isDirectedCut_reverseCut O W)
      (by simp [Finset.mem_compl, hu]) (by simp [Finset.mem_compl, hv]),
      flow_reverseCut_in O W hcut hv hu]
  · rw [flow_reverseCut_out _ _ (by simp [Finset.mem_compl, hu]) (by simp [Finset.mem_compl, hv]),
      hcut u v hu hv]
  · rw [flow_reverseCut_same _ _ (by simp [Finset.mem_compl, hu, hv]),
      flow_reverseCut_same _ _ (by simp [hu, hv])]

/-- Any directed path of an acyclic orientation is non-repeating, packaged for lists. -/
private lemma nodup_of_isChain {O : CFOrientation G} (hO : isAcyclic G O) {l : List G.V}
    (h : List.IsChain (directedEdge G O) l) : l.Nodup := by
  cases l with
  | nil => exact List.nodup_nil
  | cons a t => exact hO ⟨a :: t, by simp, h⟩

/-- If no edge of `O'` leaves `W`, then membership in `W` is inherited along any directed
path of `O'` from its first vertex. -/
private lemma mem_of_isChain_head {O' : CFOrientation G} {W : Finset G.V}
    (hout : ∀ u v : G.V, u ∈ W → v ∉ W → flow O' u v = 0) :
    ∀ l : List G.V, List.IsChain (directedEdge G O') l →
      (∀ a ∈ l.head?, a ∈ W) → ∀ x ∈ l, x ∈ W := by
  intro l
  induction l with
  | nil => intro _ _ x hx; simp at hx
  | cons a t ih =>
    intro hchain hhead x hx
    have ha : a ∈ W := hhead a rfl
    rcases List.mem_cons.mp hx with rfl | hxt
    · exact ha
    · refine ih (List.isChain_cons.mp hchain).2 (fun b hb => ?_) x hxt
      by_contra hbW
      have hedge := (List.isChain_cons.mp hchain).1 b hb
      rw [directed_edge_iff_flow_pos] at hedge
      have := hout a b ha hbW
      omega

/-- **Cocycle reversal preserves acyclicity.** A directed path of `reverseCut O W` first
runs outside `W` and then, once it enters `W`, stays there — because after the reversal no
edge leaves `W`. Each of the two stretches lies on one side of the cut, where the reversed
orientation agrees with `O`, so each is a directed path of the acyclic `O` and is therefore
non-repeating; and the two stretches are disjoint, being on opposite sides of `W`. -/
theorem isAcyclic_reverseCut (O : CFOrientation G) (W : Finset G.V) (hO : isAcyclic G O) :
    isAcyclic G (reverseCut O W) := by
  classical
  set p : G.V → Bool := fun x => decide (x ∉ W) with hp
  have hout : ∀ u v : G.V, u ∈ W → v ∉ W → flow (reverseCut O W) u v = 0 :=
    fun u v hu hv => flow_reverseCut_out O W hu hv
  intro path
  have hchain : List.IsChain (directedEdge G (reverseCut O W)) path.vertices := path.valid_edges
  have hsplit :
      path.vertices.takeWhile p ++ path.vertices.dropWhile p = path.vertices :=
    List.takeWhile_append_dropWhile
  rw [← hsplit] at hchain
  have hc₁ := hchain.left_of_append
  have hc₂ := hchain.right_of_append
  have h₁ : ∀ x ∈ path.vertices.takeWhile p, x ∉ W := by
    intro x hx
    simpa only [hp, decide_eq_true_eq] using List.mem_takeWhile_imp hx
  have h₂ : ∀ x ∈ path.vertices.dropWhile p, x ∈ W := by
    refine mem_of_isChain_head hout _ hc₂ fun a ha => ?_
    have hnot := List.head?_dropWhile_not p path.vertices
    rw [Option.mem_def] at ha
    rw [ha] at hnot
    simpa only [hp, decide_eq_false_iff_not, not_not] using hnot
  have hc₁O : List.IsChain (directedEdge G O) (path.vertices.takeWhile p) := by
    refine List.IsChain.imp_of_mem_imp (fun a b ha hb hab => ?_) hc₁
    rw [directed_edge_iff_flow_pos] at hab ⊢
    rwa [flow_reverseCut_same O W (iff_of_false (h₁ a ha) (h₁ b hb))] at hab
  have hc₂O : List.IsChain (directedEdge G O) (path.vertices.dropWhile p) := by
    refine List.IsChain.imp_of_mem_imp (fun a b ha hb hab => ?_) hc₂
    rw [directed_edge_iff_flow_pos] at hab ⊢
    rwa [flow_reverseCut_same O W (iff_of_true (h₂ a ha) (h₂ b hb))] at hab
  change path.vertices.Nodup
  rw [← hsplit, List.nodup_append]
  refine ⟨nodup_of_isChain hO hc₁O, nodup_of_isChain hO hc₂O, fun a ha b hb hab => ?_⟩
  exact h₁ a ha (hab ▸ h₂ b hb)

/-! ## 5. The reversal equivalence and Gioan's theorem -/

/-- One **reversal move**: turn a directed cycle — finely (`reverseCycleOne`, one edge at
each step, the classical move) or coarsely (`reverseCycle`, the whole parallel class at each
step) — or turn a directed cut. Each in either direction; the relation is symmetric by
construction, which is all the `←` disjuncts are for.

Both cycle moves are included deliberately. The fine one is the move Gioan's theorem is
about, and it is the only one `gioan_reversalEquiv_of_linear_equiv` actually uses; the coarse
one is kept because it costs nothing — `isAcyclic_of_reversalStep` rules out *any* cycle
reversal at an acyclic orientation — and a larger step relation only makes an implication
*into* `ReversalEquiv` easier. Concretely, the proof of Gioan's theorem below reaches for
exactly two of the six disjuncts: the forward fine cycle reversal and the forward cut
reversal. -/
def ReversalStep (O₁ O₂ : CFOrientation G) : Prop :=
  (∃ C : DirectedCycle O₁, O₂ = reverseCycle O₁ C) ∨
  (∃ C : DirectedCycle O₂, O₁ = reverseCycle O₂ C) ∨
  (∃ C : DirectedCycle O₁, O₂ = reverseCycleOne O₁ C) ∨
  (∃ C : DirectedCycle O₂, O₁ = reverseCycleOne O₂ C) ∨
  (∃ W : Finset G.V, IsDirectedCut O₁ W ∧ O₂ = reverseCut O₁ W) ∨
  (∃ W : Finset G.V, IsDirectedCut O₂ W ∧ O₁ = reverseCut O₂ W)

/-- Reversal moves are symmetric. -/
lemma ReversalStep.symm {O₁ O₂ : CFOrientation G} (h : ReversalStep O₁ O₂) :
    ReversalStep O₂ O₁ := by
  rcases h with h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

/-- Two orientations are **reversal equivalent** when a finite sequence of cycle and cocycle
reversals turns one into the other. -/
def ReversalEquiv (O₁ O₂ : CFOrientation G) : Prop :=
  Relation.ReflTransGen (ReversalStep (G := G)) O₁ O₂

@[refl] lemma ReversalEquiv.refl (O : CFOrientation G) : ReversalEquiv O O :=
  Relation.ReflTransGen.refl

lemma ReversalEquiv.symm {O₁ O₂ : CFOrientation G} (h : ReversalEquiv O₁ O₂) :
    ReversalEquiv O₂ O₁ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head hstep.symm ih

lemma ReversalEquiv.trans {O₁ O₂ O₃ : CFOrientation G} (h₁ : ReversalEquiv O₁ O₂)
    (h₂ : ReversalEquiv O₂ O₃) : ReversalEquiv O₁ O₃ :=
  Relation.ReflTransGen.trans h₁ h₂

/-- **A single reversal move out of an acyclic orientation lands on an acyclic
orientation.** A cycle reversal of either kind is simply unavailable at an acyclic
orientation: in the forward direction there is no directed cycle to turn, and in the backward
direction the reversed cycle (`DirectedCycle.reversed`, `DirectedCycle.reversedOne`) would be
a directed cycle of the acyclic orientation we started from. A cocycle reversal preserves
acyclicity by
`isAcyclic_reverseCut`, in either direction because `reverseCut_reverseCut` exhibits the
inverse move as another cocycle reversal. -/
theorem isAcyclic_of_reversalStep {O₁ O₂ : CFOrientation G} (h : ReversalStep O₁ O₂)
    (hO₁ : isAcyclic G O₁) : isAcyclic G O₂ := by
  rcases h with ⟨C, -⟩ | ⟨C, hEq⟩ | ⟨C, -⟩ | ⟨C, hEq⟩ | ⟨W, -, hEq⟩ | ⟨W, hcut, hEq⟩
  · exact absurd hO₁ (not_isAcyclic_of_directedCycle O₁ C)
  · subst hEq
    exact absurd hO₁ (not_isAcyclic_of_directedCycle _ C.reversed)
  · exact absurd hO₁ (not_isAcyclic_of_directedCycle O₁ C)
  · subst hEq
    exact absurd hO₁ (not_isAcyclic_of_directedCycle _ C.reversedOne)
  · subst hEq
    exact isAcyclic_reverseCut O₁ W hO₁
  · subst hEq
    rw [← reverseCut_reverseCut O₂ W hcut]
    exact isAcyclic_reverseCut _ Wᶜ hO₁

/-- **The reversal class of an acyclic orientation consists of acyclic orientations.** -/
theorem isAcyclic_of_reversalEquiv {O₁ O₂ : CFOrientation G} (h : ReversalEquiv O₁ O₂)
    (hO₁ : isAcyclic G O₁) : isAcyclic G O₂ := by
  induction h with
  | refl => exact hO₁
  | tail _ hstep ih => exact isAcyclic_of_reversalStep hstep ih

/-! ### The signed difference of two orientations

Everything below reads the pair `(O₁, O₂)` through one object: the antisymmetric integer
vector `diffFlow O₁ O₂` on ordered vertex pairs, which is the "signed edge set on which the
two orientations disagree" of Gioan's argument. Antisymmetry (`diffFlow_antisymm`) is the
`count_preserving` field, and `sum_diffFlow` says its divergence is the in-degree
difference. -/

/-- The **signed disagreement** of two orientations on the parallel class `(u, v)`: how many
more edges `O₁` sends from `u` to `v` than `O₂` does. -/
def diffFlow (O₁ O₂ : CFOrientation G) (u v : G.V) : ℤ :=
  (flow O₁ u v : ℤ) - (flow O₂ u v : ℤ)

/-- The signed disagreement is antisymmetric: both orientations saturate the same parallel
class, so a surplus one way is a deficit the other. -/
lemma diffFlow_antisymm (O₁ O₂ : CFOrientation G) (u v : G.V) :
    diffFlow O₁ O₂ u v = - diffFlow O₁ O₂ v u := by
  have h₁ := flow_add_flow_rev O₁ u v
  have h₂ := flow_add_flow_rev O₂ u v
  simp only [diffFlow]
  omega

/-- The divergence of the signed disagreement is the in-degree difference. -/
lemma sum_diffFlow (O₁ O₂ : CFOrientation G) (v : G.V) :
    ∑ w : G.V, diffFlow O₁ O₂ w v = (indeg G O₁ v : ℤ) - (indeg G O₂ v : ℤ) := by
  have h₁ : (indeg G O₁ v : ℤ) = ∑ w : G.V, (flow O₁ w v : ℤ) := by
    rw [indeg_eq_sum_flow O₁ v]; push_cast; ring
  have h₂ : (indeg G O₂ v : ℤ) = ∑ w : G.V, (flow O₂ w v : ℤ) := by
    rw [indeg_eq_sum_flow O₂ v]; push_cast; ring
  simp only [diffFlow]
  rw [h₁, h₂, ← Finset.sum_sub_distrib]

/-- Two orientations with the same flow function are reversal equivalent, trivially. -/
lemma reversalEquiv_of_flow_eq {O₁ O₂ : CFOrientation G}
    (h : ∀ u v : G.V, flow O₁ u v = flow O₂ u v) : ReversalEquiv O₁ O₂ := by
  have hEq := orientation_ext h
  subst hEq
  exact ReversalEquiv.refl _

/-! ### Step 1 of Gioan's theorem: equal in-degrees

This is where the *fine* cycle move earns its place. If `O₁` and `O₂` have the same in-degree
function then `diffFlow O₁ O₂` is a nonzero circulation, so following the pairs where `O₁`
beats `O₂` never gets stuck (`nonempty_relCycle_of_forward_step`). The resulting cycle is a
directed cycle of `O₁`, and reversing it *finely* moves exactly one unit of flow off each of
its steps: in-degrees are untouched (`indeg_reverseCycleOne`) and the disagreement strictly
shrinks. -/

private lemma reversalEquiv_of_indeg_eq_aux (n : ℕ) : ∀ O₁ O₂ : CFOrientation G,
    (∀ v : G.V, indeg G O₁ v = indeg G O₂ v) →
    (∑ p : G.V × G.V, (diffFlow O₁ O₂ p.1 p.2).toNat) ≤ n →
    ReversalEquiv O₁ O₂ := by
  induction n with
  | zero =>
    intro O₁ O₂ _ hN
    refine reversalEquiv_of_flow_eq fun u v => ?_
    have hz : ∀ x y : G.V, (diffFlow O₁ O₂ x y).toNat = 0 := by
      intro x y
      have := Finset.single_le_sum
        (f := fun p : G.V × G.V => (diffFlow O₁ O₂ p.1 p.2).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (x, y))
      dsimp only at this
      omega
    have h1 := hz u v
    have h2 := hz v u
    have h3 := flow_add_flow_rev O₁ u v
    have h4 := flow_add_flow_rev O₂ u v
    simp only [diffFlow, Int.toNat_eq_zero] at h1 h2
    omega
  | succ n ih =>
    intro O₁ O₂ hindeg hN
    by_cases hEq : ∀ u v : G.V, flow O₁ u v = flow O₂ u v
    · exact reversalEquiv_of_flow_eq hEq
    push Not at hEq
    obtain ⟨u₀, v₀, hne⟩ := hEq
    set R : G.V → G.V → Prop := fun u v => flow O₂ u v < flow O₁ u v with hR
    have hzero : ∀ v : G.V, ∑ w : G.V, diffFlow O₁ O₂ w v = 0 := by
      intro v
      rw [sum_diffFlow, hindeg v]
      ring
    have hirr : ∀ v : G.V, ¬ R v v := by
      intro v hv
      have h := flow_add_flow_rev O₁ v v
      rw [num_edges_self_zero] at h
      simp only [hR] at hv
      omega
    have hstart : ∃ u v : G.V, R u v := by
      rcases Nat.lt_or_ge (flow O₂ u₀ v₀) (flow O₁ u₀ v₀) with h | h
      · exact ⟨u₀, v₀, h⟩
      · refine ⟨v₀, u₀, ?_⟩
        have h₁ := flow_add_flow_rev O₁ u₀ v₀
        have h₂ := flow_add_flow_rev O₂ u₀ v₀
        simp only [hR]
        omega
    obtain ⟨u₁, v₁, hR₁⟩ := hstart
    -- Kirchhoff: a pair where `O₁` wins is followed by another such pair.
    have hforward : ∀ v : G.V, (∃ u, R u v) → ∃ w, (∃ u, R u w) ∧ R v w := by
      intro v hv
      obtain ⟨u, hu⟩ := hv
      by_contra hcon
      push Not at hcon
      have hno : ∀ w : G.V, ¬ R v w := fun w h => hcon w ⟨v, h⟩ h
      have hnonneg : ∀ w : G.V, 0 ≤ diffFlow O₁ O₂ w v := by
        intro w
        have hw := hno w
        simp only [hR, not_lt] at hw
        have := diffFlow_antisymm O₁ O₂ w v
        simp only [diffFlow] at this ⊢
        omega
      have hpos : 0 < diffFlow O₁ O₂ u v := by
        simp only [hR] at hu
        simp only [diffFlow]
        omega
      have hsum : 0 < ∑ w : G.V, diffFlow O₁ O₂ w v :=
        Finset.sum_pos' (fun w _ => hnonneg w) ⟨u, Finset.mem_univ u, hpos⟩
      rw [hzero v] at hsum
      exact lt_irrefl 0 hsum
    obtain ⟨C⟩ := nonempty_relCycle_of_forward_step hirr hforward ⟨u₁, hR₁⟩
    have hedge : ∀ u v : G.V, R u v → directedEdge G O₁ u v := by
      intro u v h
      simp only [hR] at h
      exact (directed_edge_iff_flow_pos O₁ u v).mpr (by omega)
    set D : DirectedCycle O₁ := C.toDirectedCycle hedge with hD
    have hpredR : ∀ u v : G.V, D.pred u v → R u v := by
      rintro u v ⟨i, rfl, rfl⟩
      exact C.edge i
    have hnotboth : ∀ u v : G.V, D.pred u v → ¬ D.pred v u := by
      intro u v h₁ h₂
      have k₁ := hpredR u v h₁
      have k₂ := hpredR v u h₂
      have e₁ := flow_add_flow_rev O₁ u v
      have e₂ := flow_add_flow_rev O₂ u v
      simp only [hR] at k₁ k₂
      omega
    have hflow : ∀ u v : G.V, (flow (reverseCycleOne O₁ D) u v : ℤ)
        = (flow O₁ u v : ℤ) - (if D.pred u v then 1 else 0)
            + (if D.pred v u then 1 else 0) := by
      intro u v
      rw [flow_reverseCycleOne]
      split_ifs with h₁ h₂ h₂
      · exact absurd h₂ (hnotboth u v h₁)
      · have := D.flow_pos_of_pred h₁; omega
      · omega
      · omega
    have hle : ∀ p : G.V × G.V,
        (diffFlow (reverseCycleOne O₁ D) O₂ p.1 p.2).toNat
          ≤ (diffFlow O₁ O₂ p.1 p.2).toNat := by
      rintro ⟨u, v⟩
      have h := hflow u v
      simp only [diffFlow]
      by_cases h₁ : D.pred u v
      · have hp := hpredR u v h₁
        simp only [hR] at hp
        rw [ite_eq_left h₁, ite_eq_right (hnotboth u v h₁)] at h
        omega
      · by_cases h₂ : D.pred v u
        · have hp := hpredR v u h₂
          have e₁ := flow_add_flow_rev O₁ u v
          have e₂ := flow_add_flow_rev O₂ u v
          simp only [hR] at hp
          rw [ite_eq_right h₁, ite_eq_left h₂] at h
          omega
        · rw [ite_eq_right h₁, ite_eq_right h₂] at h
          omega
    have hstrict : (diffFlow (reverseCycleOne O₁ D) O₂ (D.vert 0) (D.vert (0 + 1))).toNat
        < (diffFlow O₁ O₂ (D.vert 0) (D.vert (0 + 1))).toNat := by
      have h₁ : D.pred (D.vert 0) (D.vert (0 + 1)) := ⟨0, rfl, rfl⟩
      have hp := hpredR _ _ h₁
      have h := hflow (D.vert 0) (D.vert (0 + 1))
      rw [ite_eq_left h₁, ite_eq_right (hnotboth _ _ h₁)] at h
      simp only [hR] at hp
      simp only [diffFlow]
      omega
    have hsum : (∑ p : G.V × G.V, (diffFlow (reverseCycleOne O₁ D) O₂ p.1 p.2).toNat)
        < ∑ p : G.V × G.V, (diffFlow O₁ O₂ p.1 p.2).toNat :=
      Finset.sum_lt_sum (fun p _ => hle p)
        ⟨(D.vert 0, D.vert (0 + 1)), Finset.mem_univ _, hstrict⟩
    refine Relation.ReflTransGen.head (Or.inr (Or.inr (Or.inl ⟨D, rfl⟩)))
      (ih (reverseCycleOne O₁ D) O₂ (fun v => ?_) (by omega))
    rw [indeg_reverseCycleOne]
    exact hindeg v

/-- **Orientations with the same in-degree function are reversal equivalent**, by fine cycle
reversals alone.

This is the `σ = 0` case of Gioan's theorem, and it is the exact analogue of
`eq_of_indeg_eq_of_isAcyclic` without the acyclicity hypothesis: instead of forcing the two
orientations to coincide, the disagreement is peeled off one directed cycle at a time. -/
theorem reversalEquiv_of_indeg_eq {O₁ O₂ : CFOrientation G}
    (h : ∀ v : G.V, indeg G O₁ v = indeg G O₂ v) : ReversalEquiv O₁ O₂ :=
  reversalEquiv_of_indeg_eq_aux _ O₁ O₂ h le_rfl

/-! ### Step 2 of Gioan's theorem: the cut part

Write `d = indeg O₁ − indeg O₂`. Linear equivalence of the two orientation divisors says
`d = ∂∂ᵀψ` for an integer potential `ψ`, i.e. `d v = ∑ u (ψ u − ψ v) · numEdges v u`. The
whole of the cut half of Gioan's argument is then the following observation, which needs no
decomposition theory at all:

> Let `W` be the set where `ψ` attains its minimum. Then **every** edge between `W` and its
> complement points *into* `W` under `O₁`.

Indeed for `v ∈ W` every summand of `d v` is non-negative and the ones at `u ∉ W` are at
least `numEdges v u`, so `∑_{v ∈ W} d v ≥ e(W, Wᶜ)`. On the other hand the disagreement of
`O₁` and `O₂` inside `W` cancels by antisymmetry, so `∑_{v ∈ W} d v` is exactly
`(inflow into W under O₁) − (inflow into W under O₂)`, which is at most `e(W, Wᶜ)`. The two
bounds pin both quantities: the second inflow is `0` and the first is everything.

So `Wᶜ` is a directed cut of `O₁` and may be reversed. The reversal replaces `ψ` by
`ψ + χ_W`, which raises the minimum by one and leaves the maximum alone, so the *spread* of
the potential strictly drops and the induction is on that. -/

/-- **The minimum level set of the potential is a directed cut, already correctly oriented.**
See the section header for the two-inequality squeeze that proves it. -/
private lemma isDirectedCut_compl_of_min (O₁ O₂ : CFOrientation G) (ψ : G.V → ℤ) (m : ℤ)
    (hd : ∀ v : G.V, (indeg G O₁ v : ℤ) - (indeg G O₂ v : ℤ)
      = ∑ u : G.V, (ψ u - ψ v) * (numEdges G v u : ℤ))
    (hmin : ∀ v : G.V, m ≤ ψ v) (W : Finset G.V) (hW : ∀ v : G.V, v ∈ W ↔ ψ v = m) :
    IsDirectedCut O₁ Wᶜ := by
  classical
  have hWc : ∀ v : G.V, v ∈ Wᶜ ↔ m + 1 ≤ ψ v := by
    intro v
    rw [Finset.mem_compl, hW]
    have := hmin v
    omega
  -- (1) Inside `W` the disagreement cancels: an antisymmetric matrix has zero total.
  have hinner : ∑ v ∈ W, ∑ w ∈ W, diffFlow O₁ O₂ w v = 0 := by
    have h1 : ∑ v ∈ W, ∑ w ∈ W, diffFlow O₁ O₂ w v
        = ∑ v ∈ W, ∑ w ∈ W, diffFlow O₁ O₂ v w := Finset.sum_comm
    have h2 : ∑ v ∈ W, ∑ w ∈ W, diffFlow O₁ O₂ v w
        = ∑ v ∈ W, ∑ w ∈ W, -diffFlow O₁ O₂ w v :=
      Finset.sum_congr rfl fun v _ =>
        Finset.sum_congr rfl fun w _ => diffFlow_antisymm O₁ O₂ v w
    have h3 : ∑ v ∈ W, ∑ w ∈ W, -diffFlow O₁ O₂ w v
        = -∑ v ∈ W, ∑ w ∈ W, diffFlow O₁ O₂ w v := by
      simp only [Finset.sum_neg_distrib]
    linarith [h1.trans (h2.trans h3)]
  -- (2) so the in-degree difference over `W` is the difference of the two inflows.
  have hcross : ∑ v ∈ W, ((indeg G O₁ v : ℤ) - (indeg G O₂ v : ℤ))
      = ∑ v ∈ W, ∑ w ∈ Wᶜ, diffFlow O₁ O₂ w v := by
    have hsplit : ∀ v : G.V, ((indeg G O₁ v : ℤ) - (indeg G O₂ v : ℤ))
        = (∑ w ∈ W, diffFlow O₁ O₂ w v) + ∑ w ∈ Wᶜ, diffFlow O₁ O₂ w v := by
      intro v
      rw [← sum_diffFlow]
      exact (Finset.sum_add_sum_compl W _).symm
    rw [Finset.sum_congr rfl fun v (_ : v ∈ W) => hsplit v, Finset.sum_add_distrib, hinner,
      zero_add]
  -- (3) the minimality of `ψ` on `W` bounds that difference below by the whole cut.
  have hlow : ∑ v ∈ W, ∑ u ∈ Wᶜ, (numEdges G v u : ℤ)
      ≤ ∑ v ∈ W, ((indeg G O₁ v : ℤ) - (indeg G O₂ v : ℤ)) := by
    refine Finset.sum_le_sum fun v hv => ?_
    rw [hd v, ← Finset.sum_add_sum_compl W fun u => (ψ u - ψ v) * (numEdges G v u : ℤ)]
    have hz : ∑ u ∈ W, (ψ u - ψ v) * (numEdges G v u : ℤ) = 0 :=
      Finset.sum_eq_zero fun u hu => by rw [(hW u).mp hu, (hW v).mp hv, sub_self, zero_mul]
    have hge : ∑ u ∈ Wᶜ, (numEdges G v u : ℤ)
        ≤ ∑ u ∈ Wᶜ, (ψ u - ψ v) * (numEdges G v u : ℤ) := by
      refine Finset.sum_le_sum fun u hu => ?_
      have h1 : m + 1 ≤ ψ u := (hWc u).mp hu
      have h2 : ψ v = m := (hW v).mp hv
      have h3 : (0 : ℤ) ≤ (numEdges G v u : ℤ) := Int.natCast_nonneg _
      nlinarith
    linarith
  -- (4) the squeeze.
  have hPQ : ∑ v ∈ W, ∑ w ∈ Wᶜ, diffFlow O₁ O₂ w v
      = (∑ v ∈ W, ∑ w ∈ Wᶜ, (flow O₁ w v : ℤ))
        - ∑ v ∈ W, ∑ w ∈ Wᶜ, (flow O₂ w v : ℤ) := by
    simp only [diffFlow, Finset.sum_sub_distrib]
  have hPS : (∑ v ∈ W, ∑ w ∈ Wᶜ, (flow O₁ w v : ℤ))
      + (∑ v ∈ W, ∑ w ∈ Wᶜ, (flow O₁ v w : ℤ))
      = ∑ v ∈ W, ∑ u ∈ Wᶜ, (numEdges G v u : ℤ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    have h := flow_add_flow_rev O₁ w v
    have hs := num_edges_symmetric G w v
    omega
  have hQnn : 0 ≤ ∑ v ∈ W, ∑ w ∈ Wᶜ, (flow O₂ w v : ℤ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have hSnn : 0 ≤ ∑ v ∈ W, ∑ w ∈ Wᶜ, (flow O₁ v w : ℤ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have hSzero : ∑ v ∈ W, ∑ w ∈ Wᶜ, (flow O₁ v w : ℤ) = 0 := by
    rw [hcross, hPQ] at hlow
    linarith
  -- (5) a sum of non-negative terms vanishing means every edge out of `W` is absent.
  intro u v hu hv
  simp only [Finset.mem_compl, not_not] at hu
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _)).mp hSzero u hu
  have hlast := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Int.natCast_nonneg _)).mp hterm v hv
  exact_mod_cast hlast

/-- **The in-degree bookkeeping of a cut reversal**, in the exact shape the induction wants:
reversing the directed cut `Wᶜ` changes the in-degree function by the principal divisor of
the `{0,1}`-firing script `χ_W`. -/
private lemma indeg_reverseCut_compl (O : CFOrientation G) (W : Finset G.V)
    (hcut : IsDirectedCut O Wᶜ) (v : G.V) :
    (indeg G (reverseCut O Wᶜ) v : ℤ) = (indeg G O v : ℤ)
      + ∑ u : G.V, ((if u ∈ W then (1 : ℤ) else 0) - (if v ∈ W then (1 : ℤ) else 0))
          * (numEdges G v u : ℤ) := by
  classical
  have hout : v ∈ W → ∀ w : G.V, w ∉ W → flow O v w = 0 := fun h1 w h2 =>
    hcut v w (by simp only [Finset.mem_compl, not_not]; exact h1) (Finset.mem_compl.mpr h2)
  have hin : v ∉ W → ∀ w : G.V, w ∈ W → flow O w v = 0 := fun h1 w h2 =>
    hcut w v (by simp only [Finset.mem_compl, not_not]; exact h2) (Finset.mem_compl.mpr h1)
  have hterm : ∀ w : G.V,
      ((if w ∈ W then (1 : ℤ) else 0) - (if v ∈ W then (1 : ℤ) else 0))
          * (numEdges G v w : ℤ)
        = -(if (w ∈ Wᶜ ∧ v ∉ Wᶜ) then (flow O w v : ℤ) else 0)
            + (if (v ∈ Wᶜ ∧ w ∉ Wᶜ) then (flow O v w : ℤ) else 0) := by
    intro w
    have hsum := flow_add_flow_rev O v w
    have hsum' := flow_add_flow_rev O w v
    have hsym := num_edges_symmetric G v w
    by_cases hvW : v ∈ W <;> by_cases hwW : w ∈ W
    · rw [ite_eq_left hwW, ite_eq_left hvW,
        ite_eq_right (fun hc => (Finset.mem_compl.mp hc.1) hwW),
        ite_eq_right (fun hc => (Finset.mem_compl.mp hc.1) hvW)]
      ring
    · rw [ite_eq_right hwW, ite_eq_left hvW,
        ite_eq_left ⟨Finset.mem_compl.mpr hwW, by simp only [Finset.mem_compl, not_not]; exact hvW⟩,
        ite_eq_right (fun hc => (Finset.mem_compl.mp hc.1) hvW)]
      have := hout hvW w hwW
      push_cast
      omega
    · rw [ite_eq_left hwW, ite_eq_right hvW,
        ite_eq_right (fun hc => (Finset.mem_compl.mp hc.1) hwW),
        ite_eq_left ⟨Finset.mem_compl.mpr hvW, by simp only [Finset.mem_compl, not_not]; exact hwW⟩]
      have := hin hvW w hwW
      push_cast
      omega
    · rw [ite_eq_right hwW, ite_eq_right hvW,
        ite_eq_right (fun hc => hc.2 (Finset.mem_compl.mpr hvW)),
        ite_eq_right (fun hc => hc.2 (Finset.mem_compl.mpr hwW))]
      ring
  rw [reverseCut, indeg_reverseOn,
    Finset.sum_congr rfl fun u (_ : u ∈ Finset.univ) => hterm u,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

/-- **The cut induction.** `ψ` is a potential realising the in-degree difference, and `n`
bounds its spread; each step reverses the directed cut at the minimum level set of `ψ`,
which raises the minimum by one and so lowers the spread. -/
private lemma reversalEquiv_of_potential (n : ℕ) :
    ∀ (O₁ O₂ : CFOrientation G) (ψ : G.V → ℤ),
      (∀ v : G.V, (indeg G O₁ v : ℤ) - (indeg G O₂ v : ℤ)
        = ∑ u : G.V, (ψ u - ψ v) * (numEdges G v u : ℤ)) →
      (∀ v w : G.V, ψ v - ψ w ≤ (n : ℤ)) →
      ReversalEquiv O₁ O₂ := by
  classical
  induction n with
  | zero =>
    intro O₁ O₂ ψ hd hsp
    refine reversalEquiv_of_indeg_eq fun v => ?_
    have hc : ∀ u : G.V, ψ u = ψ v := by
      intro u
      have h1 := hsp u v
      have h2 := hsp v u
      push_cast at h1 h2
      omega
    have hzero : ∑ u : G.V, (ψ u - ψ v) * (numEdges G v u : ℤ) = 0 :=
      Finset.sum_eq_zero fun u _ => by rw [hc u, sub_self, zero_mul]
    have hv := hd v
    rw [hzero] at hv
    omega
  | succ n ih =>
    intro O₁ O₂ ψ hd hsp
    obtain ⟨v₀, -, hmin0⟩ := Finset.exists_min_image (Finset.univ : Finset G.V) ψ
      ⟨Classical.arbitrary G.V, Finset.mem_univ _⟩
    have hmin : ∀ v : G.V, ψ v₀ ≤ ψ v := fun v => hmin0 v (Finset.mem_univ v)
    obtain ⟨W, hW⟩ : ∃ W : Finset G.V, ∀ v : G.V, v ∈ W ↔ ψ v = ψ v₀ :=
      ⟨Finset.univ.filter fun v => ψ v = ψ v₀, fun v => by simp⟩
    by_cases hall : ∀ v : G.V, v ∈ W
    · -- `ψ` is constant, so the two in-degree functions already agree.
      refine reversalEquiv_of_indeg_eq fun v => ?_
      have hzero : ∑ u : G.V, (ψ u - ψ v) * (numEdges G v u : ℤ) = 0 :=
        Finset.sum_eq_zero fun u _ => by
          rw [(hW u).mp (hall u), (hW v).mp (hall v), sub_self, zero_mul]
      have hv := hd v
      rw [hzero] at hv
      omega
    · push Not at hall
      obtain ⟨v₁, hv₁⟩ := hall
      have hcut := isDirectedCut_compl_of_min O₁ O₂ ψ (ψ v₀) hd hmin W hW
      have hstep : ReversalStep O₁ (reverseCut O₁ Wᶜ) :=
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Wᶜ, hcut, rfl⟩))))
      obtain ⟨ψ', hψ'⟩ : ∃ ψ' : G.V → ℤ,
          ∀ x : G.V, ψ' x = ψ x + (if x ∈ W then (1 : ℤ) else 0) := ⟨_, fun _ => rfl⟩
      have hb1 : ∀ x : G.V, x ∈ W → ψ x = ψ v₀ := fun x h => (hW x).mp h
      have hb2 : ∀ x : G.V, x ∉ W → ψ v₀ + 1 ≤ ψ x := by
        intro x h
        have h1 := hmin x
        have h2 : ψ x ≠ ψ v₀ := fun heq => h ((hW x).mpr heq)
        omega
      refine Relation.ReflTransGen.head hstep (ih (reverseCut O₁ Wᶜ) O₂ ψ' (fun v => ?_)
        (fun v w => ?_))
      · rw [indeg_reverseCut_compl O₁ W hcut v]
        have hsplit : ∑ u : G.V, (ψ' u - ψ' v) * (numEdges G v u : ℤ)
            = (∑ u : G.V, (ψ u - ψ v) * (numEdges G v u : ℤ))
              + ∑ u : G.V, ((if u ∈ W then (1 : ℤ) else 0)
                  - (if v ∈ W then (1 : ℤ) else 0)) * (numEdges G v u : ℤ) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun u _ => by rw [hψ' u, hψ' v]; ring
        rw [hsplit, ← hd v]
        ring
      · rw [hψ' v, hψ' w]
        have hsv := hsp v v₀
        push_cast at hsv ⊢
        by_cases hvW : v ∈ W
        · by_cases hwW : w ∈ W
          · rw [ite_eq_left hvW, ite_eq_left hwW, hb1 v hvW, hb1 w hwW]
            omega
          · rw [ite_eq_left hvW, ite_eq_right hwW, hb1 v hvW]
            have := hb2 w hwW
            omega
        · by_cases hwW : w ∈ W
          · rw [ite_eq_right hvW, ite_eq_left hwW, hb1 w hwW]
            omega
          · rw [ite_eq_right hvW, ite_eq_right hwW]
            have := hb2 w hwW
            omega

/-- **Gioan's theorem, one direction:** orientations with linearly
equivalent orientation divisors are connected by cycle and cocycle reversals.

Reference: E. Gioan, *Enumerating degree sequences in digraphs and a cycle–cocycle reversing
system*, European J. Combin. 28 (2007) 1351–1366, where the cycle–cocycle reversing system
is introduced and its classes are identified with the classes of `D(𝒪)` modulo linear
equivalence. For the related existence of an orientation divisor in every degree-`g-1`
class, see An–Baker–Kuperberg–Shokrieh, Theorem 4.10 of
[arXiv:1304.4259v2](https://arxiv.org/pdf/1304.4259v2).

**The proof, in two halves.** `linearEquiv` hands over a firing script `σ` with
`ordiv 𝒪₂ − ordiv 𝒪₁ = prin σ`, i.e. a potential `ψ = −σ` with
`indeg 𝒪₁ − indeg 𝒪₂ = ∂∂ᵀψ` pointwise. The induction is on the **spread**
`max ψ − min ψ`, a natural number because `G.V` is finite.

* **Spread `0`** — `ψ` constant, so the two in-degree functions agree, and
  `reversalEquiv_of_indeg_eq` finishes with fine cycle reversals alone: the signed
  disagreement `diffFlow` is then a circulation, following its positive support never gets
  stuck, and each directed cycle so found can be reversed one edge at a time, preserving
  in-degrees (`indeg_reverseCycleOne`) and strictly shrinking the disagreement.
* **Spread positive** — `isDirectedCut_compl_of_min` shows that the complement of the
  minimum level set `W` of `ψ` is *already* a directed cut of `𝒪₁`, so it may be reversed;
  `indeg_reverseCut_compl` identifies the effect on in-degrees as `prin χ_W`, which replaces
  `ψ` by `ψ + χ_W` and drops the spread by exactly one.

Notably no cycle/cut decomposition of `ℤ^E` is needed.  It is replaced by the observation in
`isDirectedCut_compl_of_min`, whose proof is two counting inequalities that squeeze each
other. `eq_of_indeg_eq_of_isAcyclic` above is the degenerate case `σ = 0` with `𝒪` acyclic.

Reference: E. Gioan, *Enumerating degree sequences in digraphs and a cycle–cocycle reversing
system*, European J. Combin. 28 (2007) 1351–1366. The proof here is not Gioan's.

**Model note (2026-08-20).** This used to carry a caveat saying the classical proof does not
transcribe, because a `CFOrientation` cycle reversal had to turn a whole parallel class. That
caveat is gone: `CFOrientation` is now an arbitrary edge-level orientation, and
`ReversalStep` includes the *fine* move `reverseCycleOne`, which turns a single edge at each
step and is exactly the move Gioan's system is built from. So on an arbitrary multigraph this
is now literally Gioan's theorem, hypothesis-free — in particular no simplicity and no
connectivity.

The converse implication is *not* stated, and is false as long as the coarse move is a legal
step: cocycle reversal preserves the class of `ordiv` (it changes it by the firing vector of
`W`) and so does the fine cycle reversal (`ordiv_reverseCycleOne`), but the coarse one does
not in general. -/
theorem gioan_reversalEquiv_of_linear_equiv {O₁ O₂ : CFOrientation G}
    (h : linearEquiv G (ordiv G O₁) (ordiv G O₂)) :
    ReversalEquiv O₁ O₂ := by
  classical
  have hmem : ordiv G O₂ - ordiv G O₁ ∈ principalDivisors G := h
  obtain ⟨σ, hσ⟩ := (principal_iff_eq_prin G _).mp hmem
  -- `ψ = -σ` is the potential of the in-degree difference `indeg O₁ - indeg O₂`.
  have hd : ∀ v : G.V, (indeg G O₁ v : ℤ) - (indeg G O₂ v : ℤ)
      = ∑ u : G.V, ((-σ u) - (-σ v)) * (numEdges G v u : ℤ) := by
    intro v
    have hv := congrFun hσ v
    have hv' : (indeg G O₂ v : ℤ) - 1 - ((indeg G O₁ v : ℤ) - 1)
        = ∑ u : G.V, (σ u - σ v) * (numEdges G v u : ℤ) := hv
    have hneg : ∑ u : G.V, ((-σ u) - (-σ v)) * (numEdges G v u : ℤ)
        = -∑ u : G.V, (σ u - σ v) * (numEdges G v u : ℤ) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [hneg, ← hv']
    ring
  -- The spread of `ψ` is bounded, since `G.V` is finite.
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image (Finset.univ : Finset G.V) (fun v => -σ v)
    ⟨Classical.arbitrary G.V, Finset.mem_univ _⟩
  obtain ⟨b, -, hb⟩ := Finset.exists_min_image (Finset.univ : Finset G.V) (fun v => -σ v)
    ⟨Classical.arbitrary G.V, Finset.mem_univ _⟩
  refine reversalEquiv_of_potential ((-σ a - -σ b).toNat) O₁ O₂ (fun v => -σ v) hd
    fun v w => ?_
  have h1 := ha v (Finset.mem_univ v)
  have h2 := hb w (Finset.mem_univ w)
  omega

/-! ## 6. Winnability of divisors of cyclic orientations -/

/-- **An orientation with a directed cycle has winnable `ordiv`.**

If `ordiv G O` were unwinnable then, having degree `genus G - 1`
(`degree_ordiv`), it would by `unwinnable_iff_exists_acyclic_ordiv` be linearly equivalent to
`ordiv G O'` for some *acyclic* `O'`; Gioan then puts `O` and `O'` in one reversal class, and
`isAcyclic_of_reversalEquiv` propagates acyclicity from `O'` to `O`, contradicting the
hypothesis. -/
theorem winnable_ordiv_of_not_isAcyclic {G : CFGraph} (h_conn : graphConnected G)
    (O : CFOrientation G) (hO : ¬ isAcyclic G O) : winnable G (ordiv G O) := by
  by_contra hw
  obtain ⟨O', hO'acyc, hequiv⟩ :=
    (unwinnable_iff_exists_acyclic_ordiv h_conn (ordiv G O) (degree_ordiv O)).mp hw
  exact hO (isAcyclic_of_reversalEquiv
    (gioan_reversalEquiv_of_linear_equiv hequiv).symm hO'acyc)

/-- The contrapositive: an orientation whose divisor is
unwinnable is acyclic. Together with `ordiv_unwinnable` (`Orientation.lean`) this makes
`isAcyclic G O ↔ ¬ winnable G (ordiv G O)` — see `isAcyclic_iff_not_winnable_ordiv`. -/
theorem isAcyclic_of_not_winnable_ordiv {G : CFGraph} (h_conn : graphConnected G)
    (O : CFOrientation G) (hw : ¬ winnable G (ordiv G O)) : isAcyclic G O := by
  by_contra hO
  exact hw (winnable_ordiv_of_not_isAcyclic h_conn O hO)

/-- **Orientation criterion.** An orientation is acyclic exactly
when its divisor is unwinnable. -/
theorem isAcyclic_iff_not_winnable_ordiv {G : CFGraph} (h_conn : graphConnected G)
    (O : CFOrientation G) : isAcyclic G O ↔ ¬ winnable G (ordiv G O) :=
  ⟨ordiv_unwinnable G O, isAcyclic_of_not_winnable_ordiv h_conn O⟩

end Utilities
