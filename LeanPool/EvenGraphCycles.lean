/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.IntervalCases

/-!
# Even graphs are edge-disjoint unions of cycles

Source: url:https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/b3423f3e8c8db7c2d1b279673293ef3079faf903/preprints/PAPER_III/05_formalization/lean_v1.4_freeze/Contrib/EvenGraphCycles.lean
Authors: Juan Pablo Traverso Gianini, Aristotle
Status: verified
Main declarations: `Finset.exists_cycleDecomp`, `Finset.exists_edge_pairing_of_even`
Tags: graph-theory, eulerian-graphs, cycle-decompositions
MSC: 05C45
-/

/-!
# Even graphs are edge-disjoint unions of cycles

A finite graph, encoded as a finite set of edges `E : Finset (Sym2 V)`, all of whose degrees are
even is the edge-disjoint union of cycles.  As a consequence the edges at each vertex can be
paired up, simultaneously at every vertex ("Eulerian pairing").

## Main results

* `Finset.exists_cycleDecomp`:
  `theorem Finset.exists_cycleDecomp {V : Type*} [DecidableEq V] {E : Finset (Sym2 V)}
      (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (heven : ∀ v : V, Even (E.cycleEdgeDegree v)) :
      ∃ cs : List (List V), (∀ c ∈ cs, c.Nodup ∧ 3 ≤ c.length) ∧
        (cs.flatMap List.cycleEdges).Nodup ∧ (cs.flatMap List.cycleEdges).toFinset = E`
* `Finset.exists_edge_pairing_of_even`:
  `theorem Finset.exists_edge_pairing_of_even {V : Type*} [DecidableEq V] {E : Finset (Sym2 V)}
      (heven : ∀ v : V, Even (E.cycleEdgeDegree v)) :
      ∃ pair : V → Sym2 V → Sym2 V, ∀ v : V, ∀ e ∈ E, v ∈ e →
        pair v e ∈ E ∧ v ∈ pair v e ∧ pair v e ≠ e ∧ pair v (pair v e) = e`

Along the way we prove `Finset.exists_cycle_of_even` (a nonempty loopless even graph contains a
cycle), `Finset.exists_cycleDecomp_finset` (the decomposition stated as a pairwise disjoint family
of edge sets) and `Finset.exists_involution_of_even_card` (a finite set of even size carries a
fixed-point-free involution).

## Implementation notes

Graphs are encoded as finite sets of edges `E : Finset (Sym2 V)`;
`E.cycleEdgeDegree v` is the number of edges of `E` incident with `v`.  A cycle is encoded by a
list `l : List V` of pairwise distinct
vertices with `3 ≤ l.length`, its edge list being `l.cycleEdges`, the list of pairs of cyclically
consecutive entries of `l`.

The cycle decomposition is proved by strong induction on the edge set: a nonempty even graph has
minimum positive degree at least two, so a path of maximal length closes up into a cycle
(`Finset.exists_cycle_of_even`); removing the edges of that cycle keeps all degrees even
(`List.even_edgeDegree_cycleEdges`), and one recurses.

## Main definitions

* `List.pathEdges`, `List.cycleEdges`: the edges of a walk, resp. of a closed walk, given as a
  list of vertices;
* `Finset.cycleEdgeDegree`: the degree of a vertex in a finite edge set;
* `Finset.edgeSupport`: the set of vertices incident with an edge of a finite edge set.
-/

open Finset

namespace List

variable {V : Type*}

/-- The list of edges of the walk `l`: the pairs of consecutive vertices of `l`. -/
def pathEdges : List V → List (Sym2 V)
  | [] => []
  | [_] => []
  | a :: b :: l => s(a, b) :: pathEdges (b :: l)

/-- The list of edges of the closed walk `l`: the pairs of cyclically consecutive vertices
of `l`. -/
def cycleEdges (l : List V) : List (Sym2 V) := pathEdges (l ++ l.take 1)

/-- The empty walk has no edges. -/
@[simp] lemma pathEdges_nil : pathEdges ([] : List V) = [] := rfl

/-- A one-vertex walk has no edges. -/
@[simp] lemma pathEdges_singleton (a : V) : pathEdges [a] = [] := rfl

/-- The edges of the walk `a :: b :: l` are `s(a, b)` together with the edges of `b :: l`. -/
@[simp] lemma pathEdges_cons_cons (a b : V) (l : List V) :
    pathEdges (a :: b :: l) = s(a, b) :: pathEdges (b :: l) := rfl

/-- A walk on `n` vertices has `n - 1` edges. -/
lemma length_pathEdges (l : List V) : (pathEdges l).length = l.length - 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l => simp [pathEdges, ih]

/-- A closed walk on `n` vertices has `n` edges. -/
lemma length_cycleEdges (l : List V) : (cycleEdges l).length = l.length := by
  cases l with
  | nil => simp [cycleEdges]
  | cons a l => simp [cycleEdges, length_pathEdges]

/-- Taking an initial segment of a list does not change its entries in that segment. -/
lemma getD_take (l : List V) (d : V) {k i : ℕ} (h : i < k) :
    (l.take k).getD i d = l.getD i d := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi,
      List.getElem_take]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

/-- The `i`-th edge of a walk joins its `i`-th and its `(i + 1)`-st vertex. -/
lemma pathEdges_getD (d : Sym2 V) (e : V) :
    ∀ (l : List V) (i : ℕ), i + 1 < l.length →
      (pathEdges l).getD i d = s(l.getD i e, l.getD (i + 1) e) := by
  intro l
  induction l with
  | nil => intro i hi; simp at hi
  | cons a l ih =>
    intro i hi
    cases l with
    | nil => simp at hi
    | cons b l =>
      cases i with
      | zero => simp [pathEdges, List.getD]
      | succ i =>
        have hi' : i + 1 < (b :: l).length := by simpa using hi
        have := ih i hi'
        simpa [pathEdges, List.getD_cons_succ] using this

/-- The `i`-th edge of a closed walk joins its `i`-th and its `(i + 1)`-st vertex, cyclically. -/
lemma cycleEdges_getD (d : Sym2 V) (e : V) (l : List V) (i : ℕ) (hi : i < l.length) :
    (cycleEdges l).getD i d = s(l.getD i e, l.getD ((i + 1) % l.length) e) := by
  cases l with
  | nil => simp at hi
  | cons a l =>
    set L : List V := a :: l with hL
    have hlen : (L ++ L.take 1).length = L.length + 1 := by simp [hL]
    have h1 : i + 1 < (L ++ L.take 1).length := by omega
    have h2 := pathEdges_getD d e (L ++ L.take 1) i h1
    have hgi : (L ++ L.take 1).getD i e = L.getD i e := List.getD_append _ _ _ _ hi
    rw [cycleEdges, h2, hgi]
    congr 1
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with h | h
    · have hmod : (i + 1) % L.length = i + 1 := Nat.mod_eq_of_lt h
      rw [hmod, List.getD_append _ _ _ _ h]
    · -- wrap around: the last edge closes the walk
      have hmod : (i + 1) % L.length = 0 := by rw [← h]; simp
      rw [hmod]
      have hlast : (L ++ L.take 1).getD (i + 1) e = (L.take 1).getD 0 e := by
        rw [List.getD_append_right _ _ _ _ (by omega)]
        congr 1
        omega
      rw [hlast, hL]
      simp [List.getD]

/-- The edges of a walk are exactly the pairs of consecutive vertices. -/
lemma mem_pathEdges_iff (d : V) (l : List V) (e : Sym2 V) :
    e ∈ pathEdges l ↔ ∃ i, i + 1 < l.length ∧ e = s(l.getD i d, l.getD (i + 1) d) := by
  constructor
  · intro he
    obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 he
    have hlen : i + 1 < l.length := by
      have := length_pathEdges l
      omega
    refine ⟨i, hlen, ?_⟩
    have h := pathEdges_getD s(d, d) d l i hlen
    rw [List.getD_eq_getElem _ _ hi] at h
    rw [← hie, h]
  · rintro ⟨i, hi, rfl⟩
    have hlen : i < (pathEdges l).length := by
      have := length_pathEdges l
      omega
    have h := pathEdges_getD s(d, d) d l i hi
    rw [List.getD_eq_getElem _ _ hlen] at h
    rw [← h]
    exact List.getElem_mem hlen

/-- The edges of a closed walk are exactly the pairs of cyclically consecutive vertices. -/
lemma mem_cycleEdges_iff (d : V) (l : List V) (e : Sym2 V) :
    e ∈ cycleEdges l ↔ ∃ i, i < l.length ∧ e = s(l.getD i d, l.getD ((i + 1) % l.length) d) := by
  constructor
  · intro he
    obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 he
    have hlen : i < l.length := by
      have := length_cycleEdges l
      omega
    refine ⟨i, hlen, ?_⟩
    have h := cycleEdges_getD s(d, d) d l i hlen
    rw [List.getD_eq_getElem _ _ hi] at h
    rw [← hie, h]
  · rintro ⟨i, hi, rfl⟩
    have hlen : i < (cycleEdges l).length := by
      have := length_cycleEdges l
      omega
    have h := cycleEdges_getD s(d, d) d l i hi
    rw [List.getD_eq_getElem _ _ hlen] at h
    rw [← h]
    exact List.getElem_mem hlen

/-- An endpoint of an edge of a closed walk is a vertex of that walk. -/
lemma mem_of_mem_cycleEdges {l : List V} {e : Sym2 V} (he : e ∈ cycleEdges l) {x : V}
    (hx : x ∈ e) : x ∈ l := by
  have hne : l ≠ [] := by
    rintro rfl
    simp [cycleEdges] at he
  obtain ⟨d, hd⟩ : ∃ d, d ∈ l := by
    cases l with
    | nil => exact absurd rfl hne
    | cons a l => exact ⟨a, by simp⟩
  obtain ⟨i, hi, rfl⟩ := (mem_cycleEdges_iff d l e).1 he
  have h1 : l.getD i d ∈ l := by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have h2 : l.getD ((i + 1) % l.length) d ∈ l := by
    rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ (by omega))]
    exact List.getElem_mem _
  rcases Sym2.mem_iff.1 hx with rfl | rfl
  · exact h1
  · exact h2

/-- The edges of a cycle are pairwise distinct. -/
lemma nodup_cycleEdges {l : List V} (hnd : l.Nodup) (hlen : 3 ≤ l.length) :
    (cycleEdges l).Nodup := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, d ∈ l := by
    cases l with
    | nil => simp at hlen
    | cons a l => exact ⟨a, by simp⟩
  rw [List.nodup_iff_injective_getElem]
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  have hlc := length_cycleEdges l
  have hi' : i < l.length := by omega
  have hj' : j < l.length := by omega
  have hei := cycleEdges_getD s(d, d) d l i hi'
  have hej := cycleEdges_getD s(d, d) d l j hj'
  rw [List.getD_eq_getElem _ _ hi] at hei
  rw [List.getD_eq_getElem _ _ hj] at hej
  simp only at hij
  rw [hei, hej] at hij
  have hget : ∀ {p q : ℕ} (hp : p < l.length) (hq : q < l.length),
      l.getD p d = l.getD q d → p = q := by
    intro p q hp hq h
    rw [List.getD_eq_getElem _ _ hp, List.getD_eq_getElem _ _ hq] at h
    exact hnd.getElem_inj_iff.1 h
  have hmod : ∀ p, p < l.length → (p + 1) % l.length < l.length := fun p _ =>
    Nat.mod_lt _ (by omega)
  rw [Sym2.eq_iff] at hij
  rcases hij with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact Fin.ext (hget hi' hj' h1)
  · exfalso
    have e1 : i = (j + 1) % l.length := hget hi' (hmod j hj') h1
    have e2 : (i + 1) % l.length = j := hget (hmod i hi') hj' h2
    rcases Nat.lt_or_ge (j + 1) l.length with h | h
    · rw [Nat.mod_eq_of_lt h] at e1
      subst e1
      rcases Nat.lt_or_ge (j + 1 + 1) l.length with h' | h'
      · rw [Nat.mod_eq_of_lt h'] at e2; omega
      · have : (j + 1 + 1) % l.length = 0 := by
          have : j + 1 + 1 = l.length := by omega
          rw [this, Nat.mod_self]
        rw [this] at e2
        omega
    · have hj1 : j + 1 = l.length := by omega
      have : (j + 1) % l.length = 0 := by rw [hj1, Nat.mod_self]
      rw [this] at e1
      subst e1
      have : (0 + 1) % l.length = 1 := Nat.mod_eq_of_lt (by omega)
      rw [this] at e2
      omega

/-- A cycle has no loops. -/
lemma not_isDiag_of_mem_cycleEdges {l : List V} (hnd : l.Nodup) (hlen : 2 ≤ l.length)
    {e : Sym2 V} (he : e ∈ cycleEdges l) : ¬ e.IsDiag := by
  obtain ⟨d, hd⟩ : ∃ d, d ∈ l := by
    cases l with
    | nil => simp at hlen
    | cons a l => exact ⟨a, by simp⟩
  obtain ⟨i, hi, rfl⟩ := (mem_cycleEdges_iff d l e).1 he
  have hmod : (i + 1) % l.length < l.length := Nat.mod_lt _ (by omega)
  intro hdiag
  have heq : l.getD i d = l.getD ((i + 1) % l.length) d := by simpa using hdiag
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hmod] at heq
  have : i = (i + 1) % l.length := hnd.getElem_inj_iff.1 heq
  rcases Nat.lt_or_ge (i + 1) l.length with h | h
  · rw [Nat.mod_eq_of_lt h] at this; omega
  · have h1 : i + 1 = l.length := by omega
    rw [h1, Nat.mod_self] at this
    omega

end List

namespace Finset

variable {V : Type*} [DecidableEq V]

/-- The number of edges of `E` incident with `v`.

The project-specific name avoids colliding with analogous definitions in other pooled projects. -/
def cycleEdgeDegree (E : Finset (Sym2 V)) (v : V) : ℕ := (E.filter fun e ↦ v ∈ e).card

/-- The raw-edge degree agrees with `SimpleGraph.degree` on a graph's edge finset. -/
lemma cycleEdgeDegree_edgeFinset {G : SimpleGraph V} [Fintype G.edgeSet]
    (v : V) [Fintype (G.neighborSet v)] :
    G.edgeFinset.cycleEdgeDegree v = G.degree v := by
  rw [cycleEdgeDegree, ← G.incidenceFinset_eq_filter v, G.card_incidenceFinset_eq_degree]

/-- The set of vertices incident with an edge of the finite edge set `E`. -/
def edgeSupport (E : Finset (Sym2 V)) : Finset V := E.biUnion Sym2.toFinset

/-- A vertex lies in the support of `E` if and only if it is incident with an edge of `E`. -/
lemma mem_edgeSupport {E : Finset (Sym2 V)} {v : V} : v ∈ E.edgeSupport ↔ ∃ e ∈ E, v ∈ e := by
  simp [edgeSupport]

/-- Degrees are monotone in the edge set. -/
lemma edgeDegree_mono {E F : Finset (Sym2 V)} (h : E ⊆ F) (v : V) :
    E.cycleEdgeDegree v ≤ F.cycleEdgeDegree v :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- Deleting a set of edges subtracts its degrees. -/
lemma edgeDegree_sdiff {E A : Finset (Sym2 V)} (h : A ⊆ E) (v : V) :
    (E \ A).cycleEdgeDegree v = E.cycleEdgeDegree v - A.cycleEdgeDegree v := by
  unfold cycleEdgeDegree
  have hfil : ((E \ A).filter fun e => v ∈ e)
      = (E.filter fun e => v ∈ e) \ (A.filter fun e => v ∈ e) := by
    ext e; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [hfil, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ h)]

/-! ### The degrees of a cycle -/

/-- Every degree of a cycle is even (in fact `0` or `2`). -/
lemma even_edgeDegree_cycleEdges {l : List V} (hnd : l.Nodup) (hlen : 3 ≤ l.length) (v : V) :
    Even ((l.cycleEdges.toFinset).cycleEdgeDegree v) := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, d ∈ l := by
    cases l with
    | nil => simp at hlen
    | cons a l => exact ⟨a, by simp⟩
  by_cases hv : v ∈ l
  · obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.1 hv
    have hivd : l.getD i d = v := by rw [List.getD_eq_getElem _ _ hi, hiv]
    -- the two edges at `v`
    set i' : ℕ := (i + l.length - 1) % l.length with hi'
    have hi'lt : i' < l.length := Nat.mod_lt _ (by omega)
    have hsucc : (i' + 1) % l.length = i := by
      rw [hi']
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · have h0 : (0 + l.length - 1) % l.length = l.length - 1 := by
          rw [Nat.zero_add]
          exact Nat.mod_eq_of_lt (by omega)
        rw [h0]
        have : l.length - 1 + 1 = l.length := by omega
        rw [this, Nat.mod_self]
      · have h0 : (i + l.length - 1) % l.length = i - 1 := by
          have : i + l.length - 1 = (i - 1) + l.length := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [h0]
        have : i - 1 + 1 = i := by omega
        rw [this, Nat.mod_eq_of_lt hi]
    set e₁ : Sym2 V := s(l.getD i d, l.getD ((i + 1) % l.length) d) with he₁
    set e₂ : Sym2 V := s(l.getD i' d, l.getD ((i' + 1) % l.length) d) with he₂
    have hfil : (l.cycleEdges.toFinset.filter fun e => v ∈ e) = {e₁, e₂} := by
      ext e
      simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨he, hve⟩
        obtain ⟨j, hj, rfl⟩ := (List.mem_cycleEdges_iff d l e).1 he
        have hjlt : (j + 1) % l.length < l.length := Nat.mod_lt _ (by omega)
        have hget : ∀ {p q : ℕ}, p < l.length → q < l.length → l.getD p d = l.getD q d → p = q := by
          intro p q hp hq h
          rw [List.getD_eq_getElem _ _ hp, List.getD_eq_getElem _ _ hq] at h
          exact hnd.getElem_inj_iff.1 h
        rcases Sym2.mem_iff.1 hve with h | h
        · left
          have : j = i := hget hj hi (by rw [← h, hivd])
          rw [this]
        · right
          have hji : (j + 1) % l.length = i := hget hjlt hi (by rw [← h, hivd])
          have : j = i' := by
            rw [hi']
            rcases Nat.lt_or_ge (j + 1) l.length with hlt | hge
            · rw [Nat.mod_eq_of_lt hlt] at hji
              subst hji
              have : j + 1 + l.length - 1 = j + l.length := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            · have hjl : j + 1 = l.length := by omega
              have h0 : (j + 1) % l.length = 0 := by rw [hjl, Nat.mod_self]
              rw [h0] at hji
              rw [← hji]
              have : 0 + l.length - 1 = l.length - 1 := by omega
              rw [this, Nat.mod_eq_of_lt (by omega)]
              omega
          rw [this]
      · have hmem : ∀ p, p < l.length →
            s(l.getD p d, l.getD ((p + 1) % l.length) d) ∈ l.cycleEdges := by
          intro p hp
          exact (List.mem_cycleEdges_iff d l _).2 ⟨p, hp, rfl⟩
        rintro (rfl | rfl)
        · exact ⟨hmem i hi, by rw [he₁, hivd]; simp⟩
        · refine ⟨hmem i' hi'lt, ?_⟩
          rw [he₂, hsucc, hivd]
          simp
    have hget : ∀ {p q : ℕ}, p < l.length → q < l.length → l.getD p d = l.getD q d → p = q := by
      intro p q hp hq hh
      rw [List.getD_eq_getElem _ _ hp, List.getD_eq_getElem _ _ hq] at hh
      exact hnd.getElem_inj_iff.1 hh
    have hmodne : ∀ p q : ℕ, p < l.length → q < l.length →
        (p + 1) % l.length = q → (q + 1) % l.length = p → False := by
      intro p q hp hq h1 h2
      rcases Nat.lt_or_ge (p + 1) l.length with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at h1
        subst h1
        rcases Nat.lt_or_ge (p + 1 + 1) l.length with hlt' | hge'
        · rw [Nat.mod_eq_of_lt hlt'] at h2; omega
        · have he : p + 1 + 1 = l.length := by omega
          rw [he, Nat.mod_self] at h2
          omega
      · have he : p + 1 = l.length := by omega
        rw [he, Nat.mod_self] at h1
        subst h1
        rw [Nat.mod_eq_of_lt (by omega)] at h2
        omega
    have hne : e₁ ≠ e₂ := by
      intro h
      rw [he₁, he₂, Sym2.eq_iff] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hii : i = i' := hget hi hi'lt h1
        rw [← hii] at hsucc
        exact hmodne i i hi hi hsucc hsucc
      · have h3 : (i + 1) % l.length = i' :=
          hget (Nat.mod_lt _ (by omega)) hi'lt h2
        exact hmodne i i' hi hi'lt h3 hsucc
    rw [cycleEdgeDegree, hfil,
      Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
    exact ⟨1, rfl⟩
  · have hemp : (l.cycleEdges.toFinset.filter fun e => v ∈ e) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e he hve
      exact hv (List.mem_of_mem_cycleEdges (List.mem_toFinset.1 he) hve)
    rw [cycleEdgeDegree, hemp]
    exact ⟨0, rfl⟩

/-! ### A nonempty even graph contains a cycle -/

/-- **Every nonempty loopless graph with all degrees even contains a cycle.**  The cycle is found
at the end of a path of maximal length. -/
theorem exists_cycle_of_even {E : Finset (Sym2 V)} (hne : E.Nonempty)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (heven : ∀ v : V, Even (E.cycleEdgeDegree v)) :
    ∃ l : List V, l.Nodup ∧ 3 ≤ l.length ∧ ∀ e ∈ l.cycleEdges, e ∈ E := by
  classical
  set S : Finset V := E.edgeSupport with hS
  set P : ℕ → Prop := fun m => ∃ l : List V, l.Nodup ∧ (∀ x ∈ l, x ∈ S) ∧
      (∀ e ∈ l.pathEdges, e ∈ E) ∧ l.length = m with hP
  have hbound : ∀ m, P m → m ≤ S.card := by
    rintro m ⟨l, hnd, hsub, -, rfl⟩
    have h1 : l.toFinset ⊆ S := fun x hx => hsub x (List.mem_toFinset.1 hx)
    calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ ≤ S.card := Finset.card_le_card h1
  -- a first path, consisting of a single edge
  obtain ⟨e₀, he₀⟩ := hne
  obtain ⟨a, b, hab, rfl⟩ : ∃ a b, a ≠ b ∧ e₀ = s(a, b) := by
    induction e₀ with
    | h a b =>
      refine ⟨a, b, ?_, rfl⟩
      intro h
      exact hdiag _ he₀ (by simp [h])
  have haS : a ∈ S := mem_edgeSupport.2 ⟨_, he₀, by simp⟩
  have hbS : b ∈ S := mem_edgeSupport.2 ⟨_, he₀, by simp⟩
  have hP2 : P 2 := by
    refine ⟨[a, b], by simp [hab], ?_, ?_, rfl⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact haS
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact hbS
        · simp at hx
    · intro e he
      simp only [List.pathEdges, List.mem_singleton] at he
      rw [he]
      exact he₀
  have h2S : 2 ≤ S.card := hbound 2 hP2
  set m : ℕ := Nat.findGreatest P S.card with hm
  have hPm : P m := Nat.findGreatest_spec h2S hP2
  have hmax : ∀ n, P n → n ≤ m := fun n hn => Nat.le_findGreatest (hbound n hn) hn
  have h2m : 2 ≤ m := hmax 2 hP2
  obtain ⟨l, hnd, hsub, hpe, hlen⟩ := hPm
  -- write the path as `v₀ :: v₁ :: rest`
  rcases l with _ | ⟨v₀, _ | ⟨v₁, rest⟩⟩
  · simp at hlen; omega
  · simp at hlen; omega
  · have hedge01 : s(v₀, v₁) ∈ E := hpe _ (by simp [List.pathEdges])
    -- every neighbour of `v₀` lies on the path
    have hmaximal : ∀ u : V, s(u, v₀) ∈ E → u ∈ (v₀ :: v₁ :: rest) := by
      intro u hu
      by_contra hmem
      have hnd' : (u :: v₀ :: v₁ :: rest).Nodup := List.nodup_cons.2 ⟨hmem, hnd⟩
      have hsub' : ∀ x ∈ (u :: v₀ :: v₁ :: rest), x ∈ S := by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact mem_edgeSupport.2 ⟨_, hu, by simp⟩
        · exact hsub x hx
      have hpe' : ∀ e ∈ (u :: v₀ :: v₁ :: rest).pathEdges, e ∈ E := by
        intro e he
        rw [List.pathEdges_cons_cons] at he
        rcases List.mem_cons.1 he with rfl | he
        · exact hu
        · exact hpe e he
      have hP' : P (m + 1) := ⟨_, hnd', hsub', hpe', by simp [← hlen]⟩
      have := hmax _ hP'
      omega
    -- `v₀` has at least two neighbours
    have hdeg : 2 ≤ (E.filter fun e => v₀ ∈ e).card := by
      have h1 : 1 ≤ (E.filter fun e => v₀ ∈ e).card :=
        Finset.card_pos.2 ⟨s(v₀, v₁), Finset.mem_filter.2 ⟨hedge01, by simp⟩⟩
      have hev := heven v₀
      unfold cycleEdgeDegree at hev
      rcases hev with ⟨t, ht⟩
      omega
    obtain ⟨e₁, he₁, e₂, he₂, hne₁₂⟩ := Finset.one_lt_card.1 hdeg
    have hother : ∀ e ∈ E.filter fun e => v₀ ∈ e, ∃ u, u ≠ v₀ ∧ e = s(v₀, u) := by
      intro e he
      obtain ⟨heE, hv₀⟩ := Finset.mem_filter.1 he
      induction e with
      | h x y =>
        have hxy : x ≠ y := fun h => hdiag _ heE (by simp [h])
        rcases Sym2.mem_iff.1 hv₀ with rfl | rfl
        · exact ⟨y, fun h => hxy h.symm, rfl⟩
        · exact ⟨x, hxy, Sym2.eq_swap⟩
    obtain ⟨u₁, hu₁ne, hu₁⟩ := hother e₁ he₁
    obtain ⟨u₂, hu₂ne, hu₂⟩ := hother e₂ he₂
    have hu₁₂ : u₁ ≠ u₂ := by
      rintro rfl
      exact hne₁₂ (hu₁.trans hu₂.symm)
    -- pick a neighbour different from `v₁`
    obtain ⟨u, huE, huv₀, huv₁⟩ : ∃ u, s(v₀, u) ∈ E ∧ u ≠ v₀ ∧ u ≠ v₁ := by
      by_cases h : u₁ = v₁
      · exact ⟨u₂, by rw [← hu₂]; exact (Finset.mem_filter.1 he₂).1, hu₂ne,
          by rw [← h]; exact hu₁₂.symm⟩
      · exact ⟨u₁, by rw [← hu₁]; exact (Finset.mem_filter.1 he₁).1, hu₁ne, h⟩
    have humem : u ∈ (v₀ :: v₁ :: rest) := hmaximal u (by rwa [Sym2.eq_swap])
    obtain ⟨j, hj, hju⟩ := List.mem_iff_getElem.1 humem
    have hj2 : 2 ≤ j := by
      rcases Nat.lt_or_ge j 2 with h | h
      · interval_cases j
        · exact absurd hju.symm (by simpa using huv₀)
        · exact absurd hju.symm (by simpa using huv₁)
      · exact h
    -- the cycle is the initial segment of the path up to `u`
    refine ⟨(v₀ :: v₁ :: rest).take (j + 1), ?_, ?_, ?_⟩
    · exact hnd.sublist (List.take_sublist _ _)
    · simp only [List.length_take]
      omega
    · intro e he
      set L : List V := v₀ :: v₁ :: rest with hL
      have hlenT : (L.take (j + 1)).length = j + 1 := by
        simp only [hL, List.length_take]
        omega
      obtain ⟨i, hi, rfl⟩ := (List.mem_cycleEdges_iff v₀ (L.take (j + 1)) e).1 he
      rw [hlenT] at hi ⊢
      rcases Nat.lt_or_ge i j with hij | hij
      · have h1 : (i + 1) % (j + 1) = i + 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1, List.getD_take L v₀ (by omega), List.getD_take L v₀ (by omega)]
        refine hpe _ ((List.mem_pathEdges_iff v₀ L _).2 ⟨i, ?_, rfl⟩)
        simp only [hL, List.length_cons] at hj ⊢
        omega
      · have hij' : i = j := by omega
        subst hij'
        have h1 : (i + 1) % (i + 1) = 0 := Nat.mod_self _
        rw [h1, List.getD_take L v₀ (by omega), List.getD_take L v₀ (by omega)]
        have h2 : L.getD i v₀ = u := by
          rw [List.getD_eq_getElem _ _ hj, hju]
        have h3 : L.getD 0 v₀ = v₀ := by simp [hL, List.getD]
        rw [h2, h3, Sym2.eq_swap]
        exact huE

/-! ### The cycle decomposition -/

/-- **Every finite loopless graph with all degrees even is the edge-disjoint union of cycles.**

The cycles are given as a list `cs` of lists of pairwise distinct vertices, each of length at
least three; their edge lists concatenate, without repetition, to the edge set `E`. -/
theorem exists_cycleDecomp {E : Finset (Sym2 V)} (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v : V, Even (E.cycleEdgeDegree v)) :
    ∃ cs : List (List V), (∀ c ∈ cs, c.Nodup ∧ 3 ≤ c.length) ∧
      (cs.flatMap List.cycleEdges).Nodup ∧ (cs.flatMap List.cycleEdges).toFinset = E := by
  classical
  revert hdiag heven
  induction E using Finset.strongInduction with
  | _ E ih =>
    intro hdiag heven
    rcases E.eq_empty_or_nonempty with rfl | hne
    · exact ⟨[], by simp, by simp, by simp⟩
    obtain ⟨l, hnd, hlen, hsub⟩ := exists_cycle_of_even hne hdiag heven
    set C : Finset (Sym2 V) := l.cycleEdges.toFinset with hC
    have hCsub : C ⊆ E := fun e he => hsub e (List.mem_toFinset.1 he)
    have hCne : C.Nonempty := by
      have hlc : l.cycleEdges.length = l.length := List.length_cycleEdges l
      have hnil : l.cycleEdges ≠ [] := by
        intro h
        rw [h] at hlc
        simp at hlc
        omega
      obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hnil
      exact ⟨e, List.mem_toFinset.2 he⟩
    have hssub : E \ C ⊂ E := Finset.sdiff_ssubset hCsub hCne
    have hdiag' : ∀ e ∈ E \ C, ¬ e.IsDiag := fun e he => hdiag e (Finset.mem_sdiff.1 he).1
    have heven' : ∀ v : V, Even ((E \ C).cycleEdgeDegree v) := by
      intro v
      rw [edgeDegree_sdiff hCsub]
      have hle : C.cycleEdgeDegree v ≤ E.cycleEdgeDegree v := edgeDegree_mono hCsub v
      rw [Nat.even_sub hle]
      exact ⟨fun _ => even_edgeDegree_cycleEdges hnd hlen v, fun _ => heven v⟩
    obtain ⟨cs, hcs, hndcs, hcsE⟩ := ih (E \ C) hssub hdiag' heven'
    refine ⟨l :: cs, ?_, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨hnd, hlen⟩
      · exact hcs c hc
    · rw [List.flatMap_cons, List.nodup_append]
      refine ⟨List.nodup_cycleEdges hnd hlen, hndcs, ?_⟩
      rintro e he e' he' rfl
      have h1 : e ∈ C := List.mem_toFinset.2 he
      have h2 : e ∈ E \ C := by rw [← hcsE]; exact List.mem_toFinset.2 he'
      exact (Finset.mem_sdiff.1 h2).2 h1
    · rw [List.flatMap_cons, List.toFinset_append, hcsE, ← hC,
        Finset.union_sdiff_self_eq_union]
      exact Finset.union_eq_right.2 hCsub

/-- **Every finite loopless graph with all degrees even decomposes into edge-disjoint cycles**,
stated as a family of edge sets: the cycles are given as a list `Cs` of edge sets, each of them
the edge set `l.cycleEdges` of a cycle `l` (a list of pairwise distinct vertices of length at
least three); they are pairwise disjoint and their union is `E`. -/
theorem exists_cycleDecomp_finset {E : Finset (Sym2 V)} (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v : V, Even (E.cycleEdgeDegree v)) :
    ∃ Cs : List (Finset (Sym2 V)),
      (∀ C ∈ Cs, ∃ l : List V, l.Nodup ∧ 3 ≤ l.length ∧ C = l.cycleEdges.toFinset) ∧
      Cs.Pairwise Disjoint ∧ ∀ e : Sym2 V, e ∈ E ↔ ∃ C ∈ Cs, e ∈ C := by
  classical
  obtain ⟨cs, hcs, hnd, hunion⟩ := exists_cycleDecomp hdiag heven
  refine ⟨cs.map fun c => c.cycleEdges.toFinset, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hC
    exact ⟨c, (hcs c hc).1, (hcs c hc).2, rfl⟩
  · refine List.Pairwise.map _ ?_ (List.nodup_flatMap.1 hnd).2
    intro a b hab
    rw [Finset.disjoint_left]
    intro e he he'
    exact hab (List.mem_toFinset.1 he) (List.mem_toFinset.1 he')
  · intro e
    constructor
    · intro he
      obtain ⟨c, hc, hec⟩ := List.mem_flatMap.1 (List.mem_toFinset.1 (hunion ▸ he))
      exact ⟨c.cycleEdges.toFinset, List.mem_map.2 ⟨c, hc, rfl⟩, List.mem_toFinset.2 hec⟩
    · rintro ⟨C, hC, heC⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hC
      rw [← hunion]
      exact List.mem_toFinset.2 (List.mem_flatMap.2 ⟨c, hc, List.mem_toFinset.1 heC⟩)

/-! ### Pairing up a set of even size -/

/-- **Every finite set of even size carries a fixed-point-free involution.** -/
theorem exists_involution_of_even_card {α : Type*} {S : Finset α}
    (hev : Even S.card) : ∃ f : α → α, ∀ a ∈ S, f a ∈ S ∧ f a ≠ a ∧ f (f a) = a := by
  classical
  revert hev
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hev
    rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨id, by simp⟩
    have h2 : 2 ≤ S.card := by
      rcases hev with ⟨m, hm⟩
      have : 0 < S.card := Finset.card_pos.2 ⟨a, ha⟩
      omega
    obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) a
    set T : Finset α := (S.erase a).erase b with hT
    have hTcard : T.card + 2 = S.card := by
      rw [hT, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hba, hb⟩),
        Finset.card_erase_of_mem ha]
      omega
    have hTev : Even T.card := by
      rcases hev with ⟨m, hm⟩
      exact ⟨m - 1, by omega⟩
    have hTsub : T ⊆ S := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    have hTss : T ⊂ S :=
      Finset.ssubset_iff_subset_ne.2 ⟨hTsub, fun h => by rw [h] at hTcard; omega⟩
    obtain ⟨g, hg⟩ := ih T hTss hTev
    refine ⟨fun x => if x = a then b else if x = b then a else g x, ?_⟩
    intro x hx
    by_cases hxa : x = a
    · refine ⟨?_, ?_, ?_⟩
      · simpa only [ite_eq_left hxa] using hb
      · simpa only [ite_eq_left hxa] using fun h : b = x => hba (h.trans hxa)
      · simp only [ite_eq_left hxa, ite_eq_right hba]
        exact hxa.symm
    · by_cases hxb : x = b
      · refine ⟨?_, ?_, ?_⟩
        · simpa only [ite_eq_right hxa, ite_eq_left hxb] using ha
        · simpa only [ite_eq_right hxa, ite_eq_left hxb] using fun h : a = x => hxa h.symm
        · simp only [ite_eq_right hxa, ite_eq_left hxb]
          exact hxb.symm
      · have hxT : x ∈ T := Finset.mem_erase.2 ⟨hxb, Finset.mem_erase.2 ⟨hxa, hx⟩⟩
        obtain ⟨hgx, hgxne, hgg⟩ := hg x hxT
        have hgxa : g x ≠ a := fun h => (Finset.mem_erase.1 (Finset.mem_erase.1 hgx).2).1 h
        have hgxb : g x ≠ b := fun h => (Finset.mem_erase.1 hgx).1 h
        simp only [ite_eq_right hxa, ite_eq_right hxb, ite_eq_right hgxa, ite_eq_right hgxb]
        exact ⟨hTsub hgx, hgxne, hgg⟩

/-! ### The Eulerian pairing -/

/-- **The Eulerian pairing.**  If every degree of `E` is even then the edges of `E` at every
vertex `v` can be paired up: `pair v` is a fixed-point-free involution of the set of edges of `E`
incident with `v`.  The pairing is defined at every vertex simultaneously, so each edge `xy` of `E`
is paired with an edge at `x` and with an edge at `y`. -/
theorem exists_edge_pairing_of_even {E : Finset (Sym2 V)}
    (heven : ∀ v : V, Even (E.cycleEdgeDegree v)) :
    ∃ pair : V → Sym2 V → Sym2 V, ∀ v : V, ∀ e ∈ E, v ∈ e →
      pair v e ∈ E ∧ v ∈ pair v e ∧ pair v e ≠ e ∧ pair v (pair v e) = e := by
  classical
  have hstep : ∀ v : V, ∃ f : Sym2 V → Sym2 V, ∀ e ∈ E.filter fun e => v ∈ e,
      f e ∈ E.filter (fun e => v ∈ e) ∧ f e ≠ e ∧ f (f e) = e := fun v =>
    exists_involution_of_even_card (heven v)
  choose pair hpair using hstep
  refine ⟨pair, ?_⟩
  intro v e he hve
  have hmem : e ∈ E.filter fun e => v ∈ e := Finset.mem_filter.2 ⟨he, hve⟩
  obtain ⟨h1, h2, h3⟩ := hpair v e hmem
  exact ⟨(Finset.mem_filter.1 h1).1, (Finset.mem_filter.1 h1).2, h2, h3⟩

end Finset

namespace SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- A finite simple graph of even degree decomposes into edge-disjoint simple cycles. -/
theorem exists_cycleDecomp_of_even_degree (G : SimpleGraph V) [Fintype G.edgeSet]
    [∀ v, Fintype (G.neighborSet v)]
    (heven : ∀ v : V, Even (G.degree v)) :
    ∃ cs : List (List V), (∀ c ∈ cs, c.Nodup ∧ 3 ≤ c.length) ∧
      (cs.flatMap List.cycleEdges).Nodup ∧
      (cs.flatMap List.cycleEdges).toFinset = G.edgeFinset := by
  apply Finset.exists_cycleDecomp
  · exact fun e he ↦ G.not_isDiag_of_mem_edgeFinset he
  · intro v
    rw [Finset.cycleEdgeDegree_edgeFinset]
    exact heven v

omit [DecidableEq V] in
/-- The incident edges of a finite simple graph of even degree admit Eulerian pairings. -/
theorem exists_edge_pairing_of_even_degree (G : SimpleGraph V) [Fintype G.edgeSet]
    [∀ v, Fintype (G.neighborSet v)]
    (heven : ∀ v : V, Even (G.degree v)) :
    ∃ pair : V → Sym2 V → Sym2 V, ∀ v : V, ∀ e ∈ G.edgeFinset, v ∈ e →
      pair v e ∈ G.edgeFinset ∧ v ∈ pair v e ∧ pair v e ≠ e ∧ pair v (pair v e) = e := by
  classical
  apply Finset.exists_edge_pairing_of_even
  intro v
  rw [Finset.cycleEdgeDegree_edgeFinset]
  exact heven v

end SimpleGraph
