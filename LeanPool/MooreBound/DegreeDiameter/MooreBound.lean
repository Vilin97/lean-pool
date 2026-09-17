/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

import LeanPool.MooreBound.DegreeDiameter.Framework

/-!
# The exact Moore bound

This module proves the standard breadth-first (Moore) bound used in the
degree--diameter problem.  Starting from a root, a shortest route has at most
`d` choices for its first edge and at most `d - 1` choices for each later
edge: the edge just traversed cannot immediately be traversed backwards.

The route types below make that argument literal.  In particular, the proof
does not obtain the leading term indirectly from the coarser `(d + 1)^k`
bound in `Framework`.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

namespace MooreBound

open Set

namespace DegreeDiameter

open SimpleGraph

universe u

/-- A possible next vertex after traversing `previous -- current`, excluding
the immediate reverse step. -/
def ForwardNeighbor {V : Type u} (G : SimpleGraph V) (previous current : V) :=
  {next : V // G.Adj current next ∧ next ≠ previous}

instance finite_forwardNeighbor {V : Type u} [Finite V] (G : SimpleGraph V)
    (previous current : V) : Finite (ForwardNeighbor G previous current) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- An exact-length nonbacktracking continuation, after an initial directed
edge `previous -- current` has already been traversed. -/
def NBContinuation {V : Type u} (G : SimpleGraph V) : V → V → ℕ → Type u
  | _, _, 0 => PUnit
  | previous, current, n + 1 =>
      Σ next : ForwardNeighbor G previous current,
        NBContinuation G current next.1 n

instance finite_nbContinuation {V : Type u} [Finite V] (G : SimpleGraph V)
    (previous current : V) (n : ℕ) : Finite (NBContinuation G previous current n) := by
  classical
  induction n generalizing previous current with
  | zero => exact inferInstanceAs (Finite PUnit)
  | succ n ih =>
      change Finite
        (Σ next : ForwardNeighbor G previous current,
          NBContinuation G current next.1 n)
      let (next : ForwardNeighbor G previous current) :
          Finite (NBContinuation G current next.1 n) := ih current next.1
      let : Fintype (ForwardNeighbor G previous current) := Fintype.ofFinite _
      let (next : ForwardNeighbor G previous current) :
          Fintype (NBContinuation G current next.1 n) := Fintype.ofFinite _
      infer_instance

/-- An exact-length nonbacktracking route beginning at `root`. -/
def ExactNBRoute {V : Type u} (G : SimpleGraph V) (root : V) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => Σ first : G.neighborSet root, NBContinuation G root first.1 n

instance finite_exactNBRoute {V : Type u} [Finite V] (G : SimpleGraph V)
    (root : V) (n : ℕ) : Finite (ExactNBRoute G root n) := by
  classical
  cases n with
  | zero => exact inferInstanceAs (Finite PUnit)
  | succ n =>
      change Finite (Σ first : G.neighborSet root, NBContinuation G root first.1 n)
      let (first : G.neighborSet root) :
          Finite (NBContinuation G root first.1 n) := finite_nbContinuation G root first.1 n
      let : Fintype (G.neighborSet root) := Fintype.ofFinite _
      let (first : G.neighborSet root) :
          Fintype (NBContinuation G root first.1 n) := Fintype.ofFinite _
      infer_instance

/-- The last vertex of a nonbacktracking continuation. -/
def NBContinuation.endpoint {V : Type u} (G : SimpleGraph V) :
    {previous current : V} → {n : ℕ} → NBContinuation G previous current n → V
  | _, current, 0, _ => current
  | _, _, _ + 1, route => endpoint G route.2

/-- The last vertex of an exact nonbacktracking route. -/
def ExactNBRoute.endpoint {V : Type u} (G : SimpleGraph V) (root : V) :
    {n : ℕ} → ExactNBRoute G root n → V
  | 0, _ => root
  | _ + 1, route => NBContinuation.endpoint G route.2

lemma ExactNBRoute.endpoint_cast {V : Type u} (G : SimpleGraph V) (root : V)
    {m n : ℕ} (h : m = n) (route : ExactNBRoute G root m) :
    ExactNBRoute.endpoint G root (h ▸ route) =
      ExactNBRoute.endpoint G root route := by
  cases h
  rfl

/-- Convert a path beginning at `current`, which avoids `previous`, into the
corresponding nonbacktracking continuation. -/
def NBContinuation.ofPath {V : Type u} {G : SimpleGraph V} :
    {previous current target : V} → (p : G.Walk current target) →
      p.IsPath → previous ∉ p.support → NBContinuation G previous current p.length
  | _, _, _, .nil, _, _ => PUnit.unit
  | previous, current, target, .cons hadj tail, hp, hprevious =>
      ⟨⟨_, hadj, fun h ↦ hprevious (by
          simp only [Walk.support_cons, List.mem_cons]
          exact Or.inr (by simpa [h] using tail.start_mem_support))⟩,
        ofPath tail hp.of_cons ((Walk.cons_isPath_iff hadj tail).mp hp).2⟩

lemma NBContinuation.endpoint_ofPath {V : Type u} {G : SimpleGraph V}
    {previous current target : V} (p : G.Walk current target) (hp : p.IsPath)
    (hprevious : previous ∉ p.support) :
    (NBContinuation.ofPath p hp hprevious).endpoint G = target := by
  induction p generalizing previous with
  | nil => rfl
  | @cons current next target hadj tail ih =>
      simp only [NBContinuation.ofPath]
      exact ih hp.of_cons ((Walk.cons_isPath_iff hadj tail).mp hp).2

/-- Every path gives an exact nonbacktracking route with the same endpoint. -/
def ExactNBRoute.ofPath {V : Type u} {G : SimpleGraph V} {root target : V}
    (p : G.Walk root target) (hp : p.IsPath) : ExactNBRoute G root p.length :=
  match p with
  | .nil => PUnit.unit
  | .cons hadj tail =>
      ⟨⟨_, hadj⟩,
        NBContinuation.ofPath tail hp.of_cons
          ((Walk.cons_isPath_iff hadj tail).mp hp).2⟩

lemma ExactNBRoute.endpoint_ofPath {V : Type u} {G : SimpleGraph V}
    {root target : V} (p : G.Walk root target) (hp : p.IsPath) :
    (ExactNBRoute.ofPath p hp).endpoint G root = target := by
  cases p with
  | nil => rfl
  | @cons root next target hadj tail =>
      exact NBContinuation.endpoint_ofPath tail hp.of_cons
        ((Walk.cons_isPath_iff hadj tail).mp hp).2

/-- Removing the vertex just left leaves at most `d - 1` choices. -/
lemma natCard_forwardNeighbor_le {V : Type u} {G : SimpleGraph V}
    {d : ℕ} (hdegree : MaxDegreeLE G d) {previous current : V}
    (hpc : G.Adj previous current) :
    Nat.card (ForwardNeighbor G previous current) ≤ d - 1 := by
  change ({next : V | G.Adj current next ∧ next ≠ previous} : Set V).ncard ≤ d - 1
  have hset : {next : V | G.Adj current next ∧ next ≠ previous} =
      G.neighborSet current \ {previous} := by
    ext next
    simp [and_comm]
  rw [hset, Set.ncard_sdiff_singleton_of_mem]
  · exact Nat.sub_le_sub_right (hdegree current) 1
  · exact hpc.symm

/-- There are at most `(d - 1)^n` nonbacktracking continuations of length
`n` after a directed edge. -/
lemma natCard_nbContinuation_le {V : Type u} [Finite V] {G : SimpleGraph V}
    {d : ℕ} (hdegree : MaxDegreeLE G d) {previous current : V}
    (hpc : G.Adj previous current) (n : ℕ) :
    Nat.card (NBContinuation G previous current n) ≤ (d - 1) ^ n := by
  classical
  induction n generalizing previous current with
  | zero => simp [NBContinuation]
  | succ n ih =>
      let : Fintype (ForwardNeighbor G previous current) := Fintype.ofFinite _
      let (next : ForwardNeighbor G previous current) :
          Fintype (NBContinuation G current next.1 n) := Fintype.ofFinite _
      rw [show Nat.card (NBContinuation G previous current (n + 1)) =
          ∑ next : ForwardNeighbor G previous current,
            Nat.card (NBContinuation G current next.1 n) by
        change Nat.card
            (Σ next : ForwardNeighbor G previous current,
              NBContinuation G current next.1 n) = _
        rw [Nat.card_sigma]]
      calc
        ∑ next : ForwardNeighbor G previous current,
            Nat.card (NBContinuation G current next.1 n)
            ≤ ∑ _next : ForwardNeighbor G previous current, (d - 1) ^ n := by
              apply Finset.sum_le_sum
              intro next _
              exact ih next.2.1
        _ = Nat.card (ForwardNeighbor G previous current) * (d - 1) ^ n := by
              simp
        _ ≤ (d - 1) * (d - 1) ^ n :=
              Nat.mul_le_mul_right ((d - 1) ^ n)
                (natCard_forwardNeighbor_le hdegree hpc)
        _ = (d - 1) ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

/-- The distance-`n+1` route layer has at most `d(d-1)^n` members. -/
lemma natCard_exactNBRoute_succ_le {V : Type u} [Finite V] {G : SimpleGraph V}
    {d : ℕ} (hdegree : MaxDegreeLE G d) (root : V) (n : ℕ) :
    Nat.card (ExactNBRoute G root (n + 1)) ≤ d * (d - 1) ^ n := by
  classical
  let : Fintype (G.neighborSet root) := Fintype.ofFinite _
  let (first : G.neighborSet root) :
      Fintype (NBContinuation G root first.1 n) := Fintype.ofFinite _
  rw [show Nat.card (ExactNBRoute G root (n + 1)) =
      ∑ first : G.neighborSet root,
        Nat.card (NBContinuation G root first.1 n) by
    change Nat.card
        (Σ first : G.neighborSet root, NBContinuation G root first.1 n) = _
    rw [Nat.card_sigma]]
  calc
    ∑ first : G.neighborSet root,
        Nat.card (NBContinuation G root first.1 n)
        ≤ ∑ _first : G.neighborSet root, (d - 1) ^ n := by
          apply Finset.sum_le_sum
          intro first _
          exact natCard_nbContinuation_le hdegree first.2 n
    _ = Nat.card (G.neighborSet root) * (d - 1) ^ n := by simp
    _ ≤ d * (d - 1) ^ n := by
          apply Nat.mul_le_mul_right
          simpa [Nat.card_coe_set_eq] using hdegree root

/-- Routes of length at most `k`, presented recursively as the disjoint union
of the earlier layers and the exact length-`k` layer. -/
def BoundedNBRoute {V : Type u} (G : SimpleGraph V) (root : V) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => BoundedNBRoute G root k ⊕ ExactNBRoute G root (k + 1)

instance finite_boundedNBRoute {V : Type u} [Finite V] (G : SimpleGraph V)
    (root : V) (k : ℕ) : Finite (BoundedNBRoute G root k) := by
  classical
  induction k with
  | zero => exact inferInstanceAs (Finite PUnit)
  | succ k ih =>
      change Finite (BoundedNBRoute G root k ⊕ ExactNBRoute G root (k + 1))
      let : Finite (BoundedNBRoute G root k) := ih
      let : Fintype (BoundedNBRoute G root k) := Fintype.ofFinite _
      let : Fintype (ExactNBRoute G root (k + 1)) := Fintype.ofFinite _
      infer_instance

/-- Endpoint of a route of length at most `k`. -/
def BoundedNBRoute.endpoint {V : Type u} (G : SimpleGraph V) (root : V) :
    {k : ℕ} → BoundedNBRoute G root k → V
  | 0, _ => root
  | _ + 1, .inl route => endpoint G root route
  | _ + 1, .inr route => route.endpoint G root

/-- A path of length at most `k` belongs to the bounded route type and keeps
its endpoint.  This is the formal shortest/nonbacktracking-route step in the
standard Moore-bound proof. -/
lemma exists_boundedNBRoute_endpoint_of_path {V : Type u} {G : SimpleGraph V}
    {root target : V} (p : G.Walk root target) (hp : p.IsPath) {k : ℕ}
    (hlength : p.length ≤ k) :
    ∃ route : BoundedNBRoute G root k, route.endpoint G root = target := by
  induction k with
  | zero =>
      have hz : p.length = 0 := Nat.eq_zero_of_le_zero hlength
      have hrt : root = target := p.eq_of_length_eq_zero hz
      subst target
      exact ⟨PUnit.unit, rfl⟩
  | succ k ih =>
      by_cases hle : p.length ≤ k
      · obtain ⟨route, hroute⟩ := ih hle
        exact ⟨Sum.inl route, hroute⟩
      · have heq : p.length = k + 1 := by omega
        let route : ExactNBRoute G root (k + 1) :=
          heq ▸ ExactNBRoute.ofPath p hp
        refine ⟨Sum.inr route, ?_⟩
        change ExactNBRoute.endpoint G root route = target
        rw [show ExactNBRoute.endpoint G root route =
            ExactNBRoute.endpoint G root (ExactNBRoute.ofPath p hp) by
          exact ExactNBRoute.endpoint_cast G root heq (ExactNBRoute.ofPath p hp)]
        exact ExactNBRoute.endpoint_ofPath p hp

/-- The recursive bounded-route type has exactly the cardinality estimate in
the Moore expression. -/
lemma natCard_boundedNBRoute_le {V : Type u} [Finite V] {G : SimpleGraph V}
    {d : ℕ} (hdegree : MaxDegreeLE G d) (root : V) (k : ℕ) :
    Nat.card (BoundedNBRoute G root k) ≤ mooreBound k d := by
  induction k with
  | zero => simp [BoundedNBRoute, mooreBound]
  | succ k ih =>
      change Nat.card
          (BoundedNBRoute G root k ⊕ ExactNBRoute G root (k + 1)) ≤
        mooreBound (k + 1) d
      rw [Nat.card_sum]
      calc
        Nat.card (BoundedNBRoute G root k) +
            Nat.card (ExactNBRoute G root (k + 1))
            ≤ mooreBound k d + d * (d - 1) ^ k :=
              Nat.add_le_add ih (natCard_exactNBRoute_succ_le hdegree root k)
        _ = mooreBound (k + 1) d := by
              simp [mooreBound, Finset.sum_range_succ, Nat.mul_add, Nat.add_assoc]

/-- The exact Moore expression is bounded by the convenient leading-term
comparison `(d + 1)^k`.  This lemma is used only after the exact graph bound
has been established. -/
lemma mooreBound_le_add_one_pow (k d : ℕ) : mooreBound k d ≤ (d + 1) ^ k := by
  induction k with
  | zero => simp [mooreBound]
  | succ k ih =>
      rw [show mooreBound (k + 1) d =
          mooreBound k d + d * (d - 1) ^ k by
        simp [mooreBound, Finset.sum_range_succ, Nat.mul_add, Nat.add_assoc]]
      calc
        mooreBound k d + d * (d - 1) ^ k ≤
            (d + 1) ^ k + d * (d + 1) ^ k := by
          exact Nat.add_le_add ih
            (Nat.mul_le_mul_left d (Nat.pow_le_pow_left (by omega) k))
        _ = (d + 1) ^ (k + 1) := by
          rw [pow_succ, Nat.mul_add, Nat.mul_one,
            Nat.mul_comm d ((d + 1) ^ k), Nat.add_comm]

/-- Exact Moore bound for every finite graph of maximum degree at most `d`
and extended diameter at most `k`. -/
theorem natCard_le_mooreBound_of_ediam_le {V : Type u} [Finite V] [Nonempty V]
    {G : SimpleGraph V} {d k : ℕ} (hdegree : MaxDegreeLE G d)
    (hdiam : G.ediam ≤ (k : ℕ∞)) : Nat.card V ≤ mooreBound k d := by
  let root : V := Classical.ofNonempty
  have hsurj : Function.Surjective
      (BoundedNBRoute.endpoint G root (k := k)) := by
    intro target
    have hdist : G.edist root target ≤ (k : ℕ∞) :=
      SimpleGraph.edist_le_ediam.trans hdiam
    have hfinite : G.edist root target ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.natCast_ne_top k) hdist
    have hreachable : G.Reachable root target :=
      SimpleGraph.reachable_of_edist_ne_top hfinite
    obtain ⟨p, hp, hlengthDist⟩ := hreachable.exists_path_of_dist
    have hlength : p.length ≤ k := by
      rw [hlengthDist]
      exact_mod_cast hreachable.coe_dist_eq_edist.trans_le hdist
    exact exists_boundedNBRoute_endpoint_of_path p hp hlength
  calc
    Nat.card V ≤ Nat.card (BoundedNBRoute G root k) :=
      Nat.card_le_card_of_surjective _ hsurj
    _ ≤ mooreBound k d := natCard_boundedNBRoute_le hdegree root k

/-- The exact Moore bound, including the empty vertex type. -/
theorem natCard_le_mooreBound_of_ediam_le' {V : Type u} [Finite V]
    {G : SimpleGraph V} {d k : ℕ} (hdegree : MaxDegreeLE G d)
    (hdiam : G.ediam ≤ (k : ℕ∞)) : Nat.card V ≤ mooreBound k d := by
  cases isEmpty_or_nonempty V
  · simp
  · exact natCard_le_mooreBound_of_ediam_le hdegree hdiam

/-- Every graph order admitted in the definition of `nKD` obeys the exact
Moore bound. -/
theorem orderAdmissible_le_mooreBound {k d n : ℕ}
    (hn : OrderAdmissible k d n) : n ≤ mooreBound k d := by
  rcases hn with ⟨V, G, hfinite, hcard, hdegree, hdiam⟩
  let : Finite V := hfinite
  rw [← hcard]
  exact natCard_le_mooreBound_of_ediam_le' hdegree hdiam

/-- The exact paper inequality `n_k(d) ≤ 1 + d ∑_{j<k}(d-1)^j`. -/
theorem nKD_le_mooreBound (k d : ℕ) : nKD k d ≤ mooreBound k d :=
  orderAdmissible_le_mooreBound (nKD_admissible k d)

end DegreeDiameter

end MooreBound
