/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import LeanPool.ACMax.AHL.NBWalk

/-!
# Counting and extending non-backtracking walks

This module provides the counting vocabulary for the Alon–Hoory–Linial bound.
It builds on `IsNonBacktracking`, counts walks by their start and end vertices,
and describes the one-edge extension operation used in the weighted argument.

## Contents

* **`nb_concat_iff`** — the *extension characterization*: a non-nil walk `p` extended by an edge to
  `t` stays non-backtracking iff `p` was and `t` differs from `p`'s penultimate vertex.  This is the
  per-step branching rule the count is built on.
* **`nbWalksFrom`** — the finset of length-`k` non-backtracking walks starting at `x`, bundled with
  their (varying) endpoints as a sigma type; `card_nbWalksFrom` identifies its cardinality with the
  sum over endpoints of the filtered `finsetWalkLength`.

## Formalization note

The bundled count is `∑ v, ((G.finsetWalkLength r x v).filter IsNonBacktracking).card`, which equals
the cardinality of the sigma-`biUnion` `nbWalksFrom G x r` (the endpoints vary, so a bare `biUnion`
over `fun v => Finset (G.Walk x v)` is not type-correct — the fibers must be tagged by their
endpoint first, which is exactly what `nbWalksFrom` does).
-/

public section

namespace ACMax

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

/-- `IsNonBacktracking` is decidable: the defining `∀ i, i + 2 ≤ length → …` is a bounded quantifier
(any witness has `i < length`), so it reduces to a `Nat.decidableBallLT`-style decision. -/
instance decidableIsNonBacktracking [DecidableEq V] {u v : V} :
    DecidablePred (IsNonBacktracking : G.Walk u v → Prop) := fun w =>
  decidable_of_iff (∀ i, i < w.length → i + 2 ≤ w.length → w.getVert (i + 2) ≠ w.getVert i)
    ⟨fun H i hi => H i (by omega) hi, fun H i _ hi => H i hi⟩

/-- **Extension characterization.**  A non-nil walk `p : G.Walk x y` followed by an edge `h : Adj
y t`
is non-backtracking iff `p` is and the new vertex `t` differs from `p`'s penultimate vertex (so the
last step does not reverse the previous one). -/
theorem nb_concat_iff {x y t : V} (p : G.Walk x y) (hp : ¬ p.Nil) (h : G.Adj y t) :
    IsNonBacktracking (p.concat h) ↔ IsNonBacktracking p ∧ t ≠ p.penultimate := by
  have hL : 1 ≤ p.length := Walk.not_nil_iff_lt_length.mp hp
  have hcl : (p.concat h).length = p.length + 1 := Walk.length_concat p h
  have hgv : ∀ i, i ≤ p.length → (p.concat h).getVert i = p.getVert i := by
    intro i hi
    rw [Walk.concat_eq_append, Walk.getVert_append]
    rcases hi.lt_or_eq with hlt | heq
    · rw [ite_eq_left hlt]
    · rw [heq, ite_eq_right (lt_irrefl _), Nat.sub_self]; simp
  have hgt : (p.concat h).getVert (p.length + 1) = t := by
    rw [Walk.concat_eq_append, Walk.getVert_append, ite_eq_right (by omega),
      show p.length + 1 - p.length = 1 by omega]
    simp
  constructor
  · intro hq
    refine ⟨fun i hi => ?_, fun heq => ?_⟩
    · have hne := hq i (by rw [hcl]; omega)
      rwa [hgv (i + 2) (by omega), hgv i (by omega)] at hne
    · have hne := hq (p.length - 1) (by rw [hcl]; omega)
      rw [show p.length - 1 + 2 = p.length + 1 by omega, hgt, hgv (p.length - 1) (by omega)] at hne
      exact hne heq
  · rintro ⟨hnb, hne⟩ i hi
    rw [hcl] at hi
    rcases lt_or_ge (i + 2) (p.length + 1) with hlt | hge
    · rw [hgv (i + 2) (by omega), hgv i (by omega)]
      exact hnb i (by omega)
    · rw [show i + 2 = p.length + 1 by omega, hgt, hgv i (by omega), show i = p.length - 1 by omega]
      exact hne

/-- The embedding tagging a walk `p : G.Walk x v` with its endpoint `v`. -/
def sigmaWalkEmb (G : SimpleGraph V) (x v : V) : G.Walk x v ↪ Σ w : V, G.Walk x w :=
  ⟨fun p => ⟨v, p⟩, fun a b hab => by simpa using hab⟩

/-- The finset of length-`k` non-backtracking walks starting at `x`, bundled with their endpoints.
-/
def nbWalksFrom (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (x : V) (k : ℕ) : Finset (Σ v : V, G.Walk x v) :=
  univ.biUnion fun v =>
    ((G.finsetWalkLength k x v).filter IsNonBacktracking).map (sigmaWalkEmb G x v)

/-- Membership in `nbWalksFrom`: a bundled walk lies in it iff it has the right length and is
non-backtracking. -/
theorem mem_nbWalksFrom [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {x : V} {k : ℕ}
    {s : Σ v : V, G.Walk x v} :
    s ∈ nbWalksFrom G x k ↔ s.2.length = k ∧ IsNonBacktracking s.2 := by
  simp only [nbWalksFrom, mem_biUnion, mem_univ, true_and, mem_map, mem_filter,
    mem_finsetWalkLength_iff, sigmaWalkEmb]
  constructor
  · rintro ⟨v, p, ⟨hlen, hnb⟩, rfl⟩
    exact ⟨hlen, hnb⟩
  · rintro ⟨hlen, hnb⟩
    exact ⟨s.1, s.2, ⟨hlen, hnb⟩, rfl⟩

/-- The bundled count equals the sum over endpoints of the filtered `finsetWalkLength`
cardinality. -/
theorem card_nbWalksFrom [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (x : V) (k : ℕ) :
    (nbWalksFrom G x k).card =
      ∑ v : V, ((G.finsetWalkLength k x v).filter IsNonBacktracking).card := by
  have hdisj : Set.PairwiseDisjoint (↑(univ : Finset V))
      (fun v => ((G.finsetWalkLength k x v).filter IsNonBacktracking).map (sigmaWalkEmb G x v)) :=
        by
    intro v _ v' _ hvv
    refine Finset.disjoint_left.mpr fun s hs hs' => ?_
    simp only [mem_map, sigmaWalkEmb] at hs hs'
    obtain ⟨p, _, rfl⟩ := hs
    obtain ⟨p', _, hp'⟩ := hs'
    exact hvv (congrArg Sigma.fst hp').symm
  rw [nbWalksFrom, card_biUnion hdisj]
  exact Finset.sum_congr rfl fun v _ => card_map _

/-- The one-edge non-backtracking extensions of a bundled walk `s = ⟨u, p⟩`: for each neighbour `t`
of `u` other than the penultimate vertex of `p`, the walk `p.concat _`. -/
@[expose] def nbExtend (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (x : V)
    (s : Σ v : V, G.Walk x v) : Finset (Σ v : V, G.Walk x v) :=
  (G.neighborFinset s.1 \ {s.2.penultimate}).image fun t =>
    if h : G.Adj s.1 t then ⟨t, s.2.concat h⟩ else ⟨x, Walk.nil⟩

end ACMax
