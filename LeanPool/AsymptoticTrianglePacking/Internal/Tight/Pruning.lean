/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import LeanPool.AsymptoticTrianglePacking.Internal.Greedy
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — deterministic pruning counts

Each nibble round produces a small set `B` of vertices whose safe degree left the target band; the
tight-band invariant is restored by DELETING them (and the edges through them).  Deleting `B` costs
every other vertex the edges it shares with `B`, and this file bounds that cost:

* `card_edges_meeting_le` — at most `|B|·Δ` edges meet `B`;
* `card_heavyLoss_le` — at most `r·|B|·Δ/t` vertices lose `≥ t` edges to the deletion;
* `degree_prune_ge` — the degree in the pruned hypergraph is the old degree minus the lost edges.

Pure `Finset` combinatorics, no probability.  placeholder-free and axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

public section

open Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The edges lost at `v` when the vertex set `B` is deleted. -/
@[expose] def lostDegree (H : Finset (Finset V)) (B : Finset V) (v : V) : ℕ :=
  (H.filter (fun e => v ∈ e ∧ ¬ Disjoint e B)).card

/-- The hypergraph with all edges meeting `B` removed. -/
@[expose] def prune (H : Finset (Finset V)) (B : Finset V) : Finset (Finset V) :=
  H.filter (fun e => Disjoint e B)

omit [Fintype V] in
/-- At most `|B|·Δ` edges meet `B`. -/
theorem card_edges_meeting_le {H : Finset (Finset V)} {Δ : ℕ} (hΔ : ∀ x, degree H x ≤ Δ)
    (B : Finset V) : (H.filter (fun e => ¬ Disjoint e B)).card ≤ B.card * Δ := by
  classical
  calc (H.filter (fun e => ¬ Disjoint e B)).card
      ≤ ∑ x ∈ B, degree H x := Hypergraph.edges_meeting_le_of_not_disjoint H B
    _ ≤ ∑ _x ∈ B, Δ := Finset.sum_le_sum (fun x _ => hΔ x)
    _ = B.card * Δ := by rw [Finset.sum_const, smul_eq_mul]

omit [Fintype V] in
/-- **Pruning splits the degree.** -/
theorem degree_prune_ge {H : Finset (Finset V)} (B : Finset V) (v : V) :
    degree H v ≤ degree (prune H B) v + lostDegree H B v := by
  classical
  have hsplit : degree H v
      = ((H.filter (fun e => v ∈ e)).filter (fun e => Disjoint e B)).card
        + ((H.filter (fun e => v ∈ e)).filter (fun e => ¬ Disjoint e B)).card := by
    rw [Finset.card_filter_add_card_filter_not]
    rfl
  have h1 : (H.filter (fun e => v ∈ e)).filter (fun e => Disjoint e B)
      = (prune H B).filter (fun e => v ∈ e) := by
    unfold prune
    ext e
    simp only [Finset.mem_filter]
    tauto
  have h2 : (H.filter (fun e => v ∈ e)).filter (fun e => ¬ Disjoint e B)
      = H.filter (fun e => v ∈ e ∧ ¬ Disjoint e B) := by
    ext e
    simp only [Finset.mem_filter]
    tauto
  rw [hsplit, h1, h2]
  rfl

/-- **Few vertices lose many edges.**  At most `r·|B|·Δ/t` vertices lose `≥ t` edges when `B` is
deleted. -/
theorem card_heavyLoss_le {H : Finset (Finset V)} {r Δ : ℕ} (hr : IsUniform H r)
    (hΔ : ∀ x, degree H x ≤ Δ) (B : Finset V) (t : ℕ) :
    (Finset.univ.filter (fun v => t ≤ lostDegree H B v)).card * t ≤ r * (B.card * Δ) := by
  classical
  set T := Finset.univ.filter (fun v => t ≤ lostDegree H B v) with hT
  have hsum : ∑ v : V, lostDegree H B v
      = ∑ e ∈ H.filter (fun e => ¬ Disjoint e B), e.card := by
    have h1 : ∀ v : V, lostDegree H B v
        = ∑ e ∈ H, (if v ∈ e ∧ ¬ Disjoint e B then 1 else 0) := by
      intro v; unfold lostDegree; rw [Finset.card_filter]
    simp_rw [h1]
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases hd : Disjoint e B
    · simp [hd]
    · simp [hd, Finset.sum_ite_mem]
  have hcard : T.card * t ≤ ∑ v ∈ T, lostDegree H B v := by
    calc T.card * t = ∑ _v ∈ T, t := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ T, lostDegree H B v :=
        Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
  have hle : ∑ v ∈ T, lostDegree H B v ≤ ∑ v : V, lostDegree H B v :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hedges : ∑ e ∈ H.filter (fun e => ¬ Disjoint e B), e.card
      ≤ r * (B.card * Δ) := by
    calc ∑ e ∈ H.filter (fun e => ¬ Disjoint e B), e.card
        = ∑ _e ∈ H.filter (fun e => ¬ Disjoint e B), r :=
          Finset.sum_congr rfl (fun e he => hr e (Finset.mem_of_mem_filter e he))
      _ = (H.filter (fun e => ¬ Disjoint e B)).card * r := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (B.card * Δ) * r := Nat.mul_le_mul_right _ (card_edges_meeting_le hΔ B)
      _ = r * (B.card * Δ) := Nat.mul_comm _ _
  omega

end LeanPool.AsymptoticTrianglePacking.Internal
