/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Ring

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — Module A3 : greedy / maximal-matching lower bound

Standalone, Mathlib-only. Foundation for the Rödl-nibble project.

Content:
* `matching_support_card` — a matching in an `r`-uniform hypergraph covers exactly `r · |M|`
  vertices.
* `edges_meeting_le` — the number of edges meeting a vertex set `S` is at most `∑_{v∈S} deg v`.
* `greedy_bound` — for a *maximal* matching `M` (every edge meets its support) with max degree
  `≤ Δ`, `|H| ≤ r · Δ · |M|`, i.e. `ν(H) ≥ |E| / (rΔ)`.

Definitions (`degree`, `IsUniform`, `IsMatching`) come from
`LeanPool.AsymptoticTrianglePacking.Internal.Basic`.
Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- The support (vertex set) of a family of edges. -/
def support (M : Finset (Finset V)) : Finset V := M.biUnion id

/-- **A3a — support cardinality.** A matching of an `r`-uniform hypergraph covers exactly
`r * |M|` vertices. -/
theorem matching_support_card {H M : Finset (Finset V)} {r : ℕ}
    (hr : IsUniform H r) (hM : IsMatching H M) :
    (support M).card = r * M.card := by
  classical
  unfold support
  rw [Finset.card_biUnion]
  · have : ∀ e ∈ M, (id e : Finset V).card = r := by
      intro e he; simpa using hr e (hM.subset he)
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]
  · intro x hx y hy hxy
    change Disjoint x y
    exact hM.disjoint x hx y hy hxy

/-- **A3b — edges meeting a set.** The number of edges of `H` meeting a vertex set `S` is at
most `∑_{v ∈ S} degree H v`. -/
theorem edges_meeting_le (H : Finset (Finset V)) (S : Finset V) :
    (H.filter (fun e => (e ∩ S).Nonempty)).card ≤ ∑ v ∈ S, degree H v := by
  classical
  have hsub : H.filter (fun e => (e ∩ S).Nonempty)
      ⊆ S.biUnion (fun v => H.filter (fun e => v ∈ e)) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heH, v, hv⟩ := he
    rw [Finset.mem_inter] at hv
    rw [Finset.mem_biUnion]
    exact ⟨v, hv.2, Finset.mem_filter.mpr ⟨heH, hv.1⟩⟩
  calc (H.filter (fun e => (e ∩ S).Nonempty)).card
      ≤ (S.biUnion (fun v => H.filter (fun e => v ∈ e))).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ S, (H.filter (fun e => v ∈ e)).card := Finset.card_biUnion_le
    _ = ∑ v ∈ S, degree H v := rfl

/-- The same incidence bound with meeting expressed as non-disjointness. -/
theorem edges_meeting_le_of_not_disjoint (H : Finset (Finset V)) (S : Finset V) :
    (H.filter (fun e => ¬ Disjoint e S)).card ≤ ∑ v ∈ S, degree H v := by
  classical
  have hfilter : H.filter (fun e => ¬ Disjoint e S) =
      H.filter (fun e => (e ∩ S).Nonempty) := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he, hnd⟩
      obtain ⟨x, hxe, hxS⟩ := Finset.not_disjoint_iff.mp hnd
      exact ⟨he, ⟨x, Finset.mem_inter.mpr ⟨hxe, hxS⟩⟩⟩
    · rintro ⟨he, x, hx⟩
      exact ⟨he, Finset.not_disjoint_iff.mpr ⟨x, (Finset.mem_inter.mp hx).1,
        (Finset.mem_inter.mp hx).2⟩⟩
  rw [hfilter]
  exact edges_meeting_le H S

/-- **A3 — greedy / maximal-matching bound.** If `M` is a matching whose support meets every
edge of `H` (a *maximal* matching) and every vertex has degree `≤ Δ`, then
`|H| ≤ r · Δ · |M|`. Equivalently `ν(H) ≥ |E| / (rΔ)`. -/
theorem greedy_bound {H M : Finset (Finset V)} {r Δ : ℕ}
    (hr : IsUniform H r) (hM : IsMatching H M)
    (hcov : ∀ e ∈ H, (e ∩ support M).Nonempty)
    (hΔ : ∀ v, degree H v ≤ Δ) :
    H.card ≤ r * Δ * M.card := by
  classical
  have hfilt : H.filter (fun e => (e ∩ support M).Nonempty) = H :=
    Finset.filter_true_of_mem hcov
  have hΔsum : ∑ v ∈ support M, degree H v ≤ (support M).card * Δ := by
    calc ∑ v ∈ support M, degree H v
        ≤ ∑ _v ∈ support M, Δ := Finset.sum_le_sum (fun v _ => hΔ v)
      _ = (support M).card * Δ := by rw [Finset.sum_const, smul_eq_mul]
  calc H.card = (H.filter (fun e => (e ∩ support M).Nonempty)).card := by rw [hfilt]
    _ ≤ ∑ v ∈ support M, degree H v := edges_meeting_le H (support M)
    _ ≤ (support M).card * Δ := hΔsum
    _ = r * M.card * Δ := by rw [matching_support_card hr hM]
    _ = r * Δ * M.card := by ring

end Hypergraph
