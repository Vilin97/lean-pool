/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# LeanPool.AsymptoticTrianglePacking.Internal — Module C4b-0 : the conflict count of an edge (deterministic)

Standalone, Mathlib-only. Foundation for the Rödl-nibble project.

In one nibble round an edge `e` is placed in the matching iff it is retained and none of its
*conflicting* edges (other edges sharing a vertex with `e`) is retained. The number of conflicting
edges controls the correlation between "e survives" events; this module bounds it deterministically.

* `conflicts H e` — the edges of `H` other than `e` that meet `e`.
* `conflicts_card_le` — `|conflicts H e| ≤ ∑_{x∈e} deg x`.
* `conflicts_card_le_of_uniform` — for an `r`-uniform hypergraph with max degree `≤ Δ`,
  `|conflicts H e| ≤ r · Δ`.

Definitions (`degree`, `IsUniform`) come from `LeanPool.AsymptoticTrianglePacking.Internal.Basic`.
Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Bound

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- The conflict set of an edge `e`: the other edges of `H` that meet `e`. -/
def conflicts (H : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  H.filter (fun f => f ≠ e ∧ (e ∩ f).Nonempty)

/-- **C4b-0a — conflict-count bound by degrees.** `|conflicts H e| ≤ ∑_{x∈e} deg x`. -/
theorem conflicts_card_le (H : Finset (Finset V)) (e : Finset V) :
    (conflicts H e).card ≤ ∑ x ∈ e, degree H x := by
  classical
  have hsub : conflicts H e ⊆ e.biUnion (fun x => H.filter (fun f => x ∈ f)) := by
    intro f hf
    rw [conflicts, Finset.mem_filter] at hf
    obtain ⟨hfH, _, x, hx⟩ := hf
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_biUnion]
    exact ⟨x, hx.1, Finset.mem_filter.mpr ⟨hfH, hx.2⟩⟩
  calc (conflicts H e).card
      ≤ (e.biUnion (fun x => H.filter (fun f => x ∈ f))).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ e, (H.filter (fun f => x ∈ f)).card := Finset.card_biUnion_le
    _ = ∑ x ∈ e, degree H x := rfl

/-- **C4b-0b — conflict-count bound for a regular uniform hypergraph.** If `H` is `r`-uniform and
every vertex has degree `≤ Δ`, then every edge conflicts with at most `r · Δ` others. -/
theorem conflicts_card_le_of_uniform {H : Finset (Finset V)} {r Δ : ℕ}
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) {e : Finset V} (he : e ∈ H) :
    (conflicts H e).card ≤ r * Δ := by
  calc (conflicts H e).card
      ≤ ∑ x ∈ e, degree H x := conflicts_card_le H e
    _ ≤ ∑ _x ∈ e, Δ := Finset.sum_le_sum (fun x _ => hΔ x)
    _ = e.card * Δ := by rw [Finset.sum_const, smul_eq_mul]
    _ = r * Δ := by rw [hr e he]

end Hypergraph
