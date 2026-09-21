/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — hypergraph foundations and the handshake identity

Standalone, Mathlib-only. Destined for a Mathlib PR. Foundation for the Rödl-nibble project.
A `r`-uniform hypergraph on a vertex type `V` is modelled as a `Finset (Finset V)` all of whose
edges have cardinality `r`.

Goals of this module:
* A1 — definitions: `degree`, `codegree`, `IsMatching`.
* A2 — the handshake identity `∑_v degree v = r * H.card` and the codegree double-count.

Everything here must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The degree of a vertex `v` in a hypergraph `H`: the number of edges containing `v`. -/
def degree (H : Finset (Finset V)) (v : V) : ℕ := (H.filter (fun e => v ∈ e)).card

/-- The codegree of a pair `x y`: the number of edges containing both. -/
def codegree (H : Finset (Finset V)) (x y : V) : ℕ :=
  (H.filter (fun e => x ∈ e ∧ y ∈ e)).card

/-- `H` is `r`-uniform: every edge has exactly `r` vertices. -/
def IsUniform (H : Finset (Finset V)) (r : ℕ) : Prop := ∀ e ∈ H, e.card = r

/-- A matching `M` in `H`: a subfamily of pairwise-disjoint edges. -/
structure IsMatching (H M : Finset (Finset V)) : Prop where
  subset : M ⊆ H
  disjoint : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

/-- **A2 — handshake identity.** For an `r`-uniform hypergraph,
`∑_v degree v = r * |H|`. Proof idea: double count the set of incidences
`{(v, e) : v ∈ e ∈ H}`; summing over `v` gives `∑ degree`, while summing over
`e` gives `∑_{e} |e| = r|H|`. -/
theorem sum_degree (H : Finset (Finset V)) {r : ℕ} (hr : IsUniform H r) :
    ∑ v : V, degree H v = r * H.card := by
  have hdeg (v : V) : degree H v = ∑ e ∈ H, if v ∈ e then 1 else 0 := by
    rw [degree, card_eq_sum_ones, sum_filter]
  simp_rw [hdeg]
  rw [sum_comm]
  calc
    ∑ e ∈ H, ∑ v : V, (if v ∈ e then (1 : ℕ) else 0) = ∑ e ∈ H, e.card := by
      apply sum_congr rfl
      intro e he
      rw [← sum_filter]
      simp
    _ = r * H.card := by
      calc
        ∑ e ∈ H, e.card = ∑ e ∈ H, r := by
          apply sum_congr rfl
          exact hr
        _ = r * H.card := by simp [Nat.mul_comm]

/-- **A2' — codegree double-count.** `∑_v (degree H v).choose 2 = ∑ over unordered pairs …`
stated here in the convenient ordered form: the number of (edge, ordered pair-in-edge) incidences
equals `∑_e |e|*(|e|-1) = r*(r-1)*|H|` for an `r`-uniform hypergraph. -/
theorem sum_codegree (H : Finset (Finset V)) {r : ℕ} (hr : IsUniform H r) :
    ∑ x : V, ∑ y : V, codegree H x y = r * r * H.card := by
  have hcode (x y : V) : codegree H x y =
      ∑ e ∈ H, if x ∈ e ∧ y ∈ e then 1 else 0 := by
    rw [codegree, card_eq_sum_ones, sum_filter]
  have hedge (e : Finset V) :
      (∑ x : V, ∑ y : V, if x ∈ e ∧ y ∈ e then (1 : ℕ) else 0) =
        e.card * e.card := by
    calc
      _ = ∑ x : V, if x ∈ e then e.card else 0 := by
        apply sum_congr rfl
        intro x hx
        by_cases hxe : x ∈ e
        · simp only [hxe, true_and, ite_true]
          rw [← sum_filter]
          simp
        · simp [hxe]
      _ = e.card * e.card := by
        rw [← sum_filter]
        simp
  simp_rw [hcode]
  calc
    ∑ x : V, ∑ y : V, ∑ e ∈ H, (if x ∈ e ∧ y ∈ e then (1 : ℕ) else 0) =
        ∑ x : V, ∑ e ∈ H, ∑ y : V,
          (if x ∈ e ∧ y ∈ e then (1 : ℕ) else 0) := by
      apply sum_congr rfl
      intro x hx
      rw [sum_comm]
    _ = ∑ e ∈ H, ∑ x : V, ∑ y : V,
          (if x ∈ e ∧ y ∈ e then (1 : ℕ) else 0) := by
      rw [sum_comm]
    _ = ∑ e ∈ H, e.card * e.card := by simp_rw [hedge]
    _ = r * r * H.card := by
      calc
        ∑ e ∈ H, e.card * e.card = ∑ e ∈ H, r * r := by
          apply sum_congr rfl
          intro e he
          rw [hr e he]
        _ = r * r * H.card := by
          simp [Nat.mul_comm]

end Hypergraph
