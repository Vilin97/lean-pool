/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# LeanPool.AsymptoticTrianglePacking.Internal — Module C4b-3b (part 1) : probability a vertex is covered

Standalone, Mathlib-only. Foundation for the Rödl-nibble project.

Under a Bernoulli retention, a vertex `x` is *covered* in a round when it lies in some edge of the
round's matching. Since a matched edge is in particular retained, the covered event is contained in
the union of the retention events of the edges through `x`; a union bound gives

  `ℙ(x covered) ≤ deg(x) · p`.

This union-bound estimate deliberately sidesteps the delicate correlation structure of the matching
(we only use "matched ⟹ retained"), and feeds the residual-degree mean lower bound
`E[deg_residual(v)] ≥ deg(v)·(1 - r·d·p)` (module C4b-3b part 2).

`retainedSet ρ ω` is the (classically decidable) set of retained edges at outcome `ω`.
Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Basic
import LeanPool.AsymptoticTrianglePacking.Internal.Round
import LeanPool.AsymptoticTrianglePacking.Internal.Survival
import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]

/-- The set of retained edges at outcome `ω` (classically decidable membership in the events). -/
noncomputable def retainedSet (H : Finset (Finset V)) {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (ω : Ω) : Finset (Finset V) :=
  H.filter (fun e => ω ∈ ρ.A e)

/-- **C4b-3b(1) — vertex-covered probability bound.** The probability that a vertex `x` is covered
by the round's matching is at most `deg(x) · p`. -/
theorem prob_vertex_covered {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (x : V) :
    (ℙ : Measure Ω) {ω | x ∈ support (roundMatching (retainedSet H ρ ω))}
      ≤ (degree H x : ENNReal) * ENNReal.ofReal p := by
  have hsub : {ω | x ∈ support (roundMatching (retainedSet H ρ ω))}
      ⊆ ⋃ e ∈ H.filter (fun e => x ∈ e), ρ.A e := by
    intro ω hω
    simp only [Set.mem_setOf_eq, support, Finset.mem_biUnion, id_eq] at hω
    obtain ⟨e, hem, hxe⟩ := hω
    have heR : e ∈ retainedSet H ρ ω := roundMatching_subset _ hem
    rw [retainedSet, Finset.mem_filter] at heR
    rw [Set.mem_iUnion₂]
    exact ⟨e, Finset.mem_filter.mpr ⟨heR.1, hxe⟩, heR.2⟩
  calc (ℙ : Measure Ω) {ω | x ∈ support (roundMatching (retainedSet H ρ ω))}
      ≤ (ℙ : Measure Ω) (⋃ e ∈ H.filter (fun e => x ∈ e), ρ.A e) := measure_mono hsub
    _ ≤ ∑ e ∈ H.filter (fun e => x ∈ e), (ℙ : Measure Ω) (ρ.A e) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _e ∈ H.filter (fun e => x ∈ e), ENNReal.ofReal p :=
        Finset.sum_congr rfl (fun e he => ρ.prob e (Finset.mem_of_mem_filter e he))
    _ = (degree H x : ENNReal) * ENNReal.ofReal p := by
        rw [Finset.sum_const, nsmul_eq_mul, degree]

/-- **C4b-3b(2) — edge-hit probability.** The probability that an edge `e` loses a vertex to the
covered set (so it fails to survive into the residual) is at most `∑_{x∈e} deg(x)·p`. Union bound
over the vertices of `e` of `prob_vertex_covered`. -/
theorem prob_edge_hit {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e : Finset V) :
    (ℙ : Measure Ω) {ω | ∃ x ∈ e, x ∈ support (roundMatching (retainedSet H ρ ω))}
      ≤ ∑ x ∈ e, (degree H x : ENNReal) * ENNReal.ofReal p := by
  have hsub : {ω | ∃ x ∈ e, x ∈ support (roundMatching (retainedSet H ρ ω))}
      ⊆ ⋃ x ∈ e, {ω | x ∈ support (roundMatching (retainedSet H ρ ω))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    obtain ⟨x, hxe, hx⟩ := hω
    rw [Set.mem_iUnion₂]
    exact ⟨x, hxe, hx⟩
  calc (ℙ : Measure Ω) {ω | ∃ x ∈ e, x ∈ support (roundMatching (retainedSet H ρ ω))}
      ≤ (ℙ : Measure Ω) (⋃ x ∈ e, {ω | x ∈ support (roundMatching (retainedSet H ρ ω))}) :=
        measure_mono hsub
    _ ≤ ∑ x ∈ e, (ℙ : Measure Ω) {ω | x ∈ support (roundMatching (retainedSet H ρ ω))} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ e, (degree H x : ENNReal) * ENNReal.ofReal p :=
        Finset.sum_le_sum (fun x _ => prob_vertex_covered ρ x)

/-- **C4b-3b(2') — edge-hit probability, regular form.** For an `r`-uniform hypergraph with max
degree `≤ Δ`, an edge is hit with probability at most `r·Δ·p`. -/
theorem prob_edge_hit_le {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ)
    {e : Finset V} (he : e ∈ H) :
    (ℙ : Measure Ω) {ω | ∃ x ∈ e, x ∈ support (roundMatching (retainedSet H ρ ω))}
      ≤ (r : ENNReal) * (Δ : ENNReal) * ENNReal.ofReal p := by
  calc (ℙ : Measure Ω) {ω | ∃ x ∈ e, x ∈ support (roundMatching (retainedSet H ρ ω))}
      ≤ ∑ x ∈ e, (degree H x : ENNReal) * ENNReal.ofReal p := prob_edge_hit ρ e
    _ ≤ ∑ _x ∈ e, (Δ : ENNReal) * ENNReal.ofReal p := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_left (by exact_mod_cast hΔ x) _
    _ = (r : ENNReal) * ((Δ : ENNReal) * ENNReal.ofReal p) := by
        rw [Finset.sum_const, nsmul_eq_mul, hr e he]
    _ = (r : ENNReal) * (Δ : ENNReal) * ENNReal.ofReal p := by rw [mul_assoc]

end LeanPool.AsymptoticTrianglePacking.Internal
