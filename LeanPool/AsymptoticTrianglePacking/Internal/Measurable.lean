/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import LeanPool.AsymptoticTrianglePacking.Internal.Round
public import LeanPool.AsymptoticTrianglePacking.Internal.Survival
public import LeanPool.AsymptoticTrianglePacking.Internal.Covered
public import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — Module C4b-3b (measurability) : the covered event is
measurable

Standalone, Mathlib-only. Foundation for the Rödl-nibble project.

To integrate the residual degree (turning survival probabilities into an expected-value bound) we
need the covered events to be measurable. Since the retained set at `ω` is `H.filter (ω ∈ A ·)`
and the round's matching / covered set are finite Boolean combinations of the retention events
`A e` (over the finite edge set `H`), each covered event is measurable.

Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]

/-- **Measurability of the vertex-covered event.** `{ω | x ∈ covered(ω)}` is measurable: it is a
finite Boolean combination of the retention events `ρ.A e`, `e ∈ H`.

Hint: `x ∈ support (roundMatching (retainedSet H ρ ω))` unfolds to
`∃ e ∈ retainedSet H ρ ω, x ∈ e ∧ (∀ f ∈ retainedSet H ρ ω, f ≠ e → Disjoint e f)`, and
`e ∈ retainedSet H ρ ω ↔ e ∈ H ∧ ω ∈ ρ.A e`. Rewrite the set as a finite
`⋃ e ∈ H.filter (x ∈ ·), (ρ.A e ∩ ⋂ f ∈ H.filter (fun f => f ≠ e ∧ ¬ Disjoint e f), (ρ.A f)ᶜ)`
(or an equivalent finite Boolean combination), then close by `MeasurableSet.iUnion` /
`.biUnion` / `.iInter` / `.inter` / `.compl` using `ρ.meas`. All index sets are finite `Finset`s,
so the combination is finite. -/
theorem measurableSet_vertex_covered {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (x : V) :
    MeasurableSet {ω | x ∈ support (roundMatching (retainedSet H ρ ω))} := by
  have hrepr :
      {ω | x ∈ support (roundMatching (retainedSet H ρ ω))} =
        ⋃ e ∈ H.filter (fun e => x ∈ e),
          (ρ.A e ∩ ⋂ f ∈ H.filter (fun f => f ≠ e ∧ ¬ Disjoint e f), (ρ.A f)ᶜ) := by
    ext ω
    simp only [support, Finset.mem_biUnion, id_eq, roundMatching,
      Finset.mem_filter, retainedSet, Set.mem_ofPred_eq, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨e, ⟨⟨heH, heA⟩, hisolated⟩, hxe⟩
      refine ⟨e, ⟨heH, hxe⟩, heA, ?_⟩
      intro f hf hfA
      rcases hf with ⟨hfH, hfe, hconf⟩
      exact hconf (hisolated f ⟨hfH, hfA⟩ hfe)
    · rintro ⟨e, ⟨heH, hxe⟩, heA, hconf⟩
      refine ⟨e, ⟨⟨heH, heA⟩, ?_⟩, hxe⟩
      intro f hf hfe
      by_contra hdis
      exact hconf f ⟨hf.1, hfe, hdis⟩ hf.2
  rw [hrepr]
  apply Finset.measurableSet_biUnion
  intro e he
  apply MeasurableSet.inter (ρ.meas e)
  apply Finset.measurableSet_biInter
  intro f hf
  exact (ρ.meas f).compl

end LeanPool.AsymptoticTrianglePacking.Internal
