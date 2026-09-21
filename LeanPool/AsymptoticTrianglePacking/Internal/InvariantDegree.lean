/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# LeanPool.AsymptoticTrianglePacking.Internal — step-2 invariant : the residual keeps max degree `≤ Δ`

Standalone, Mathlib-only. The "free" half of the step-2 round invariant: since every nibble residual
is a sub-hypergraph of `H` (`nibbleResidual_subset`), degrees only drop, so a global max-degree bound
`Δ` on `H` is inherited by every residual. (`r`-uniformity is likewise inherited, via
`nibbleResidual_uniform`.) These are the hypotheses of `exists_good_retention'` that hold for free
each round; the LOWER near-regularity (which does degrade) is the substantive part.

Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Basic
import LeanPool.AsymptoticTrianglePacking.Internal.Round
import LeanPool.AsymptoticTrianglePacking.Internal.Iteration

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- Degree is monotone under sub-hypergraphs. -/
theorem degree_mono {S H : Finset (Finset V)} (hSH : S ⊆ H) (v : V) :
    degree S v ≤ degree H v :=
  Finset.card_le_card (Finset.filter_subset_filter _ hSH)

/-- **Invariant (free half) — the residual keeps max degree `≤ Δ`.** -/
theorem degree_nibbleResidual_le {R : Finset (Finset V) → Finset (Finset V)}
    (H : Finset (Finset V)) (k : ℕ) {Δ : ℕ} (hΔ : ∀ x, degree H x ≤ Δ) (v : V) :
    degree (nibbleResidual R H k) v ≤ Δ :=
  le_trans (degree_mono (nibbleResidual_subset R H k) v) (hΔ v)

end Hypergraph
