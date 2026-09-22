/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

import LeanPool.AsymptoticTrianglePacking.Internal.Tight.RoundExplicit
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.Pruning

/-!
# Iterable tight-band round

This module establishes the one-round estimates used by the finite near-regular hypergraph nibble.
It packages retention, concentration, degree-band, codegree, and cover-rate bounds in a form that
can be iterated by the schedule.
-/

open Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

/-- **The iterable (sharp) nibble round.**

For uniformity `r ≥ 2` and free parameters

* `γ` — the round rate (retention `p = γ/(rΔ)`),
* `ε` — the relative tolerance: both band tolerances are `ε·γΔ`, a factor `ε` below the first-order
  per-round gain `≍ γΔ`,
* `θ` — the exceptional fraction: at most `θ|V|` vertices leave the band,
* `α` — the guaranteed relative size of the live set `A`,

there are a degree threshold `D₀` and a codegree factor `c₀` such that every `r`-uniform hypergraph
`K` with

* a GLOBAL degree ceiling `Δ`,
* a degree floor `δ` on the live set `A`, with `Δ ≤ 2δ`,
* codegrees at most `κ ≤ c₀Δ`,
* `Δ ≥ D₀`, `|V| ≥ D₀` and `|A| ≥ α|V|`,

admits a retained set `R' ⊆ K` and an exceptional set `B`, `|B| ≤ θ|V|`, such that

* every live, uncovered `v ∉ B` has residual degree at least `δ − ((r−1)/r)γΔ − εγΔ` and at most
  `Δ − ((r−1)/r)·γ·(δ − lost(v))·δ·(1−γ)/Δ + εγΔ`, where `lost(v) = lostDegree K Aᶜ v` counts the
  edges at `v` leaving `A`, and
* the round covers at least a `γ/(8r)` fraction of `A`. -/
def SharpRoundFor (r : ℕ) (γ ε θ α D₀ c₀ : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (K : Finset (Finset V)) (A : Finset V)
    (δ Δ κ : ℝ),
    IsUniform K r →
    (∀ v : V, (degree K v : ℝ) ≤ Δ) →
    (∀ v ∈ A, δ ≤ (degree K v : ℝ)) →
    (∀ x y : V, x ≠ y → (codegree K x y : ℝ) ≤ κ) →
    0 ≤ κ → κ ≤ c₀ * Δ → D₀ ≤ Δ → Δ ≤ 2 * δ →
    D₀ ≤ (Fintype.card V : ℝ) → α * (Fintype.card V : ℝ) ≤ (A.card : ℝ) →
    ∃ R' : Finset (Finset V), R' ⊆ K ∧ ∃ B : Finset V,
      (B.card : ℝ) ≤ θ * (Fintype.card V : ℝ) ∧
      (∀ v ∈ A, v ∉ B → v ∉ covered R' →
        δ - ((r : ℝ) - 1) / r * γ * Δ - ε * γ * Δ
            ≤ (degree (Hypergraph.residual K R') v : ℝ)
        ∧ (degree (Hypergraph.residual K R') v : ℝ)
            ≤ Δ - ((r : ℝ) - 1) / r * γ * (δ - (lostDegree K Aᶜ v : ℝ)) * δ * (1 - γ) / Δ
                + ε * γ * Δ) ∧
      γ / (8 * (r : ℝ)) * (A.card : ℝ) ≤ ((covered R').card : ℝ)

/-- **The iterable (sharp) nibble round**, packaged: for every uniformity and every choice of the
four free parameters there are a degree threshold `D₀` and a codegree factor `c₀` for which
`LeanPool.AsymptoticTrianglePacking.Internal.SharpRoundFor` holds. -/
def SharpRoundHyp : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (γ ε θ α : ℝ), 0 < γ → γ ≤ 1 / 2 → 0 < ε → ε ≤ 1 →
      0 < θ → θ ≤ 1 → 0 < α → α ≤ 1 →
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ SharpRoundFor r γ ε θ α D₀ c₀

end LeanPool.AsymptoticTrianglePacking.Internal
