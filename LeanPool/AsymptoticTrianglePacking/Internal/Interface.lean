/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import LeanPool.AsymptoticTrianglePacking.Internal.Regular

/-!
# Near-regular hypergraph nibble interface

The interface records the finite matching statement established by the nibble construction:
near-regular, low-codegree uniform hypergraphs have near-perfect matchings.

Definitions come from `LeanPool.AsymptoticTrianglePacking.Internal.Basic` (`IsUniform`,
`IsMatching`) and `LeanPool.AsymptoticTrianglePacking.Internal.Regular`
(`NearlyRegular`, `CodegreeBounded`).
-/

public section

open Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

/-- **T3 interface — the nibble theorem.** For `r ≥ 2` and any target `β > 0`, there is a
near-regularity/codegree tolerance `μ > 0` such that every `r`-uniform hypergraph on a finite vertex
set that is `(1±μ)`-nearly `d`-regular with codegree `≤ μd` has a matching covering at least a
`(1-β)` fraction of the maximum possible (`|V|/r`). -/
def NibbleTheorem : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β → ∃ μ : ℝ, 0 < μ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
      IsUniform H r → NearlyRegular H d μ → CodegreeBounded H (μ * d) →
      ∃ M : Finset (Finset V), IsMatching H M ∧
        (1 - β) * ((Fintype.card V : ℝ) / r) ≤ (M.card : ℝ)

end LeanPool.AsymptoticTrianglePacking.Internal
