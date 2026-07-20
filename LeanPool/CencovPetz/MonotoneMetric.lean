/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.CencovPetz.MarkovMorphism


/-!
# `CencovPetz.MonotoneMetric`

An interface for **monotone Riemannian metrics** on the finite open probability simplex
(Čencov/Chentsov setting), together with basic consequences.

We model a metric as a family of bilinear forms on the canonical tangent space
`tangentSpace α = {u : α → ℝ | ∑ u = 0}`.  A *monotone metric family* is one that is contractive
under Markov morphisms (`CencovPetz.MarkovMorphism`).

This file does **not** prove the full Čencov uniqueness theorem; it sets up the infrastructure
needed for that proof.

## Main definitions

- `CencovPetz.MonotoneMetricFamily`: assigns a pointwise metric to each finite type, and
  is monotone under Markov morphisms.
- `CencovPetz.fisherMetricFamily`: the Fisher metric family, as a monotone metric family.

## Main results

-/

namespace LeanPool.CencovPetz
open scoped BigOperators

universe u

/-- A *finite monotone metric family* on open simplices.

`g p` is a bilinear form on the canonical tangent space at `p`, and `monotone` asserts the
data-processing inequality under Markov morphisms. -/
structure MonotoneMetricFamily : Type _ where
  /-- The bilinear form at `p : Simplex α`. -/
  g :
    ∀ {α : Type u} [Fintype α], Simplex α → LinearMap.BilinForm ℝ (tangentSpace (α := α))
  /-- Symmetry of the bilinear form. -/
  symm :
    ∀ {α : Type u} [Fintype α] (p : Simplex α) (u v : tangentSpace (α := α)),
      g (α := α) p u v = g (α := α) p v u
  /-- Positive definiteness on tangent vectors. -/
  pos :
    ∀ {α : Type u} [Fintype α] (p : Simplex α) (u : tangentSpace (α := α)),
      u ≠ 0 → 0 < g (α := α) p u u
  /-- Monotonicity under Markov morphisms. -/
  monotone :
    ∀ {α β : Type u} [Fintype α] [Fintype β] (κ : MarkovMorphism α β) (p : Simplex α)
        (u : tangentSpace (α := α)),
      g (α := β) (κ.pushforward p) (κ.tangentPushforward u) (κ.tangentPushforward u) ≤
        g (α := α) p u u

/-- The Fisher metric family is a monotone metric family. -/
noncomputable def fisherMetricFamily : MonotoneMetricFamily where
  g := fun {α} _ => fisherBilin
  symm := by
    intro α _ p u v
    exact fisherBilin.comm (p := p) u v
  pos := by
    intro α _ p u hu
    exact fisherBilin.pos (p := p) u hu
  monotone := by
    intro α β _ _ κ p u
    exact fisherBilin_pushforward_le_of_markovMorphism (κ := κ) p u
end LeanPool.CencovPetz
