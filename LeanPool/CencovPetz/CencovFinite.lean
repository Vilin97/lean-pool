/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.CencovPetz.CencovSplitPoint
import LeanPool.CencovPetz.ContinuousExtension
import LeanPool.CencovPetz.FisherContinuity
import LeanPool.CencovPetz.RationalDensity


/-!
# `CencovPetz.CencovFinite`

The finite/discrete Čencov (Chentsov) uniqueness theorem under continuity hypotheses.

In the purely algebraic part of the argument, one proves the scalar-multiple identity on:
1. the uniform point;
2. all common-denominator (“rational”) points via splitting.

This file provides the final topological step: since rational points are dense and Fisher is
continuous, any *continuous* monotone metric family coincides everywhere with a fixed scalar
multiple of Fisher.

## Main result

- `CencovPetz.MonotoneMetricFamily.eq_smul_fisher_of_continuous`
-/

namespace LeanPool.CencovPetz
open scoped BigOperators

namespace MonotoneMetricFamily

theorem eq_smul_fisher_of_continuous (G : MonotoneMetricFamily)
    {α : Type} [Fintype α] [Nonempty α]
    {a0 a1 : α} (ha01 : a0 ≠ a1)
    (hG : ∀ u v : tangentSpace (α := α), Continuous fun p : Simplex α => G.g (α := α) p u v) :
    ∀ (p : Simplex α) (u v : tangentSpace (α := α)),
      G.g (α := α) p u v = (uniformScalar G 2 (by decide)) * fisherBilin p u v := by
  classical
  let s : Set (Simplex α) := {p : Simplex α | Simplex.IsRational (α := α) p}
  have hs : Dense s := by
    simpa [s] using (Simplex.dense_setOf_isRational (α := α))
  let c : ℝ := uniformScalar G 2 (by decide)
  have hF : ∀ u v : tangentSpace (α := α),
      Continuous fun p : Simplex α => c * fisherBilin p u v := by
    intro u v
    exact (Simplex.continuous_fisherBilin_apply (α := α) u v).const_mul c
  have hEqOn : ∀ p ∈ s, ∀ u v : tangentSpace (α := α),
      G.g (α := α) p u v = c * fisherBilin p u v := by
    intro p hp u v
    simpa [c, s] using (eq_smul_fisher_of_isRational (G := G) (p := p) hp ha01 u v)
  simpa [c] using
    (eq_of_eqOn_dense₂ (α := α) (s := s) hs
      (f := fun p u v => G.g (α := α) p u v)
      (g := fun p u v => c * fisherBilin p u v)
      hG hF hEqOn)

end MonotoneMetricFamily
end LeanPool.CencovPetz
