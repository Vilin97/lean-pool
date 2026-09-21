/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleMainTerm
import LeanPool.QuadraticCarleson.QuadraticCarleson.SchwartzModularOperator

/-!
# From a pointwise dyadic witness to the lacunary level-set lower bound

This module isolates the final measure-theoretic transfer in the negative
endpoint argument.  Once the analytic packet estimates supply a dyadic
modulation at every point of `E_N`, the actual lacunary operator has a level
set of measure at least an explicit positive multiple of `N`.
-/

open MeasureTheory Set
open scoped ENNReal SchwartzMap

namespace QuadraticCarleson


/-- The explicit coefficient in the proved translated-Bohr-set estimate. -/
noncomputable def negativeEndpointDelta : ℝ :=
  1 / (30720 * ((2 : ℝ) ^ 100 + 1))

theorem negativeEndpointDelta_pos : 0 < negativeEndpointDelta := by
  unfold negativeEndpointDelta
  positivity

theorem dyadicModulation_natCast (n : ℕ) :
    dyadicModulation (n : ℤ) = (2 : ℝ) ^ n := by
  simp [dyadicModulation]

/-- A single dyadic fixed-modulation lower bound is inherited by the
lacunary supremum. -/
theorem fixed_dyadic_le_lacunaryQuadraticCarlesonSchwartz
    (n : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ENNReal.ofReal ‖quadraticHilbertSchwartz ((2 : ℝ) ^ n) f x‖ ≤
      lacunaryQuadraticCarlesonSchwartz f x := by
  rw [← dyadicModulation_natCast n]
  exact quadraticHilbertSchwartz_le_lacunaryQuadraticCarlesonSchwartz (n : ℤ) f x

/-- Pointwise dyadic witnesses on the paper's set imply its inclusion in the
actual lacunary level set. -/
theorem paperTranslatedBohrSet_subset_lacunaryLevelSet_of_pointwise
    {N : ℕ} {L c : ℝ}
    (hpoint : ∀ x ∈ paperTranslatedBohrSet N L, ∃ n : ℕ,
      counterexampleHeight c N ≤
        ‖quadraticHilbertSchwartz ((2 : ℝ) ^ n) (counterexampleSchwartz N) x‖) :
    paperTranslatedBohrSet N L ⊆
      {x | ENNReal.ofReal (counterexampleHeight c N) ≤
        lacunaryQuadraticCarlesonSchwartz (counterexampleSchwartz N) x} := by
  intro x hx
  obtain ⟨n, hn⟩ := hpoint x hx
  exact (ENNReal.ofReal_le_ofReal hn).trans
    (fixed_dyadic_le_lacunaryQuadraticCarlesonSchwartz
      n (counterexampleSchwartz N) x)

/-- The full linear-in-`N` analytic level-set estimate follows from the
pointwise packet estimate on `E_N`.  The coefficient is the same explicit
positive constant already obtained from the Bohr second-moment argument. -/
theorem lacunary_counterexample_level_volume_ge_of_pointwise
    {N : ℕ} {L c : ℝ} (hN : 100 ≤ N)
    (hL : 2 ≤ 3 * (N : ℝ) ^ 2 / 5 + L)
    (hpoint : ∀ x ∈ paperTranslatedBohrSet N L, ∃ n : ℕ,
      counterexampleHeight c N ≤
        ‖quadraticHilbertSchwartz ((2 : ℝ) ^ n) (counterexampleSchwartz N) x‖) :
    ENNReal.ofReal (negativeEndpointDelta * (N : ℝ)) ≤
      volume {x | ENNReal.ofReal (counterexampleHeight c N) ≤
        lacunaryQuadraticCarlesonSchwartz (counterexampleSchwartz N) x} := by
  have hfinite : volume (paperTranslatedBohrSet N L) ≠ ∞ :=
    measure_ne_top_of_subset (paperTranslatedBohrSet_subset_Icc hN) (by simp)
  calc
    ENNReal.ofReal (negativeEndpointDelta * (N : ℝ)) =
        ENNReal.ofReal
          ((N : ℝ) / (30720 * ((2 : ℝ) ^ 100 + 1))) := by
      congr 1
      unfold negativeEndpointDelta
      ring
    _ ≤ ENNReal.ofReal (volume.real (paperTranslatedBohrSet N L)) :=
      ENNReal.ofReal_le_ofReal (paperTranslatedBohrSet_volume_real_ge (by omega) hL)
    _ = volume (paperTranslatedBohrSet N L) := ofReal_measureReal hfinite
    _ ≤ volume {x | ENNReal.ofReal (counterexampleHeight c N) ≤
        lacunaryQuadraticCarlesonSchwartz (counterexampleSchwartz N) x} :=
      measure_mono (paperTranslatedBohrSet_subset_lacunaryLevelSet_of_pointwise hpoint)

end QuadraticCarleson
