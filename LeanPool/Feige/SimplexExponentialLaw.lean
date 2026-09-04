/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.NormalizedExponentialProbability
import LeanPool.Feige.GeometryBridge

/-!
# Uniform simplex law from normalized exponentials

This module identifies the factorial-density simplex measure obtained by
the normalized-exponential calculation with the project's existing uniform
simplex probability measure.
-/

open scoped ENNReal
open MeasureTheory Set

namespace Feige

variable {n : ℕ}

theorem normalizedExponentialSimplexMeasure_eq_uniform :
    normalizedExponentialSimplexMeasure (n := n) =
      simplexUniformMeasure (Fin n) := by
  unfold normalizedExponentialSimplexMeasure simplexUniformMeasure
    simplexRestrictedVolume
  rw [volume_fullSimplex_eq_factorial_inv (n := n)]
  rw [inv_inv]

/-- The normalized-coordinate map on real product coordinates. -/
noncomputable def normalizedExponentialCoordinates
    (e : ℝ × (Fin n → ℝ)) : Fin n → ℝ :=
  (exponentialSimplexInverse e).2

/-- Independent unit exponentials on the positive real orthant, written as
an absolutely continuous measure in real product coordinates. -/
noncomputable def realExponentialProductMeasure :
    Measure (ℝ × (Fin n → ℝ)) :=
  (volume.restrict (positiveExponentialOrthant (n := n))).withDensity
    (fun e ↦ ENNReal.ofReal (Real.exp (-exponentialTotal e)))

theorem realExponentialProductMeasure_lintegral
    (h : (Fin n → ℝ) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ e, h (normalizedExponentialCoordinates e)
        ∂(realExponentialProductMeasure (n := n)) =
      ∫⁻ x, h x ∂(simplexUniformMeasure (Fin n)) := by
  rw [realExponentialProductMeasure,
    lintegral_withDensity_eq_lintegral_mul]
  · change
      (∫⁻ e in positiveExponentialOrthant (n := n),
        ENNReal.ofReal (Real.exp (-exponentialTotal e)) *
          h (exponentialSimplexInverse e).2 ∂volume) = _
    rw [lintegral_normalizedExponential_eq_simplex h hh,
      normalizedExponentialSimplexMeasure_eq_uniform]
  · exact continuous_exponentialTotal.measurable.neg.exp.ennreal_ofReal
  · exact hh.comp measurable_exponentialSimplexInverse.snd

theorem measurable_normalizedExponentialCoordinates :
    Measurable (normalizedExponentialCoordinates (n := n)) :=
  measurable_exponentialSimplexInverse.snd

/-- Measure-level pushforward form of the normalized exponential law. -/
theorem map_realExponentialProductMeasure_normalizedCoordinates :
    Measure.map (normalizedExponentialCoordinates (n := n))
        (realExponentialProductMeasure (n := n)) =
      simplexUniformMeasure (Fin n) := by
  ext s hs
  have htest : Measurable
      (fun x : Fin n → ℝ ↦ s.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) := by
    exact measurable_one.indicator hs
  have h := realExponentialProductMeasure_lintegral
    (n := n) (fun x ↦ s.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) htest
  rw [Measure.map_apply measurable_normalizedExponentialCoordinates hs]
  calc
    realExponentialProductMeasure (n := n)
        (normalizedExponentialCoordinates ⁻¹' s) =
      ∫⁻ e, (normalizedExponentialCoordinates ⁻¹' s).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) e
        ∂(realExponentialProductMeasure (n := n)) := by
          rw [lintegral_indicator
            (hs.preimage measurable_normalizedExponentialCoordinates)]
          simp
    _ = ∫⁻ e, s.indicator (fun _ ↦ (1 : ℝ≥0∞))
        (normalizedExponentialCoordinates e)
        ∂(realExponentialProductMeasure (n := n)) := by
          apply lintegral_congr
          intro e
          rfl
    _ = _ := by
      rw [lintegral_indicator hs] at h
      simpa using h

end Feige
