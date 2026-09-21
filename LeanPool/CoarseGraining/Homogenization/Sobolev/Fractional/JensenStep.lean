/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.Definitions
import LeanPool.CoarseGraining.Homogenization.Multiscale.OverlapLp

/-!
# Jensen/averaging step for the Gagliardo seminorm on overlap cubes

This file proves the per-cube Jensen step (U1): for an overlap cube `S`, the
`p`-th power of the `L^p(μ)` oscillation of `u` around its cube average is
controlled by the doubled `L^p` difference integral, where
`μ = ScalarOverlap.normalizedCubeMeasure S` is the probability normalization
of volume on the enlarged cube of `S`.

The proof is the standard one: the deviation from the average is the average
of differences (probability measure), the enorm of a Bochner integral is at
most the lintegral of enorms, and `L^1(μ) ↪ L^p(μ)` on a probability measure
(Jensen/Hölder).
-/

namespace Homogenization
namespace Gagliardo

open MeasureTheory
open scoped ENNReal

/-- U1 (Jensen per cube): the `p`-th power of the `L^p` oscillation around the
cube average is at most the doubled `L^p` difference integral, for a
probability normalization and `1 ≤ p < ∞`. -/
theorem eLpNorm_sub_average_rpow_le_double_lintegral {d : ℕ}
    (S : TriadicCube d) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {u : Vec d → ℝ}
    (hu : MeasureTheory.MemLp u p (ScalarOverlap.normalizedCubeMeasure S)) :
    (MeasureTheory.eLpNorm (fun x => u x - ScalarOverlap.cubeAverage S u) p
        (ScalarOverlap.normalizedCubeMeasure S)) ^ p.toReal ≤
      ∫⁻ x, ∫⁻ y, ‖u x - u y‖ₑ ^ p.toReal
        ∂(ScalarOverlap.normalizedCubeMeasure S)
        ∂(ScalarOverlap.normalizedCubeMeasure S) := by
  set μ : Measure (Vec d) := ScalarOverlap.normalizedCubeMeasure S with hμ
  -- The normalized cube measure is a probability measure.
  have hprob : IsProbabilityMeasure μ :=
    ⟨ScalarOverlap.normalizedCubeMeasure_apply_univ S⟩
  -- Exponent bookkeeping.
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  -- `u` is integrable on the probability measure.
  have hInt : Integrable u μ := hu.integrable hp
  -- Step 1: the deviation from the average is the average of differences.
  have havg : ∀ x : Vec d,
      u x - ScalarOverlap.cubeAverage S u = ∫ y, (u x - u y) ∂μ := by
    intro x
    have hsub : ∫ y, (u x - u y) ∂μ = (∫ _, u x ∂μ) - ∫ y, u y ∂μ :=
      integral_sub (integrable_const (u x)) hInt
    have hconst : (∫ _, u x ∂μ) = u x := by
      rw [integral_const, probReal_univ, one_smul]
    rw [hsub, hconst, ScalarOverlap.cubeAverage_eq_integral_normalizedCubeMeasure]
  -- Steps 2–3: pointwise bound for each fixed `x`.
  have hpoint : ∀ x : Vec d,
      ‖u x - ScalarOverlap.cubeAverage S u‖ₑ ^ p.toReal ≤
        ∫⁻ y, ‖u x - u y‖ₑ ^ p.toReal ∂μ := by
    intro x
    have hmeas : AEStronglyMeasurable (fun y => u x - u y) μ :=
      aestronglyMeasurable_const.sub hu.aestronglyMeasurable
    -- Step 2: enorm of the integral is at most the lintegral of enorms.
    have h1 : ‖u x - ScalarOverlap.cubeAverage S u‖ₑ ≤
        ∫⁻ y, ‖u x - u y‖ₑ ∂μ := by
      rw [havg x]
      exact enorm_integral_le_lintegral_enorm _
    -- Step 3: `L^1 ↪ L^p` on the probability measure `μ`.
    have h2 : ∫⁻ y, ‖u x - u y‖ₑ ∂μ ≤
        (∫⁻ y, ‖u x - u y‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
      have hle : eLpNorm (fun y => u x - u y) 1 μ ≤
          eLpNorm (fun y => u x - u y) p μ :=
        eLpNorm_le_eLpNorm_of_exponent_le hp hmeas
      rwa [eLpNorm_one_eq_lintegral_enorm,
        eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt] at hle
    calc ‖u x - ScalarOverlap.cubeAverage S u‖ₑ ^ p.toReal
        ≤ ((∫⁻ y, ‖u x - u y‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)) ^ p.toReal :=
          ENNReal.rpow_le_rpow (h1.trans h2) hpr.le
      _ = ∫⁻ y, ‖u x - u y‖ₑ ^ p.toReal ∂μ := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hpr.ne', ENNReal.rpow_one]
  -- Step 4: assemble via the `L^p` representation of the left-hand side.
  have hLHS : (eLpNorm (fun x => u x - ScalarOverlap.cubeAverage S u) p μ)
      ^ p.toReal =
      ∫⁻ x, ‖u x - ScalarOverlap.cubeAverage S u‖ₑ ^ p.toReal ∂μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, ← ENNReal.rpow_mul,
      one_div_mul_cancel hpr.ne', ENNReal.rpow_one]
  calc (eLpNorm (fun x => u x - ScalarOverlap.cubeAverage S u) p μ) ^ p.toReal
      = ∫⁻ x, ‖u x - ScalarOverlap.cubeAverage S u‖ₑ ^ p.toReal ∂μ := hLHS
    _ ≤ ∫⁻ x, ∫⁻ y, ‖u x - u y‖ₑ ^ p.toReal ∂μ ∂μ :=
        lintegral_mono fun x => hpoint x

end Gagliardo
end Homogenization
