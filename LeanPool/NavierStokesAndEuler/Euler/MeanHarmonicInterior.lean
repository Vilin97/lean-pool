/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicH2

@[expose] public section

/-!
# A proved interior bound for ordinary three-dimensional harmonic functions

The constant is built from fixed smooth cutoffs and the already proved Fourier
Sobolev inequality. It is independent of the harmonic function. The argument
uses two actual Caccioppoli estimates; no harmonic mean-value theorem or
interior regularity estimate is assumed.
-/

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus EulerSobolev
open scoped ContDiff

theorem localized_second_norm_le (h : Space → ℝ) (hh : ContDiff ℝ ∞ h)
    (hLp : MemLp h 2 volume) (hharmonic : ∀ x ∈ Metric.ball 0 (1 : ℝ), Δ h x = 0)
    (i : Fin 3) :
    lpNorm (partialDerivative (partialDerivative (innerCutoff * h) i) i) 2 volume ≤
      Real.sqrt interiorSecondEnergyConstant * lpNorm h 2 volume := by
  apply (sq_le_sq₀ lpNorm_nonneg (mul_nonneg (Real.sqrt_nonneg _) lpNorm_nonneg)).1
  rw [mul_pow, Real.sq_sqrt interiorSecondEnergyConstant_nonneg]
  exact localized_second_energy_le h hh hLp hharmonic i

theorem localized_norm_le (h : Space → ℝ) (hLp : MemLp h 2 volume) :
    lpNorm (innerCutoff * h) 2 volume ≤ lpNorm h 2 volume := by
  have H : lpNorm (innerCutoff * h) 2 volume ≤ lpNorm (fun x => ‖h x‖) 2 volume := by
    apply lpNorm_mono_real hLp.norm
    intro x
    calc
      ‖(innerCutoff * h) x‖ = |innerCutoff x| * ‖h x‖ := by
        simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
      _ ≤ 1 * ‖h x‖ := mul_le_mul_of_nonneg_right (abs_inner_le_one x) (norm_nonneg _)
      _ = ‖h x‖ := one_mul _
  simpa only [lpNorm_norm hLp.aestronglyMeasurable] using H

def harmonicInteriorConstant : ℝ :=
  embeddingConstant 3 2 (by norm_num) *
    (1 + (2 * Real.pi) ^ (-2 : ℤ) * (3 * Real.sqrt interiorSecondEnergyConstant))

theorem harmonicInteriorConstant_nonneg : 0 ≤ harmonicInteriorConstant := by
  unfold harmonicInteriorConstant embeddingConstant
  positivity

/-- A genuine L²-to-pointwise interior estimate on the unit ball in R³. -/
theorem harmonic_pointwise_halfBall (h : Space → ℝ) (hh : ContDiff ℝ ∞ h)
    (hLp : MemLp h 2 volume) (hharmonic : ∀ x ∈ Metric.ball 0 (1 : ℝ), Δ h x = 0)
    (x : Space) (hx : x ∈ Metric.closedBall 0 (1/2 : ℝ)) :
    |h x| ≤ harmonicInteriorConstant * lpNorm h 2 volume := by
  have hc : HasCompactSupport (innerCutoff * h) := inner_compact.mul_right (f' := h)
  have H := scalar_pointwise_le_H2 (innerCutoff * h) (inner_smooth.mul hh) hc x
  have hval : (innerCutoff * h) x = h x := by
    rw [Pi.mul_apply, inner_one_on_halfBall hx, one_mul]
  rw [hval] at H
  have hsum : (∑ i : Fin 3,
      lpNorm (partialDerivative (partialDerivative (innerCutoff * h) i) i) 2 volume) ≤
      3 * (Real.sqrt interiorSecondEnergyConstant * lpNorm h 2 volume) := by
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
      localized_second_norm_le h hh hLp hharmonic i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat] using hsum
  calc
    _ ≤ embeddingConstant 3 2 (by norm_num) *
        (lpNorm (innerCutoff * h) 2 volume + (2 * Real.pi) ^ (-2 : ℤ) *
          ∑ i : Fin 3, lpNorm (partialDerivative (partialDerivative (innerCutoff * h) i) i) 2
            volume) := H
    _ ≤ embeddingConstant 3 2 (by norm_num) *
        (lpNorm h 2 volume + (2 * Real.pi) ^ (-2 : ℤ) *
          (3 * (Real.sqrt interiorSecondEnergyConstant * lpNorm h 2 volume))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact add_le_add (localized_norm_le h hLp)
        (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = _ := by unfold harmonicInteriorConstant; ring

end EulerMeanHarmonic
