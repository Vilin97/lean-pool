/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.OscillatoryReductionSeries

/-!
# The exact oscillatory action on integrable inputs

The global annular amplitude bounds decay geometrically with the height.
They justify the actual height series and its high-pass integral for every
integrable input, without compact-support or convergence assumptions.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuadraticCarleson
namespace OscillatoryReduction

theorem fixedHeightRadius_eq_zero_mul_pow (lam : ℝ) (hlam : lam ≠ 0) (r : ℕ) :
    fixedHeightRadius lam r hlam = fixedHeightRadius lam 0 hlam * (2 : ℝ) ^ r := by
  unfold fixedHeightRadius
  rw [oscillatoryScaleIndex_eq_add]
  rw [show oscillatoryScaleIndex lam 0 hlam + (r : ℤ) - 1 =
    (oscillatoryScaleIndex lam 0 hlam - 1) + (r : ℤ) by ring]
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]

theorem summable_fixedHeightKernelBounds (lam : ℝ) (hlam : lam ≠ 0) :
    Summable (fun r : ℕ ↦ (2 * positiveDyadicAmplitudeBound) /
      fixedHeightRadius lam r hlam) := by
  have hs : Summable (fun r : ℕ ↦ (1 / 2 : ℝ) ^ r) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  apply (hs.mul_left ((2 * positiveDyadicAmplitudeBound) /
    fixedHeightRadius lam 0 hlam)).congr
  intro r
  rw [fixedHeightRadius_eq_zero_mul_pow lam hlam r, div_pow]
  simp only [one_pow]
  ring

theorem summable_integral_norm_fixedHeight (lam : ℝ) (hlam : lam ≠ 0)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Summable (fun r : ℕ ↦ ∫ y,
      ‖fixedHeightQuadraticKernel lam r hlam (x - y) * f y‖) := by
  apply Summable.of_nonneg_of_le (fun r ↦ integral_nonneg (fun y ↦ norm_nonneg _))
    (f := fun r ↦ ((2 * positiveDyadicAmplitudeBound) /
      fixedHeightRadius lam r hlam) * ∫ y, ‖f y‖)
  · intro r
    calc
      _ ≤ ∫ y, ((2 * positiveDyadicAmplitudeBound) /
          fixedHeightRadius lam r hlam) * ‖f y‖ := by
        apply integral_mono
        · exact (PositiveLowFullEstimate.integrable_fixedHeightQuadraticKernel_mul_locallyIntegrable
            hf.locallyIntegrable r lam hlam x).norm
        · exact hf.norm.const_mul _
        · intro y
          dsimp only
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (norm_fixedHeightQuadraticKernel_le lam r hlam (x-y))
            (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  · exact (summable_fixedHeightKernelBounds lam hlam).mul_right _

theorem hasSum_oscillatoryIntegrals_of_integrable (lam : ℝ) (hlam : lam ≠ 0)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    HasSum (fun r : ℕ ↦ ∫ t, f (x - t) *
      (dyadicPsi (oscillatoryScaleIndex lam r hlam) t : ℂ) * phase (lam * t ^ 2))
      (∫ y, highPassKernel lam hlam (x - y) * f y) := by
  have hs := hasSum_integral_of_summable_integral_norm
    (fun r ↦ PositiveLowFullEstimate.integrable_fixedHeightQuadraticKernel_mul_locallyIntegrable
      hf.locallyIntegrable r lam hlam x)
    (summable_integral_norm_fixedHeight lam hlam hf x)
  have hp (y : ℝ) : (∑' r : ℕ, fixedHeightQuadraticKernel lam r hlam (x - y) * f y) =
      highPassKernel lam hlam (x - y) * f y :=
    ((hasSum_oscillatoryKernels lam hlam (x - y)).mul_right (f y)).tsum_eq
  simp_rw [hp] at hs
  exact hs.congr_fun (fun r ↦
    (fixedHeightQuadraticKernel_integral_eq_paper r lam hlam f x).symm)

theorem paperOscillatoryAction_eq_integral_of_integrable (lam : ℝ) (hlam : lam ≠ 0)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    paperOscillatoryAction lam hlam f x =
      ∫ y, highPassKernel lam hlam (x - y) * f y :=
  (hasSum_oscillatoryIntegrals_of_integrable lam hlam hf x).tsum_eq

theorem integrable_highPassKernel_mul (lam : ℝ) (hlam : lam ≠ 0)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Integrable (fun y ↦ highPassKernel lam hlam (x - y) * f y) := by
  exact hf.bdd_mul
    ((measurable_highPassKernel lam hlam).comp (measurable_const.sub
      measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y ↦ highPassKernel_norm_le lam hlam (x-y))

/-- Linearity of the genuine height series follows from its proved bounded
high-pass integral representation. -/
theorem paperOscillatoryAction_add_of_integrable (lam : ℝ) (hlam : lam ≠ 0)
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    paperOscillatoryAction lam hlam (f + g) x =
      paperOscillatoryAction lam hlam f x + paperOscillatoryAction lam hlam g x := by
  rw [paperOscillatoryAction_eq_integral_of_integrable lam hlam (hf.add hg),
    paperOscillatoryAction_eq_integral_of_integrable lam hlam hf,
    paperOscillatoryAction_eq_integral_of_integrable lam hlam hg]
  simp only [Pi.add_apply, mul_add]
  exact integral_add (integrable_highPassKernel_mul lam hlam hf x)
    (integrable_highPassKernel_mul lam hlam hg x)

end OscillatoryReduction
end QuadraticCarleson
