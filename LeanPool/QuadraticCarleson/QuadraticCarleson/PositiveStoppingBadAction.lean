/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveStoppingBadRecombination
public import LeanPool.QuadraticCarleson.QuadraticCarleson.OscillatoryReductionL1
public import LeanPool.QuadraticCarleson.QuadraticCarleson.OscillatoryReductionMaximal

/-! # Genuine oscillatory action of the canonical stopping bad part -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveStoppingBadEstimate

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open PositiveEndpointOptimization PositiveHighHeightEstimate PositiveLowFullEstimate
open OscillatoryReduction

theorem tsum_lintegral_enorm_highPass_stoppingLevels_lt_top
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (lam : ℝ) (hlam : lam ≠ 0) (x : ℝ) :
    (∑' k, ∫⁻ y, ‖highPassKernel lam hlam (x-y) * stoppingLevelBadPart f k y‖ₑ) < ∞ := by
  have hp (k : ℕ) : (∫⁻ y, ‖highPassKernel lam hlam (x-y) * stoppingLevelBadPart f k y‖ₑ) ≤
      ENNReal.ofReal (2 / innerRadius lam hlam) * ∫⁻ y, ‖stoppingLevelBadPart f k y‖ₑ := by
    calc
      _ ≤ ∫⁻ y, ENNReal.ofReal (2 / innerRadius lam hlam) * ‖stoppingLevelBadPart f k y‖ₑ := by
        apply lintegral_mono
        intro y
        dsimp only
        rw [enorm_mul]
        exact mul_le_mul' (by
          simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal
            (highPassKernel_norm_le lam hlam (x-y))) le_rfl
      _ = _ := lintegral_const_mul' _ _ (by finiteness)
  have hs := ENNReal.tsum_le_tsum hp
  rw [ENNReal.tsum_mul_left] at hs
  exact hs.trans_lt (ENNReal.mul_lt_top (by finiteness)
    ((tsum_lintegral_enorm_stoppingLevelBadPart_le hf).trans_lt
      (ENNReal.mul_lt_top (by finiteness) hfi.hasFiniteIntegral)))

/-- This is an actual integral/series interchange, not a supplied assembly
identity. It holds at every point and every nonzero real modulation. -/
theorem paperOscillatoryAction_stoppingBadPart_eq_tsum
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (lam : ℝ) (hlam : lam ≠ 0) (x : ℝ) :
    paperOscillatoryAction lam hlam (stoppingBadPart f) x =
      ∑' k, paperOscillatoryAction lam hlam (stoppingLevelBadPart f k) x := by
  rw [paperOscillatoryAction_eq_integral_of_integrable lam hlam
    (integrable_stoppingBadPart hf hfi)]
  simp_rw [paperOscillatoryAction_eq_integral_of_integrable lam hlam
    (integrable_stoppingLevelBadPart hf hfi _)]
  have hp (y : ℝ) : highPassKernel lam hlam (x-y) * stoppingBadPart f y =
      ∑' k, highPassKernel lam hlam (x-y) * stoppingLevelBadPart f k y := by
    rw [← tsum_stoppingLevelBadPart hf hfi y, tsum_mul_left]
  simp_rw [hp]
  exact integral_tsum
    (fun k ↦ (integrable_highPassKernel_mul lam hlam (integrable_stoppingLevelBadPart hf hfi k)
      x).1)
    (tsum_lintegral_enorm_highPass_stoppingLevels_lt_top hf hfi lam hlam x).ne

theorem paperOscillatoryAction_eq_low_add_high {b : ℝ → ℂ} (hb : Integrable b)
    (B : ℕ) (lam : ℝ) (hlam : lam ≠ 0) (x : ℝ) :
    paperOscillatoryAction lam hlam b x =
      (∑ r ∈ Finset.range (B+1), ∫ t, b (x-t) *
        (dyadicPsi (oscillatoryScaleIndex lam r hlam) t : ℂ) * phase (lam*t^2)) +
      ∑' n : ℕ, ∫ t, b (x-t) *
        (dyadicPsi (oscillatoryScaleIndex lam (B+n+1) hlam) t : ℂ) * phase (lam*t^2) := by
  have hs := (hasSum_oscillatoryIntegrals_of_integrable lam hlam hb x).summable
  simpa only [paperOscillatoryAction, show ∀ n : ℕ, n + (B+1) = B+n+1 by omega] using
    (hs.sum_add_tsum_nat_add (B+1)).symm

/-- Pointwise domination by precisely the already-estimated finite low
heights and strict high tail, with the canonical stopping interval family. -/
theorem paperOscillatoryMaximal_stoppingBadPart_le_low_add_high
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) (x : ℝ) :
    paperOscillatoryMaximal (stoppingBadPart f) x ≤
      paperFullLowHeightContribution f (stoppingCenter (f := f)) stoppingLength x +
        paperHighContribution fullHighCutoff (stoppingLevelBadPart f) x := by
  apply iSup_le
  intro lam
  rw [paperOscillatoryAction_stoppingBadPart_eq_tsum hf hfi lam.1 lam.2 x]
  apply enorm_tsum_le_tsum_enorm.trans
  unfold paperFullLowHeightContribution paperHighContribution
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro k
  rw [paperOscillatoryAction_eq_low_add_high (integrable_stoppingLevelBadPart hf hfi k)
    (fullHighCutoff k) lam.1 lam.2 x]
  apply (enorm_add_le _ _).trans
  apply add_le_add
  · exact le_iSup (fun μ : {μ : ℝ // μ ≠ 0} ↦
      ‖∑ r ∈ Finset.range (fullHighCutoff k+1), ∫ t, stoppingLevelBadPart f k (x-t) *
        (dyadicPsi (oscillatoryScaleIndex μ.1 r μ.2) t : ℂ) * phase (μ.1*t^2)‖ₑ) lam
  · exact le_iSup (fun μ : {μ : ℝ // μ ≠ 0} ↦
      ‖∑' n : ℕ, ∫ t, stoppingLevelBadPart f k (x-t) *
        (dyadicPsi (oscillatoryScaleIndex μ.1 (fullHighCutoff k+n+1) μ.2) t : ℂ) *
          phase (μ.1*t^2)‖ₑ) lam

end PositiveStoppingBadEstimate
end QuadraticCarleson
