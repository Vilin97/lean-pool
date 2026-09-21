/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveGoodOscillatory
import LeanPool.QuadraticCarleson.QuadraticCarleson.CalderonZygmundDyadicStopping
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The actual stopping-time good contribution

The stopping construction itself proves `∫ |g|² ≤ 5 ∫ |f|`. Combining it
with the genuine all-height oscillatory L² estimate closes the good-part
level-set estimate, both for full real and for dyadic modulations.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace PositiveGoodOscillatory

open OscillatoryReduction CalderonZygmundDyadicStopping

theorem memLp_stoppingGoodPart {f : ℝ → ℂ} (hf : Integrable f) :
    MemLp (stoppingGoodPart f) 2 :=
  (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_stoppingGoodPart hf)).mpr
    (integrable_sq_norm_stoppingGoodPart hf)

theorem lintegral_sq_enorm_stoppingGoodPart_le {f : ℝ → ℂ} (hf : Integrable f) :
    (∫⁻ x, ‖stoppingGoodPart f x‖ₑ ^ 2) ≤ 5 * ∫⁻ x, ‖f x‖ₑ := by
  have heq : (∫⁻ x, ‖stoppingGoodPart f x‖ₑ ^ 2) =
      ENNReal.ofReal (∫ x, ‖stoppingGoodPart f x‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_sq_norm_stoppingGoodPart hf)
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg ‖stoppingGoodPart f x‖)]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hmass : ENNReal.ofReal (∫ x, ‖f x‖) = ∫⁻ x, ‖f x‖ₑ := by
    simpa only [ofReal_norm] using ofReal_integral_eq_lintegral_ofReal hf.norm
      (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
  calc
    _ = ENNReal.ofReal (∫ x, ‖stoppingGoodPart f x‖ ^ 2) := heq
    _ ≤ ENNReal.ofReal (5 * ∫ x, ‖f x‖) := ENNReal.ofReal_le_ofReal
      (integral_sq_norm_stoppingGoodPart_le_five_l1 hf)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5), hmass]; norm_num

noncomputable def stoppingGoodOscillatoryConstant : ℝ≥0∞ := 5 * allHeightL2Constant ^ 2

theorem stoppingGoodOscillatoryConstant_lt_top : stoppingGoodOscillatoryConstant < ∞ :=
  ENNReal.mul_lt_top (by finiteness) (ENNReal.pow_lt_top allHeightL2Constant_lt_top)

/-- A measurable squared-L² majorant for the actual good-part oscillatory
operator, bounded directly by the original input's L¹ mass. -/
theorem stoppingGoodPart_majorant_sq_lintegral_le {f : ℝ → ℂ} (hf : Integrable f) :
    (∫⁻ x, allHeightMajorant (stoppingGoodPart f) x ^ 2) ≤
      stoppingGoodOscillatoryConstant * ∫⁻ x, ‖f x‖ₑ := by
  apply (allHeightMajorant_sq_lintegral_le (memLp_stoppingGoodPart hf)).trans
  apply (mul_le_mul' le_rfl (lintegral_sq_enorm_stoppingGoodPart_le hf)).trans_eq
  unfold stoppingGoodOscillatoryConstant
  ring

theorem stoppingGoodPart_oscillatory_eLpNorm_sq_le {f : ℝ → ℂ} (hf : Integrable f) :
    eLpNorm (paperOscillatoryMaximal (stoppingGoodPart f)) 2 ^ 2 ≤
      stoppingGoodOscillatoryConstant * ∫⁻ x, ‖f x‖ₑ := by
  have h := pow_le_pow_left₀ bot_le
    (paperOscillatoryMaximal_eLpNorm_le (memLp_stoppingGoodPart hf)) 2
  rw [mul_pow, eLpNorm_two_sq_lintegral (stoppingGoodPart f)] at h
  apply h.trans
  apply (mul_le_mul' le_rfl (lintegral_sq_enorm_stoppingGoodPart_le hf)).trans_eq
  unfold stoppingGoodOscillatoryConstant
  ring

theorem stoppingGoodPart_oscillatory_levelSet_mul_le {f : ℝ → ℂ} (hf : Integrable f)
    (a : ℝ≥0∞) :
    a ^ 2 * volume {x | a < paperOscillatoryMaximal (stoppingGoodPart f) x} ≤
      stoppingGoodOscillatoryConstant * ∫⁻ x, ‖f x‖ₑ := by
  apply (paperOscillatoryMaximal_levelSet_mul_le (memLp_stoppingGoodPart hf) a).trans
  apply (mul_le_mul' le_rfl (lintegral_sq_enorm_stoppingGoodPart_le hf)).trans_eq
  unfold stoppingGoodOscillatoryConstant
  ring

/-- The full-real good contribution at the normalized endpoint threshold. -/
theorem stoppingGoodPart_oscillatory_levelSet_le {f : ℝ → ℂ} (hf : Integrable f) :
    volume {x | 1 < paperOscillatoryMaximal (stoppingGoodPart f) x} ≤
      stoppingGoodOscillatoryConstant * ∫⁻ x, ‖f x‖ₑ := by
  simpa only [one_pow, one_mul] using stoppingGoodPart_oscillatory_levelSet_mul_le hf 1

theorem stoppingGoodPart_lacunaryOscillatory_eLpNorm_sq_le
    {f : ℝ → ℂ} (hf : Integrable f) :
    eLpNorm (paperLacunaryOscillatoryMaximal (stoppingGoodPart f)) 2 ^ 2 ≤
      stoppingGoodOscillatoryConstant * ∫⁻ x, ‖f x‖ₑ := by
  have h := pow_le_pow_left₀ bot_le
    (paperLacunaryOscillatoryMaximal_eLpNorm_le (memLp_stoppingGoodPart hf)) 2
  rw [mul_pow, eLpNorm_two_sq_lintegral (stoppingGoodPart f)] at h
  apply h.trans
  apply (mul_le_mul' le_rfl (lintegral_sq_enorm_stoppingGoodPart_le hf)).trans_eq
  unfold stoppingGoodOscillatoryConstant
  ring

theorem stoppingGoodPart_lacunaryOscillatory_levelSet_mul_le
    {f : ℝ → ℂ} (hf : Integrable f) (a : ℝ≥0∞) :
    a ^ 2 * volume {x | a < paperLacunaryOscillatoryMaximal (stoppingGoodPart f) x} ≤
      stoppingGoodOscillatoryConstant * ∫⁻ x, ‖f x‖ₑ := by
  apply (paperLacunaryOscillatoryMaximal_levelSet_mul_le (memLp_stoppingGoodPart hf) a).trans
  apply (mul_le_mul' le_rfl (lintegral_sq_enorm_stoppingGoodPart_le hf)).trans_eq
  unfold stoppingGoodOscillatoryConstant
  ring

/-- The dyadic-modulation good contribution obeys the same endpoint estimate. -/
theorem stoppingGoodPart_lacunaryOscillatory_levelSet_le {f : ℝ → ℂ} (hf : Integrable f) :
    volume {x | 1 < paperLacunaryOscillatoryMaximal (stoppingGoodPart f) x} ≤
      stoppingGoodOscillatoryConstant * ∫⁻ x, ‖f x‖ₑ := by
  simpa only [one_pow, one_mul] using stoppingGoodPart_lacunaryOscillatory_levelSet_mul_le hf 1

/-- The actual good-part series converges absolutely outside one null set,
simultaneously for all nonzero real modulations. -/
theorem ae_summable_norm_stoppingGoodPart_oscillatoryIntegrals
    {f : ℝ → ℂ} (hf : Integrable f) :
    ∀ᵐ x, ∀ lam : {lam : ℝ // lam ≠ 0}, Summable (fun r : ℕ ↦
      ‖∫ t, stoppingGoodPart f (x - t) *
        (dyadicPsi (oscillatoryScaleIndex lam.1 r lam.2) t : ℂ) * phase (lam.1 * t ^ 2)‖) :=
  ae_summable_norm_oscillatoryIntegrals (memLp_stoppingGoodPart hf)

end PositiveGoodOscillatory
end QuadraticCarleson
