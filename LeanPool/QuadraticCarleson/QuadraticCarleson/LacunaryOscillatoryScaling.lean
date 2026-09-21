/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryOscillatoryAssembly
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveFullOscillatoryScaling

/-!
# Genuine lacunary homogeneity and arbitrary endpoint thresholds

The normalized estimate is applied to the actual input `(3 / α) f`.
Its individual frozen-block hypothesis is stated for that input, not
transported through the nonlinear stopping decomposition. A uniform
individual-block formulation is also supplied for the eventual KL theorem.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace LacunaryOscillatoryScaling

open OscillatoryReduction PositiveGoodOscillatory PositiveFullOscillatoryEndpoint
open PositiveEndpointOptimization PositiveHighHeightEstimate
open LacunaryMiddleKalton LacunaryOscillatoryAssembly


/-- Homogeneity of the genuine countable modulation supremum, through the
already-established integral representation of each oscillatory action. -/
theorem paperLacunaryOscillatoryMaximal_const_mul
    {f : ℝ → ℂ} (hf : Integrable f) (c : ℂ) (x : ℝ) :
    paperLacunaryOscillatoryMaximal (fun y ↦ c * f y) x =
      ‖c‖ₑ * paperLacunaryOscillatoryMaximal f x := by
  unfold paperLacunaryOscillatoryMaximal
  simp_rw [paperOscillatoryAction_const_mul _ _ hf, enorm_mul]
  exact (ENNReal.mul_iSup _ _).symm

theorem paperLacunaryOscillatoryMaximal_normalizedInput
    {α : ℝ} (hα : 0 < α) {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    paperLacunaryOscillatoryMaximal (normalizedOscillatoryInput α f) x =
      paperLacunaryOscillatoryMaximal f x / ENNReal.ofReal α := by
  change paperLacunaryOscillatoryMaximal (fun y ↦ (α : ℂ)⁻¹ * f y) x = _
  rw [paperLacunaryOscillatoryMaximal_const_mul hf]
  have hc : ‖(α : ℂ)⁻¹‖ₑ = (ENNReal.ofReal α)⁻¹ := by
    rw [← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα,
      ENNReal.ofReal_inv_of_pos hα]
  rw [hc, div_eq_mul_inv, mul_comm]

theorem lacunary_levelSet_eq_three_normalized
    {α : ℝ} (hα : 0 < α) {f : ℝ → ℂ} (hf : Integrable f) :
    {x | ENNReal.ofReal α < paperLacunaryOscillatoryMaximal f x} =
      {x | 3 < paperLacunaryOscillatoryMaximal
        (normalizedOscillatoryInput (α / 3) f) x} := by
  have hα3 : 0 < α / 3 := by positivity
  have hprod : (3 : ℝ≥0∞) * ENNReal.ofReal (α / 3) = ENNReal.ofReal α := by
    rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  ext x
  change ENNReal.ofReal α < paperLacunaryOscillatoryMaximal f x ↔
    3 < paperLacunaryOscillatoryMaximal (normalizedOscillatoryInput (α / 3) f) x
  rw [paperLacunaryOscillatoryMaximal_normalizedInput hα3 hf]
  simpa only [hprod] using (ENNReal.lt_div_iff_mul_lt
    (a := paperLacunaryOscillatoryMaximal f x) (b := ENNReal.ofReal (α / 3)) (c := 3)
    (Or.inl (ENNReal.ofReal_pos.mpr hα3).ne') (Or.inl ENNReal.ofReal_ne_top)).symm

/-- A fixed dilation is harmless for every iterated source logarithm. -/
theorem paperLog_three_mul_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    paperLog n (3 * t) ≤ 3 * paperLog n t := by
  induction n with
  | zero => simp only [paperLog_zero, le_refl]
  | succ n ih =>
      have hn := paperLog_nonnegative n ht
      have hn3 := paperLog_nonnegative n (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) ht)
      rw [paperLog_succ, paperLog_succ]
      calc
        _ ≤ Real.log ((10 + paperLog n t) ^ 3) := by
          apply Real.log_le_log (by linarith)
          nlinarith [sq_nonneg (paperLog n t), pow_nonneg hn 3]
        _ = _ := by rw [Real.log_pow]; norm_num

/-- Exact source Orlicz modular under the only fixed dilation required by
the threshold-three assembly. -/
theorem lacunaryOrlicz_three_mul_le {t : ℝ} (ht : 0 ≤ t) :
    (3 * t) * paperLog 2 (3 * t) ^ 2 * paperLog 4 (3 * t) ≤
      81 * (t * paperLog 2 t ^ 2 * paperLog 4 t) := by
  have h2 := paperLog_three_mul_le 2 ht
  have h4 := paperLog_three_mul_le 4 ht
  have ht3 : 0 ≤ 3 * t := by positivity
  calc
    _ ≤ (3 * t) * (3 * paperLog 2 t) ^ 2 * (3 * paperLog 4 t) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (paperLog_nonnegative 2 ht3) h2 2) ht3
      · exact h4
      · exact paperLog_nonnegative 4 ht3
      · positivity
    _ = _ := by ring

/-- The oscillatory endpoint constant after the spatial scaling step. -/
noncomputable def lacunaryScaledEndpointConstant (C : ℝ) : ℝ≥0∞ :=
  81 * lacunaryOscillatoryEndpointConstant C

theorem lacunaryScaledEndpointConstant_lt_top (C : ℝ) :
    lacunaryScaledEndpointConstant C < ∞ :=
  ENNReal.mul_lt_top (by finiteness) (lacunaryOscillatoryEndpointConstant_lt_top C)

/-- Arbitrary positive threshold in the paper's exact modular form. The
individual-block input is explicitly attached to `(3 / α) f`. -/
theorem paperLacunaryOscillatoryMaximal_levelSet_le_scaled_orlicz
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) {α : ℝ} (hα : 0 < α)
    {C : ℝ} (hblock : HasLogSquaredFrozenBlockWeakBounds
      (normalizedOscillatoryInput (α / 3) f) lacunaryHighCutoff 0 C) :
    volume {x | ENNReal.ofReal α < paperLacunaryOscillatoryMaximal f x} ≤
      lacunaryScaledEndpointConstant C * ∫⁻ x, ENNReal.ofReal
        ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) := by
  have h := paperLacunaryOscillatoryMaximal_levelSet_three_le_orlicz
    (measurable_normalizedOscillatoryInput hf (α / 3))
    (integrable_normalizedOscillatoryInput hfi (α / 3)) (by intro k; omega) hblock
  rw [← lacunary_levelSet_eq_three_normalized hα hfi] at h
  have hnorm (x : ℝ) : ‖normalizedOscillatoryInput (α / 3) f x‖ = 3 * (‖f x‖ / α) := by
    rw [norm_normalizedOscillatoryInput (by positivity : 0 < α / 3)]
    ring
  simp_rw [hnorm] at h
  apply h.trans
  calc
    _ ≤ lacunaryOscillatoryEndpointConstant C *
        ∫⁻ x, ENNReal.ofReal (81 *
          ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α))) := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal (lacunaryOrlicz_three_mul_le (by positivity))
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 81)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp only [ENNReal.ofReal_ofNat, lacunaryScaledEndpointConstant]
      ring

/-- Exactly the uniform individual finite-block theorem still required from
the KL sparse estimate. This does not assume any assembled endpoint bound. -/
def HasUniformLogSquaredFrozenBlockWeakBounds (C : ℝ) : Prop :=
  ∀ (g : ℝ → ℂ), Measurable g → Integrable g →
    HasLogSquaredFrozenBlockWeakBounds g lacunaryHighCutoff 0 C

/-- The weaker uniform form actually required by the paper-facing endpoint:
only bounded compactly supported measurable inputs and their scalar
normalizations occur in the assembly. -/
def HasUniformL0LogSquaredFrozenBlockWeakBounds (C : ℝ) : Prop :=
  ∀ g : L0Infinity,
    HasLogSquaredFrozenBlockWeakBounds (g : ℝ → ℂ) lacunaryHighCutoff 0 C

theorem paperLacunaryOscillatoryMaximal_levelSet_le_scaled_orlicz_of_uniform
    {C : ℝ} (hblock : HasUniformLogSquaredFrozenBlockWeakBounds C)
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal α < paperLacunaryOscillatoryMaximal f x} ≤
      lacunaryScaledEndpointConstant C * ∫⁻ x, ENNReal.ofReal
        ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) :=
  paperLacunaryOscillatoryMaximal_levelSet_le_scaled_orlicz hf hfi hα
    (hblock _ (measurable_normalizedOscillatoryInput hf (α / 3))
      (integrable_normalizedOscillatoryInput hfi (α / 3)))

theorem paperLacunaryOscillatoryMaximal_L0Infinity_levelSet_le_scaled_orlicz
    {C : ℝ} (hblock : HasUniformL0LogSquaredFrozenBlockWeakBounds C)
    (f : L0Infinity) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal α < paperLacunaryOscillatoryMaximal f x} ≤
      lacunaryScaledEndpointConstant C * ∫⁻ x, ENNReal.ofReal
        ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) :=
  paperLacunaryOscillatoryMaximal_levelSet_le_scaled_orlicz
    f.measurable_toFun f.integrable hα (by
      let g : L0Infinity := L0Infinity.smul ((α / 3 : ℝ) : ℂ)⁻¹ f
      change HasLogSquaredFrozenBlockWeakBounds
        (g : ℝ → ℂ) lacunaryHighCutoff 0 C
      exact hblock g)


end LacunaryOscillatoryScaling
end QuadraticCarleson
