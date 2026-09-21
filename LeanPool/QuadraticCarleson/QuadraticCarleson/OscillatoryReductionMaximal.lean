/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.OscillatoryReductionSeries
import LeanPool.QuadraticCarleson.QuadraticCarleson.L0LacunaryOperator

/-!
# Reduction of quadratic principal-value truncations to oscillatory heights

The right side consists of the genuine nonnegative-height oscillatory series,
the ordinary (zero-modulation) Hilbert maximal truncation, and the measurable
centered Hardy--Littlewood maximal function. No principal-value existence or
Hilbert-transform boundedness assertion is used as a hypothesis.
-/

open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace QuadraticCarleson
namespace OscillatoryReduction

theorem integrable_kernel_mul_l0 (f : L0Infinity) (x : ℝ) {K : ℝ → ℂ} {C : ℝ}
    (hK : Measurable K) (hb : ∀ t, ‖K t‖ ≤ C) :
    Integrable (fun y ↦ K (x - y) * f y) := by
  apply f.integrable.bdd_mul
  · exact (hK.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · exact Eventually.of_forall (fun y ↦ hb (x - y))

theorem bounded_ball_kernel_enorm_le_maximal
    {K : ℝ → ℂ} {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hb : ∀ t, ‖K t‖ ≤ C / ρ) (hs : support K ⊆ closedBall 0 ρ)
    {f : ℝ → ℂ} (_hf : Measurable f) (x : ℝ) :
    ‖∫ y, K (x - y) * f y‖ₑ ≤
      ENNReal.ofReal (4 * C) * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  have hden : ENNReal.ofReal (2 * ρ) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  calc
    _ ≤ ∫⁻ y, ‖K (x - y) * f y‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y in closedBall x ρ, ENNReal.ofReal (C / ρ) * ‖f y‖ₑ := by
      rw [← lintegral_indicator measurableSet_closedBall]
      apply lintegral_mono
      intro y
      dsimp only
      by_cases hy : y ∈ closedBall x ρ
      · rw [indicator_of_mem hy, enorm_mul]
        apply mul_le_mul' ?_ le_rfl
        simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (hb (x - y))
      · rw [indicator_of_notMem hy]
        have hz : K (x - y) = 0 := by
          apply notMem_support.mp
          intro ht
          apply hy
          simpa only [mem_closedBall, Real.dist_eq, sub_zero, abs_sub_comm] using hs ht
        simp [hz]
    _ = ENNReal.ofReal (2 * C) * centeredAverage ρ (fun y ↦ ‖f y‖ₑ) x := by
      rw [lintegral_const_mul' _ _ (by finiteness)]
      have hm : (∫⁻ y in closedBall x ρ, ‖f y‖ₑ) =
          ENNReal.ofReal (2 * ρ) * centeredAverage ρ (fun y ↦ ‖f y‖ₑ) x := by
        unfold centeredAverage
        rw [mul_comm]
        exact (ENNReal.div_mul_cancel hden ENNReal.ofReal_ne_top).symm
      rw [hm, ← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hC hρ.le)]
      congr 2
      field_simp
    _ ≤ ENNReal.ofReal (2 * C) *
        (2 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) :=
      mul_le_mul' le_rfl (centeredAverage_le_two_mul_centeredHardyLittlewoodMaximal hρ _ x)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * C)]
      congr 2
      ring

theorem smallPhaseOperator_enorm_le_maximal (lam ε : ℝ) (hlam : lam ≠ 0)
    {f : ℝ → ℂ} (hf : Measurable f) (x : ℝ) :
    ‖∫ y, smallPhaseKernel lam ε (innerRadius lam hlam) (x - y) * f y‖ₑ ≤
      ENNReal.ofReal (8 * Real.pi) * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  simpa only [show (4 : ℝ) * (2 * Real.pi) = 8 * Real.pi by ring] using
    bounded_ball_kernel_enorm_le_maximal (by positivity : 0 ≤ 2 * Real.pi)
      (innerRadius_pos lam hlam) (smallPhaseKernel_norm_le lam ε hlam)
      (smallPhaseKernel_support_subset lam ε (innerRadius lam hlam)) hf x

theorem quadraticHilbertTrunc_eq_oscillatory_reduction
    (lam ε : ℝ) (hlam : lam ≠ 0) (hε : 0 < ε) (hερ : ε ≤ innerRadius lam hlam)
    (f : L0Infinity) (x : ℝ) :
    quadraticHilbertTrunc lam ε f x = paperOscillatoryAction lam hlam f x +
      (∫ y, cutoffBoundaryKernel lam (innerRadius lam hlam) (x - y) * f y) +
      quadraticHilbertTrunc 0 ε f x - quadraticHilbertTrunc 0 (innerRadius lam hlam) f x +
      ∫ y, smallPhaseKernel lam ε (innerRadius lam hlam) (x - y) * f y := by
  have h1 := integrable_kernel_mul_l0 f x (measurable_highPassKernel lam hlam)
    (highPassKernel_norm_le lam hlam)
  have h2 := integrable_kernel_mul_l0 f x (measurable_cutoffBoundaryKernel lam _)
    (fun t ↦ cutoffBoundaryKernel_norm_le (t := t) lam (innerRadius_pos lam hlam))
  have h3 := integrable_kernel_mul_l0 f x (measurable_sharpQuadraticTailKernel 0 ε)
    (fun t ↦ sharpQuadraticTailKernel_norm_le (t := t) 0 hε)
  have h4 := integrable_kernel_mul_l0 f x (measurable_sharpQuadraticTailKernel 0 _)
    (fun t ↦ sharpQuadraticTailKernel_norm_le (t := t) 0 (innerRadius_pos lam hlam))
  have h5 := integrable_kernel_mul_l0 f x (measurable_smallPhaseKernel lam ε _)
    (smallPhaseKernel_norm_le lam ε hlam)
  rw [← quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc,
    paperOscillatoryAction_eq_integral]
  unfold quadraticHilbertConvolutionTrunc
  calc
    _ = ∫ y, (highPassKernel lam hlam (x - y) +
        cutoffBoundaryKernel lam (innerRadius lam hlam) (x - y) +
        sharpQuadraticTailKernel 0 ε (x - y) -
        sharpQuadraticTailKernel 0 (innerRadius lam hlam) (x - y) +
        smallPhaseKernel lam ε (innerRadius lam hlam) (x - y)) * f y := by
      apply integral_congr_ae
      filter_upwards with y
      rw [sharpQuadraticTailKernel_eq_oscillatory_reduction lam ε hlam hε hερ]
    _ = _ := by
      simp only [add_mul, sub_mul]
      have hi5 := integral_add (((h1.add h2).add h3).sub h4) h5
      have hi4 := integral_sub ((h1.add h2).add h3) h4
      have hi3 := integral_add (h1.add h2) h3
      have hi2 := integral_add h1 h2
      simp only [Pi.add_apply, Pi.sub_apply] at hi5 hi4 hi3 hi2
      rw [hi5, hi4, hi3, hi2]
      change _ + _ + quadraticHilbertConvolutionTrunc 0 ε f x -
        quadraticHilbertConvolutionTrunc 0 (innerRadius lam hlam) f x + _ = _
      rw [quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc,
        quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc]

/-- The uniform maximal-function constant controlling the regularization error. -/
noncomputable def maximalErrorConstant : ℝ≥0∞ := 8 + ENNReal.ofReal (8 * Real.pi)

theorem maximalErrorConstant_lt_top : maximalErrorConstant < ∞ := by
  unfold maximalErrorConstant
  finiteness

theorem quadraticHilbertTrunc_enorm_le_oscillatory
    (lam ε : ℝ) (hlam : lam ≠ 0) (hε : 0 < ε) (hερ : ε ≤ innerRadius lam hlam)
    (f : L0Infinity) (x : ℝ) :
    ‖quadraticHilbertTrunc lam ε f x‖ₑ ≤ ‖paperOscillatoryAction lam hlam f x‖ₑ +
      2 * quadraticHilbertMaximalTruncation 0 f x +
      maximalErrorConstant * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  let O := paperOscillatoryAction lam hlam f x
  let E := ∫ y, cutoffBoundaryKernel lam (innerRadius lam hlam) (x - y) * f y
  let A := quadraticHilbertTrunc 0 ε f x
  let D := quadraticHilbertTrunc 0 (innerRadius lam hlam) f x
  let S := ∫ y, smallPhaseKernel lam ε (innerRadius lam hlam) (x - y) * f y
  let H := quadraticHilbertMaximalTruncation 0 f x
  let M := centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x
  have hA : ‖A‖ₑ ≤ H := le_iSup
    (fun δ : {δ : ℝ // 0 < δ} ↦ ‖quadraticHilbertTrunc 0 δ f x‖ₑ) ⟨ε, hε⟩
  have hD : ‖D‖ₑ ≤ H := le_iSup
    (fun δ : {δ : ℝ // 0 < δ} ↦ ‖quadraticHilbertTrunc 0 δ f x‖ₑ)
      ⟨innerRadius lam hlam, innerRadius_pos lam hlam⟩
  have hE : ‖E‖ₑ ≤ 8 * M :=
    cutoffBoundaryOperator_enorm_le_maximal lam (innerRadius_pos lam hlam) f f.measurable_toFun x
  have hS : ‖S‖ₑ ≤ ENNReal.ofReal (8 * Real.pi) * M :=
    smallPhaseOperator_enorm_le_maximal lam ε hlam f.measurable_toFun x
  rw [quadraticHilbertTrunc_eq_oscillatory_reduction lam ε hlam hε hερ f x]
  change ‖O + E + A - D + S‖ₑ ≤ ‖O‖ₑ + 2 * H + maximalErrorConstant * M
  calc
    _ ≤ ‖O + E + A - D‖ₑ + ‖S‖ₑ := enorm_add_le _ _
    _ ≤ (‖O + E + A‖ₑ + ‖D‖ₑ) + ‖S‖ₑ := add_le_add enorm_sub_le le_rfl
    _ ≤ ((‖O + E‖ₑ + ‖A‖ₑ) + ‖D‖ₑ) + ‖S‖ₑ := by
      gcongr
      exact enorm_add_le _ _
    _ ≤ (((‖O‖ₑ + ‖E‖ₑ) + ‖A‖ₑ) + ‖D‖ₑ) + ‖S‖ₑ := by
      gcongr
      exact enorm_add_le _ _
    _ ≤ (((‖O‖ₑ + 8 * M) + H) + H) + ENNReal.ofReal (8 * Real.pi) * M := by gcongr
    _ = _ := by unfold maximalErrorConstant; ring

/-- Pointwise reduction for the paper-domain principal-value magnitude
defined by the canonical truncation limsup. This does not assume that the
principal value exists at the point in question. -/
theorem quadraticHilbertL0Limsup_le_oscillatory
    (lam : ℝ) (hlam : lam ≠ 0) (f : L0Infinity) (x : ℝ) :
    quadraticHilbertL0Limsup lam f x ≤ ‖paperOscillatoryAction lam hlam f x‖ₑ +
      2 * quadraticHilbertMaximalTruncation 0 f x +
      maximalErrorConstant * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  apply limsup_le_of_le (by isBoundedDefault)
  have hr : ∀ᶠ m : ℕ in atTop, principalValueRadius m ≤ innerRadius lam hlam :=
    ((tendsto_principalValueRadius.mono_right nhdsWithin_le_nhds).eventually
      (eventually_lt_nhds (innerRadius_pos lam hlam))).mono (fun _ h ↦ h.le)
  filter_upwards [hr] with m hm
  simpa only [quadraticHilbertL0TruncNorm, ofReal_norm] using
    quadraticHilbertTrunc_enorm_le_oscillatory lam (principalValueRadius m) hlam
      (principalValueRadius_pos m) hm f x

/-- The supremum of oscillatory actions over all nonzero real modulations. -/
noncomputable def paperOscillatoryMaximal (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ lam : {lam : ℝ // lam ≠ 0}, ‖paperOscillatoryAction lam.1 lam.2 f x‖ₑ

theorem nonzeroQuadraticCarlesonL0_le_oscillatory (f : L0Infinity) (x : ℝ) :
    (⨆ lam : {lam : ℝ // lam ≠ 0}, quadraticHilbertL0Limsup lam.1 f x) ≤
      paperOscillatoryMaximal f x + 2 * quadraticHilbertMaximalTruncation 0 f x +
      maximalErrorConstant * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  apply iSup_le
  intro lam
  apply (quadraticHilbertL0Limsup_le_oscillatory lam.1 lam.2 f x).trans
  apply add_le_add ?_ le_rfl
  apply add_le_add ?_ le_rfl
  exact le_iSup (fun μ : {μ : ℝ // μ ≠ 0} ↦ ‖paperOscillatoryAction μ.1 μ.2 f x‖ₑ) lam

end OscillatoryReduction
end QuadraticCarleson
