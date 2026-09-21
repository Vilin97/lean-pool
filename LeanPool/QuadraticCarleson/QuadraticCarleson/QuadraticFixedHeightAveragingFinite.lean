/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveraging

/-!
# Finite maximal consequence of the fixed-height quadratic kernel estimate

This file connects the explicit correlation majorant proved in `QuadraticTTStar`
to finite measurable linearization and the actual integral operator. The
correlation estimate remains an explicit input in this intermediate theorem;
the concrete annular cutoff specialization is not silently assumed.
-/

open MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate

namespace QuadraticCarleson

namespace FiniteRangeKernel

/-- The actual linearized operator estimate resulting from the precise
near-diagonal and off-diagonal quadratic kernel majorant. -/
theorem sq_lintegral_le_of_quadraticFixedHeightMajorant {N : ℕ}
    (K : FiniteRangeKernel) (r : Fin N → ℝ) (hr : ∀ i, 0 < r i)
    {σ : ℝ → Fin N} (hσ : Measurable σ) {B u : ℝ} (hB : 0 ≤ B) (hu : 0 < u)
    (hcorrelation : ∀ x y, ‖K.correlation x y‖ ≤
      quadraticFixedHeightMajorant B u (max (r (σ x)) (r (σ y))) (x - y))
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ x, ‖K.applyIntegral f x‖ₑ ^ 2) ≤
      ENNReal.ofReal (2218647684 * B * u) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  apply K.sq_lintegral_le_of_correlation_form_bound _ ?_ hf
  intro g hgm
  calc
    _ ≤ ∫⁻ x, ∫⁻ y,
        ENNReal.ofReal (quadraticFixedHeightMajorant B u
          (max (r (σ x)) (r (σ y))) (x - y)) * g x * g y := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      apply mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
      simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hcorrelation x y)
    _ ≤ _ := quadraticFixedHeightMajorant_pairing_le r hr hσ hB hu hgm

end FiniteRangeKernel

/-- The finite maximal convolution output, written using the extended norm
so its squared integral is meaningful without any prior integrability. -/
noncomputable def finiteConvolutionMaximal {N : ℕ}
    (κ : Fin N → ℝ → ℂ) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ i : Fin N, ‖∫ t, κ i (x - t) * f t‖ₑ

theorem measurable_finiteConvolutionMaximal {N : ℕ}
    (κ : Fin N → ℝ → ℂ) (hκ : ∀ i, Measurable (κ i))
    {f : ℝ → ℂ} (hf : Measurable f) : Measurable (finiteConvolutionMaximal κ f) := by
  apply Measurable.iSup
  intro i
  have hm : Measurable (fun z : ℝ × ℝ ↦ κ i (z.1 - z.2) * f z.2) :=
    ((hκ i).comp (measurable_fst.sub measurable_snd)).mul (hf.comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable.enorm

/-- Measurable finite linearization turns the concrete fixed-height kernel
correlation estimate into the maximal second-moment estimate. -/
theorem finiteConvolutionMaximal_sq_lintegral_le_of_quadraticFixedHeightMajorant_measurable
    (n : ℕ) (κ : Fin (n + 1) → ℝ → ℂ)
    (hc : ∀ i, Continuous (κ i)) (hs : ∀ i, HasCompactSupport (κ i))
    (r : Fin (n + 1) → ℝ) (hr : ∀ i, 0 < r i)
    {B u : ℝ} (hB : 0 ≤ B) (hu : 0 < u)
    (hcorrelation : ∀ i j x y,
      ‖∫ t, κ i (x - t) * conj (κ j (y - t))‖ ≤
        quadraticFixedHeightMajorant B u (max (r i) (r j)) (x - y))
    {f : ℝ → ℂ} (hfm : Measurable f) (hf : MemLp f 2) :
    (∫⁻ x, finiteConvolutionMaximal κ f x ^ 2) ≤
      ENNReal.ofReal (2218647684 * B * u) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  obtain ⟨σ, K, hσ, hK, hmax⟩ :=
    FiniteRangeKernel.exists_finite_maximal_linearization n κ hc hs hfm
  have hpoint (x : ℝ) : finiteConvolutionMaximal κ f x ≤ ‖K.applyIntegral f x‖ₑ := by
    apply iSup_le
    intro i
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hmax x i)
  calc
    _ ≤ ∫⁻ x, ‖K.applyIntegral f x‖ₑ ^ 2 := by
      apply lintegral_mono
      intro x
      exact pow_le_pow_left₀ bot_le (hpoint x) 2
    _ ≤ _ := by
      apply K.sq_lintegral_le_of_quadraticFixedHeightMajorant r hr hσ hB hu ?_ hf
      intro x y
      simpa only [FiniteRangeKernel.correlation, hK] using hcorrelation (σ x) (σ y) x y

/-- Almost-everywhere input equality gives pointwise equality of every
finite maximal convolution output. -/
theorem finiteConvolutionMaximal_congr_ae {N : ℕ}
    (κ : Fin N → ℝ → ℂ) {f g : ℝ → ℂ} (hfg : f =ᵐ[volume] g) :
    finiteConvolutionMaximal κ f = finiteConvolutionMaximal κ g := by
  funext x
  apply congrArg iSup
  funext i
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg] with t ht
  rw [ht]

/-- The finite-modulation maximal consequence of the fixed-height quadratic
correlation majorant, for arbitrary `L²` inputs and with a constant independent
of the finite family. The annular correlation hypothesis is explicit here,
pending its concrete dyadic-cutoff instantiation. -/
theorem finiteConvolutionMaximal_sq_lintegral_le_of_quadraticFixedHeightMajorant
    (n : ℕ) (κ : Fin (n + 1) → ℝ → ℂ)
    (hc : ∀ i, Continuous (κ i)) (hs : ∀ i, HasCompactSupport (κ i))
    (r : Fin (n + 1) → ℝ) (hr : ∀ i, 0 < r i)
    {B u : ℝ} (hB : 0 ≤ B) (hu : 0 < u)
    (hcorrelation : ∀ i j x y,
      ‖∫ t, κ i (x - t) * conj (κ j (y - t))‖ ≤
        quadraticFixedHeightMajorant B u (max (r i) (r j)) (x - y))
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ x, finiteConvolutionMaximal κ f x ^ 2) ≤
      ENNReal.ofReal (2218647684 * B * u) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  let g := hf.aestronglyMeasurable.mk f
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : MemLp g 2 := hf.ae_eq hfg
  rw [finiteConvolutionMaximal_congr_ae κ hfg]
  have hint : (∫⁻ x, ‖g x‖ₑ ^ 2) = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
    apply lintegral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
  exact (finiteConvolutionMaximal_sq_lintegral_le_of_quadraticFixedHeightMajorant_measurable
    n κ hc hs r hr hB hu hcorrelation hgm hg).trans_eq
      (congrArg (fun v ↦ ENNReal.ofReal (2218647684 * B * u) * v) hint)

end QuadraticCarleson
