/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveragingSigned

/-!
# Every fixed oscillation height, including height zero

The single lowest height is bounded by the centered maximal operator. All
positive heights use the proved quadratic oscillatory decay. Thus the final
finite-modulation estimate has no restriction on the natural height.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson

/-- A finite family of bounded interval-supported kernels is pointwise
controlled by a finite centered maximal operator. -/
theorem finiteConvolutionMaximal_le_centered {N : ℕ}
    (κ : Fin N → ℝ → ℂ) (r : Fin N → ℝ) (hr : ∀ i, 0 < r i)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ i t, ‖κ i t‖ ≤ L / r i)
    (hzero : ∀ i t, r i < |t| → κ i t = 0)
    {f : ℝ → ℂ} (hfm : Measurable f) (x : ℝ) :
    finiteConvolutionMaximal κ f x ≤
      ENNReal.ofReal (2 * L) * finiteCenteredMaximal r (fun t ↦ ‖f t‖ₑ) x := by
  have hpoint (i : Fin N) (t : ℝ) : ‖κ i (x - t)‖ₑ ≤
      ENNReal.ofReal (2 * L) * selectedAverageKernel r (fun _ ↦ i) x t := by
    have hp : ‖κ i (x - t)‖ ≤ 2 * L * realCenteredAverageKernel (r i) x t := by
      by_cases hd : |x - t| ≤ r i
      · have hid : 2 * L * (2 * r i)⁻¹ = L / r i := by field_simp
        rw [realCenteredAverageKernel, ite_eq_left hd, hid]
        exact hbound i (x - t)
      · rw [hzero i (x - t) (lt_of_not_ge hd)]
        simp [realCenteredAverageKernel, hd]
    have h := ENNReal.ofReal_le_ofReal hp
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * L),
      ofReal_realCenteredAverageKernel r hr (fun _ ↦ i) x t] at h
    simpa only [ofReal_norm] using h
  apply iSup_le
  intro i
  calc
    _ ≤ ∫⁻ t, ‖κ i (x - t) * f t‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t, ENNReal.ofReal (2 * L) *
        (selectedAverageKernel r (fun _ ↦ i) x t * ‖f t‖ₑ) := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [enorm_mul, ← mul_assoc]
      exact mul_le_mul' (hpoint i t) le_rfl
    _ = ENNReal.ofReal (2 * L) * centeredAverage (r i) (fun t ↦ ‖f t‖ₑ) x := by
      rw [lintegral_const_mul' _ _ (by finiteness),
        lintegral_selectedAverageKernel_mul r (fun _ ↦ i) hfm.enorm]
    _ ≤ _ := mul_le_mul' le_rfl (le_iSup (fun i ↦ centeredAverage (r i) (fun t ↦ ‖f t‖ₑ) x) i)

theorem finiteConvolutionMaximal_sq_lintegral_le_interval_bound {N : ℕ}
    (κ : Fin N → ℝ → ℂ) (r : Fin N → ℝ) (hr : ∀ i, 0 < r i)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ i t, ‖κ i t‖ ≤ L / r i)
    (hzero : ∀ i t, r i < |t| → κ i t = 0)
    {f : ℝ → ℂ} (hfm : Measurable f) :
    (∫⁻ x, finiteConvolutionMaximal κ f x ^ 2) ≤
      ENNReal.ofReal (128 * L ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  calc
    _ ≤ ∫⁻ x, (ENNReal.ofReal (2 * L) * finiteCenteredMaximal r (fun t ↦ ‖f t‖ₑ) x) ^ 2 := by
      apply lintegral_mono
      intro x
      exact pow_le_pow_left₀ bot_le (finiteConvolutionMaximal_le_centered κ r hr hL hbound hzero
        hfm x) 2
    _ = ENNReal.ofReal (2 * L) ^ 2 * ∫⁻ x, finiteCenteredMaximal r (fun t ↦ ‖f t‖ₑ) x ^ 2 := by
      simp_rw [mul_pow]
      exact lintegral_const_mul' _ _ (by finiteness)
    _ ≤ ENNReal.ofReal (2 * L) ^ 2 * (32 * ∫⁻ x, ‖f x‖ₑ ^ 2) :=
      mul_le_mul' le_rfl (finiteCenteredMaximal_sq_lintegral_le r hr hfm.enorm)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * L),
        ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (sq_nonneg (2 * L))]
      congr 2
      ring

theorem norm_fixedHeightQuadraticKernel_le
    (lam : ℝ) (height : ℕ) (hlam : lam ≠ 0) (t : ℝ) :
    ‖fixedHeightQuadraticKernel lam height hlam t‖ ≤
      (2 * positiveDyadicAmplitudeBound) / fixedHeightRadius lam height hlam := by
  rw [fixedHeightQuadraticKernel_eq_positive_sub_reflect]
  calc
    _ ≤ ‖positiveFixedHeightQuadraticKernel lam height hlam t‖ +
        ‖positiveFixedHeightQuadraticKernel lam height hlam (-t)‖ := norm_sub_le _ _
    _ ≤ positiveDyadicAmplitudeBound / fixedHeightRadius lam height hlam +
        positiveDyadicAmplitudeBound / fixedHeightRadius lam height hlam := by
      simp only [positiveFixedHeightQuadraticKernel, annularQuadraticKernel, norm_mul,
        norm_phase, mul_one]
      exact add_le_add (norm_positiveDyadicAmplitude_le _ t) (norm_positiveDyadicAmplitude_le _
        (-t))
    _ = _ := by ring

theorem fixedHeightQuadraticKernel_eq_zero_of_radius_lt
    (lam : ℝ) (height : ℕ) (hlam : lam ≠ 0) (t : ℝ)
    (ht : fixedHeightRadius lam height hlam < |t|) : fixedHeightQuadraticKernel lam height hlam
      t = 0 := by
  have hz : dyadicPsi (oscillatoryScaleIndex lam height hlam) t = 0 := by
    by_contra h
    have hs := dyadicPsi_support_subset (oscillatoryScaleIndex lam height hlam) h
    exact (not_lt_of_ge ht.le) hs.2
  simp only [fixedHeightQuadraticKernel, hz, Complex.ofReal_zero, zero_mul]

/-- A uniform nonoscillatory bound, used only to include the lowest height. -/
theorem finite_fixedHeightQuadraticKernel_maximal_sq_bound
    (n height : ℕ) (lam : Fin (n + 1) → ℝ) (hlam : ∀ i, lam i ≠ 0)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ x, finiteConvolutionMaximal
      (fun i ↦ fixedHeightQuadraticKernel (lam i) height (hlam i)) f x ^ 2) ≤
      ENNReal.ofReal (512 * positiveDyadicAmplitudeBound ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  apply finiteConvolutionMaximal_bound_of_measurable_memLp _ _ ?_ hf
  intro g hgm _hg
  have h := finiteConvolutionMaximal_sq_lintegral_le_interval_bound
    (fun i ↦ fixedHeightQuadraticKernel (lam i) height (hlam i))
    (fun i ↦ fixedHeightRadius (lam i) height (hlam i))
    (fun i ↦ fixedHeightRadius_pos _ _ _)
    (show 0 ≤ 2 * positiveDyadicAmplitudeBound by positivity [positiveDyadicAmplitudeBound_nonneg])
    (fun i ↦ norm_fixedHeightQuadraticKernel_le _ _ _)
    (fun i ↦ fixedHeightQuadraticKernel_eq_zero_of_radius_lt _ _ _) hgm
  convert h using 1
  congr 2
  ring

/-- Fixed-height quadratic finite maximal `L²` decay for every natural height
and every finite family of arbitrary nonzero real modulations. There are no
analytic hypotheses beyond `MemLp f 2`. -/
theorem finite_fixedHeightQuadraticKernel_maximal_sq_decay_all_heights
    (n height : ℕ) (lam : Fin (n + 1) → ℝ) (hlam : ∀ i, lam i ≠ 0)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ x, finiteConvolutionMaximal
      (fun i ↦ fixedHeightQuadraticKernel (lam i) height (hlam i)) f x ^ 2) ≤
      ENNReal.ofReal (70996725888 * positiveDyadicAmplitudeBound ^ 2 /
        (2 : ℝ) ^ ((height - 1) / 5)) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  by_cases hh : 1 ≤ height
  · exact finite_fixedHeightQuadraticKernel_maximal_sq_decay n height hh lam hlam hf
  · have hz : height = 0 := by omega
    subst height
    simp only [Nat.zero_sub, Nat.zero_div, pow_zero, div_one]
    apply (finite_fixedHeightQuadraticKernel_maximal_sq_bound n 0 lam hlam hf).trans
    apply mul_le_mul' ?_ le_rfl
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg positiveDyadicAmplitudeBound]

end QuadraticCarleson
