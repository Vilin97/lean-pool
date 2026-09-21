/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveragingDyadic

/-!
# Spatial and modulation signs in the finite fixed-height theorem
-/

open MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate

namespace QuadraticCarleson

theorem ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  by_cases ha : a = ⊤
  · subst a
    simp
  by_cases hb : b = ⊤
  · subst b
    simp
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  exact_mod_cast (show ((a : ℝ) + (b : ℝ)) ^ 2 ≤ 2 * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) by
    nlinarith [sq_nonneg ((a : ℝ) - (b : ℝ))])

theorem lintegral_sq_le_of_le_add {F G H : ℝ → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) (h : ∀ x, H x ≤ F x + G x) :
    (∫⁻ x, H x ^ 2) ≤ 2 * ((∫⁻ x, F x ^ 2) + ∫⁻ x, G x ^ 2) := by
  calc
    _ ≤ ∫⁻ x, 2 * (F x ^ 2 + G x ^ 2) := by
      apply lintegral_mono
      intro x
      exact (pow_le_pow_left₀ bot_le (h x) 2).trans (ennreal_add_sq_le _ _)
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left (hF.pow_const 2) _]

/-- Continuous compactly supported kernels can be integrated against any
`L²` input at every point, not only almost everywhere. -/
theorem integrable_convolution_row_of_memLp {κ f : ℝ → ℂ}
    (hc : Continuous κ) (hs : HasCompactSupport κ) (hf : MemLp f 2) (x : ℝ) :
    Integrable (fun t ↦ κ (x - t) * f t) := by
  have hloc := hf.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact hloc.integrable_smul_left_of_hasCompactSupport
    (hc.comp (continuous_const.sub continuous_id)) (hs.comp_homeomorph (Homeomorph.subLeft x))

theorem finiteConvolutionMaximal_reflect {N : ℕ} (κ : Fin N → ℝ → ℂ)
    (f : ℝ → ℂ) (x : ℝ) :
    finiteConvolutionMaximal (fun i t ↦ κ i (-t)) f x =
      finiteConvolutionMaximal κ (fun t ↦ f (-t)) (-x) := by
  apply congrArg iSup
  funext i
  congr 1
  calc
    (∫ t, κ i (-(x - t)) * f t) = ∫ t, κ i (-(x - -t)) * f (-t) :=
      (integral_neg_eq_self (fun t ↦ κ i (-(x - t)) * f t) volume).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      congr 2
      ring

theorem finiteConvolutionMaximal_conj {N : ℕ} (κ : Fin N → ℝ → ℂ)
    (f : ℝ → ℂ) (x : ℝ) :
    finiteConvolutionMaximal (fun i t ↦ conj (κ i t)) f x =
      finiteConvolutionMaximal κ (fun t ↦ conj (f t)) x := by
  apply congrArg iSup
  funext i
  have heq : (∫ t, conj (κ i (x - t)) * f t) =
      conj (∫ t, κ i (x - t) * conj (f t)) := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [map_mul, starRingEnd_self_apply]
  rw [heq]
  simp only [← ofReal_norm, RCLike.norm_conj]

theorem finiteConvolutionMaximal_sub_le {N : ℕ} (κ η : Fin N → ℝ → ℂ)
    (hcκ : ∀ i, Continuous (κ i)) (hsκ : ∀ i, HasCompactSupport (κ i))
    (hcη : ∀ i, Continuous (η i)) (hsη : ∀ i, HasCompactSupport (η i))
    {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    finiteConvolutionMaximal (fun i t ↦ κ i t - η i t) f x ≤
      finiteConvolutionMaximal κ f x + finiteConvolutionMaximal η f x := by
  apply iSup_le
  intro i
  have hid : (∫ t, (κ i (x - t) - η i (x - t)) * f t) =
      (∫ t, κ i (x - t) * f t) - ∫ t, η i (x - t) * f t := by
    simp_rw [sub_mul]
    exact integral_sub (integrable_convolution_row_of_memLp (hcκ i) (hsκ i) hf x)
      (integrable_convolution_row_of_memLp (hcη i) (hsη i) hf x)
  rw [hid]
  exact enorm_sub_le.trans (add_le_add
    (le_iSup (fun i ↦ ‖∫ t, κ i (x - t) * f t‖ₑ) i)
    (le_iSup (fun i ↦ ‖∫ t, η i (x - t) * f t‖ₑ) i))

/-- Passing from a positive spatial half to its odd extension costs only a
fixed factor in the squared maximal bound. -/
theorem finiteConvolutionMaximal_sub_reflect_sq_bound {N : ℕ}
    (κ : Fin N → ℝ → ℂ) (hc : ∀ i, Continuous (κ i)) (hs : ∀ i, HasCompactSupport (κ i))
    (C : ℝ≥0∞)
    (hbound : ∀ f : ℝ → ℂ, MemLp f 2 →
      (∫⁻ x, finiteConvolutionMaximal κ f x ^ 2) ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2)
    {f : ℝ → ℂ} (hfm : Measurable f) (hf : MemLp f 2) :
    (∫⁻ x, finiteConvolutionMaximal (fun i t ↦ κ i t - κ i (-t)) f x ^ 2) ≤
      (4 * C) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  have hfr : MemLp (fun t ↦ f (-t)) 2 := hf.comp_measurePreserving (Measure.measurePreserving_neg volume)
  have hmr := measurable_finiteConvolutionMaximal κ (fun i ↦ (hc i).measurable)
    (hfm.comp measurable_neg)
  have hmf := measurable_finiteConvolutionMaximal κ (fun i ↦ (hc i).measurable) hfm
  have hpoint (x : ℝ) :
      finiteConvolutionMaximal (fun i t ↦ κ i t - κ i (-t)) f x ≤
        finiteConvolutionMaximal κ f x + finiteConvolutionMaximal κ (fun t ↦ f (-t)) (-x) := by
    rw [← finiteConvolutionMaximal_reflect]
    exact finiteConvolutionMaximal_sub_le κ (fun i t ↦ κ i (-t)) hc hs
      (fun i ↦ (hc i).comp continuous_neg) (fun i ↦ (hs i).comp_homeomorph (Homeomorph.neg ℝ)) hf x
  calc
    _ ≤ 2 * ((∫⁻ x, finiteConvolutionMaximal κ f x ^ 2) +
        ∫⁻ x, finiteConvolutionMaximal κ (fun t ↦ f (-t)) (-x) ^ 2) :=
      lintegral_sq_le_of_le_add hmf (hmr.comp measurable_neg) hpoint
    _ = 2 * ((∫⁻ x, finiteConvolutionMaximal κ f x ^ 2) +
        ∫⁻ x, finiteConvolutionMaximal κ (fun t ↦ f (-t)) x ^ 2) := by
      rw [lintegral_neg_eq_self (fun x ↦ finiteConvolutionMaximal κ (fun t ↦ f (-t)) x ^ 2)]
    _ ≤ 2 * (C * (∫⁻ x, ‖f x‖ₑ ^ 2) + C * ∫⁻ x, ‖f (-x)‖ₑ ^ 2) :=
      mul_le_mul' le_rfl (add_le_add (hbound f hf) (hbound _ hfr))
    _ = _ := by rw [lintegral_neg_eq_self (fun x ↦ ‖f x‖ₑ ^ 2)]; ring

/-- A family in which each kernel is either a chosen kernel or its complex
conjugate is controlled by two maximal outputs. -/
theorem finiteConvolutionMaximal_eq_or_conj_le {N : ℕ}
    (κ τ : Fin N → ℝ → ℂ)
    (hτ : ∀ i, τ i = κ i ∨ τ i = fun t ↦ conj (κ i t)) (f : ℝ → ℂ) (x : ℝ) :
    finiteConvolutionMaximal τ f x ≤ finiteConvolutionMaximal κ f x +
      finiteConvolutionMaximal κ (fun t ↦ conj (f t)) x := by
  apply iSup_le
  intro i
  rcases hτ i with hi | hi
  · rw [hi]
    exact (le_iSup (fun i ↦ ‖∫ t, κ i (x - t) * f t‖ₑ) i).trans (le_add_right le_rfl)
  · rw [hi]
    have h := le_iSup (fun i ↦ ‖∫ t, conj (κ i (x - t)) * f t‖ₑ) i
    change _ ≤ finiteConvolutionMaximal (fun i t ↦ conj (κ i t)) f x at h
    rw [finiteConvolutionMaximal_conj] at h
    exact h.trans (le_add_left le_rfl)

theorem finiteConvolutionMaximal_eq_or_conj_sq_bound {N : ℕ}
    (κ τ : Fin N → ℝ → ℂ) (hκ : ∀ i, Measurable (κ i))
    (hτ : ∀ i, τ i = κ i ∨ τ i = fun t ↦ conj (κ i t)) (C : ℝ≥0∞)
    (hbound : ∀ f : ℝ → ℂ, MemLp f 2 →
      (∫⁻ x, finiteConvolutionMaximal κ f x ^ 2) ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2)
    {f : ℝ → ℂ} (hfm : Measurable f) (hf : MemLp f 2) :
    (∫⁻ x, finiteConvolutionMaximal τ f x ^ 2) ≤ (4 * C) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  have hfc : MemLp (fun t ↦ conj (f t)) 2 := hf.star
  have hfmconj := Complex.continuous_conj.measurable.comp hfm
  have hnorm (t : ℝ) : ‖conj (f t)‖ₑ = ‖f t‖ₑ := by
    simp only [← ofReal_norm, RCLike.norm_conj]
  calc
    _ ≤ 2 * ((∫⁻ x, finiteConvolutionMaximal κ f x ^ 2) +
        ∫⁻ x, finiteConvolutionMaximal κ (fun t ↦ conj (f t)) x ^ 2) :=
      lintegral_sq_le_of_le_add (measurable_finiteConvolutionMaximal κ hκ hfm)
        (measurable_finiteConvolutionMaximal κ hκ hfmconj)
        (finiteConvolutionMaximal_eq_or_conj_le κ τ hτ f)
    _ ≤ 2 * (C * (∫⁻ x, ‖f x‖ₑ ^ 2) + C * ∫⁻ x, ‖conj (f x)‖ₑ ^ 2) :=
      mul_le_mul' le_rfl (add_le_add (hbound f hf) (hbound _ hfc))
    _ = _ := by simp_rw [hnorm]; ring

/-- Remove a measurable-representative condition from finite maximal bounds. -/
theorem finiteConvolutionMaximal_bound_of_measurable_memLp {N : ℕ}
    (κ : Fin N → ℝ → ℂ) (C : ℝ≥0∞)
    (hbound : ∀ f : ℝ → ℂ, Measurable f → MemLp f 2 →
      (∫⁻ x, finiteConvolutionMaximal κ f x ^ 2) ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ x, finiteConvolutionMaximal κ f x ^ 2) ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  let g := hf.aestronglyMeasurable.mk f
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : MemLp g 2 := hf.ae_eq hfg
  rw [finiteConvolutionMaximal_congr_ae κ hfg]
  have hint : (∫⁻ x, ‖g x‖ₑ ^ 2) = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
    apply lintegral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
  exact (hbound g hgm hg).trans_eq (congrArg (fun v ↦ C * v) hint)

/-- The positive one-sided amplitude recovers the full odd dyadic quotient. -/
theorem dyadicPsi_eq_positive_sub_reflect (j : ℤ) (t : ℝ) :
    (dyadicPsi j t : ℂ) = positiveDyadicAmplitude j t - positiveDyadicAmplitude j (-t) := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rw [positiveDyadicAmplitude_eq, positiveDyadicAmplitude_eq]
    simp only [not_lt.mpr ht.le, ↓reduceIte, neg_pos.mpr ht, zero_sub]
    rw [dyadicPsi_odd j t]
    simp
  · subst t
    simp [positiveDyadicAmplitude_eq, dyadicPsi_zero]
  · rw [positiveDyadicAmplitude_eq, positiveDyadicAmplitude_eq]
    simp [ht, not_lt.mpr (neg_nonpos.mpr ht.le)]

/-- The actual full fixed-height dyadic kernel from the paper. -/
noncomputable def fixedHeightQuadraticKernel (lam : ℝ) (height : ℕ) (hlam : lam ≠ 0) (t : ℝ) : ℂ :=
  (dyadicPsi (oscillatoryScaleIndex lam height hlam) t : ℂ) * phase (lam * t ^ 2)

theorem fixedHeightQuadraticKernel_eq_positive_sub_reflect
    (lam : ℝ) (height : ℕ) (hlam : lam ≠ 0) (t : ℝ) :
    fixedHeightQuadraticKernel lam height hlam t =
      positiveFixedHeightQuadraticKernel lam height hlam t -
        positiveFixedHeightQuadraticKernel lam height hlam (-t) := by
  unfold fixedHeightQuadraticKernel positiveFixedHeightQuadraticKernel annularQuadraticKernel
  rw [dyadicPsi_eq_positive_sub_reflect]
  simp only [neg_sq]
  ring

theorem continuous_positiveFixedHeightQuadraticKernel
    (lam : ℝ) (height : ℕ) (hlam : lam ≠ 0) :
    Continuous (positiveFixedHeightQuadraticKernel lam height hlam) := by
  have ha : Continuous (positiveDyadicAmplitude (oscillatoryScaleIndex lam height hlam)) :=
    continuous_iff_continuousAt.mpr (fun t ↦ (hasDerivAt_positiveDyadicAmplitude _ t).continuousAt)
  unfold positiveFixedHeightQuadraticKernel annularQuadraticKernel phase
  fun_prop

theorem hasCompactSupport_positiveFixedHeightQuadraticKernel
    (lam : ℝ) (height : ℕ) (hlam : lam ≠ 0) :
    HasCompactSupport (positiveFixedHeightQuadraticKernel lam height hlam) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (fixedHeightRadius lam height hlam / 4)
      (fixedHeightRadius lam height hlam)))
  intro t ht
  apply positiveDyadicAmplitude_support_subset (oscillatoryScaleIndex lam height hlam)
  intro hz
  exact ht (by simp [positiveFixedHeightQuadraticKernel, annularQuadraticKernel, hz])

theorem continuous_fixedHeightQuadraticKernel (lam : ℝ) (height : ℕ) (hlam : lam ≠ 0) :
    Continuous (fixedHeightQuadraticKernel lam height hlam) := by
  have hc := continuous_positiveFixedHeightQuadraticKernel lam height hlam
  convert hc.sub (hc.comp continuous_neg) using 1
  funext t
  exact fixedHeightQuadraticKernel_eq_positive_sub_reflect lam height hlam t

/-- Full spatially signed dyadic finite maximal decay for positive modulations. -/
theorem finite_fixedHeightQuadraticKernel_positive_maximal_sq_decay
    (n height : ℕ) (hh : 1 ≤ height) (lam : Fin (n + 1) → ℝ) (hlam : ∀ i, 0 < lam i)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ x, finiteConvolutionMaximal
      (fun i ↦ fixedHeightQuadraticKernel (lam i) height (hlam i).ne') f x ^ 2) ≤
      ENNReal.ofReal (17749181472 * positiveDyadicAmplitudeBound ^ 2 /
        (2 : ℝ) ^ ((height - 1) / 5)) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  apply finiteConvolutionMaximal_bound_of_measurable_memLp _ _ ?_ hf
  intro g hgm hg
  have h := finiteConvolutionMaximal_sub_reflect_sq_bound
    (fun i ↦ positiveFixedHeightQuadraticKernel (lam i) height (hlam i).ne')
    (fun i ↦ continuous_positiveFixedHeightQuadraticKernel _ _ _)
    (fun i ↦ hasCompactSupport_positiveFixedHeightQuadraticKernel _ _ _)
    (ENNReal.ofReal (4437295368 * positiveDyadicAmplitudeBound ^ 2 /
      (2 : ℝ) ^ ((height - 1) / 5)))
    (fun g hg ↦ finite_positiveFixedHeightQuadraticKernel_maximal_sq_decay n height hh lam hlam hg) hgm hg
  have hk : (fun i t ↦ fixedHeightQuadraticKernel (lam i) height (hlam i).ne' t) =
      (fun i t ↦ positiveFixedHeightQuadraticKernel (lam i) height (hlam i).ne' t -
        positiveFixedHeightQuadraticKernel (lam i) height (hlam i).ne' (-t)) := by
    funext i t
    exact fixedHeightQuadraticKernel_eq_positive_sub_reflect _ _ _ _
  rw [hk]
  convert h using 1
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  congr 2
  ring

/-- The oscillatory scale depends on the modulation's absolute value. -/
theorem oscillatoryScaleIndex_abs (lam : ℝ) (height : ℕ) (hlam : lam ≠ 0) :
    oscillatoryScaleIndex lam height hlam =
      oscillatoryScaleIndex |lam| height (abs_ne_zero.mpr hlam) := by
  apply oscillatoryScaleIndex_unique |lam| height (abs_ne_zero.mpr hlam)
  simpa only [OscillatoryScaleSpec, abs_abs] using oscillatoryScaleIndex_spec lam height hlam

theorem fixedHeight_conj_phase (s : ℝ) : conj (phase s) = phase (-s) := by
  have h := (phase_sub_eq_mul_conj 0 s).symm
  simpa only [zero_sub, phase_zero, one_mul] using h

/-- Every nonzero signed modulation gives either the absolute-modulation
kernel or its complex conjugate. -/
theorem fixedHeightQuadraticKernel_eq_or_conj_abs (lam : ℝ) (height : ℕ) (hlam : lam ≠ 0) :
    fixedHeightQuadraticKernel lam height hlam =
        fixedHeightQuadraticKernel |lam| height (abs_ne_zero.mpr hlam) ∨
      fixedHeightQuadraticKernel lam height hlam =
        fun t ↦ conj (fixedHeightQuadraticKernel |lam| height (abs_ne_zero.mpr hlam) t) := by
  by_cases hp : 0 < lam
  · left
    funext t
    unfold fixedHeightQuadraticKernel
    rw [oscillatoryScaleIndex_abs lam height hlam]
    congr 1
    rw [abs_of_pos hp]
  · right
    have hn : lam < 0 := lt_of_le_of_ne (le_of_not_gt hp) hlam
    funext t
    unfold fixedHeightQuadraticKernel
    rw [oscillatoryScaleIndex_abs lam height hlam]
    simp only [map_mul, Complex.conj_ofReal, fixedHeight_conj_phase,
      abs_of_neg hn, neg_mul, neg_neg]

/-- The actual fixed-height finite-modulation maximal `L²` decay theorem for
the full signed dyadic kernel and arbitrary nonzero real modulations. Every
analytic hypothesis has been discharged; only the input's `L²` membership and
positive oscillation height remain. -/
theorem finite_fixedHeightQuadraticKernel_maximal_sq_decay
    (n height : ℕ) (hh : 1 ≤ height) (lam : Fin (n + 1) → ℝ) (hlam : ∀ i, lam i ≠ 0)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ x, finiteConvolutionMaximal
      (fun i ↦ fixedHeightQuadraticKernel (lam i) height (hlam i)) f x ^ 2) ≤
      ENNReal.ofReal (70996725888 * positiveDyadicAmplitudeBound ^ 2 /
        (2 : ℝ) ^ ((height - 1) / 5)) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  apply finiteConvolutionMaximal_bound_of_measurable_memLp _ _ ?_ hf
  intro g hgm hg
  have h := finiteConvolutionMaximal_eq_or_conj_sq_bound
    (fun i ↦ fixedHeightQuadraticKernel |lam i| height (abs_ne_zero.mpr (hlam i)))
    (fun i ↦ fixedHeightQuadraticKernel (lam i) height (hlam i))
    (fun i ↦ (continuous_fixedHeightQuadraticKernel _ _ _).measurable)
    (fun i ↦ fixedHeightQuadraticKernel_eq_or_conj_abs _ _ _)
    (ENNReal.ofReal (17749181472 * positiveDyadicAmplitudeBound ^ 2 /
      (2 : ℝ) ^ ((height - 1) / 5)))
    (fun g hg ↦ finite_fixedHeightQuadraticKernel_positive_maximal_sq_decay n height hh
      (fun i ↦ |lam i|) (fun i ↦ abs_pos.mpr (hlam i)) hg) hgm hg
  convert h using 1
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  congr 2
  ring

end QuadraticCarleson
