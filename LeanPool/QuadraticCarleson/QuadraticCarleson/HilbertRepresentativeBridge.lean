/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.HilbertPoissonFourier

/-!
# Fourier and pointwise Hilbert representatives

Fourier pairing identities identify the Poisson-smoothed Hilbert transform with its spectral
representative. This gives Cotlar bounds for the stopping good part using the canonical L²
Hilbert transform.
-/

open Filter Function MeasureTheory Set FourierTransform
open scoped ENNReal SchwartzMap Topology ContDiff

namespace QuadraticCarleson.HilbertRepresentativeBridge


theorem integral_fourier_mul_eq (f g : ℝ → ℂ)
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕 f x * g x) = ∫ x, f x * 𝓕 g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf hg
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by ext; simp
  rw [hflip] at h
  exact h

/-- The integral Fourier transform of an `L¹ ∩ L²` function agrees almost
everywhere with the canonical `L²` Fourier representative. Schwartz-test
duality avoids making an additional approximation choice. -/
theorem fourier_toLp_ae_eq {f : ℝ → ℂ} (hf : Integrable f)
    (hf₂ : MemLp f 2 volume) :
    (⇑(Lp.fourierTransformₗᵢ ℝ ℂ (hf₂.toLp f)) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  have hc : Continuous (𝓕 f) := by
    have he := Real.fourierTransform_toLp (memLp_one_iff_integrable.mpr hf)
    rw [← he]
    exact (Real.Lp.fourierTransform _).continuous
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (by norm_num)) hc.locallyIntegrable
  intro g hgs hgc
  have hgc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hgs' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let φ : 𝓢(ℝ, ℂ) := hgc'.toSchwartzMap hgs'
  have hdist := congrArg (fun T : 𝓢'(ℝ, ℂ) ↦ T φ)
    (Lp.fourier_toTemperedDistribution_eq (hf₂.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hdist
  have hinput : (∫ x, (𝓕 φ) x • hf₂.toLp f x) = ∫ x, (𝓕 φ) x * f x := by
    apply integral_congr_ae
    filter_upwards [hf₂.coeFn_toLp] with x hx
    simp only [hx, smul_eq_mul]
  rw [hinput] at hdist
  calc
    (∫ x, g x • (Lp.fourierTransformₗᵢ ℝ ℂ (hf₂.toLp f)) x) =
        ∫ x, (𝓕 φ) x * f x := by
      change (∫ x, g x • (𝓕 (hf₂.toLp f)) x) = _
      simpa [φ, Complex.real_smul] using hdist.symm
    _ = ∫ x, φ x * 𝓕 f x := by
      exact integral_fourier_mul_eq φ f φ.integrable hf
    _ = ∫ x, g x • 𝓕 f x := by simp [φ, Complex.real_smul]


open HilbertPoissonFourier HilbertL2Fourier HilbertMaximalWeakOneOne
open scoped ComplexConjugate InnerProductSpace

theorem integral_conj_mul_eq_fourier {k : ℝ → ℂ} (hk : Integrable k)
    (hk₂ : MemLp k 2 volume) (h : Lp (α := ℝ) ℂ 2 volume) :
    (∫ y, conj (k y) * h y) =
      ∫ ξ, conj (𝓕 k ξ) * (Lp.fourierTransformₗᵢ ℝ ℂ h) ξ := by
  have hi := Lp.inner_fourier_eq (hk₂.toLp k) h
  rw [L2.inner_def, L2.inner_def] at hi
  have hi' : (∫ ξ, conj (𝓕 k ξ) * (Lp.fourierTransformₗᵢ ℝ ℂ h) ξ) =
      ∫ y, conj (k y) * h y := by
    calc
      _ = ∫ ξ, ⟪(𝓕 (hk₂.toLp k)) ξ, (𝓕 h) ξ⟫_ℂ := by
        apply integral_congr_ae
        filter_upwards [fourier_toLp_ae_eq hk hk₂] with ξ hξ
        simp only [RCLike.inner_apply]
        rw [← hξ, mul_comm]
        rfl
      _ = ∫ y, ⟪hk₂.toLp k y, h y⟫_ℂ := hi
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hk₂.coeFn_toLp] with y hy
        simp [hy, RCLike.inner_apply, mul_comm]
  exact hi'.symm

theorem memLp_normalizedPoissonKernel {r : ℝ} (hr : 0 < r) :
    MemLp (normalizedPoissonKernel r) 2 volume := by
  have hae := fourier_toLp_ae_eq (integrable_poissonSpectralKernel hr)
    (memLp_two_poissonSpectralKernel hr)
  rw [fourier_poissonSpectralKernel_eq_normalized hr] at hae
  exact (memLp_congr_ae hae).mp (Lp.memLp _)

theorem fourier_translated_normalizedPoissonKernel {r : ℝ} (hr : 0 < r)
    (x ξ : ℝ) :
    𝓕 (fun y ↦ normalizedPoissonKernel r (y - x)) ξ =
      Real.fourierChar (-(x * ξ)) • poissonSpectralKernel r ξ := by
  have ht := fourier_comp_add_right_real (normalizedPoissonKernel r) (-x) ξ
  simpa only [sub_eq_add_neg, neg_mul, fourier_normalizedPoissonKernel hr] using ht


/-- Poisson convolution of any `L²` representative is given pointwise by
the absolutely convergent damped inverse Fourier integral. -/
theorem normalizedPoissonAction_eq_spectral {r : ℝ} (hr : 0 < r)
    (h : Lp (α := ℝ) ℂ 2 volume) (x : ℝ) :
    (∫ y, normalizedPoissonKernel r (x - y) * h y) =
      ∫ ξ, Real.fourierChar (x * ξ) •
        (poissonSpectralKernel r ξ * (Lp.fourierTransformₗᵢ ℝ ℂ h) ξ) := by
  let k : ℝ → ℂ := fun y ↦ normalizedPoissonKernel r (y - x)
  have hk : Integrable k := by
    simpa only [k, sub_eq_add_neg] using
      (integrable_normalizedPoissonKernel hr).comp_add_right (-x)
  have hk₂ : MemLp k 2 volume := by
    simpa only [k, Function.comp_def, sub_eq_add_neg] using
      (memLp_normalizedPoissonKernel hr).comp_measurePreserving
        (measurePreserving_add_right volume (-x))
  have hpair := integral_conj_mul_eq_fourier hk hk₂ h
  calc
    _ = ∫ y, conj (k y) * h y := by
      congr 1
      funext y
      congr 1
      simp only [k, normalizedPoissonKernel, Complex.conj_ofReal]
      congr 2
      unfold cotlarPoissonKernel
      rw [show (x - y) ^ 2 = (y - x) ^ 2 by ring]
    _ = ∫ ξ, conj (𝓕 k ξ) * (Lp.fourierTransformₗᵢ ℝ ℂ h) ξ := hpair
    _ = _ := by
      congr 1
      funext ξ
      rw [show 𝓕 k ξ = Real.fourierChar (-(x * ξ)) • poissonSpectralKernel r ξ from
        fourier_translated_normalizedPoissonKernel hr x ξ]
      simp [Circle.smul_def, poissonSpectralKernel, ← Complex.exp_conj, mul_assoc,
        map_ofNat]


/-- The genuine conjugate-Poisson action equals Poisson smoothing of the
Fourier-defined ordinary Hilbert transform, at every center and radius. -/
theorem cotlarConjugatePoissonAction_eq_poisson_hilbert
    {g : ℝ → ℂ} (hg : Integrable g) (hg₂ : MemLp g 2 volume)
    {r : ℝ} (hr : 0 < r) (x : ℝ) :
    cotlarConjugatePoissonAction r g x =
      (Real.pi : ℂ)⁻¹ *
        cotlarPoissonAction r (ordinaryHilbertTransformL2 (hg₂.toLp g)) x := by
  rw [cotlarConjugatePoissonAction_eq_hilbertSpectral hr hg x]
  have hs := normalizedPoissonAction_eq_spectral hr
    (ordinaryHilbertTransformL2 (hg₂.toLp g)) x
  have hspec : cotlarHilbertSpectralAction r g x =
      ∫ ξ, Real.fourierChar (x * ξ) •
        (poissonSpectralKernel r ξ *
          (Lp.fourierTransformₗᵢ ℝ ℂ (ordinaryHilbertTransformL2 (hg₂.toLp g))) ξ) := by
    apply integral_congr_ae
    filter_upwards [coe_fourier_ordinaryHilbertTransformL2_ae (hg₂.toLp g),
      fourier_toLp_ae_eq hg hg₂] with ξ hH hF
    simp only [hH, multipliedFourierRepresentative, fourierL2Representative, hF]
    rw [mul_assoc]
  rw [hspec, ← hs]
  rw [cotlarPoissonAction, ← integral_const_mul]
  congr 1
  funext y
  simp [normalizedPoissonKernel, div_eq_mul_inv, mul_comm, mul_left_comm]


open CalderonZygmundDyadicStopping

theorem cotlarConjugatePoissonAction_stoppingGoodPart_eq_poisson
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {r : ℝ} (hr : 0 < r) (x : ℝ) :
    cotlarConjugatePoissonAction r (stoppingGoodPart f) x =
      (Real.pi : ℂ)⁻¹ * cotlarPoissonAction r
        (measurableStoppingGoodHilbertRepresentative f hfi) x := by
  rw [cotlarConjugatePoissonAction_eq_poisson_hilbert
    (integrable_stoppingGoodPart_for_hilbert hf hfi) (memLp_two_stoppingGoodPart hfi) hr x]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_eq_measurableStoppingGoodHilbertRepresentative hfi] with y hy
  change (cotlarPoissonKernel r (x - y) : ℂ) *
    stoppingGoodHilbertL2Representative f hfi y = _
  rw [hy]

/-- The missing pointwise Cotlar bound for the genuine sharp truncation of
the canonical stopping good part. -/
theorem enorm_quadraticHilbertTrunc_stoppingGoodPart_le_cotlar
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ‖quadraticHilbertTrunc 0 r (stoppingGoodPart f) x‖ₑ ≤
      ENNReal.ofReal Real.pi⁻¹ * (20 * centeredHardyLittlewoodMaximal
        (fun y ↦ ‖measurableStoppingGoodHilbertRepresentative f hfi y‖ₑ) x) +
      ENNReal.ofReal (44 / 3) * centeredHardyLittlewoodMaximal
        (fun y ↦ ‖stoppingGoodPart f y‖ₑ) x := by
  apply (enorm_quadraticHilbertTrunc_stoppingGoodPart_le_conjugatePoisson hf hfi hr x).trans
  apply add_le_add ?_ le_rfl
  rw [cotlarConjugatePoissonAction_stoppingGoodPart_eq_poisson hf hfi hr x, enorm_mul]
  have hpi : ‖(Real.pi : ℂ)⁻¹‖ₑ = ENNReal.ofReal Real.pi⁻¹ := by
    rw [← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hpi]
  exact mul_le_mul' le_rfl
    (enorm_cotlarPoissonAction_stoppingGoodHilbert_le_maximal hfi hr x)

/-- Taking the actual supremum over all positive radii preserves the
uniform Cotlar estimate. -/
theorem quadraticHilbertMaximalTruncation_stoppingGoodPart_le_cotlar
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) (x : ℝ) :
    quadraticHilbertMaximalTruncation 0 (stoppingGoodPart f) x ≤
      ENNReal.ofReal Real.pi⁻¹ * (20 * centeredHardyLittlewoodMaximal
        (fun y ↦ ‖measurableStoppingGoodHilbertRepresentative f hfi y‖ₑ) x) +
      ENNReal.ofReal (44 / 3) * centeredHardyLittlewoodMaximal
        (fun y ↦ ‖stoppingGoodPart f y‖ₑ) x := by
  apply iSup_le
  intro r
  exact enorm_quadraticHilbertTrunc_stoppingGoodPart_le_cotlar hf hfi r.2 x


end QuadraticCarleson.HilbertRepresentativeBridge
