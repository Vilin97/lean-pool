/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PVSymmetricLimit
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Differential prerequisites for the principal-value Fourier identity

For the canonical distribution defined by symmetric truncations, we prove
`x * p.v. (1 / x) = 1` and hence `(𝓕 p.v. (1 / x))' = -2π i δ₀`.
The jump calculation `sign' = 2 δ₀` shows that the error in the desired
Fourier identity has derivative zero. Reflection of the defining integrals
shows that this error is also odd.

The Fourier identity therefore holds on all derivatives of Schwartz test
functions. Its extension to arbitrary Schwartz functions is reduced below
to one explicitly stated generic prerequisite: every odd Schwartz function
has a Schwartz antiderivative. The final conditional theorems expose that
prerequisite; they do not assert an unconditional Fourier identification.
-/

open MeasureTheory Set Filter FourierTransform LineDeriv
open scoped SchwartzMap Topology

namespace QuadraticCarleson

/-- The canonical direct distribution is the symmetric principal-value
limit on every Schwartz test function. -/
theorem tendsto_principalValueTruncation_oneDiv (f : 𝓢(ℝ, ℂ)) :
    Tendsto (fun ε : ℝ ↦ principalValueTruncation ε f) (𝓝[>] 0)
      (𝓝 (principalValueOneDiv f)) := by
  simpa only [principalValueOneDiv_apply] using tendsto_principalValueTruncation f

/-- Multiplication by the coordinate cancels the principal-value kernel:
`x * p.v. (1 / x) = 1` as tempered distributions. -/
theorem smulLeft_id_principalValueOneDiv :
    TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) principalValueOneDiv =
      (volume : Measure ℝ).toTemperedDistribution := by
  ext f
  have hpoly : (fun x : ℝ ↦ (x : ℂ)).HasTemperateGrowth := by fun_prop
  let g := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) f
  have hg : ∀ x, g x = (x : ℂ) * f x := by
    intro x
    simp [g, SchwartzMap.smulLeftCLM_apply_apply hpoly, smul_eq_mul]
  have ha : (fun x : ℝ ↦ g x / (x : ℂ)) =ᵐ[volume] f := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    rw [hg]
    exact mul_div_cancel_left₀ (f x) (Complex.ofReal_ne_zero.mpr hx)
  have hn : principalValueNearIntegrand g =ᵐ[volume] f := by
    filter_upwards [ha] with x hx
    simpa only [principalValueNearIntegrand, hg 0, Complex.ofReal_zero, zero_mul,
      sub_zero] using hx
  change principalValuePairing g = ∫ x : ℝ, f x
  rw [principalValuePairing,
    integral_congr_ae (ae_restrict_of_ae hn), integral_congr_ae (ae_restrict_of_ae ha)]
  have hc : {x : ℝ | 1 ≤ |x|} = (Ioo (-1 : ℝ) 1)ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_compl_iff, mem_Ioo, ← abs_lt, not_lt]
  rw [hc]
  exact integral_add_compl measurableSet_Ioo f.integrable

/-- The integral of a Schwartz derivative on a positive half-line is its
negative boundary value. -/
theorem integral_Ioi_schwartz_deriv (f : 𝓢(ℝ, ℂ)) (a : ℝ) :
    (∫ x in Ioi a, deriv f x) = -f a := by
  simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ ↦ f.hasDerivAt x) (SchwartzMap.derivCLM ℂ ℂ f).integrable.integrableOn
    (f.tendsto_cocompact.mono_left atTop_le_cocompact)

/-- The integral of a Schwartz derivative on a negative half-line is its
boundary value. -/
theorem integral_Iio_schwartz_deriv (f : 𝓢(ℝ, ℂ)) (a : ℝ) :
    (∫ x in Iio a, deriv f x) = f a := by
  rw [← integral_Iic_eq_integral_Iio]
  simpa only [sub_zero] using integral_Iic_of_hasDerivAt_of_tendsto'
    (fun x _ ↦ f.hasDerivAt x) (SchwartzMap.derivCLM ℂ ℂ f).integrable.integrableOn
    (f.tendsto_cocompact.mono_left atBot_le_cocompact)

/-- The jump of the sign distribution has size two at the origin. -/
theorem deriv_signTemperedDistribution :
    TemperedDistribution.derivCLM ℂ signTemperedDistribution =
      (2 : ℂ) • TemperedDistribution.delta (0 : ℝ) := by
  ext f
  change signTemperedDistribution (-SchwartzMap.derivCLM ℂ ℂ f) =
    (2 : ℂ) * f 0
  simp only [signTemperedDistribution_apply, neg_apply, SchwartzMap.derivCLM_apply,
    integral_neg, integral_Ioi_schwartz_deriv, integral_Iio_schwartz_deriv]
  ring

theorem schwartz_lineDeriv_one_eq_deriv (f : 𝓢(ℝ, ℂ)) :
    ∂_{(1 : ℝ)} f = SchwartzMap.derivCLM ℂ ℂ f := by
  ext x
  simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem distribution_lineDeriv_one_eq_deriv (T : 𝓢'(ℝ, ℂ)) :
    ∂_{(1 : ℝ)} T = TemperedDistribution.derivCLM ℂ T := by
  ext f
  rw [TemperedDistribution.lineDerivOp_apply_apply,
    TemperedDistribution.derivCLM_apply_apply, schwartz_lineDeriv_one_eq_deriv]

/-- The inverse Fourier transform of the delta at zero is the constant
distribution with density one. -/
theorem fourierInv_delta_zero :
    𝓕⁻ (TemperedDistribution.delta (0 : ℝ)) =
      (volume : Measure ℝ).toTemperedDistribution := by
  ext f
  simp [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]

/-- The Fourier transform of the constant distribution with density one
is the delta at zero. -/
theorem fourier_volume :
    𝓕 (volume : Measure ℝ).toTemperedDistribution =
      TemperedDistribution.delta (0 : ℝ) := by
  rw [← fourierInv_delta_zero, fourier_fourierInv_eq]

/-- The Fourier transform of the direct principal-value distribution has
the derivative required by `-π i sign`. -/
theorem deriv_fourier_principalValueOneDiv :
    TemperedDistribution.derivCLM ℂ (𝓕 principalValueOneDiv) =
      (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) •
        TemperedDistribution.delta (0 : ℝ) := by
  rw [← distribution_lineDeriv_one_eq_deriv,
    TemperedDistribution.lineDerivOp_fourier_eq]
  have hm : TemperedDistribution.smulLeftCLM ℂ
      (fun x : ℝ ↦ ((inner ℝ x 1 : ℝ) : ℂ)) principalValueOneDiv =
        (volume : Measure ℝ).toTemperedDistribution := by
    simpa using smulLeft_id_principalValueOneDiv
  rw [hm, fourier_smul, fourier_volume]

/-- The remaining error in the desired principal-value Fourier identity
has zero distributional derivative. -/
theorem deriv_principalValueFourier_error_eq_zero :
    TemperedDistribution.derivCLM ℂ
      (𝓕 principalValueOneDiv -
        (-((Real.pi : ℂ) * Complex.I)) • signTemperedDistribution) = 0 := by
  rw [map_sub, map_smul, deriv_fourier_principalValueOneDiv,
    deriv_signTemperedDistribution, smul_smul]
  have hc : -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) =
      (-((Real.pi : ℂ) * Complex.I)) * 2 := by ring
  rw [hc, sub_self]

/-- The full principal-value Fourier identity already holds on every
Schwartz test function which is a derivative of a Schwartz function. -/
theorem fourier_principalValueOneDiv_apply_deriv (f : 𝓢(ℝ, ℂ)) :
    (𝓕 principalValueOneDiv) (SchwartzMap.derivCLM ℂ ℂ f) =
      (-((Real.pi : ℂ) * Complex.I)) *
        signTemperedDistribution (SchwartzMap.derivCLM ℂ ℂ f) := by
  have h := congrArg (fun T : 𝓢'(ℝ, ℂ) ↦ T f)
    deriv_principalValueFourier_error_eq_zero
  change (𝓕 principalValueOneDiv -
      (-((Real.pi : ℂ) * Complex.I)) • signTemperedDistribution)
      (-SchwartzMap.derivCLM ℂ ℂ f) = 0 at h
  rw [map_neg, neg_eq_zero] at h
  exact sub_eq_zero.mp h

/-- Reflection of a Schwartz test function about the origin. -/
noncomputable def schwartzReflection : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ))

@[simp]
theorem schwartzReflection_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzReflection f x = f (-x) := rfl

theorem schwartzReflection_fourier (f : 𝓢(ℝ, ℂ)) :
    schwartzReflection (𝓕 f) = 𝓕 (schwartzReflection f) := by
  ext x
  change 𝓕 (f : ℝ → ℂ) (LinearIsometryEquiv.neg ℝ x) =
    𝓕 ((f : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ) x
  exact (Real.fourier_comp_linearIsometry _ _ _).symm

theorem principalValueTruncation_reflection (ε : ℝ) (f : 𝓢(ℝ, ℂ)) :
    principalValueTruncation ε (schwartzReflection f) =
      -principalValueTruncation ε f := by
  let s : Set ℝ := {x : ℝ | ε < |x|}
  have hs : MeasurableSet s :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  let F : ℝ → ℂ := s.indicator (fun x ↦ f x / (x : ℂ))
  have hneg : (fun x ↦ s.indicator
      (fun y ↦ schwartzReflection f y / (y : ℂ)) x) = fun x ↦ -F (-x) := by
    funext x
    simp only [F, s, Set.indicator, Set.mem_ofPred_eq, abs_neg,
      schwartzReflection_apply, Complex.ofReal_neg, div_neg]
    split_ifs <;> simp
  unfold principalValueTruncation
  change (∫ x in s, schwartzReflection f x / (x : ℂ)) =
    -(∫ x in s, f x / (x : ℂ))
  rw [← integral_indicator hs, ← integral_indicator hs, hneg,
    integral_neg, integral_neg_eq_self]

/-- The canonical direct principal-value distribution is odd. -/
theorem principalValueOneDiv_reflection (f : 𝓢(ℝ, ℂ)) :
    principalValueOneDiv (schwartzReflection f) = -principalValueOneDiv f := by
  apply tendsto_nhds_unique (tendsto_principalValueTruncation_oneDiv (schwartzReflection f))
  simpa only [principalValueTruncation_reflection] using
    (tendsto_principalValueTruncation_oneDiv f).neg

theorem signTemperedDistribution_reflection (f : 𝓢(ℝ, ℂ)) :
    signTemperedDistribution (schwartzReflection f) = -signTemperedDistribution f := by
  have hp : (∫ x in Ioi (0 : ℝ), f (-x)) = ∫ x in Iio (0 : ℝ), f x := by
    rw [integral_comp_neg_Ioi, neg_zero, integral_Iic_eq_integral_Iio]
  have hn : (∫ x in Iio (0 : ℝ), f (-x)) = ∫ x in Ioi (0 : ℝ), f x := by
    rw [← integral_Iic_eq_integral_Iio, integral_comp_neg_Iic, neg_zero]
  simp only [signTemperedDistribution_apply, schwartzReflection_apply, hp, hn]
  ring

/-- The error in the desired Fourier identity is odd, so the remaining
zero-derivative uniqueness argument cannot leave a nonzero constant. -/
theorem principalValueFourier_error_reflection (f : 𝓢(ℝ, ℂ)) :
    (𝓕 principalValueOneDiv -
      (-((Real.pi : ℂ) * Complex.I)) • signTemperedDistribution)
      (schwartzReflection f) =
    -(𝓕 principalValueOneDiv -
      (-((Real.pi : ℂ) * Complex.I)) • signTemperedDistribution) f := by
  change principalValueOneDiv (𝓕 (schwartzReflection f)) -
      (-((Real.pi : ℂ) * Complex.I)) *
        signTemperedDistribution (schwartzReflection f) =
    -(principalValueOneDiv (𝓕 f) -
      (-((Real.pi : ℂ) * Complex.I)) * signTemperedDistribution f)
  rw [← schwartzReflection_fourier, principalValueOneDiv_reflection,
    signTemperedDistribution_reflection]
  ring

/-- Exact reduction of the one-dimensional distributional uniqueness
argument to the existence of Schwartz antiderivatives of odd Schwartz
functions. No antiderivative existence is assumed by the preceding results. -/
theorem distribution_eq_zero_of_odd_schwartz_antiderivatives
    (hprimitive : ∀ f : 𝓢(ℝ, ℂ), Function.Odd (f : ℝ → ℂ) →
      ∃ g : 𝓢(ℝ, ℂ), SchwartzMap.derivCLM ℂ ℂ g = f)
    (T : 𝓢'(ℝ, ℂ)) (hderiv : TemperedDistribution.derivCLM ℂ T = 0)
    (hodd : ∀ f : 𝓢(ℝ, ℂ), T (schwartzReflection f) = -T f) : T = 0 := by
  ext f
  have ho : Function.Odd ((f - schwartzReflection f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    intro x
    simp only [sub_apply, schwartzReflection_apply, neg_neg]
    ring
  obtain ⟨g, hg⟩ := hprimitive (f - schwartzReflection f) ho
  have h := congrArg (fun U : 𝓢'(ℝ, ℂ) ↦ U g) hderiv
  change T (-SchwartzMap.derivCLM ℂ ℂ g) = 0 at h
  rw [map_neg, neg_eq_zero, hg, map_sub, hodd] at h
  exact self_eq_neg.mp (sub_eq_zero.mp h)

/-- Once odd Schwartz antiderivatives are available, all analytic
prerequisites proved above yield the desired Fourier characterization of
the canonical symmetric principal-value distribution. -/
theorem fourier_principalValueOneDiv_of_odd_schwartz_antiderivatives
    (hprimitive : ∀ f : 𝓢(ℝ, ℂ), Function.Odd (f : ℝ → ℂ) →
      ∃ g : 𝓢(ℝ, ℂ), SchwartzMap.derivCLM ℂ ℂ g = f) :
    𝓕 principalValueOneDiv =
      (-((Real.pi : ℂ) * Complex.I)) • signTemperedDistribution := by
  apply sub_eq_zero.mp
  exact distribution_eq_zero_of_odd_schwartz_antiderivatives hprimitive _
    deriv_principalValueFourier_error_eq_zero principalValueFourier_error_reflection

theorem principalValueOneDiv_eq_FourierCandidate_of_odd_schwartz_antiderivatives
    (hprimitive : ∀ f : 𝓢(ℝ, ℂ), Function.Odd (f : ℝ → ℂ) →
      ∃ g : 𝓢(ℝ, ℂ), SchwartzMap.derivCLM ℂ ℂ g = f) :
    principalValueOneDiv = principalValueOneDivFourierCandidate := by
  have h := congrArg (fun T : 𝓢'(ℝ, ℂ) ↦ 𝓕⁻ T)
    (fourier_principalValueOneDiv_of_odd_schwartz_antiderivatives hprimitive)
  simpa only [fourierInv_fourier_eq, fourierInv_smul,
    principalValueOneDivFourierCandidate] using h

end QuadraticCarleson
