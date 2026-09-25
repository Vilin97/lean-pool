/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# The principal-value distribution `p.v. (1 / x)`

This file constructs the Hilbert-transform kernel directly from Parissis's
cancelled integral formula. On a Schwartz test function `f`, the pairing is

`∫_{|x|<1} (f(x)-f(0))/x dx + ∫_{|x|≥1} f(x)/x dx`.

The cancellation controls the singularity by the first derivative Schwartz
seminorm, while Schwartz decay controls the tail. The resulting functional
is continuous, hence a tempered distribution. `PVSymmetricLimit.lean` proves
that it is exactly the limit of symmetric truncations. We also define the
Fourier-side candidate `-π i · 𝓕⁻ sign`; identifying it with the direct
construction is kept as a theorem rather than assumed by definition.
-/

@[expose] public section

open MeasureTheory Set
open FourierTransform
open scoped SchwartzMap

namespace QuadraticCarleson

/-- Lebesgue measure restricted to the positive half-line. -/
noncomputable def positiveHalfLineMeasure : Measure ℝ :=
  volume.restrict (Ioi 0)

/-- Lebesgue measure restricted to the negative half-line. -/
noncomputable def negativeHalfLineMeasure : Measure ℝ :=
  volume.restrict (Iio 0)

noncomputable instance positiveHalfLineMeasure_hasTemperateGrowth :
    positiveHalfLineMeasure.HasTemperateGrowth := by
  obtain ⟨n, hn⟩ :=
    (inferInstance : (volume : Measure ℝ).HasTemperateGrowth).exists_integrable
  exact ⟨⟨n, hn.mono_measure Measure.restrict_le_self⟩⟩

noncomputable instance negativeHalfLineMeasure_hasTemperateGrowth :
    negativeHalfLineMeasure.HasTemperateGrowth := by
  obtain ⟨n, hn⟩ :=
    (inferInstance : (volume : Measure ℝ).HasTemperateGrowth).exists_integrable
  exact ⟨⟨n, hn.mono_measure Measure.restrict_le_self⟩⟩

/-- The tempered distribution associated to the sign function. -/
noncomputable def signTemperedDistribution : 𝓢'(ℝ, ℂ) :=
  positiveHalfLineMeasure.toTemperedDistribution -
    negativeHalfLineMeasure.toTemperedDistribution

theorem signTemperedDistribution_apply (f : 𝓢(ℝ, ℂ)) :
    signTemperedDistribution f =
      (∫ x in Ioi (0 : ℝ), f x) - ∫ x in Iio (0 : ℝ), f x := by
  rfl

/-- The symmetric truncation of the principal-value pairing with a Schwartz
test function. The set of integration is exactly `{x | ε < |x|}`, so the
same radius is removed on the positive and negative sides of the origin. -/
noncomputable def principalValueTruncation (ε : ℝ) (f : 𝓢(ℝ, ℂ)) : ℂ :=
  ∫ x in {x : ℝ | ε < |x|}, f x / (x : ℂ)

/-- A symmetric truncation is an ordinary Bochner integral whenever the
deleted radius is positive. Thus no value is assigned at the singularity
and no principal-value limit is being assumed here. -/
theorem integrableOn_schwartz_div_id {ε : ℝ} (hε : 0 < ε) (f : 𝓢(ℝ, ℂ)) :
    IntegrableOn (fun x : ℝ ↦ f x / (x : ℂ)) {x : ℝ | ε < |x|} := by
  let s : Set ℝ := {x : ℝ | ε < |x|}
  have hs : MeasurableSet s := (isOpen_lt continuous_const continuous_abs).measurableSet
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦ f x / (x : ℂ))
      (volume.restrict s) :=
    (f.continuous.measurable.div Complex.continuous_ofReal.measurable).aestronglyMeasurable
  refine ((f.integrable.norm.const_mul ε⁻¹).integrableOn).mono' hmeas ?_
  filter_upwards [ae_restrict_mem hs] with x hx
  change ‖f x / (x : ℂ)‖ ≤ ε⁻¹ * ‖f x‖
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv]
  calc
    ‖f x‖ * |x|⁻¹ ≤ ‖f x‖ * ε⁻¹ :=
      mul_le_mul_of_nonneg_left
        ((inv_le_inv₀ (hε.trans hx) hε).2 (le_of_lt hx)) (norm_nonneg _)
    _ = ε⁻¹ * ‖f x‖ := mul_comm _ _

/-- The first Schwartz seminorm controls increments of a test function. This
is the mean-value estimate used to cancel the singularity in `p.v. (1 / x)`. -/
theorem norm_schwartz_sub_le_derivSeminorm (f : 𝓢(ℝ, ℂ)) (x y : ℝ) :
    ‖f y - f x‖ ≤ SchwartzMap.seminorm ℂ 0 1 f * |y - x| := by
  apply convex_univ.norm_image_sub_le_of_norm_deriv_le
      (s := (Set.univ : Set ℝ)) (𝕜 := ℝ) (fun z _ ↦ f.differentiableAt)
      (fun z _ ↦ ?_) (Set.mem_univ x) (Set.mem_univ y)
  simpa only [← iteratedDeriv_one, pow_zero, one_mul] using f.le_seminorm' ℂ 0 1 z

/-- The nonsingular representative used for the local part of the
principal-value functional. -/
noncomputable def principalValueNearIntegrand (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  (f x - f 0) / (x : ℂ)

/-- Pointwise cancellation estimate at the singularity. -/
theorem norm_principalValueNearIntegrand_le (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖principalValueNearIntegrand f x‖ ≤ SchwartzMap.seminorm ℂ 0 1 f := by
  by_cases hx : x = 0
  · simp [principalValueNearIntegrand, hx]
  · rw [principalValueNearIntegrand, norm_div, Complex.norm_real, Real.norm_eq_abs]
    apply (div_le_iff₀ (abs_pos.mpr hx)).2
    simpa only [sub_zero, mul_comm] using norm_schwartz_sub_le_derivSeminorm f 0 x

/-- Cancellation of the constant term makes the local principal-value
integrand integrable. -/
theorem integrableOn_principalValueNearIntegrand (f : 𝓢(ℝ, ℂ)) :
    IntegrableOn (principalValueNearIntegrand f) (Ioo (-1 : ℝ) 1) := by
  have hs : MeasurableSet (Ioo (-1 : ℝ) 1) := measurableSet_Ioo
  have hmeas : AEStronglyMeasurable (principalValueNearIntegrand f)
      (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    ((f.continuous.sub continuous_const).measurable.div
      Complex.continuous_ofReal.measurable).aestronglyMeasurable
  refine (integrableOn_const (hs := ne_of_lt measure_Ioo_lt_top) : IntegrableOn
      (fun _ : ℝ ↦ SchwartzMap.seminorm ℂ 0 1 f) (Ioo (-1 : ℝ) 1)).mono' hmeas ?_
  filter_upwards with x
  exact norm_principalValueNearIntegrand_le f x

theorem norm_integral_principalValueNearIntegrand_le (f : 𝓢(ℝ, ℂ)) :
    ‖∫ x in Ioo (-1 : ℝ) 1, principalValueNearIntegrand f x‖ ≤
      2 * SchwartzMap.seminorm ℂ 0 1 f := by
  calc
    ‖∫ x in Ioo (-1 : ℝ) 1, principalValueNearIntegrand f x‖ ≤
        SchwartzMap.seminorm ℂ 0 1 f * (volume.real (Ioo (-1 : ℝ) 1)) :=
      norm_setIntegral_le_of_norm_le_const measure_Ioo_lt_top
        (fun x _ ↦ norm_principalValueNearIntegrand_le f x)
    _ = 2 * SchwartzMap.seminorm ℂ 0 1 f := by
      rw [Measure.real, Real.volume_Ioo]
      norm_num
      ring

/-- Away from the origin, division by `x` preserves integrability of a
Schwartz test function. -/
theorem integrableOn_principalValueFarIntegrand (f : 𝓢(ℝ, ℂ)) :
    IntegrableOn (fun x : ℝ ↦ f x / (x : ℂ)) {x : ℝ | 1 ≤ |x|} := by
  let s : Set ℝ := {x : ℝ | 1 ≤ |x|}
  have hs : MeasurableSet s := (isClosed_le continuous_const continuous_abs).measurableSet
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦ f x / (x : ℂ))
      (volume.restrict s) :=
    (f.continuous.measurable.div Complex.continuous_ofReal.measurable).aestronglyMeasurable
  refine f.integrable.norm.integrableOn.mono' hmeas ?_
  filter_upwards [ae_restrict_mem hs] with x hx
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
  exact div_le_self (norm_nonneg _) hx

theorem norm_integral_principalValueFarIntegrand_le (f : 𝓢(ℝ, ℂ)) :
    ‖∫ x in {x : ℝ | 1 ≤ |x|}, f x / (x : ℂ)‖ ≤ ∫ x : ℝ, ‖f x‖ := by
  let s : Set ℝ := {x : ℝ | 1 ≤ |x|}
  calc
    ‖∫ x in s, f x / (x : ℂ)‖ ≤ ∫ x in s, ‖f x / (x : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in s, ‖f x‖ := by
      apply setIntegral_mono_ae_restrict
        (integrableOn_principalValueFarIntegrand f).norm f.integrable.norm.integrableOn
      filter_upwards [ae_restrict_mem
        ((isClosed_le continuous_const continuous_abs).measurableSet)] with x hx
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_self (norm_nonneg _) hx
    _ ≤ ∫ x : ℝ, ‖f x‖ :=
      setIntegral_le_integral f.integrable.norm
        (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))

/-- Parissis's direct formula for the principal-value pairing: subtract the
constant term near zero, and use the ordinary integral away from zero. -/
noncomputable def principalValuePairing (f : 𝓢(ℝ, ℂ)) : ℂ :=
  (∫ x in Ioo (-1 : ℝ) 1, principalValueNearIntegrand f x) +
    ∫ x in {x : ℝ | 1 ≤ |x|}, f x / (x : ℂ)

theorem principalValuePairing_add (f g : 𝓢(ℝ, ℂ)) :
    principalValuePairing (f + g) = principalValuePairing f + principalValuePairing g := by
  have hnear : principalValueNearIntegrand (f + g) =
      fun x ↦ principalValueNearIntegrand f x + principalValueNearIntegrand g x := by
    funext x
    simp [principalValueNearIntegrand]
    ring
  have hfar : (fun x : ℝ ↦ (f + g) x / (x : ℂ)) =
    fun x ↦ f x / (x : ℂ) + g x / (x : ℂ) := by
    funext x
    simp only [add_apply, add_div]
  rw [principalValuePairing, principalValuePairing, principalValuePairing, hnear,
    hfar, integral_add (integrableOn_principalValueNearIntegrand f)
      (integrableOn_principalValueNearIntegrand g),
    integral_add (integrableOn_principalValueFarIntegrand f)
      (integrableOn_principalValueFarIntegrand g)]
  ring

theorem principalValuePairing_smul (a : ℂ) (f : 𝓢(ℝ, ℂ)) :
    principalValuePairing (a • f) = a • principalValuePairing f := by
  have hnear : principalValueNearIntegrand (a • f) =
      fun x ↦ a • principalValueNearIntegrand f x := by
    funext x
    simp [principalValueNearIntegrand, smul_eq_mul]
    ring
  have hfar : (fun x : ℝ ↦ (a • f) x / (x : ℂ)) =
      fun x ↦ a • (f x / (x : ℂ)) := by
    funext x
    simp [smul_eq_mul]
    ring
  rw [principalValuePairing, principalValuePairing, hnear, hfar,
    integral_smul, integral_smul]
  simp only [smul_eq_mul]
  ring

/-- A fixed finite constant controlling the `L¹` norm of Schwartz functions
by two Schwartz seminorms. -/
noncomputable def principalValueTailBound : ℝ :=
  2 ^ (volume : Measure ℝ).integrablePower *
    ∫ x : ℝ, (1 + ‖x‖) ^ (-((volume : Measure ℝ).integrablePower : ℝ))

theorem principalValueTailBound_nonneg : 0 ≤ principalValueTailBound := by
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro x
  positivity

theorem integral_norm_schwartz_le (f : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, ‖f x‖ ≤ principalValueTailBound *
      (SchwartzMap.seminorm ℂ 0 0 f +
        SchwartzMap.seminorm ℂ (volume : Measure ℝ).integrablePower 0 f) := by
  simpa only [principalValueTailBound, pow_zero, one_mul,
    norm_iteratedFDeriv_zero, zero_add] using
      f.integral_pow_mul_iteratedFDeriv_le ℂ (volume : Measure ℝ) 0 0

theorem norm_principalValuePairing_le (f : 𝓢(ℝ, ℂ)) :
    ‖principalValuePairing f‖ ≤
      2 * SchwartzMap.seminorm ℂ 0 1 f + principalValueTailBound *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (volume : Measure ℝ).integrablePower 0 f) := by
  calc
    ‖principalValuePairing f‖ ≤
        ‖∫ x in Ioo (-1 : ℝ) 1, principalValueNearIntegrand f x‖ +
          ‖∫ x in {x : ℝ | 1 ≤ |x|}, f x / (x : ℂ)‖ := by
      exact norm_add_le _ _
    _ ≤ 2 * SchwartzMap.seminorm ℂ 0 1 f + ∫ x : ℝ, ‖f x‖ :=
      add_le_add (norm_integral_principalValueNearIntegrand_le f)
        (norm_integral_principalValueFarIntegrand_le f)
    _ ≤ 2 * SchwartzMap.seminorm ℂ 0 1 f + principalValueTailBound *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (volume : Measure ℝ).integrablePower 0 f) :=
      add_le_add le_rfl (integral_norm_schwartz_le f)

/-- The direct principal-value pairing, bundled as a continuous linear
functional on Schwartz space. -/
noncomputable def principalValuePairingCLM : 𝓢(ℝ, ℂ) →L[ℂ] ℂ := by
  refine SchwartzMap.mkCLMtoNormedSpace principalValuePairing
    principalValuePairing_add principalValuePairing_smul ?_
  let n : ℕ := (volume : Measure ℝ).integrablePower
  let s : Finset (ℕ × ℕ) := Finset.range (n + 1) ×ˢ Finset.range 2
  let C : ℝ := 2 + 2 * principalValueTailBound
  refine ⟨s, C, ?_, fun f ↦ ?_⟩
  · dsimp [C]
    exact add_nonneg (by norm_num)
      (mul_nonneg (by norm_num) principalValueTailBound_nonneg)
  · let M : ℝ := s.sup (schwartzSeminormFamily ℂ ℝ ℂ) f
    have h1 : SchwartzMap.seminorm ℂ 0 1 f ≤ M := by
      change (schwartzSeminormFamily ℂ ℝ ℂ (0, 1)) f ≤
        (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f
      exact (Finset.le_sup (f := schwartzSeminormFamily ℂ ℝ ℂ)
        (show (0, 1) ∈ s by simp [s])) f
    have h0 : SchwartzMap.seminorm ℂ 0 0 f ≤ M := by
      change (schwartzSeminormFamily ℂ ℝ ℂ (0, 0)) f ≤
        (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f
      exact (Finset.le_sup (f := schwartzSeminormFamily ℂ ℝ ℂ)
        (show (0, 0) ∈ s by simp [s])) f
    have hn : SchwartzMap.seminorm ℂ n 0 f ≤ M := by
      change (schwartzSeminormFamily ℂ ℝ ℂ (n, 0)) f ≤
        (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f
      exact (Finset.le_sup (f := schwartzSeminormFamily ℂ ℝ ℂ)
        (show (n, 0) ∈ s by simp [s])) f
    calc
      ‖principalValuePairing f‖ ≤
          2 * SchwartzMap.seminorm ℂ 0 1 f + principalValueTailBound *
            (SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ n 0 f) := by
        simpa only [n] using norm_principalValuePairing_le f
      _ ≤ 2 * M + principalValueTailBound * (M + M) := by
        gcongr
        exact principalValueTailBound_nonneg
      _ = C * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) f := by
        dsimp [C, M]
        ring

/-- The Hilbert-transform kernel `p.v. (1 / x)` as a tempered distribution,
defined directly by the cancellation formula on Schwartz test functions. -/
noncomputable def principalValueOneDiv : 𝓢'(ℝ, ℂ) :=
  ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _ principalValuePairingCLM

@[simp]
theorem principalValueOneDiv_apply (f : 𝓢(ℝ, ℂ)) :
    principalValueOneDiv f = principalValuePairing f := by
  rfl

/-- The Fourier-side candidate for `p.v. (1 / x)`. Its equality with the
direct symmetric-principal-value construction is a theorem, not a definition.
The normalization is `𝓕 f(ξ) = ∫ exp(-2π i xξ) f(x) dx`. -/
noncomputable def principalValueOneDivFourierCandidate : 𝓢'(ℝ, ℂ) :=
  (-((Real.pi : ℂ) * Complex.I)) • 𝓕⁻ signTemperedDistribution

theorem fourier_principalValueOneDivFourierCandidate :
    𝓕 principalValueOneDivFourierCandidate =
      (-((Real.pi : ℂ) * Complex.I)) • signTemperedDistribution := by
  simp [principalValueOneDivFourierCandidate]

end QuadraticCarleson
