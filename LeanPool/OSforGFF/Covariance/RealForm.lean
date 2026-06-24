/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Complex.Basic

import LeanPool.OSforGFF.Spacetime.Basic
import LeanPool.OSforGFF.Spacetime.PositiveTimeTestFunction
import LeanPool.OSforGFF.Spacetime.DiscreteSymmetry
import LeanPool.OSforGFF.Covariance.Position
import LeanPool.OSforGFF.Spacetime.ComplexTestFunction
import LeanPool.OSforGFF.Covariance.Momentum

/-!
# Real Covariance Form and Square Root Propagator Embedding

This file provides the real covariance form infrastructure along with the proof of the
square root propagator embedding theorem.

## Main Results

- `freeCovarianceFormR`: The real covariance bilinear form
- `sqrtPropagatorEmbedding`: Existence of linear embedding realizing covariance as squared norm
- `freeCovarianceFormR_continuous`: Continuity of the quadratic form f ↦ C(f,f)
- `freeCovarianceFormR_pos`: Positivity of the quadratic form
-/

open MeasureTheory Complex Matrix
open scoped Real InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace QFT

/-! ## Real Covariance Form -/

/-- Real covariance bilinear form induced by the free covariance kernel. -/
noncomputable def freeCovarianceFormR (m : ℝ) (f g : TestFunction) : ℝ :=
  ∫ x, ∫ y, (f x) * (freeCovariance m x y) * (g y) ∂volume ∂volume

theorem freeCovarianceℂ_bilinear_agrees_on_reals
  (m : ℝ) (f g : TestFunction) :
    freeCovarianceℂBilinear m (toComplex f) (toComplex g)
      = (freeCovarianceFormR m f g : ℂ) := by
  unfold freeCovarianceℂBilinear freeCovarianceFormR
  simp only [toComplex_apply]
  have h : ∀ (x y : SpaceTime),
    ((f x : ℂ)) * ((freeCovariance m x y : ℂ)) * ((g y : ℂ))
    = (((f x) * (freeCovariance m x y) * (g y) : ℝ) : ℂ) := by
    intro x y
    simp only [ofReal_mul]
  simp_rw [h]
  have step1 : ∫ x, ∫ y, ((f x * freeCovariance m x y * g y : ℝ) : ℂ)
             = ∫ x, ((∫ y, f x * freeCovariance m x y * g y : ℝ) : ℂ) := by
    congr 1 with x
    exact integral_ofReal
  rw [step1]
  exact integral_ofReal

/-! ## Weighted L² Space Construction -/

/-- The weighted measure on momentum space with density (‖k‖² + m²)⁻¹. -/
noncomputable def momentumWeightMeasure (m : ℝ) : Measure SpaceTime :=
  volume.withDensity (fun k => ENNReal.ofReal (momentumWeight m k))

/-- For `c : ℝ` and Schwartz functions over ℂ, ℝ-smul equals ℂ-smul by the canonical coercion. -/
private lemma schwartz_real_smul_eq_complex (c : ℝ) (f : SchwartzMap SpaceTime ℂ) :
    c • f = (c : ℂ) • f := by
  ext x; simp

/-- For `c : ℝ` and `Lp ℂ 2`, ℝ-smul equals ℂ-smul by the canonical coercion. -/
private lemma lp_real_smul_eq_complex (c : ℝ) (g : Lp ℂ 2 (volume : Measure SpaceTime)) :
    c • g = (c : ℂ) • g := by
  ext1; filter_upwards [Lp.coeFn_smul c g, Lp.coeFn_smul (c : ℂ) g] with x h1 h2
  rw [h1, h2]
  have : c • (g : SpaceTime → ℂ) x = (c : ℂ) • (g : SpaceTime → ℂ) x := by
    rw [Complex.real_smul, smul_eq_mul]
  exact this

/-- ℝ-linear view of the complex Fourier transform on Schwartz space.

Note: we build this manually instead of using `restrictScalars` because the
`LinearMap.CompatibleSMul` instance is not found automatically in mathlib v4.29.
-/
noncomputable def fourierTransformCLMReal :
    TestFunctionℂ →L[ℝ] TestFunctionℂ where
  toLinearMap :=
    { toFun := SchwartzMap.fourierTransformCLM ℂ
      map_add' := fun x y => map_add _ x y
      map_smul' := fun c x => by
        change SchwartzMap.fourierTransformCLM ℂ (c • x) = c • SchwartzMap.fourierTransformCLM ℂ x
        have hcx : c • x = (c : ℂ) • x := schwartz_real_smul_eq_complex c x
        have hmap : SchwartzMap.fourierTransformCLM ℂ ((c : ℂ) • x) =
            (c : ℂ) • SchwartzMap.fourierTransformCLM ℂ x :=
          ContinuousLinearMap.map_smul _ _ _
        rw [hcx, hmap, ← schwartz_real_smul_eq_complex] }
  cont := (SchwartzMap.fourierTransformCLM ℂ).continuous

/-- ℝ-linear view of the Schwartz-to-`L²` embedding. -/
noncomputable def schwartzToL2CLMReal (_m : ℝ) :
    TestFunctionℂ →L[ℝ] Lp ℂ 2 (volume : Measure SpaceTime) :=
  let _ := _m
  { toLinearMap :=
      { toFun := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure SpaceTime)
        map_add' := fun x y => map_add _ x y
        map_smul' := fun c x => by
          change SchwartzMap.toLpCLM ℂ ℂ 2 volume (c • x) =
            c • SchwartzMap.toLpCLM ℂ ℂ 2 volume x
          have hcx : c • x = (c : ℂ) • x := schwartz_real_smul_eq_complex c x
          have hmap : SchwartzMap.toLpCLM ℂ ℂ 2 volume ((c : ℂ) • x) =
              (c : ℂ) • SchwartzMap.toLpCLM ℂ ℂ 2 volume x :=
            ContinuousLinearMap.map_smul _ _ _
          rw [hcx, hmap, ← lp_real_smul_eq_complex] }
    cont := (SchwartzMap.toLpCLM ℂ ℂ 2 volume).continuous }

/-! ## The Embedding Map -/

/-- The embedding T maps a test function to a weighted function in momentum space.
    Conceptually: T f = FourierTransform(f) * (‖k‖² + m²)^(-1/2).
-/
noncomputable def sqrtPropagatorMap (m : ℝ) (f : TestFunction) : SpaceTime → ℂ :=
  fun k =>
    (SchwartzMap.fourierTransformCLM ℂ (toComplex f)) k
      * momentumWeightSqrtMathlib m k

/-- The sqrtPropagatorMap is square-integrable. -/
lemma sqrtPropagatorMap_sq_integrable (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
    Integrable (fun k => ‖sqrtPropagatorMap m f k‖ ^ 2) volume := by
  classical
  set F := SchwartzMap.fourierTransformCLM ℂ (toComplex f)
  have hF_sq : Integrable (fun k => ‖F k‖ ^ 2) volume :=
    schwartz_L2_integrable F
  have hF_meas : AEStronglyMeasurable F volume := (F.memLp 2 volume).1
  have h_weight_meas : AEStronglyMeasurable (momentumWeightSqrtMathlib m) volume :=
    (momentumWeightSqrt_mathlib_measurable (m := m)).aestronglyMeasurable
  have h_map_meas : AEStronglyMeasurable (sqrtPropagatorMap m f) volume := by
    have h_weight_C : AEStronglyMeasurable (fun k => (momentumWeightSqrtMathlib m k : ℂ)) volume :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable h_weight_meas
    have : AEStronglyMeasurable (fun k => F k * (momentumWeightSqrtMathlib m k : ℂ)) volume :=
      hF_meas.mul h_weight_C
    refine AEStronglyMeasurable.congr this ?_
    filter_upwards with k
    unfold sqrtPropagatorMap
    rfl
  have h_sq_meas : AEStronglyMeasurable (fun k => ‖sqrtPropagatorMap m f k‖ ^ 2) volume :=
    (Continuous.comp_aestronglyMeasurable (by fun_prop) h_map_meas).pow 2
  have h_dom_integrable : Integrable (fun k => (1 / m) ^ 2 * ‖F k‖ ^ 2) volume := by
    have := Integrable.const_mul hF_sq ((1 / m) ^ 2)
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc]
      using this
  have h_dom_pointwise : ∀ᵐ k ∂volume,
      ‖‖sqrtPropagatorMap m f k‖ ^ 2‖ ≤ ‖(1 / m) ^ 2 * ‖F k‖ ^ 2‖ := by
    have hmpos : 0 < m := Fact.out
    refine Filter.Eventually.of_forall ?_
    intro k
    have h_weight_le : (momentumWeightSqrtMathlib m k) ^ 2 ≤ (1 / m) ^ 2 := by
      have h_le := momentumWeightSqrt_mathlib_le_inv_mass (m := m) (k := k)
      have h_pos : 0 ≤ momentumWeightSqrtMathlib m k := (momentumWeightSqrt_mathlib_pos (m := m)
        k).le
      gcongr
    have h_nonneg_dom : 0 ≤ (1 / m) ^ 2 * ‖F k‖ ^ 2 := by positivity
    calc ‖‖sqrtPropagatorMap m f k‖ ^ 2‖
        = ‖sqrtPropagatorMap m f k‖ ^ 2 := by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
      _ = ‖F k * (momentumWeightSqrtMathlib m k : ℂ)‖ ^ 2 := by
          unfold sqrtPropagatorMap; rfl
      _ = (‖F k‖ * ‖(momentumWeightSqrtMathlib m k : ℂ)‖) ^ 2 := by
          rw [norm_mul]
      _ = (‖F k‖ * (momentumWeightSqrtMathlib m k)) ^ 2 := by
          congr 1
          rw [Complex.norm_real, Real.norm_of_nonneg (momentumWeightSqrt_mathlib_pos (m := m) k).le]
      _ = ‖F k‖ ^ 2 * (momentumWeightSqrtMathlib m k) ^ 2 := by
          rw [mul_pow]
      _ ≤ ‖F k‖ ^ 2 * (1 / m) ^ 2 := by
          gcongr
      _ = (1 / m) ^ 2 * ‖F k‖ ^ 2 := by ring
      _ = ‖(1 / m) ^ 2 * ‖F k‖ ^ 2‖ := by
          rw [Real.norm_of_nonneg h_nonneg_dom]
  exact h_dom_integrable.mono h_sq_meas h_dom_pointwise

/-- The weighted Fourier representative lies in L². -/
lemma sqrtPropagatorMap_memLp (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
    MemLp (sqrtPropagatorMap m f) 2 volume := by
  classical
  set F := SchwartzMap.fourierTransformCLM ℂ (toComplex f)
  have hF_meas : AEStronglyMeasurable F volume := (F.memLp 2 volume).1
  have h_weight_meas : AEStronglyMeasurable (momentumWeightSqrtMathlib m) volume :=
    (momentumWeightSqrt_mathlib_measurable (m := m)).aestronglyMeasurable
  have h_weight_C : AEStronglyMeasurable (fun k => (momentumWeightSqrtMathlib m k : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable h_weight_meas
  have h_meas_mul : AEStronglyMeasurable (fun k => F k * (momentumWeightSqrtMathlib m k : ℂ))
    volume :=
    hF_meas.mul h_weight_C
  have h_meas : AEStronglyMeasurable (sqrtPropagatorMap m f) volume :=
    h_meas_mul.congr <| Filter.Eventually.of_forall fun k => by
      unfold sqrtPropagatorMap
      rfl
  have h_sq := sqrtPropagatorMap_sq_integrable (m := m) (f := f)
  exact (memLp_two_iff_integrable_sq_norm h_meas).2 h_sq

/-- The squared L² norm of the mapped function. -/
noncomputable def sqrtPropagatorMapNormSq (m : ℝ) (f : TestFunction) : ℝ :=
  ∫ k, ‖sqrtPropagatorMap m f k‖ ^ 2 ∂volume

/-- The map is linear in f (additive). -/
lemma sqrtPropagatorMap_linear_add (m : ℝ) [Fact (0 < m)] (f g : TestFunction) :
    sqrtPropagatorMap m (f + g) = sqrtPropagatorMap m f + sqrtPropagatorMap m g := by
  ext k
  unfold sqrtPropagatorMap
  have hadd : toComplex (f + g) = toComplex f + toComplex g := toComplex_add f g
  have hmap : SchwartzMap.fourierTransformCLM ℂ (toComplex f + toComplex g) =
      SchwartzMap.fourierTransformCLM ℂ (toComplex f) +
        SchwartzMap.fourierTransformCLM ℂ (toComplex g) :=
    map_add _ _ _
  simp only [hadd, hmap, _root_.add_apply, Pi.add_apply, add_mul]

/-- The map is ℝ-linear (scalar multiplication). -/
lemma sqrtPropagatorMap_linear_smul (m : ℝ) [Fact (0 < m)] (c : ℝ) (f : TestFunction) :
    sqrtPropagatorMap m (c • f) = c • sqrtPropagatorMap m f := by
  ext k
  unfold sqrtPropagatorMap
  have hsmul : toComplex (c • f) = (c : ℂ) • toComplex f := toComplex_smul c f
  have hmap : SchwartzMap.fourierTransformCLM ℂ ((c : ℂ) • toComplex f) =
      (c : ℂ) • SchwartzMap.fourierTransformCLM ℂ (toComplex f) :=
    ContinuousLinearMap.map_smul _ _ _
  simp only [hsmul, hmap, _root_.smul_apply, smul_eq_mul, Pi.smul_apply, Complex.real_smul]
  ring

/-! ## Connection to Covariance -/

/-- For real test functions, the star (conjugation) of toComplex is the identity. -/
lemma toComplex_star (f : TestFunction) (x : SpaceTime) :
    starRingEnd ℂ (toComplex f x) = toComplex f x := by
  simp [toComplex_apply]

/-- For real test functions, freeCovarianceℂ agrees with freeCovarianceℂBilinear. -/
lemma freeCovarianceℂ_eq_bilinear_on_reals (m : ℝ) (f g : TestFunction) :
    freeCovarianceℂ m (toComplex f) (toComplex g)
      = freeCovarianceℂBilinear m (toComplex f) (toComplex g) := by
  unfold freeCovarianceℂ freeCovarianceℂBilinear
  congr 1 with x
  congr 1 with y
  rw [toComplex_star]

/-- Key lemma: The squared norm equals the covariance form. -/
lemma sqrtPropagatorMap_norm_eq_covariance (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
    sqrtPropagatorMapNormSq m f = freeCovarianceFormR m f f := by
  classical
  set F := SchwartzMap.fourierTransformCLM ℂ (toComplex f)
  -- The squared norm of sqrtPropagatorMap equals |F|² * weight_mathlib
  have h_ae :
      (fun k => ‖sqrtPropagatorMap m f k‖ ^ 2)
        =ᵐ[volume] fun k => ‖F k‖ ^ 2 * momentumWeightMathlib m k := by
    refine Filter.Eventually.of_forall ?_
    intro k
    have h_nonneg : 0 ≤ momentumWeightSqrtMathlib m k := (momentumWeightSqrt_mathlib_pos (m := m)
      k).le
    have h_abs : ‖(momentumWeightSqrtMathlib m k : ℂ)‖ = momentumWeightSqrtMathlib m k := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h_nonneg]
    have h_norm : ‖sqrtPropagatorMap m f k‖ = ‖F k‖ * momentumWeightSqrtMathlib m k := by
      calc
        ‖sqrtPropagatorMap m f k‖ = ‖F k * momentumWeightSqrtMathlib m k‖ := rfl
        _ = ‖F k‖ * ‖(momentumWeightSqrtMathlib m k : ℂ)‖ := by simp
        _ = ‖F k‖ * momentumWeightSqrtMathlib m k := by
          have h := congrArg (fun t : ℝ => ‖F k‖ * t) h_abs
          simpa using h
    have h_sq : ‖sqrtPropagatorMap m f k‖ ^ 2
        = ‖F k‖ ^ 2 * (momentumWeightSqrtMathlib m k) ^ 2 := by
      simp [pow_two, h_norm, mul_comm, mul_left_comm, mul_assoc]
    have h_sq_goal : ‖sqrtPropagatorMap m f k‖ ^ 2
        = ‖F k‖ ^ 2 * momentumWeightMathlib m k := by
      simpa [F, momentumWeightSqrt_mathlib_sq] using h_sq
    exact h_sq_goal
  have h_norm_int :
      sqrtPropagatorMapNormSq m f
        = ∫ k, ‖F k‖ ^ 2 * momentumWeightMathlib m k ∂volume := by
    simpa [sqrtPropagatorMapNormSq]
      using MeasureTheory.integral_congr_ae h_ae
  -- momentumWeightMathlib = freePropagatorMomentumMathlib by definition
  have h_integral_eq :
      ∫ k, ‖F k‖ ^ 2 * momentumWeightMathlib m k ∂volume
        = (freeCovarianceℂ m (toComplex f) (toComplex f)).re := by
    -- momentumWeightMathlib = freePropagatorMomentumMathlib
    have h_eq : ∀ k, momentumWeightMathlib m k = freePropagatorMomentumMathlib m k := fun _ => rfl
    simp_rw [h_eq]
    exact (parseval_covariance_schwartz_bessel (m := m) (f := toComplex f)).symm
  have h_real_cov :
      (freeCovarianceℂ m (toComplex f) (toComplex f)).re = freeCovarianceFormR m f f := by
    have h_complex :
        freeCovarianceℂ m (toComplex f) (toComplex f)
          = (freeCovarianceFormR m f f : ℂ) := by
      calc
        freeCovarianceℂ m (toComplex f) (toComplex f)
            = freeCovarianceℂBilinear m (toComplex f) (toComplex f) :=
                freeCovarianceℂ_eq_bilinear_on_reals m f f
        _ = (freeCovarianceFormR m f f : ℂ) :=
                freeCovarianceℂ_bilinear_agrees_on_reals m f f
    have := congrArg (fun z : ℂ => z.re) h_complex
    simpa using this
  calc
    sqrtPropagatorMapNormSq m f
        = ∫ k, ‖F k‖ ^ 2 * momentumWeightMathlib m k ∂volume := h_norm_int
    _ = (freeCovarianceℂ m (toComplex f) (toComplex f)).re := h_integral_eq
    _ = freeCovarianceFormR m f f := h_real_cov

/-! ## The Proof of sqrtPropagatorEmbedding -/

/-- The target Hilbert space: L²(SpaceTime, Lebesgue) with complex values. -/
abbrev TargetHilbertSpace (_m : ℝ) : Type :=
  let _ := _m
  Lp (E := ℂ) 2 (volume : Measure SpaceTime)

/-- The linear map T: TestFunction → L². -/
noncomputable def embeddingMap (m : ℝ) [Fact (0 < m)] :
    TestFunction →ₗ[ℝ] TargetHilbertSpace m :=
  { toFun := fun f =>
      (sqrtPropagatorMap_memLp (m := m) (f := f)).toLp (sqrtPropagatorMap m f)
    map_add' := by
      intro f g
      have hf := sqrtPropagatorMap_memLp (m := m) (f := f)
      have hg := sqrtPropagatorMap_memLp (m := m) (f := g)
      have hfg := sqrtPropagatorMap_memLp (m := m) (f := f + g)
      have h_linear : sqrtPropagatorMap m (f + g) =ᵐ[volume] sqrtPropagatorMap m f +
        sqrtPropagatorMap m g := by
        filter_upwards with k
        exact sqrtPropagatorMap_linear_add m f g ▸ rfl
      rw [← MeasureTheory.MemLp.toLp_add hf hg]
      exact MeasureTheory.MemLp.toLp_congr hfg (hf.add hg) h_linear
    map_smul' := by
      intro c f
      have hf := sqrtPropagatorMap_memLp (m := m) (f := f)
      have hcf := sqrtPropagatorMap_memLp (m := m) (f := c • f)
      have h_linear : sqrtPropagatorMap m (c • f) =ᵐ[volume] c • sqrtPropagatorMap m f := by
        filter_upwards with k
        exact sqrtPropagatorMap_linear_smul m c f ▸ rfl
      have : hcf.toLp (sqrtPropagatorMap m (c • f)) = (hf.const_smul c).toLp (c • sqrtPropagatorMap
        m f) :=
        MeasureTheory.MemLp.toLp_congr hcf (hf.const_smul c) h_linear
      rw [this]
      exact MeasureTheory.MemLp.toLp_const_smul c hf }

/-- Squared L² norm of the embedded function in terms of the pointwise integral. -/
lemma embeddingMap_norm_sq (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
    ‖embeddingMap m f‖ ^ 2 = ∫ (k : SpaceTime), ‖sqrtPropagatorMap m f k‖ ^ 2 ∂volume := by
  have h_memLp := sqrtPropagatorMap_memLp (m := m) (f := f)
  change ‖h_memLp.toLp (sqrtPropagatorMap m f)‖ ^ 2 = _
  have h_norm : ‖h_memLp.toLp (sqrtPropagatorMap m f)‖
      = ENNReal.toReal (eLpNorm (sqrtPropagatorMap m f) 2 volume) :=
    MeasureTheory.Lp.norm_toLp (sqrtPropagatorMap m f) h_memLp
  rw [h_norm]
  have h_integrable := sqrtPropagatorMap_sq_integrable (m := m) (f := f)
  have h_two_ne : (2 : NNReal) ≠ 0 := by norm_num
  calc
    (ENNReal.toReal (eLpNorm (sqrtPropagatorMap m f) 2 volume)) ^ 2
        = ENNReal.toReal ((eLpNorm (sqrtPropagatorMap m f) 2 volume) ^ 2) := by
            symm; exact ENNReal.toReal_pow _ 2
    _ = ENNReal.toReal (∫⁻ k, (‖sqrtPropagatorMap m f k‖₊ : ENNReal) ^ 2) := by
            congr 1
            have h_eq := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
              (f := sqrtPropagatorMap m f) (p := 2) (μ := volume) h_two_ne
            simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at h_eq
            have h_pow_cast : (eLpNorm (sqrtPropagatorMap m f) 2 volume) ^ (2 : ℕ)
                = (eLpNorm (sqrtPropagatorMap m f) 2 volume) ^ (2 : ℝ) := by
              simp [pow_two]
            calc (eLpNorm (sqrtPropagatorMap m f) 2 volume) ^ (2 : ℕ)
                = (eLpNorm (sqrtPropagatorMap m f) 2 volume) ^ (2 : ℝ) := h_pow_cast
              _ = ∫⁻ (x : SpaceTime), ‖sqrtPropagatorMap m f x‖ₑ ^ 2 := h_eq
              _ = ∫⁻ (k : SpaceTime), (‖sqrtPropagatorMap m f k‖₊ : ENNReal) ^ 2 := by
                refine lintegral_congr_ae ?_
                filter_upwards with k
                simp only [enorm]
                norm_cast
    _ = ∫ k, ‖sqrtPropagatorMap m f k‖ ^ 2 := by
            have h_ae_meas := h_integrable.aestronglyMeasurable
            have h_nonneg : ∀ᵐ k ∂volume, 0 ≤ ‖sqrtPropagatorMap m f k‖ ^ 2 :=
              Filter.Eventually.of_forall fun k => sq_nonneg _
            rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae h_nonneg h_ae_meas]
            congr 1
            refine lintegral_congr_ae ?_
            filter_upwards with k
            rw [ENNReal.ofReal_pow (norm_nonneg _)]
            simp only [pow_two]
            conv_rhs => arg 1; rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
            conv_rhs => arg 2; rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

/-- ℝ-linear view of the Lp multiplication CLM (avoiding `restrictScalars`). -/
private noncomputable def momentumWeightSqrt_mathlib_mul_CLM_real (m : ℝ) [Fact (0 < m)] :
    Lp ℂ 2 (volume : Measure SpaceTime) →L[ℝ]
      Lp ℂ 2 (volume : Measure SpaceTime) where
  toLinearMap :=
    { toFun := momentumWeightSqrtMathlibMulCLM m
      map_add' := fun x y => map_add _ x y
      map_smul' := fun c x => by
        change momentumWeightSqrtMathlibMulCLM m (c • x)
            = c • momentumWeightSqrtMathlibMulCLM m x
        have hcx : c • x = (c : ℂ) • x := lp_real_smul_eq_complex c x
        have hmap : momentumWeightSqrtMathlibMulCLM m ((c : ℂ) • x) =
            (c : ℂ) • momentumWeightSqrtMathlibMulCLM m x :=
          ContinuousLinearMap.map_smul _ _ _
        rw [hcx, hmap, ← lp_real_smul_eq_complex] }
  cont := (momentumWeightSqrtMathlibMulCLM m).continuous

/-- Continuous linear map obtained by composing the proven building blocks. -/
noncomputable def embeddingMapCLM (m : ℝ) [Fact (0 < m)] :
    TestFunction →L[ℝ] Lp ℂ 2 (volume : Measure SpaceTime) :=
  ((momentumWeightSqrt_mathlib_mul_CLM_real m).comp (schwartzToL2CLMReal m)).comp
    ((fourierTransformCLMReal).comp toComplexCLM)

lemma embeddingMapCLM_apply (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
    embeddingMapCLM m f = embeddingMap m f := by
  classical
  set g := SchwartzMap.fourierTransformCLM ℂ (toComplex f) with hg
  set A := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure SpaceTime)) g with hA
  have h_eval : embeddingMapCLM m f = (momentumWeightSqrtMathlibMulCLM m) A := rfl
  have h_mul := momentumWeightSqrt_mathlib_mul_CLM_spec (m := m) A
  have h_mul' : embeddingMapCLM m f =ᵐ[volume]
      fun k => (momentumWeightSqrtMathlib m k : ℂ) * A k := by
    simpa [h_eval]
  have h_A : (fun k => A k) =ᵐ[volume] fun k => g k := by
    filter_upwards [g.coeFn_toLp 2 (volume : Measure SpaceTime)] with k hk
    simpa [A, g, hA, hg] using hk
  have h_weight : (fun k => (momentumWeightSqrtMathlib m k : ℂ) * A k)
      =ᵐ[volume] fun k => (momentumWeightSqrtMathlib m k : ℂ) * g k := by
    refine h_A.mono ?_
    intro k hk
    simp [hk]
  have h_mul'' : embeddingMapCLM m f =ᵐ[volume]
      fun k => (momentumWeightSqrtMathlib m k : ℂ) * g k :=
    h_mul'.trans h_weight
  have h_sqrt : (fun k => (momentumWeightSqrtMathlib m k : ℂ) * g k)
      =ᵐ[volume] sqrtPropagatorMap m f := by
    refine Filter.Eventually.of_forall ?_
    intro k
    simp [sqrtPropagatorMap, g, mul_comm]
  have h_mem := sqrtPropagatorMap_memLp (m := m) (f := f)
  have h_lp : embeddingMap m f =ᵐ[volume] sqrtPropagatorMap m f := by
    simpa [embeddingMap] using h_mem.coeFn_toLp
  have h_ae : embeddingMapCLM m f =ᵐ[volume] embeddingMap m f :=
    (h_mul''.trans h_sqrt).trans h_lp.symm
  exact Lp.ext_iff.mpr h_ae

/-- Existence of a linear embedding realizing the free covariance as a squared norm.
    The target space H is an inner product space (L² is a Hilbert space).
    Note: InnerProductSpace ℝ H implies NormedSpace ℝ H via InnerProductSpace.toNormedSpace.
-/
theorem sqrtPropagatorEmbedding (m : ℝ) [Fact (0 < m)] :
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
    (T : TestFunction →ₗ[ℝ] H),
    ∀ f : TestFunction, freeCovarianceFormR m f f = ‖T f‖^2 := by
  refine ⟨TargetHilbertSpace m, inferInstance, inferInstance, embeddingMap m, ?_⟩
  intro f
  rw [← sqrtPropagatorMap_norm_eq_covariance]
  unfold sqrtPropagatorMapNormSq
  exact (embeddingMap_norm_sq (m := m) (f := f)).symm

/-! ## Auxiliary Lemmas for Continuity -/

lemma freeCovarianceFormR_eq_normSq (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
    freeCovarianceFormR m f f = ‖embeddingMap m f‖ ^ 2 := by
  have h_cov := sqrtPropagatorMap_norm_eq_covariance (m := m) (f := f)
  have h_norm := embeddingMap_norm_sq (m := m) (f := f)
  simpa [sqrtPropagatorMapNormSq, h_norm] using h_cov.symm

/-- The embedding map TestFunction → L² is continuous. -/
lemma embeddingMap_continuous (m : ℝ) [Fact (0 < m)] :
    Continuous (embeddingMap m) := by
  classical
  have h := (embeddingMapCLM (m := m)).continuous
  have h_fun_eq : (fun f => embeddingMapCLM m f)
      = (fun f => embeddingMap m f) := by
    funext f
    simp [embeddingMapCLM_apply]
  exact (continuous_congr (congrFun h_fun_eq)).mp h

/-- Continuity of the real covariance quadratic form f ↦ C(f,f). -/
theorem freeCovarianceFormR_continuous (m : ℝ) [Fact (0 < m)] :
    Continuous (fun f : TestFunction => freeCovarianceFormR m f f) := by
  have h_eq : (fun f => freeCovarianceFormR m f f) = (fun f => ‖embeddingMap m f‖ ^ 2) := by
    ext f
    exact freeCovarianceFormR_eq_normSq (m := m) (f := f)
  rw [h_eq]
  have h_cont_map : Continuous (embeddingMap m) := embeddingMap_continuous (m := m)
  have h_cont_norm : Continuous (fun f => ‖embeddingMap m f‖) := Continuous.norm h_cont_map
  exact Continuous.pow h_cont_norm 2

/-! ## Positivity and Other Properties -/

/-- Positivity of the real covariance quadratic form. -/
theorem freeCovarianceFormR_pos (m : ℝ) [Fact (0 < m)] :
    ∀ f : TestFunction, 0 ≤ freeCovarianceFormR m f f := by
  intro f
  have h1 : freeCovarianceℂBilinear m (toComplex f) (toComplex f) = (freeCovarianceFormR m f f :
    ℂ) :=
    freeCovarianceℂ_bilinear_agrees_on_reals m f f
  have h2 : freeCovarianceℂ m (toComplex f) (toComplex f)
              = freeCovarianceℂBilinear m (toComplex f) (toComplex f) :=
    freeCovarianceℂ_eq_bilinear_on_reals m f f
  have h3 : 0 ≤ (freeCovarianceℂ m (toComplex f) (toComplex f)).re :=
    freeCovarianceℂ_positive m (toComplex f)
  rw [h2, h1] at h3
  simpa using h3

/-- Symmetry of the real covariance bilinear form. -/
theorem freeCovarianceFormR_symm (m : ℝ) [Fact (0 < m)] (f g : TestFunction) :
    freeCovarianceFormR m f g = freeCovarianceFormR m g f := by
  apply Complex.ofReal_injective
  calc (freeCovarianceFormR m f g : ℂ)
      = freeCovarianceℂBilinear m (toComplex f) (toComplex g) := by
          rw [← freeCovarianceℂ_bilinear_agrees_on_reals m f g]
    _ = freeCovarianceℂBilinear m (toComplex g) (toComplex f) := by
          rw [freeCovarianceℂ_bilinear_symm m (toComplex f) (toComplex g)]
    _ = (freeCovarianceFormR m g f : ℂ) := by
          rw [freeCovarianceℂ_bilinear_agrees_on_reals m g f]

/-- Linearity in the first argument of the real covariance bilinear form. -/
lemma freeCovarianceFormR_add_left (m : ℝ) [Fact (0 < m)] (f₁ f₂ g : TestFunction) :
    freeCovarianceFormR m (f₁ + f₂) g = freeCovarianceFormR m f₁ g + freeCovarianceFormR m f₂ g :=
      by
  apply Complex.ofReal_injective
  have h :=
    freeCovarianceℂ_bilinear_add_left m (toComplex f₁) (toComplex f₂) (toComplex g)
  have hL :
      (freeCovarianceFormR m (f₁ + f₂) g : ℂ)
        = freeCovarianceℂBilinear m (toComplex f₁ + toComplex f₂) (toComplex g) := by
    simpa [toComplex_add]
      using (freeCovarianceℂ_bilinear_agrees_on_reals m (f₁ + f₂) g).symm
  have h' :
      (freeCovarianceFormR m (f₁ + f₂) g : ℂ)
        = (freeCovarianceFormR m f₁ g : ℂ) + (freeCovarianceFormR m f₂ g : ℂ) := by
    calc
      (freeCovarianceFormR m (f₁ + f₂) g : ℂ)
          = freeCovarianceℂBilinear m (toComplex f₁ + toComplex f₂) (toComplex g) := hL
      _ = freeCovarianceℂBilinear m (toComplex f₁) (toComplex g)
            + freeCovarianceℂBilinear m (toComplex f₂) (toComplex g) := h
      _ = (freeCovarianceFormR m f₁ g : ℂ) + (freeCovarianceFormR m f₂ g : ℂ) := by
            rw [freeCovarianceℂ_bilinear_agrees_on_reals m f₁ g,
                freeCovarianceℂ_bilinear_agrees_on_reals m f₂ g]
  simpa [Complex.ofReal_add] using h'

/-- Scalar multiplication in the first argument of the real covariance bilinear form. -/
lemma freeCovarianceFormR_smul_left (m : ℝ) [Fact (0 < m)] (c : ℝ) (f g : TestFunction) :
    freeCovarianceFormR m (c • f) g = c * freeCovarianceFormR m f g := by
  apply Complex.ofReal_injective
  have h :=
    freeCovarianceℂ_bilinear_smul_left m (c : ℂ) (toComplex f) (toComplex g)
  have hL :
      (freeCovarianceFormR m (c • f) g : ℂ)
        = freeCovarianceℂBilinear m ((c : ℂ) • toComplex f) (toComplex g) := by
    simpa [toComplex_apply]
      using (freeCovarianceℂ_bilinear_agrees_on_reals m (c • f) g).symm
  have hR :
      (freeCovarianceFormR m f g : ℂ)
        = freeCovarianceℂBilinear m (toComplex f) (toComplex g) :=
    (freeCovarianceℂ_bilinear_agrees_on_reals m f g).symm
  have h' :
      (freeCovarianceFormR m (c • f) g : ℂ)
        = (c : ℂ) * (freeCovarianceFormR m f g : ℂ) := by
    calc
      (freeCovarianceFormR m (c • f) g : ℂ)
          = freeCovarianceℂBilinear m ((c : ℂ) • toComplex f) (toComplex g) := hL
      _ = (c : ℂ) * freeCovarianceℂBilinear m (toComplex f) (toComplex g) := h
      _ = (c : ℂ) * (freeCovarianceFormR m f g : ℂ) := by
            rw [hR]
  simpa [Complex.ofReal_mul] using h'

/-- Addition in the second argument of the real covariance bilinear form. -/
lemma freeCovarianceFormR_add_right (m : ℝ) [Fact (0 < m)] (f g₁ g₂ : TestFunction) :
    freeCovarianceFormR m f (g₁ + g₂) = freeCovarianceFormR m f g₁ + freeCovarianceFormR m f g₂ :=
      by
  apply Complex.ofReal_injective
  have h :=
    freeCovarianceℂ_bilinear_add_right m (toComplex f) (toComplex g₁) (toComplex g₂)
  have hL :
      (freeCovarianceFormR m f (g₁ + g₂) : ℂ)
        = freeCovarianceℂBilinear m (toComplex f) (toComplex g₁ + toComplex g₂) := by
    simpa [toComplex_add]
      using (freeCovarianceℂ_bilinear_agrees_on_reals m f (g₁ + g₂)).symm
  have h' :
      (freeCovarianceFormR m f (g₁ + g₂) : ℂ)
        = (freeCovarianceFormR m f g₁ : ℂ) + (freeCovarianceFormR m f g₂ : ℂ) := by
    calc
      (freeCovarianceFormR m f (g₁ + g₂) : ℂ)
          = freeCovarianceℂBilinear m (toComplex f) (toComplex g₁ + toComplex g₂) := hL
      _ = freeCovarianceℂBilinear m (toComplex f) (toComplex g₁)
            + freeCovarianceℂBilinear m (toComplex f) (toComplex g₂) := h
      _ = (freeCovarianceFormR m f g₁ : ℂ) + (freeCovarianceFormR m f g₂ : ℂ) := by
            rw [freeCovarianceℂ_bilinear_agrees_on_reals m f g₁,
                freeCovarianceℂ_bilinear_agrees_on_reals m f g₂]
  simpa [Complex.ofReal_add] using h'

/-- Scalar multiplication in the second argument of the real covariance bilinear form. -/
lemma freeCovarianceFormR_smul_right (m : ℝ) [Fact (0 < m)] (c : ℝ) (f g : TestFunction) :
    freeCovarianceFormR m f (c • g) = c * freeCovarianceFormR m f g := by
  apply Complex.ofReal_injective
  have h :=
    freeCovarianceℂ_bilinear_smul_right m (c : ℂ) (toComplex f) (toComplex g)
  have hL :
    (freeCovarianceFormR m f (c • g) : ℂ)
        = freeCovarianceℂBilinear m (toComplex f) ((c : ℂ) • toComplex g) := by
    simpa [toComplex_apply]
      using (freeCovarianceℂ_bilinear_agrees_on_reals m f (c • g)).symm
  have hR :
      (freeCovarianceFormR m f g : ℂ)
        = freeCovarianceℂBilinear m (toComplex f) (toComplex g) :=
    (freeCovarianceℂ_bilinear_agrees_on_reals m f g).symm
  have h' :
      (freeCovarianceFormR m f (c • g) : ℂ)
        = (c : ℂ) * (freeCovarianceFormR m f g : ℂ) := by
    calc
      (freeCovarianceFormR m f (c • g) : ℂ)
          = freeCovarianceℂBilinear m (toComplex f) ((c : ℂ) • toComplex g) := hL
      _ = (c : ℂ) * freeCovarianceℂBilinear m (toComplex f) (toComplex g) := h
      _ = (c : ℂ) * (freeCovarianceFormR m f g : ℂ) := by
            rw [hR]
  simpa [Complex.ofReal_mul] using h'

/-- Zero in the first argument gives zero. -/
lemma freeCovarianceFormR_zero_left (m : ℝ) [Fact (0 < m)] (g : TestFunction) :
    freeCovarianceFormR m 0 g = 0 := by
  have h := freeCovarianceFormR_smul_left m (0 : ℝ) 0 g
  simp only [zero_smul] at h
  rw [h]
  simp only [zero_mul]

/-- Zero in the second argument gives zero. -/
lemma freeCovarianceFormR_zero_right (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
    freeCovarianceFormR m f 0 = 0 := by
  rw [freeCovarianceFormR_symm]
  exact freeCovarianceFormR_zero_left m f

lemma freeCovarianceFormR_reflection_invariant
    (m : ℝ) [Fact (0 < m)] (f g : TestFunction) :
    freeCovarianceFormR m (QFT.compTimeReflectionReal f)
      (QFT.compTimeReflectionReal g) = freeCovarianceFormR m f g := by
  classical
  set fc : TestFunctionℂ := toComplex f
  set gc : TestFunctionℂ := toComplex g
  have h_comp_invol (h : TestFunctionℂ) :
      QFT.compTimeReflection (QFT.compTimeReflection h) = h := by
    ext x
    simp only [QFT.compTimeReflection, SchwartzMap.compCLM_apply, Function.comp_apply]
    congr 1
    exact QFT.timeReflectionLE.right_inv x
  have h_toComplex_comp (h : TestFunction) :
      toComplex (QFT.compTimeReflectionReal h)
        = QFT.compTimeReflection (toComplex h) := by
    ext x
    simp [toComplex_apply, QFT.compTimeReflectionReal, QFT.compTimeReflection,
      QFT.timeReflectionCLM]
  have h_integrable :
      Integrable
        (fun p : SpaceTime × SpaceTime =>
          (QFT.compTimeReflection fc) p.1
            * (freeCovariance m p.1 p.2 : ℂ)
            * (QFT.compTimeReflection gc) p.2)
        (volume.prod volume) :=
    freeCovarianceℂ_bilinear_integrable (m := m)
      (f := QFT.compTimeReflection fc) (g := QFT.compTimeReflection gc)
  have h_double :=
    double_integral_timeReflection_covariance (m := m)
      (f := fc) (g := QFT.compTimeReflection gc) h_integrable
  have h_complex :
      freeCovarianceℂBilinear m (QFT.compTimeReflection fc) (QFT.compTimeReflection gc)
        = freeCovarianceℂBilinear m fc gc := by
    have h_double' := h_double
    simp_rw [covariance_timeReflection_invariant m] at h_double'
    have h_double'' :
        ∫ x, ∫ y,
            (QFT.compTimeReflection fc) x * (freeCovariance m x y : ℂ)
              * (QFT.compTimeReflection gc) y ∂volume ∂volume
          =
        ∫ x, ∫ y,
            fc x * (freeCovariance m x y : ℂ) * gc y ∂volume ∂volume := by
      calc
        ∫ x, ∫ y,
            (QFT.compTimeReflection fc) x * (freeCovariance m x y : ℂ)
              * (QFT.compTimeReflection gc) y ∂volume ∂volume
          = ∫ x, ∫ y,
              fc x * (freeCovariance m x y : ℂ)
                * (QFT.compTimeReflection (QFT.compTimeReflection gc)) y ∂volume ∂volume :=
                  h_double'
        _ = ∫ x, ∫ y,
                fc x * (freeCovariance m x y : ℂ) * gc y ∂volume ∂volume := by
              exact
                congrArg
                  (fun h : TestFunctionℂ =>
                    ∫ x, ∫ y,
                        fc x * (freeCovariance m x y : ℂ) * h y ∂volume ∂volume)
                  (h_comp_invol gc)
    unfold freeCovarianceℂBilinear
    exact h_double''
  have h₁ :
      freeCovarianceℂBilinear m (QFT.compTimeReflection fc) (QFT.compTimeReflection gc)
        = (freeCovarianceFormR m (QFT.compTimeReflectionReal f) (QFT.compTimeReflectionReal g) : ℂ)
          := by
    simpa [h_toComplex_comp f, h_toComplex_comp g, fc, gc]
      using (freeCovarianceℂ_bilinear_agrees_on_reals
        (m := m) (f := QFT.compTimeReflectionReal f) (g := QFT.compTimeReflectionReal g))
  have h₂ :
      freeCovarianceℂBilinear m fc gc
        = (freeCovarianceFormR m f g : ℂ) :=
    (freeCovarianceℂ_bilinear_agrees_on_reals (m := m) f g)
  have h_complex_eq :
      (freeCovarianceFormR m (QFT.compTimeReflectionReal f) (QFT.compTimeReflectionReal g) : ℂ)
        = (freeCovarianceFormR m f g : ℂ) := by
    calc
      (freeCovarianceFormR m (QFT.compTimeReflectionReal f) (QFT.compTimeReflectionReal g) : ℂ)
          = freeCovarianceℂBilinear m (QFT.compTimeReflection fc) (QFT.compTimeReflection gc) :=
            h₁.symm
      _ = freeCovarianceℂBilinear m fc gc := h_complex
      _ = (freeCovarianceFormR m f g : ℂ) := h₂
  exact ofReal_inj.mp h_complex_eq

/-- Mixed-time-reflection identity for the real free covariance. -/
lemma freeCovarianceFormR_reflection_cross
    (m : ℝ) [Fact (0 < m)] (f g : TestFunction) :
    freeCovarianceFormR m (QFT.compTimeReflectionReal f) g
      = freeCovarianceFormR m (QFT.compTimeReflectionReal g) f := by
  classical
  have h_invol_f :
      QFT.compTimeReflectionReal (QFT.compTimeReflectionReal f) = f := by
    ext x
    change
        (QFT.compTimeReflectionReal
            (QFT.compTimeReflectionReal f) : TestFunction) x = f x
    have h_time_aux := QFT.timeReflectionLE.right_inv x
    have h_time :
        QFT.timeReflectionLinear (QFT.timeReflectionLinear x) = x := by
      convert h_time_aux using 1
      rfl
    simp [QFT.compTimeReflectionReal, QFT.timeReflectionCLM,
      QFT.timeReflectionLinear, QFT.timeReflection]
  have h_invol_g :
      QFT.compTimeReflectionReal (QFT.compTimeReflectionReal g) = g := by
    ext x
    change
        (QFT.compTimeReflectionReal
            (QFT.compTimeReflectionReal g) : TestFunction) x = g x
    have h_time_aux := QFT.timeReflectionLE.right_inv x
    have h_time :
        QFT.timeReflectionLinear (QFT.timeReflectionLinear x) = x := by
      convert h_time_aux using 1
      rfl
    simp [QFT.compTimeReflectionReal, QFT.timeReflectionCLM,
      QFT.timeReflectionLinear, QFT.timeReflection]
  have h_step :
      freeCovarianceFormR m (QFT.compTimeReflectionReal f) g
        = freeCovarianceFormR m f (QFT.compTimeReflectionReal g) := by
    simpa [h_invol_g]
      using freeCovarianceFormR_reflection_invariant (m := m)
        (f := f) (g := QFT.compTimeReflectionReal g)
  calc
    freeCovarianceFormR m (QFT.compTimeReflectionReal f) g
        = freeCovarianceFormR m f (QFT.compTimeReflectionReal g) := h_step
    _ = freeCovarianceFormR m (QFT.compTimeReflectionReal g) f :=
        freeCovarianceFormR_symm m f (compTimeReflectionReal g)

/-- Left linearity of freeCovarianceFormR for any fixed right argument. -/
lemma freeCovarianceFormR_left_linear_any_right
    (m : ℝ) [Fact (0 < m)] {n : ℕ} (f : Fin n → PositiveTimeTestFunction) (c : Fin n → ℝ)
    (s : Finset (Fin n)) (g : TestFunction) :
    ∑ i ∈ s, c i * freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) g =
    freeCovarianceFormR m (∑ i ∈ s, c i • QFT.compTimeReflectionReal (f i).val) g := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    rw [← freeCovarianceFormR_zero_left (m := m)]
  | insert k t hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    have h_smul : c k * freeCovarianceFormR m (QFT.compTimeReflectionReal (f k).val) g =
      freeCovarianceFormR m (c k • QFT.compTimeReflectionReal (f k).val) g :=
      (freeCovarianceFormR_smul_left m (c k) (QFT.compTimeReflectionReal (f k).val) g).symm
    rw [h_smul, ih]
    rw [← freeCovarianceFormR_add_left]

end QFT

end
