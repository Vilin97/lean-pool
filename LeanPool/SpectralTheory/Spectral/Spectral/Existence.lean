/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import LeanPool.SpectralTheory.Spectral.Cayley.Inverse
public import LeanPool.SpectralTheory.Spectral.PVM.Unbounded
public import LeanPool.SpectralTheory.Spectral.Spectral.CayleyCalculus
public import LeanPool.SpectralTheory.Spectral.Spectral.Polarization
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.MetricSpace.HausdorffDistance


/-!
# Spectral theorem: existence

Starting from the continuous functional calculus of the Cayley transform, this file constructs
scalar Riesz measures, polarizes them into operator-valued projections, forms a real PVM by the
inverse Cayley coordinate, and proves that its unbounded coordinate integral is the original
self-adjoint operator.
-/

public section

open MeasureTheory
open CompactlySupported

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- View a compactly supported real continuous function as a complex continuous function. -/
def realToComplexContinuousMap {X : Type*} [TopologicalSpace X]
    (f : C_c(X, ℝ)) : C(X, ℂ) where
  toFun z := f z
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous

@[simp]
private theorem realToComplexContinuousMap_apply {X : Type*} [TopologicalSpace X]
    (f : C_c(X, ℝ)) (z : X) :
    realToComplexContinuousMap f z = (f z : ℂ) := rfl

@[simp]
private theorem realToComplexContinuousMap_add {X : Type*} [TopologicalSpace X]
    (f g : C_c(X, ℝ)) :
    realToComplexContinuousMap (f + g) =
      realToComplexContinuousMap f + realToComplexContinuousMap g := by
  ext z
  exact Complex.ofReal_add (f z) (g z)

@[simp]
private theorem realToComplexContinuousMap_smul {X : Type*} [TopologicalSpace X]
    (c : ℝ) (f : C_c(X, ℝ)) :
    realToComplexContinuousMap (c • f) =
      (c : ℂ) • realToComplexContinuousMap f := by
  ext z
  exact Complex.ofReal_mul c (f z)

private def compactlySupportedContinuousMap {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (f : C(X, ℝ)) : C_c(X, ℝ) where
  toFun := f
  hasCompactSupport' := HasCompactSupport.of_compactSpace f

/-- The real quadratic functional induced by continuous functional calculus at a vector. -/
noncomputable def normalCfcQuadraticLinearMap
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E) :
    C_c(spectrum ℂ U, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (@inner ℂ E _ x
    ((cfcHom hU) (realToComplexContinuousMap f) x)).re
  map_add' f g := by
    rw [realToComplexContinuousMap_add, map_add, add_apply,
      inner_add_right, Complex.add_re]
  map_smul' c f := by
    rw [realToComplexContinuousMap_smul, map_smul, smul_apply,
      inner_smul_right, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rfl

private noncomputable def realSqrtContinuousMap {X : Type*} [TopologicalSpace X]
    (f : C_c(X, ℝ)) : C(X, ℂ) where
  toFun z := Real.sqrt (f z)
  continuous_toFun := Complex.continuous_ofReal.comp
    (Real.continuous_sqrt.comp f.continuous)

private theorem realToComplexContinuousMap_eq_star_mul_self
    {X : Type*} [TopologicalSpace X] (f : C_c(X, ℝ)) (hf : 0 ≤ f) :
    realToComplexContinuousMap f =
      star (realSqrtContinuousMap f) * realSqrtContinuousMap f := by
  ext z
  change (f z : ℂ) = star (Real.sqrt (f z) : ℂ) * Real.sqrt (f z)
  rw [Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, Real.mul_self_sqrt (hf z)]

private theorem normalCfcQuadraticLinearMap_nonneg
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E)
    (f : C_c(spectrum ℂ U, ℝ)) (hf : 0 ≤ f) :
    0 ≤ normalCfcQuadraticLinearMap U hU x f := by
  let q := realSqrtContinuousMap f
  have hmap : (cfcHom hU) (realToComplexContinuousMap f) =
      star ((cfcHom hU) q) * (cfcHom hU) q := by
    rw [realToComplexContinuousMap_eq_star_mul_self f hf, map_mul, map_star]
  have hpos : (0 : E →L[ℂ] E) ≤
      star ((cfcHom hU) q) * (cfcHom hU) q :=
    star_mul_self_nonneg ((cfcHom hU) q)
  have hpositive : ContinuousLinearMap.IsPositive
      (star ((cfcHom hU) q) * (cfcHom hU) q) :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp hpos
  change 0 ≤ (@inner ℂ E _ x
    ((cfcHom hU) (realToComplexContinuousMap f) x)).re
  rw [hmap]
  exact hpositive.re_inner_nonneg_right x

/-- The positive real functional on the continuous functions on `spectrum ℂ U` obtained by
pairing the continuous functional calculus with a vector. -/
noncomputable def normalCfcQuadraticFunctional
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E) :
    C_c(spectrum ℂ U, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (normalCfcQuadraticLinearMap U hU x)
    (by exact normalCfcQuadraticLinearMap_nonneg U hU x)

/-- The Riesz measure representing the quadratic continuous-functional-calculus functional. -/
noncomputable def normalCfcScalarMeasure
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E) :
    Measure (spectrum ℂ U) :=
  RealRMK.rieszMeasure (normalCfcQuadraticFunctional U hU x)

noncomputable instance normalCfcScalarMeasure_isFiniteMeasure
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E) :
    IsFiniteMeasure (normalCfcScalarMeasure U hU x) := by
  unfold normalCfcScalarMeasure
  infer_instance

/-- Integration against the scalar Riesz measure recovers the corresponding CFC quadratic
functional. -/
theorem integral_normalCfcScalarMeasure
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E)
    (f : C_c(spectrum ℂ U, ℝ)) :
    ∫ z, f z ∂(normalCfcScalarMeasure U hU x) =
      (@inner ℂ E _ x ((cfcHom hU)
        (realToComplexContinuousMap f) x)).re := by
  exact RealRMK.integral_rieszMeasure
    (normalCfcQuadraticFunctional U hU x) f

private noncomputable def continuousMapRealPart {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (f : C(X, ℂ)) : C_c(X, ℝ) where
  toFun z := (f z).re
  continuous_toFun := Complex.continuous_re.comp f.continuous
  hasCompactSupport' := HasCompactSupport.of_compactSpace _

private noncomputable def continuousMapImagPart {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (f : C(X, ℂ)) : C_c(X, ℝ) where
  toFun z := (f z).im
  continuous_toFun := Complex.continuous_im.comp f.continuous
  hasCompactSupport' := HasCompactSupport.of_compactSpace _

private noncomputable def continuousMapOfRealPart {X : Type*} [TopologicalSpace X]
    (f : C(X, ℂ)) : C(X, ℂ) where
  toFun z := ((f z).re : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp f.continuous)

private noncomputable def continuousMapOfImagPart {X : Type*} [TopologicalSpace X]
    (f : C(X, ℂ)) : C(X, ℂ) where
  toFun z := ((f z).im : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (Complex.continuous_im.comp f.continuous)

private theorem cfc_inner_self_real_of_real_valued
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (f : C(spectrum ℂ U, ℂ)) (hreal : star f = f) (x : E) :
    ((@inner ℂ E _ x ((cfcHom hU) f x)).re : ℂ) =
      @inner ℂ E _ x ((cfcHom hU) f x) := by
  have hself : IsSelfAdjoint ((cfcHom hU) f) := by
    change star ((cfcHom hU) f) = (cfcHom hU) f
    rw [← map_star, hreal]
  exact hself.isSymmetric.coe_re_inner_self_apply x

/-- Complex continuous functions have the expected diagonal matrix coefficient against the
scalar Riesz measure. -/
theorem integral_normalCfcScalarMeasure_complex
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E)
    (f : C(spectrum ℂ U, ℂ)) :
    ∫ z, f z ∂(normalCfcScalarMeasure U hU x) =
      @inner ℂ E _ x ((cfcHom hU) f x) := by
  let fr : C_c(spectrum ℂ U, ℝ) := continuousMapRealPart f
  let fi : C_c(spectrum ℂ U, ℝ) := continuousMapImagPart f
  let fre : C(spectrum ℂ U, ℂ) := continuousMapOfRealPart f
  let fim : C(spectrum ℂ U, ℂ) := continuousMapOfImagPart f
  have hr := integral_normalCfcScalarMeasure U hU x fr
  have hi := integral_normalCfcScalarMeasure U hU x fi
  change (∫ z, (f z).re ∂(normalCfcScalarMeasure U hU x)) =
      (@inner ℂ E _ x ((cfcHom hU) fre x)).re at hr
  change (∫ z, (f z).im ∂(normalCfcScalarMeasure U hU x)) =
      (@inner ℂ E _ x ((cfcHom hU) fim x)).re at hi
  have hfre : star fre = fre := by
    ext z
    change star ((f z).re : ℂ) = ((f z).re : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal]
  have hfim : star fim = fim := by
    ext z
    change star ((f z).im : ℂ) = ((f z).im : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal]
  have hdecomp : f = fre + Complex.I • fim := by
    ext z
    change f z = ((f z).re : ℂ) + Complex.I * ((f z).im : ℂ)
    rw [mul_comm]
    exact (Complex.re_add_im (f z)).symm
  have hfint : Integrable f (normalCfcScalarMeasure U hU x) := by
    apply Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
    exact ae_of_all _ fun z => f.norm_coe_le_norm z
  rw [← integral_re_add_im hfint]
  change (((∫ z, (f z).re ∂(normalCfcScalarMeasure U hU x)) : ℝ) : ℂ) +
      (((∫ z, (f z).im ∂(normalCfcScalarMeasure U hU x)) : ℝ) : ℂ) *
        Complex.I = @inner ℂ E _ x ((cfcHom hU) f x)
  rw [hr, hi]
  rw [hdecomp, map_add, map_smul, add_apply, smul_apply,
    inner_add_right, inner_smul_right]
  rw [cfc_inner_self_real_of_real_valued U hU fre hfre x,
    cfc_inner_self_real_of_real_valued U hU fim hfim x]
  ring

private noncomputable def normalCfcRealOperator
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (f : C(spectrum ℂ U, ℝ)) : E →L[ℂ] E :=
  (cfcHom hU) (realToComplexContinuousMap (compactlySupportedContinuousMap f))

private theorem integral_normalCfcScalarMeasure_continuous
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E)
    (f : C(spectrum ℂ U, ℝ)) :
    ∫ z, f z ∂(normalCfcScalarMeasure U hU x) =
      (@inner ℂ E _ x (normalCfcRealOperator U hU f x)).re := by
  exact integral_normalCfcScalarMeasure U hU x (compactlySupportedContinuousMap f)

private theorem normalCfcRealOperator_isPositive
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (f : C(spectrum ℂ U, ℝ)) (hf : ∀ z, 0 ≤ f z) :
    ContinuousLinearMap.IsPositive (normalCfcRealOperator U hU f) := by
  let fs : C_c(spectrum ℂ U, ℝ) := compactlySupportedContinuousMap f
  let q := realSqrtContinuousMap fs
  have hfs : 0 ≤ fs := fun z => hf z
  have hmap : normalCfcRealOperator U hU f =
      star ((cfcHom hU) q) * (cfcHom hU) q := by
    unfold normalCfcRealOperator
    rw [realToComplexContinuousMap_eq_star_mul_self fs hfs, map_mul, map_star]
  rw [hmap]
  apply ContinuousLinearMap.nonneg_iff_isPositive.mp
  exact star_mul_self_nonneg ((cfcHom hU) q)

private theorem normalCfcRealOperator_le_one
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (f : C(spectrum ℂ U, ℝ)) (hf : ∀ z, f z ≤ 1) :
    normalCfcRealOperator U hU f ≤ 1 := by
  let g : C(spectrum ℂ U, ℝ) := 1 - f
  have hg : ∀ z, 0 ≤ g z := fun z => sub_nonneg.mpr (hf z)
  have hmap : realToComplexContinuousMap (compactlySupportedContinuousMap g) =
      1 - realToComplexContinuousMap (compactlySupportedContinuousMap f) := by
    ext z
    change ((1 - f z : ℝ) : ℂ) = 1 - (f z : ℂ)
    push_cast
    rfl
  have hop : normalCfcRealOperator U hU g = 1 - normalCfcRealOperator U hU f := by
    unfold normalCfcRealOperator
    rw [hmap, map_sub, map_one]
  rw [← sub_nonneg, ← hop]
  exact ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (normalCfcRealOperator_isPositive U hU g hg)

private theorem normalCfcRealOperator_mul
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (f g : C(spectrum ℂ U, ℝ)) :
    normalCfcRealOperator U hU f * normalCfcRealOperator U hU g =
      normalCfcRealOperator U hU (f * g) := by
  unfold normalCfcRealOperator
  rw [← map_mul]
  congr 1
  ext z
  change (f z : ℂ) * (g z : ℂ) = ((f z * g z : ℝ) : ℂ)
  exact (Complex.ofReal_mul (f z) (g z)).symm

private theorem measureReal_le_integral_of_eq_one
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu]
    {S : Set X} (hS : MeasurableSet S) (f : C(X, ℝ))
    (hf : ∀ z, 0 ≤ f z) (hfS : Set.EqOn f 1 S) :
    mu.real S ≤ ∫ z, f z ∂mu := by
  calc
    mu.real S = ∫ z, S.indicator (1 : X → ℝ) z ∂mu :=
      (integral_indicator_one hS).symm
    _ ≤ ∫ z, f z ∂mu := by
      refine integral_mono ((integrable_const 1).indicator hS)
        (compactlySupportedContinuousMap f).integrable ?_
      intro z
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz, hfS hz]
      · rw [Set.indicator_of_notMem hz]
        exact hf z

private theorem norm_sq_apply_le_re_inner_of_nonneg_of_le_one
    (D : E →L[ℂ] E) (hD0 : 0 ≤ D) (hD1 : D ≤ 1) (x : E) :
    ‖D x‖ ^ 2 ≤ (@inner ℂ E _ (D x) x).re := by
  have hDpos : ContinuousLinearMap.IsPositive D :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp hD0
  have h1D : 0 ≤ 1 - D := sub_nonneg.mpr hD1
  have hcomm : Commute D (1 - D) := (Commute.one_right D).sub_right rfl
  have hprod : 0 ≤ D * (1 - D) := Commute.mul_nonneg hD0 h1D hcomm
  have hsq : D * D ≤ D := by
    rw [← sub_nonneg]
    convert hprod using 1
    · noncomm_ring
  have hdiffpos : ContinuousLinearMap.IsPositive (D - D * D) :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hsq)
  have hq := hdiffpos.re_inner_nonneg_left x
  rw [sub_apply, mul_apply_eq_comp, inner_sub_left] at hq
  change 0 ≤ (@inner ℂ E _ (D x) x).re -
    (@inner ℂ E _ (D (D x)) x).re at hq
  have hnorm : (@inner ℂ E _ (D (D x)) x).re = ‖D x‖ ^ 2 := by
    rw [hDpos.inner_left_eq_inner_right (D x) x, inner_self_eq_norm_sq_to_K]
    calc
      (((‖D x‖ : ℂ) ^ 2).re) = (((‖D x‖ ^ 2 : ℝ) : ℂ).re) :=
        congrArg Complex.re (Complex.ofReal_pow ‖D x‖ 2).symm
      _ = ‖D x‖ ^ 2 := Complex.ofReal_re _
  rw [hnorm] at hq
  linarith

private noncomputable def closedSetApprox
    {X : Type*} [PseudoMetricSpace X] (K : Set X) (n : ℕ) : C(X, ℝ) where
  toFun z := max 0 (1 - (n : ℝ) * Metric.infDist z K)
  continuous_toFun := continuous_const.max
    (continuous_const.sub (continuous_const.mul (Metric.continuous_infDist_pt K)))

omit [CompleteSpace E] in
private theorem closedSetApprox_mem_Icc
    {X : Type*} [PseudoMetricSpace X] (K : Set X) (n : ℕ) (z : X) :
    closedSetApprox K n z ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · apply max_le zero_le_one
    have hmul : 0 ≤ (n : ℝ) * Metric.infDist z K :=
      mul_nonneg (Nat.cast_nonneg n) Metric.infDist_nonneg
    linarith

omit [CompleteSpace E] in
private theorem closedSetApprox_eq_one
    {X : Type*} [PseudoMetricSpace X] (K : Set X) (n : ℕ)
    {z : X} (hz : z ∈ K) : closedSetApprox K n z = 1 := by
  rw [closedSetApprox, ContinuousMap.coe_mk, Metric.infDist_zero_of_mem hz,
    mul_zero, sub_zero, max_eq_right zero_le_one]

omit [CompleteSpace E] in
private theorem tendsto_closedSetApprox
    {X : Type*} [PseudoMetricSpace X] (K : Set X)
    (hK : IsClosed K) (hKne : K.Nonempty) (z : X) :
    Filter.Tendsto (fun n => closedSetApprox K n z) Filter.atTop
      (nhds (K.indicator (fun _ => (1 : ℝ)) z)) := by
  by_cases hz : z ∈ K
  · rw [Set.indicator_of_mem hz]
    exact tendsto_const_nhds.congr'
      (Filter.Eventually.of_forall fun n => (closedSetApprox_eq_one K n hz).symm)
  · rw [Set.indicator_of_notMem hz]
    have hd : 0 < Metric.infDist z K := (hK.notMem_iff_infDist_pos hKne).mp hz
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (Metric.infDist z K)⁻¹
    have hNd : 1 < (N : ℝ) * Metric.infDist z K := by
      rw [← div_lt_iff₀ hd, one_div]
      exact hN
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hmul : (N : ℝ) * Metric.infDist z K ≤
        (n : ℝ) * Metric.infDist z K :=
      mul_le_mul_of_nonneg_right hcast hd.le
    rw [closedSetApprox, ContinuousMap.coe_mk, max_eq_left]
    linarith

omit [CompleteSpace E] in
private theorem tendsto_integral_closedSetApprox
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (K : Set X) (hK : IsClosed K) (hKne : K.Nonempty)
    (mu : Measure X) [IsFiniteMeasure mu] :
    Filter.Tendsto (fun n => ∫ z, closedSetApprox K n z ∂mu) Filter.atTop
      (nhds (mu.real K)) := by
  have hlim := tendsto_integral_of_dominated_convergence (μ := mu) (fun _ => (1 : ℝ))
    (fun n => (closedSetApprox K n).continuous.aestronglyMeasurable)
    (integrable_const 1)
    (fun n => ae_of_all mu fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (closedSetApprox_mem_Icc K n z).1]
      exact (closedSetApprox_mem_Icc K n z).2)
    (ae_of_all mu (tendsto_closedSetApprox K hK hKne))
  change Filter.Tendsto (fun n => ∫ z, closedSetApprox K n z ∂mu) Filter.atTop
    (nhds (∫ z, K.indicator (1 : X → ℝ) z ∂mu)) at hlim
  rw [integral_indicator_one hK.measurableSet] at hlim
  exact hlim

omit [CompleteSpace E] in
private theorem tendsto_integral_closedSetApprox_mul_self
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (K : Set X) (hK : IsClosed K) (hKne : K.Nonempty)
    (mu : Measure X) [IsFiniteMeasure mu] :
    Filter.Tendsto
      (fun n => ∫ z, (closedSetApprox K n * closedSetApprox K n) z ∂mu)
      Filter.atTop (nhds (mu.real K)) := by
  refine Filter.Tendsto.squeeze
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => mu.real K)
      Filter.atTop (nhds (mu.real K)))
    (tendsto_integral_closedSetApprox K hK hKne mu) ?_ ?_
  · intro n
    exact measureReal_le_integral_of_eq_one mu hK.measurableSet
      (closedSetApprox K n * closedSetApprox K n)
      (fun z => mul_nonneg (closedSetApprox_mem_Icc K n z).1
        (closedSetApprox_mem_Icc K n z).1)
      (fun z hz => by
        change closedSetApprox K n z * closedSetApprox K n z = (1 : ℝ)
        rw [closedSetApprox_eq_one K n hz, mul_one])
  · intro n
    refine integral_mono
      (compactlySupportedContinuousMap
        (closedSetApprox K n * closedSetApprox K n)).integrable
      (compactlySupportedContinuousMap (closedSetApprox K n)).integrable ?_
    intro z
    obtain ⟨hz0, hz1⟩ := closedSetApprox_mem_Icc K n z
    change closedSetApprox K n z * closedSetApprox K n z ≤
      closedSetApprox K n z
    nlinarith only [mul_nonneg hz0 (sub_nonneg.mpr hz1)]

omit [CompleteSpace E] in
private theorem exists_isClosed_measureReal_sdiff_lt
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure X) [IsFiniteMeasure mu]
    {S : Set X} (hS : MeasurableSet S) {eps : ℝ} (heps : 0 < eps) :
    ∃ K : Set X, K ⊆ S ∧ IsClosed K ∧ mu.real (S \ K) < eps := by
  let epsE : ENNReal := ENNReal.ofReal eps
  have hepsE : epsE ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr heps
  obtain ⟨K, hKS, hKclosed, hdiff⟩ :=
    hS.exists_isClosed_sdiff_lt (measure_ne_top mu S) hepsE
  refine ⟨K, hKS, hKclosed, ?_⟩
  have hreal := (ENNReal.toReal_lt_toReal
    (measure_ne_top mu (S \ K)) ENNReal.ofReal_ne_top).mpr hdiff
  rw [ENNReal.toReal_ofReal heps.le] at hreal
  exact hreal

private def compactlySupportedOne (X : Type*) [TopologicalSpace X]
    [CompactSpace X] : C_c(X, ℝ) where
  toFun := 1
  hasCompactSupport' := HasCompactSupport.of_compactSpace 1

@[simp]
private theorem compactlySupportedOne_apply (X : Type*) [TopologicalSpace X]
    [CompactSpace X] (z : X) : compactlySupportedOne X z = 1 := rfl

private theorem realToComplexContinuousMap_one
    (X : Type*) [TopologicalSpace X] [CompactSpace X] :
    realToComplexContinuousMap (compactlySupportedOne X) = 1 := by
  ext z
  rfl

/-- The scalar Riesz measure has total mass `‖x‖²`. -/
theorem normalCfcScalarMeasure_real_univ
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E) :
    (normalCfcScalarMeasure U hU x).real Set.univ = ‖x‖ ^ 2 := by
  let one : C_c(spectrum ℂ U, ℝ) := compactlySupportedOne (spectrum ℂ U)
  calc
    (normalCfcScalarMeasure U hU x).real Set.univ =
        ∫ _z, (1 : ℝ) ∂(normalCfcScalarMeasure U hU x) := by
          rw [integral_const, smul_eq_mul, mul_one]
    _ = ∫ z, one z ∂(normalCfcScalarMeasure U hU x) := by rfl
    _ = (@inner ℂ E _ x ((cfcHom hU)
        (realToComplexContinuousMap one) x)).re :=
      integral_normalCfcScalarMeasure U hU x one
    _ = (@inner ℂ E _ x x).re := by
      rw [show realToComplexContinuousMap one = 1 from
        realToComplexContinuousMap_one (spectrum ℂ U), map_one, one_apply_eq_self]
    _ = ‖x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re]
      norm_num [Complex.ofReal]
      ring

/-- Every scalar Riesz content is bounded by the squared norm of its vector. -/
theorem normalCfcScalarMeasure_real_le_norm_sq
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E)
    (S : Set (spectrum ℂ U)) :
    (normalCfcScalarMeasure U hU x).real S ≤ ‖x‖ ^ 2 := by
  rw [← normalCfcScalarMeasure_real_univ U hU x]
  exact measureReal_mono (Set.subset_univ S)

/-- The scalar Riesz measure is quadratic under complex scalar multiplication. -/
theorem normalCfcScalarMeasure_smul
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (c : ℂ) (x : E) :
    normalCfcScalarMeasure U hU (c • x) =
      ENNReal.ofReal (‖c‖ ^ 2) • normalCfcScalarMeasure U hU x := by
  let k : ENNReal := ENNReal.ofReal (‖c‖ ^ 2)
  have hk : k ≠ ⊤ := ENNReal.ofReal_ne_top
  let _ : (k • normalCfcScalarMeasure U hU x).Regular :=
    Measure.Regular.smul hk
  change normalCfcScalarMeasure U hU (c • x) =
    k • normalCfcScalarMeasure U hU x
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_normalCfcScalarMeasure, integral_smul_measure,
    integral_normalCfcScalarMeasure, ENNReal.toReal_ofReal (sq_nonneg ‖c‖),
    smul_eq_mul]
  change (@inner ℂ E _ (c • x)
    ((cfcHom hU) (realToComplexContinuousMap f) (c • x))).re = _
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    RCLike.conj_mul, Complex.mul_re]
  simp only [pow_two, Complex.mul_re, Complex.mul_im]
  norm_num [Complex.ofReal]

/-- The scalar Riesz measures satisfy the parallelogram identity. -/
theorem normalCfcScalarMeasure_parallelogram
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x y : E) :
    normalCfcScalarMeasure U hU (x + y) +
        normalCfcScalarMeasure U hU (x - y) =
      (normalCfcScalarMeasure U hU x + normalCfcScalarMeasure U hU x) +
        (normalCfcScalarMeasure U hU y + normalCfcScalarMeasure U hU y) := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hxyAdd : Integrable f (normalCfcScalarMeasure U hU (x + y)) := f.integrable
  have hxySub : Integrable f (normalCfcScalarMeasure U hU (x - y)) := f.integrable
  have hx : Integrable f (normalCfcScalarMeasure U hU x) := f.integrable
  have hy : Integrable f (normalCfcScalarMeasure U hU y) := f.integrable
  rw [integral_add_measure hxyAdd hxySub,
    integral_add_measure (hx.add_measure hx) (hy.add_measure hy),
    integral_add_measure hx hx, integral_add_measure hy hy,
    integral_normalCfcScalarMeasure, integral_normalCfcScalarMeasure,
    integral_normalCfcScalarMeasure, integral_normalCfcScalarMeasure]
  let T : E →L[ℂ] E := (cfcHom hU) (realToComplexContinuousMap f)
  change (@inner ℂ E _ (x + y) (T (x + y))).re +
      (@inner ℂ E _ (x - y) (T (x - y))).re =
    (@inner ℂ E _ x (T x)).re + (@inner ℂ E _ x (T x)).re +
      ((@inner ℂ E _ y (T y)).re + (@inner ℂ E _ y (T y)).re)
  simp only [map_add, map_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, Complex.add_re, Complex.sub_re]
  ring

/-- The real mass of a set under the scalar measure representing the normal CFC. -/
noncomputable def normalCfcScalarContent
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (x : E) : ℝ :=
  (normalCfcScalarMeasure U hU x).real S

private theorem normalCfcScalarContent_smul
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (c : ℂ) (x : E) :
    normalCfcScalarContent U hU S (c • x) =
      ‖c‖ ^ 2 * normalCfcScalarContent U hU S x := by
  unfold normalCfcScalarContent
  rw [normalCfcScalarMeasure_smul, measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (sq_nonneg ‖c‖)]

private theorem normalCfcScalarContent_parallelogram
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (x y : E) :
    normalCfcScalarContent U hU S (x + y) +
        normalCfcScalarContent U hU S (x - y) =
      (normalCfcScalarContent U hU S x + normalCfcScalarContent U hU S x) +
        (normalCfcScalarContent U hU S y + normalCfcScalarContent U hU S y) := by
  have h := congrArg (fun μ : Measure (spectrum ℂ U) => μ.real S)
    (normalCfcScalarMeasure_parallelogram U hU x y)
  rw [measureReal_add_apply, measureReal_add_apply, measureReal_add_apply,
    measureReal_add_apply] at h
  exact h

private theorem normalCfcScalarContent_nonneg
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (x : E) :
    0 ≤ normalCfcScalarContent U hU S x :=
  measureReal_nonneg

private theorem normalCfcScalarContent_le_norm_sq
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (x : E) :
    normalCfcScalarContent U hU S x ≤ ‖x‖ ^ 2 :=
  normalCfcScalarMeasure_real_le_norm_sq U hU x S

/-- The bounded sesquilinear form obtained by polarizing a scalar CFC measure at a set. -/
noncomputable def normalCfcSesquilinearForm
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) : E →L⋆[ℂ] E →L[ℂ] ℂ :=
  boundedSesquilinearFormOfQuadratic
    (normalCfcScalarContent U hU S)
    (by exact normalCfcScalarContent_smul U hU S)
    (by exact normalCfcScalarContent_parallelogram U hU S)
    (by exact normalCfcScalarContent_nonneg U hU S)
    (by exact normalCfcScalarContent_le_norm_sq U hU S)

/-- Polarization preserves the scalar measure on the diagonal. -/
theorem normalCfcSesquilinearForm_apply_self
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (x : E) :
    normalCfcSesquilinearForm U hU S x x =
      (normalCfcScalarMeasure U hU x).real S := by
  exact boundedSesquilinearFormOfQuadratic_apply_self
    (normalCfcScalarContent U hU S)
    (by exact normalCfcScalarContent_smul U hU S)
    (by exact normalCfcScalarContent_parallelogram U hU S)
    (by exact normalCfcScalarContent_nonneg U hU S)
    (by exact normalCfcScalarContent_le_norm_sq U hU S) x

/-- The positive operator represented by the polarized scalar CFC measures at a set. -/
noncomputable def normalCfcOperator
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) : E →L[ℂ] E :=
  InnerProductSpace.continuousLinearMapOfBilin
    (normalCfcSesquilinearForm U hU S)

/-- The quadratic matrix coefficient of the represented operator is the scalar CFC measure. -/
theorem inner_normalCfcOperator_self
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (x : E) :
    @inner ℂ E _ (normalCfcOperator U hU S x) x =
      (normalCfcScalarMeasure U hU x).real S := by
  rw [normalCfcOperator, InnerProductSpace.continuousLinearMapOfBilin_apply,
    normalCfcSesquilinearForm_apply_self]

omit [CompleteSpace E] in
private theorem continuousLinearMap_eq_of_inner_self_eq
    (T S : E →L[ℂ] E)
    (h : ∀ x : E, @inner ℂ E _ (T x) x = @inner ℂ E _ (S x) x) :
    T = S := by
  have hzero : (T.toLinearMap - S.toLinearMap) = 0 := by
    apply (inner_map_self_eq_zero (T.toLinearMap - S.toLinearMap)).mp
    intro x
    rw [LinearMap.sub_apply, inner_sub_left]
    change @inner ℂ E _ (T x) x - @inner ℂ E _ (S x) x = 0
    rw [h, sub_self]
  rw [sub_eq_zero] at hzero
  apply ContinuousLinearMap.ext
  intro x
  exact LinearMap.congr_fun hzero x

/-- Every represented scalar content gives a positive operator. -/
theorem normalCfcOperator_isPositive
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) :
    ContinuousLinearMap.IsPositive (normalCfcOperator U hU S) := by
  apply (ContinuousLinearMap.isPositive_toLinearMap_iff
    (normalCfcOperator U hU S)).mp
  rw [LinearMap.isPositive_iff_complex]
  intro x
  have hx : @inner ℂ E _ (normalCfcOperator U hU S x) x =
      ((normalCfcScalarMeasure U hU x).real S : ℂ) :=
    inner_normalCfcOperator_self U hU S x
  change ((@inner ℂ E _ (normalCfcOperator U hU S x) x).re : ℂ) =
      @inner ℂ E _ (normalCfcOperator U hU S x) x ∧
    0 ≤ (@inner ℂ E _ (normalCfcOperator U hU S x) x).re
  rw [hx]
  constructor
  · norm_num
  · exact measureReal_nonneg

/-- Every represented scalar content gives a self-adjoint operator. -/
theorem normalCfcOperator_isSelfAdjoint
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) :
    IsSelfAdjoint (normalCfcOperator U hU S) :=
  (normalCfcOperator_isPositive U hU S).isSelfAdjoint

private theorem normalCfcOperator_mono
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    {S T : Set (spectrum ℂ U)} (hST : S ⊆ T) :
    normalCfcOperator U hU S ≤ normalCfcOperator U hU T := by
  change ContinuousLinearMap.IsPositive
    (normalCfcOperator U hU T - normalCfcOperator U hU S)
  constructor
  · exact (normalCfcOperator_isPositive U hU T).isSymmetric.sub
      (normalCfcOperator_isPositive U hU S).isSymmetric
  · intro x
    change 0 ≤ (@inner ℂ E _
      ((normalCfcOperator U hU T - normalCfcOperator U hU S) x) x).re
    rw [sub_apply, inner_sub_left, inner_normalCfcOperator_self,
      inner_normalCfcOperator_self]
    exact sub_nonneg.mpr (measureReal_mono hST)

private theorem normalCfcOperator_le_one
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) :
    normalCfcOperator U hU S ≤ 1 := by
  change ContinuousLinearMap.IsPositive (1 - normalCfcOperator U hU S)
  constructor
  · exact ContinuousLinearMap.isPositive_one.isSymmetric.sub
      (normalCfcOperator_isPositive U hU S).isSymmetric
  · intro x
    change 0 ≤ (@inner ℂ E _
      ((1 - normalCfcOperator U hU S) x) x).re
    rw [sub_apply, one_apply_eq_self, inner_sub_left,
      inner_normalCfcOperator_self, inner_self_eq_norm_sq_to_K]
    rw [Complex.sub_re, Complex.ofReal_re]
    convert sub_nonneg.mpr
      (normalCfcScalarMeasure_real_le_norm_sq U hU x S) using 1
    rw [pow_two, Complex.mul_re]
    norm_num [Complex.ofReal]
    rw [pow_two]

private theorem mul_projection_eq_of_projection_le_contraction
    (Q P : E →L[ℂ] E)
    (hQid : IsIdempotentElem Q) (hQself : IsSelfAdjoint Q)
    (hP1 : P ≤ 1) (hQP : Q ≤ P) :
    P * Q = Q := by
  have hQstar : IsStarProjection Q := ⟨hQid, hQself⟩
  have hfix := hQstar.one_sub.mul_right_and_mul_left_of_nonneg_of_le
    (sub_nonneg.mpr hP1) (sub_le_sub_left hQP 1)
  have h := hfix.1
  linear_combination (norm := noncomm_ring) h

private theorem normalCfcOperator_le_realOperator
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    {S : Set (spectrum ℂ U)} (hS : MeasurableSet S)
    (f : C(spectrum ℂ U, ℝ)) (hf : ∀ z, 0 ≤ f z)
    (hfS : Set.EqOn f 1 S) :
    normalCfcOperator U hU S ≤ normalCfcRealOperator U hU f := by
  have hphi := normalCfcRealOperator_isPositive U hU f hf
  change ContinuousLinearMap.IsPositive
    (normalCfcRealOperator U hU f - normalCfcOperator U hU S)
  constructor
  · exact hphi.isSymmetric.sub (normalCfcOperator_isPositive U hU S).isSymmetric
  · intro x
    change 0 ≤ (@inner ℂ E _
      ((normalCfcRealOperator U hU f - normalCfcOperator U hU S) x) x).re
    rw [sub_apply, inner_sub_left]
    change 0 ≤ (@inner ℂ E _ (normalCfcRealOperator U hU f x) x).re -
      (@inner ℂ E _ (normalCfcOperator U hU S x) x).re
    rw [inner_normalCfcOperator_self]
    rw [hphi.inner_left_eq_inner_right x x]
    rw [← integral_normalCfcScalarMeasure_continuous]
    exact sub_nonneg.mpr (measureReal_le_integral_of_eq_one
      (normalCfcScalarMeasure U hU x) hS f hf hfS)

private theorem tendsto_normalCfcRealOperator_of_integral
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (hS : MeasurableSet S)
    (f : ℕ → C(spectrum ℂ U, ℝ))
    (hf0 : ∀ n z, 0 ≤ f n z) (hf1 : ∀ n z, f n z ≤ 1)
    (hfS : ∀ n, Set.EqOn (f n) 1 S) (x : E)
    (hint : Filter.Tendsto
      (fun n => ∫ z, f n z ∂(normalCfcScalarMeasure U hU x))
      Filter.atTop (nhds ((normalCfcScalarMeasure U hU x).real S))) :
    Filter.Tendsto (fun n => normalCfcRealOperator U hU (f n) x)
      Filter.atTop (nhds (normalCfcOperator U hU S x)) := by
  let phi : ℕ → E →L[ℂ] E := fun n => normalCfcRealOperator U hU (f n)
  let P : E →L[ℂ] E := normalCfcOperator U hU S
  have hD0 (n : ℕ) : 0 ≤ phi n - P := by
    exact sub_nonneg.mpr
      (normalCfcOperator_le_realOperator U hU hS (f n) (hf0 n) (hfS n))
  have hD1 (n : ℕ) : phi n - P ≤ 1 := by
    calc
      phi n - P ≤ phi n := sub_le_self _
        (ContinuousLinearMap.nonneg_iff_isPositive.mpr
          (normalCfcOperator_isPositive U hU S))
      _ ≤ 1 := normalCfcRealOperator_le_one U hU (f n) (hf1 n)
  have hgap : Filter.Tendsto
      (fun n => ∫ z, f n z ∂(normalCfcScalarMeasure U hU x) -
        (normalCfcScalarMeasure U hU x).real S)
      Filter.atTop (nhds 0) := by
    simpa only [sub_self] using
      hint.sub (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ => (normalCfcScalarMeasure U hU x).real S)
        Filter.atTop (nhds ((normalCfcScalarMeasure U hU x).real S)))
  have hsqrt : Filter.Tendsto
      (fun n => Real.sqrt
        ((∫ z, f n z ∂(normalCfcScalarMeasure U hU x)) -
          (normalCfcScalarMeasure U hU x).real S))
      Filter.atTop (nhds 0) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hgap
    change Filter.Tendsto
      (fun n => Real.sqrt
        ((∫ z, f n z ∂(normalCfcScalarMeasure U hU x)) -
          (normalCfcScalarMeasure U hU x).real S))
      Filter.atTop (nhds (Real.sqrt 0)) at hs
    rw [Real.sqrt_zero] at hs
    exact hs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) ?_ hsqrt
  intro n
  have hbound := norm_sq_apply_le_re_inner_of_nonneg_of_le_one
    (phi n - P) (hD0 n) (hD1 n) x
  rw [sub_apply, inner_sub_left] at hbound
  change ‖phi n x - P x‖ ^ 2 ≤
    (@inner ℂ E _ (phi n x) x).re - (@inner ℂ E _ (P x) x).re at hbound
  rw [show (@inner ℂ E _ (phi n x) x).re =
      ∫ z, f n z ∂(normalCfcScalarMeasure U hU x) by
        rw [(normalCfcRealOperator_isPositive U hU (f n) (hf0 n)).inner_left_eq_inner_right x x]
        exact (integral_normalCfcScalarMeasure_continuous U hU x (f n)).symm,
    show (@inner ℂ E _ (P x) x).re =
      (normalCfcScalarMeasure U hU x).real S by
        rw [inner_normalCfcOperator_self, Complex.ofReal_re]] at hbound
  exact Real.le_sqrt_of_sq_le hbound

private theorem tendsto_normalCfcRealOperator_closedSetApprox
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (K : Set (spectrum ℂ U)) (hK : IsClosed K) (hKne : K.Nonempty)
    (x : E) :
    Filter.Tendsto
      (fun n => normalCfcRealOperator U hU (closedSetApprox K n) x)
      Filter.atTop (nhds (normalCfcOperator U hU K x)) := by
  exact tendsto_normalCfcRealOperator_of_integral U hU K hK.measurableSet
    (closedSetApprox K) (fun n z => (closedSetApprox_mem_Icc K n z).1)
    (fun n z => (closedSetApprox_mem_Icc K n z).2)
    (fun n z hz => closedSetApprox_eq_one K n hz) x
    (tendsto_integral_closedSetApprox K hK hKne (normalCfcScalarMeasure U hU x))

/-- The operator represented by the scalar CFC measures of a closed set is idempotent. -/
theorem normalCfcOperator_isIdempotent_of_isClosed
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (K : Set (spectrum ℂ U)) (hK : IsClosed K) :
    IsIdempotentElem (normalCfcOperator U hU K) := by
  by_cases hKne : K.Nonempty
  · let phi : ℕ → E →L[ℂ] E := fun n =>
      normalCfcRealOperator U hU (closedSetApprox K n)
    let P : E →L[ℂ] E := normalCfcOperator U hU K
    change P * P = P
    apply ContinuousLinearMap.ext
    intro x
    have hphi (y : E) : Filter.Tendsto (fun n => phi n y)
        Filter.atTop (nhds (P y)) := by
      exact tendsto_normalCfcRealOperator_closedSetApprox U hU K hK hKne y
    have hphi0 (n : ℕ) : 0 ≤ phi n := by
      exact ContinuousLinearMap.nonneg_iff_isPositive.mpr
        (normalCfcRealOperator_isPositive U hU (closedSetApprox K n)
          (fun z => (closedSetApprox_mem_Icc K n z).1))
    have hphi1 (n : ℕ) : phi n ≤ 1 := by
      exact normalCfcRealOperator_le_one U hU (closedSetApprox K n)
        (fun z => (closedSetApprox_mem_Icc K n z).2)
    have hphiNorm (n : ℕ) : ‖phi n‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg (phi n) (hphi0 n)).mpr (hphi1 n)
    have hfirst : Filter.Tendsto
        (fun n => phi n (phi n x - P x)) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm (fun n => ?_)
        (tendsto_iff_norm_sub_tendsto_zero.mp (hphi x))
      calc
        ‖phi n (phi n x - P x)‖ ≤ ‖phi n‖ * ‖phi n x - P x‖ :=
          (phi n).le_opNorm _
        _ ≤ 1 * ‖phi n x - P x‖ :=
          mul_le_mul_of_nonneg_right (hphiNorm n) (norm_nonneg _)
        _ = ‖phi n x - P x‖ := one_mul _
    have hsecond : Filter.Tendsto
        (fun n => phi n (P x) - P (P x)) Filter.atTop (nhds 0) := by
      simpa only [sub_self] using
        (hphi (P x)).sub (tendsto_const_nhds : Filter.Tendsto
          (fun _ : ℕ => P (P x)) Filter.atTop (nhds (P (P x))))
    have hdiff : Filter.Tendsto
        (fun n => (phi n * phi n) x - (P * P) x)
        Filter.atTop (nhds 0) := by
      have hsum : Filter.Tendsto
          (fun n => phi n (phi n x - P x) + (phi n (P x) - P (P x)))
          Filter.atTop (nhds 0) := by
        simpa only [add_zero] using hfirst.add hsecond
      refine hsum.congr'
        (Filter.Eventually.of_forall fun n => ?_)
      change phi n (phi n x - P x) + (phi n (P x) - P (P x)) =
        phi n (phi n x) - P (P x)
      rw [map_sub]
      abel
    have hmulToPSq : Filter.Tendsto (fun n => (phi n * phi n) x)
        Filter.atTop (nhds ((P * P) x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hnorm := (continuous_norm.tendsto 0).comp hdiff
      change Filter.Tendsto
        (fun n => ‖(phi n * phi n) x - (P * P) x‖)
        Filter.atTop (nhds ‖(0 : E)‖) at hnorm
      simpa only [norm_zero] using hnorm
    have hsquareToP : Filter.Tendsto
        (fun n => normalCfcRealOperator U hU
          (closedSetApprox K n * closedSetApprox K n) x)
        Filter.atTop (nhds (P x)) := by
      exact tendsto_normalCfcRealOperator_of_integral U hU K hK.measurableSet
        (fun n => closedSetApprox K n * closedSetApprox K n)
        (fun n z => mul_nonneg (closedSetApprox_mem_Icc K n z).1
          (closedSetApprox_mem_Icc K n z).1)
        (fun n z => by
          obtain ⟨hz0, hz1⟩ := closedSetApprox_mem_Icc K n z
          change closedSetApprox K n z * closedSetApprox K n z ≤ 1
          nlinarith only [mul_nonneg hz0 (sub_nonneg.mpr hz1), hz1])
        (fun n z hz => by
          change closedSetApprox K n z * closedSetApprox K n z = (1 : ℝ)
          rw [closedSetApprox_eq_one K n hz, mul_one]) x
        (tendsto_integral_closedSetApprox_mul_self K hK hKne
          (normalCfcScalarMeasure U hU x))
    have hmulToP : Filter.Tendsto (fun n => (phi n * phi n) x)
        Filter.atTop (nhds (P x)) := by
      simpa only [phi, normalCfcRealOperator_mul] using hsquareToP
    exact tendsto_nhds_unique hmulToPSq hmulToP
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    subst K
    have hzero : normalCfcOperator U hU ∅ = 0 := by
      apply continuousLinearMap_eq_of_inner_self_eq
      intro x
      rw [inner_normalCfcOperator_self, measureReal_empty,
        zero_apply, inner_zero_left]
      rfl
    rw [hzero]
    exact IsIdempotentElem.zero

/-- Inner regularity promotes the closed-set projections to every measurable set. -/
theorem normalCfcOperator_isIdempotent
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (hS : MeasurableSet S) :
    IsIdempotentElem (normalCfcOperator U hU S) := by
  classical
  let T : E →L[ℂ] E := normalCfcOperator U hU S
  change T * T = T
  apply ContinuousLinearMap.ext
  intro x
  let mu := normalCfcScalarMeasure U hU x
  have hex (n : ℕ) : ∃ K : Set (spectrum ℂ U),
      K ⊆ S ∧ IsClosed K ∧ mu.real (S \ K) < 1 / ((n : ℝ) + 1) := by
    apply exists_isClosed_measureReal_sdiff_lt mu hS
    positivity
  choose K hKS hKclosed hdiff using hex
  let Q : ℕ → E →L[ℂ] E := fun n => normalCfcOperator U hU (K n)
  let D : ℕ → E →L[ℂ] E := fun n => T - Q n
  have hQ0 (n : ℕ) : 0 ≤ Q n :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (normalCfcOperator_isPositive U hU (K n))
  have hD0 (n : ℕ) : 0 ≤ D n := by
    exact sub_nonneg.mpr (normalCfcOperator_mono U hU (hKS n))
  have hD1 (n : ℕ) : D n ≤ 1 := by
    calc
      D n ≤ T := sub_le_self T (hQ0 n)
      _ ≤ 1 := normalCfcOperator_le_one U hU S
  have hdiff_apply (n : ℕ) : Q n x - T x = -(D n x) := by
    dsimp only [D]
    rw [sub_apply]
    abel
  have hnormdiff (n : ℕ) : ‖Q n x - T x‖ ^ 2 < 1 / ((n : ℝ) + 1) := by
    rw [hdiff_apply n, norm_neg]
    apply (norm_sq_apply_le_re_inner_of_nonneg_of_le_one
      (D n) (hD0 n) (hD1 n) x).trans_lt
    dsimp only [D, T, Q]
    rw [sub_apply, inner_sub_left, inner_normalCfcOperator_self,
      inner_normalCfcOperator_self, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_re]
    rw [← measureReal_sdiff (hKS n) (hKclosed n).measurableSet]
    exact hdiff n
  have hinv : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hbound_tendsto : Filter.Tendsto
      (fun n : ℕ => Real.sqrt (1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hinv
    rw [Real.sqrt_zero] at hsqrt
    exact hsqrt
  have hQx : Filter.Tendsto (fun n => Q n x)
      Filter.atTop (nhds (T x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero
    · exact fun _ => norm_nonneg _
    · intro n
      exact Real.le_sqrt_of_sq_le (hnormdiff n).le
    · exact hbound_tendsto
  have hfix (n : ℕ) : T * Q n = Q n := by
    apply mul_projection_eq_of_projection_le_contraction
    · exact normalCfcOperator_isIdempotent_of_isClosed U hU (K n) (hKclosed n)
    · exact normalCfcOperator_isSelfAdjoint U hU (K n)
    · exact normalCfcOperator_le_one U hU S
    · exact normalCfcOperator_mono U hU (hKS n)
  have hleft : Filter.Tendsto (fun n => T (Q n x))
      Filter.atTop (nhds (T (T x))) :=
    T.continuous.continuousAt.tendsto.comp hQx
  have hright : Filter.Tendsto (fun n => T (Q n x))
      Filter.atTop (nhds (T x)) := by
    convert hQx using 1
    funext n
    have happ := congrArg (fun R : E →L[ℂ] E => R x) (hfix n)
    simpa only [mul_apply_eq_comp] using happ
  change T (T x) = T x
  exact tendsto_nhds_unique hleft hright

/-- The represented operator of the empty measurable set is zero. -/
@[simp]
theorem normalCfcOperator_empty
    (U : E →L[ℂ] E) (hU : IsStarNormal U) :
    normalCfcOperator U hU ∅ = 0 := by
  apply continuousLinearMap_eq_of_inner_self_eq
  intro x
  rw [inner_normalCfcOperator_self, measureReal_empty,
    zero_apply, inner_zero_left]
  rfl

/-- The represented operator of the full spectrum is the identity. -/
@[simp]
theorem normalCfcOperator_univ
    (U : E →L[ℂ] E) (hU : IsStarNormal U) :
    normalCfcOperator U hU Set.univ = 1 := by
  apply continuousLinearMap_eq_of_inner_self_eq
  intro x
  rw [inner_normalCfcOperator_self,
    normalCfcScalarMeasure_real_univ, one_apply_eq_self,
    inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- Disjoint unions of measurable sets become sums of represented operators. -/
theorem normalCfcOperator_union
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    {S T : Set (spectrum ℂ U)} (hdisj : Disjoint S T)
    (hT : MeasurableSet T) :
    normalCfcOperator U hU (S ∪ T) =
      normalCfcOperator U hU S + normalCfcOperator U hU T := by
  apply continuousLinearMap_eq_of_inner_self_eq
  intro x
  rw [inner_normalCfcOperator_self, add_apply,
    inner_add_left, inner_normalCfcOperator_self, inner_normalCfcOperator_self,
    measureReal_union hdisj hT]
  push_cast
  rfl

private def initialUnion {X : Type*} (S : ℕ → Set X) (n : ℕ) : Set X :=
  ⋃ i, ⋃ (_hi : i < n), S i

private def tailUnion {X : Type*} (S : ℕ → Set X) (n : ℕ) : Set X :=
  ⋃ i, ⋃ (_hi : n ≤ i), S i

omit [CompleteSpace E] in
private theorem initialUnion_zero {X : Type*} (S : ℕ → Set X) :
    initialUnion S 0 = ∅ := by
  ext x
  constructor
  · intro hx
    rw [initialUnion] at hx
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, _hx⟩ := Set.mem_iUnion.mp hx
    omega
  · intro hx
    exact False.elim hx

omit [CompleteSpace E] in
private theorem initialUnion_succ {X : Type*} (S : ℕ → Set X) (n : ℕ) :
    initialUnion S (n + 1) = initialUnion S n ∪ S n := by
  ext x
  constructor
  · intro hx
    rw [initialUnion] at hx
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hx
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact Set.mem_union_left _ (Set.mem_iUnion_of_mem i
        (Set.mem_iUnion_of_mem hi hxi))
    · exact Set.mem_union_right _ hxi
  · intro hx
    rcases hx with hx | hx
    · rw [initialUnion] at hx ⊢
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion_of_mem i
        (Set.mem_iUnion_of_mem (Nat.lt_succ_of_lt hi) hxi)
    · rw [initialUnion]
      exact Set.mem_iUnion_of_mem n
        (Set.mem_iUnion_of_mem (Nat.lt_succ_self n) hx)

omit [CompleteSpace E] in
private theorem tailUnion_measurable {X : Type*} [MeasurableSpace X]
    (S : ℕ → Set X) (hS : ∀ i, MeasurableSet (S i)) (n : ℕ) :
    MeasurableSet (tailUnion S n) := by
  unfold tailUnion
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _hi => hS i

omit [CompleteSpace E] in
private theorem initialUnion_disjoint_tailUnion {X : Type*}
    (S : ℕ → Set X) (hpair : Pairwise fun i j => Disjoint (S i) (S j)) (n : ℕ) :
    Disjoint (initialUnion S n) (tailUnion S n) := by
  rw [Set.disjoint_left]
  intro x hxinit hxtail
  rw [initialUnion] at hxinit
  obtain ⟨i, hxinit⟩ := Set.mem_iUnion.mp hxinit
  obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hxinit
  rw [tailUnion] at hxtail
  obtain ⟨j, hxtail⟩ := Set.mem_iUnion.mp hxtail
  obtain ⟨hj, hxj⟩ := Set.mem_iUnion.mp hxtail
  have hij : i ≠ j := by omega
  exact Set.disjoint_left.mp (hpair hij) hxi hxj

omit [CompleteSpace E] in
private theorem iUnion_eq_initialUnion_union_tailUnion {X : Type*}
    (S : ℕ → Set X) (n : ℕ) :
    (⋃ i, S i) = initialUnion S n ∪ tailUnion S n := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    by_cases hi : i < n
    · exact Set.mem_union_left _ (Set.mem_iUnion_of_mem i
        (Set.mem_iUnion_of_mem hi hxi))
    · exact Set.mem_union_right _ (Set.mem_iUnion_of_mem i
        (Set.mem_iUnion_of_mem (Nat.le_of_not_gt hi) hxi))
  · intro hx
    rcases hx with hx | hx
    · rw [initialUnion] at hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨_hi, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion_of_mem i hxi
    · rw [tailUnion] at hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨_hi, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion_of_mem i hxi

private theorem normalCfcOperator_initialUnion
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : ℕ → Set (spectrum ℂ U))
    (hS : ∀ i, MeasurableSet (S i))
    (hpair : Pairwise fun i j => Disjoint (S i) (S j)) (n : ℕ) :
    normalCfcOperator U hU (initialUnion S n) =
      ∑ i ∈ Finset.range n, normalCfcOperator U hU (S i) := by
  induction n with
  | zero =>
      rw [initialUnion_zero, normalCfcOperator_empty, Finset.sum_range_zero]
  | succ n ih =>
      have hdisj : Disjoint (initialUnion S n) (S n) := by
        rw [Set.disjoint_left]
        intro x hxinit hxn
        rw [initialUnion] at hxinit
        obtain ⟨i, hxinit⟩ := Set.mem_iUnion.mp hxinit
        obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hxinit
        have hin : i ≠ n := by omega
        exact Set.disjoint_left.mp (hpair hin) hxi hxn
      rw [show n + 1 = Nat.succ n by omega, initialUnion_succ,
        normalCfcOperator_union U hU hdisj (hS n), ih,
        Finset.sum_range_succ]

/-- The represented operators are countably additive in the strong operator topology. -/
theorem normalCfcOperator_countably_additive
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : ℕ → Set (spectrum ℂ U))
    (hS : ∀ i, MeasurableSet (S i))
    (hpair : Pairwise fun i j => Disjoint (S i) (S j)) (x : E) :
    Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n, normalCfcOperator U hU (S i) x)
      Filter.atTop (nhds (normalCfcOperator U hU (⋃ i, S i) x)) := by
  have htailMeas (n : ℕ) : MeasurableSet (tailUnion S n) :=
    tailUnion_measurable S hS n
  have htailMeasure : Filter.Tendsto
      ((normalCfcScalarMeasure U hU x) ∘ tailUnion S)
      Filter.atTop (nhds 0) := by
    change Filter.Tendsto
      (fun n => normalCfcScalarMeasure U hU x
        (⋃ i, ⋃ (_hi : n ≤ i), S i)) Filter.atTop (nhds 0)
    exact tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
      (μ := normalCfcScalarMeasure U hU x)
      (fun i => (hS i).nullMeasurableSet) hpair
  have htailReal : Filter.Tendsto
      (fun n => (normalCfcScalarMeasure U hU x).real (tailUnion S n))
      Filter.atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htailMeasure
    change Filter.Tendsto
      (fun n => ENNReal.toReal
        (normalCfcScalarMeasure U hU x (tailUnion S n)))
      Filter.atTop (nhds 0)
    simpa only [Function.comp_def, ENNReal.toReal_zero] using h
  have htailNormSq : Filter.Tendsto
      (fun n => ‖normalCfcOperator U hU (tailUnion S n) x‖ ^ 2)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun n => sq_nonneg _)
      (Filter.Eventually.of_forall fun n => ?_) htailReal
    calc
      ‖normalCfcOperator U hU (tailUnion S n) x‖ ^ 2 ≤
          (@inner ℂ E _
            (normalCfcOperator U hU (tailUnion S n) x) x).re :=
        norm_sq_apply_le_re_inner_of_nonneg_of_le_one
          (normalCfcOperator U hU (tailUnion S n))
          (ContinuousLinearMap.nonneg_iff_isPositive.mpr
            (normalCfcOperator_isPositive U hU (tailUnion S n)))
          (normalCfcOperator_le_one U hU (tailUnion S n)) x
      _ = (normalCfcScalarMeasure U hU x).real (tailUnion S n) := by
        rw [inner_normalCfcOperator_self, Complex.ofReal_re]
  have htailNorm : Filter.Tendsto
      (fun n => ‖normalCfcOperator U hU (tailUnion S n) x‖)
      Filter.atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp htailNormSq
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_zero] using h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply htailNorm.congr'
  apply Filter.Eventually.of_forall
  intro n
  have hpartial := normalCfcOperator_initialUnion U hU S hS hpair n
  have hdecomp :
      normalCfcOperator U hU (⋃ i, S i) =
        normalCfcOperator U hU (initialUnion S n) +
          normalCfcOperator U hU (tailUnion S n) := by
    rw [iUnion_eq_initialUnion_union_tailUnion S n]
    exact normalCfcOperator_union U hU
      (initialUnion_disjoint_tailUnion S hpair n) (htailMeas n)
  have happ := congrArg (fun T : E →L[ℂ] E => T x) hdecomp
  rw [add_apply, hpartial, sum_apply] at happ
  change ‖normalCfcOperator U hU (tailUnion S n) x‖ =
    ‖(∑ i ∈ Finset.range n, normalCfcOperator U hU (S i) x) -
      normalCfcOperator U hU (⋃ i, S i) x‖
  rw [happ]
  rw [show (∑ i ∈ Finset.range n, normalCfcOperator U hU (S i) x) -
      ((∑ i ∈ Finset.range n, normalCfcOperator U hU (S i) x) +
        normalCfcOperator U hU (tailUnion S n) x) =
      -normalCfcOperator U hU (tailUnion S n) x by abel, norm_neg]

private theorem normalCfcOperator_compl
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S : Set (spectrum ℂ U)) (hS : MeasurableSet S) :
    normalCfcOperator U hU Sᶜ = 1 - normalCfcOperator U hU S := by
  have hsum := normalCfcOperator_union U hU disjoint_compl_right hS.compl
  rw [Set.union_compl_self, normalCfcOperator_univ] at hsum
  symm
  apply sub_eq_iff_eq_add.mpr
  simpa only [add_comm] using hsum

private theorem normalCfcOperator_mul_eq_zero_of_disjoint
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    {S T : Set (spectrum ℂ U)} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hdisj : Disjoint S T) :
    normalCfcOperator U hU S * normalCfcOperator U hU T = 0 := by
  have hTScompl : T ⊆ Sᶜ := by
    intro z hzT hzS
    exact Set.disjoint_left.mp hdisj hzS hzT
  have hfix : normalCfcOperator U hU Sᶜ * normalCfcOperator U hU T =
      normalCfcOperator U hU T := by
    apply mul_projection_eq_of_projection_le_contraction
    · exact normalCfcOperator_isIdempotent U hU T hT
    · exact normalCfcOperator_isSelfAdjoint U hU T
    · exact normalCfcOperator_le_one U hU Sᶜ
    · exact normalCfcOperator_mono U hU hTScompl
  rw [normalCfcOperator_compl U hU S hS] at hfix
  rw [sub_mul, one_mul] at hfix
  apply neg_eq_zero.mp
  calc
    -(normalCfcOperator U hU S * normalCfcOperator U hU T) =
        ((normalCfcOperator U hU T -
          normalCfcOperator U hU S * normalCfcOperator U hU T) -
          normalCfcOperator U hU T) := by abel
    _ = normalCfcOperator U hU T - normalCfcOperator U hU T := by
      rw [hfix]
    _ = 0 := sub_self _

/-- Intersections of measurable sets become products of represented projections. -/
theorem normalCfcOperator_inter
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (S T : Set (spectrum ℂ U)) (hS : MeasurableSet S)
    (hT : MeasurableSet T) :
    normalCfcOperator U hU (S ∩ T) =
      normalCfcOperator U hU S * normalCfcOperator U hU T := by
  let R : Set (spectrum ℂ U) := T \ (S ∩ T)
  have hR : MeasurableSet R := hT.diff (hS.inter hT)
  have hinterT : S ∩ T ⊆ T := Set.inter_subset_right
  have hdecomp : normalCfcOperator U hU T =
      normalCfcOperator U hU (S ∩ T) + normalCfcOperator U hU R := by
    dsimp only [R]
    rw [← normalCfcOperator_union U hU Set.disjoint_sdiff_right hR,
      Set.union_sdiff_cancel hinterT]
  have hinterfix : normalCfcOperator U hU S *
      normalCfcOperator U hU (S ∩ T) = normalCfcOperator U hU (S ∩ T) := by
    apply mul_projection_eq_of_projection_le_contraction
    · exact normalCfcOperator_isIdempotent U hU (S ∩ T) (hS.inter hT)
    · exact normalCfcOperator_isSelfAdjoint U hU (S ∩ T)
    · exact normalCfcOperator_le_one U hU S
    · exact normalCfcOperator_mono U hU Set.inter_subset_left
  have hdisj : Disjoint S R := by
    rw [Set.disjoint_left]
    intro z hzS hzR
    exact hzR.2 ⟨hzS, hzR.1⟩
  have hzero : normalCfcOperator U hU S * normalCfcOperator U hU R = 0 :=
    normalCfcOperator_mul_eq_zero_of_disjoint U hU hS hR hdisj
  rw [hdecomp, mul_add, hinterfix, hzero, add_zero]

/-- Pull the projection-valued resolution of a normal operator back along a measurable real
coordinate on its spectrum. -/
noncomputable def normalCfcPVM
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (g : spectrum ℂ U → ℝ) (hg : Measurable g) : PVM E where
  proj S := normalCfcOperator U hU (g ⁻¹' S)
  isOrthogonalProjection S hS :=
    ⟨normalCfcOperator_isSelfAdjoint U hU (g ⁻¹' S),
      normalCfcOperator_isIdempotent U hU (g ⁻¹' S) (hg hS)⟩
  empty := by
    rw [Set.preimage_empty, normalCfcOperator_empty]
  univ := by
    rw [Set.preimage_univ, normalCfcOperator_univ]
  inter S T hS hT := by
    rw [Set.preimage_inter, normalCfcOperator_inter U hU
      (g ⁻¹' S) (g ⁻¹' T) (hg hS) (hg hT)]
  countably_additive S hS hpair x := by
    have hpreMeas : ∀ i, MeasurableSet (g ⁻¹' S i) := fun i => hg (hS i)
    have hprePair : Pairwise fun i j => Disjoint (g ⁻¹' S i) (g ⁻¹' S j) := by
      intro i j hij
      rw [Set.disjoint_left]
      intro z hzi hzj
      exact Set.disjoint_left.mp (hpair hij) hzi hzj
    simpa only [Set.preimage_iUnion] using
      normalCfcOperator_countably_additive U hU
        (fun i => g ⁻¹' S i) hpreMeas hprePair x

/-- Scalar measures of a pulled-back normal CFC resolution are pushforwards of its Riesz
measures. -/
theorem normalCfcPVM_scalarMeasure
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (g : spectrum ℂ U → ℝ) (hg : Measurable g) (x : E) :
    (normalCfcPVM U hU g hg).scalarMeasure x =
      Measure.map g (normalCfcScalarMeasure U hU x) := by
  apply Measure.ext
  intro S hS
  rw [PVM.scalarMeasure_apply _ x S hS, Measure.map_apply hg hS]
  change ENNReal.ofReal
      ((@inner ℂ E _ (normalCfcOperator U hU (g ⁻¹' S) x) x).re) =
    normalCfcScalarMeasure U hU x (g ⁻¹' S)
  rw [inner_normalCfcOperator_self, Complex.ofReal_re, ofReal_measureReal]

/-- The subset of the spectrum at the singular point of the inverse Cayley transform. -/
def unitPole (U : E →L[ℂ] E) : Set (spectrum ℂ U) :=
  {z | (z : ℂ) = 1}

omit [CompleteSpace E] in
private theorem unitPole_measurable (U : E →L[ℂ] E) :
    MeasurableSet (unitPole U) := by
  exact measurableSet_singleton (1 : ℂ) |>.preimage measurable_subtype_coe

private noncomputable def distanceToOneSq (U : E →L[ℂ] E) :
    C_c(spectrum ℂ U, ℝ) where
  toFun z := ‖(z : ℂ) - 1‖ ^ 2
  continuous_toFun := ((continuous_subtype_val.sub continuous_const).norm.pow 2)
  hasCompactSupport' := HasCompactSupport.of_compactSpace _

private noncomputable def distanceToOneSqComplex (U : E →L[ℂ] E) :
    C(spectrum ℂ U, ℂ) :=
  star ((ContinuousMap.id ℂ).restrict (spectrum ℂ U) - 1) *
    ((ContinuousMap.id ℂ).restrict (spectrum ℂ U) - 1)

private theorem distanceToOneSq_ofReal (U : E →L[ℂ] E)
    (z : spectrum ℂ U) :
    ((distanceToOneSq U z : ℝ) : ℂ) = distanceToOneSqComplex U z := by
  change ((‖(z : ℂ) - 1‖ ^ 2 : ℝ) : ℂ) =
    star ((z : ℂ) - 1) * ((z : ℂ) - 1)
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]

private theorem cfcHom_distanceToOneSqComplex
    (U : E →L[ℂ] E) (hU : IsStarNormal U) :
    (cfcHom hU) (distanceToOneSqComplex U) = star (U - 1) * (U - 1) := by
  unfold distanceToOneSqComplex
  rw [map_mul, map_star, map_sub, map_one, cfcHom_id]

/-- The represented normal-CFC projection at the Cayley pole vanishes whenever `1` has no
eigenvectors. -/
theorem normalCfcOperator_unitPole_eq_zero
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (hNoFixed : ∀ x, U x = x → x = 0) :
    normalCfcOperator U hU (unitPole U) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  let P := normalCfcOperator U hU (unitPole U)
  let Q := normalCfcOperator U hU (unitPole U)ᶜ
  let y := P x
  have hQP : Q * P = 0 := by
    have hinter := normalCfcOperator_inter U hU (unitPole U)ᶜ (unitPole U)
      (unitPole_measurable U).compl (unitPole_measurable U)
    rw [Set.compl_inter_self, normalCfcOperator_empty] at hinter
    exact hinter.symm
  have hQy : Q y = 0 := by
    have happ := congrArg (fun T : E →L[ℂ] E => T x) hQP
    simpa only [mul_apply_eq_comp, zero_apply, y] using happ
  let mu := normalCfcScalarMeasure U hU y
  have hmuComplReal : mu.real (unitPole U)ᶜ = 0 := by
    have hinner := inner_normalCfcOperator_self U hU (unitPole U)ᶜ y
    change @inner ℂ E _ (Q y) y = (mu.real (unitPole U)ᶜ : ℂ) at hinner
    rw [hQy, inner_zero_left] at hinner
    exact_mod_cast hinner.symm
  have hmuCompl : mu (unitPole U)ᶜ = 0 := by
    rw [Measure.real, ENNReal.toReal_eq_zero_iff] at hmuComplReal
    exact hmuComplReal.resolve_right (measure_ne_top mu (unitPole U)ᶜ)
  have haePole : ∀ᵐ z ∂mu, z ∈ unitPole U := by
    exact mem_ae_iff.mpr hmuCompl
  have hzeroAE : (fun z => distanceToOneSq U z) =ᵐ[mu] 0 := by
    filter_upwards [haePole] with z hz
    change ‖(z : ℂ) - 1‖ ^ 2 = 0
    rw [show (z : ℂ) = 1 from hz, sub_self, norm_zero,
      zero_pow (by omega)]
  have hintegral : ∫ z, distanceToOneSq U z ∂mu = 0 :=
    integral_eq_zero_of_ae hzeroAE
  have hrepr :
      ∫ z, distanceToOneSq U z ∂mu =
        (@inner ℂ E _ y
          ((cfcHom hU) (distanceToOneSqComplex U) y)).re := by
    rw [integral_normalCfcScalarMeasure]
    congr 1
    congr 1
    apply congrArg (fun f : C(spectrum ℂ U, ℂ) => (cfcHom hU) f y)
    ext z
    exact distanceToOneSq_ofReal U z
  have hnormSq : ‖(U - 1) y‖ ^ 2 = 0 := by
    rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
    rw [← ContinuousLinearMap.star_eq_adjoint]
    change (@inner ℂ E _ y ((star (U - 1) * (U - 1)) y)).re = 0
    rw [← cfcHom_distanceToOneSqComplex U hU, ← hrepr, hintegral]
  have hUy : U y = y := by
    have hzeroNorm : ‖(U - 1) y‖ = 0 := sq_eq_zero_iff.mp hnormSq
    have hzero : (U - 1) y = 0 := norm_eq_zero.mp hzeroNorm
    simpa only [sub_apply, one_apply_eq_self, sub_eq_zero] using hzero
  rw [zero_apply]
  change y = (0 : E)
  exact hNoFixed y hUy

/-- The real inverse-Cayley coordinate, with the removable spectral point `1` assigned `0` by
the field convention `0⁻¹ = 0`. -/
noncomputable def inverseCayleyCoordinate (z : ℂ) : ℝ :=
  -z.im / (1 - z.re)

private theorem inverseCayleyCoordinate_measurable :
    Measurable inverseCayleyCoordinate := by
  exact Complex.measurable_im.neg.div
    (measurable_const.sub Complex.measurable_re)

/-- The scalar Cayley coordinate on the real line. -/
noncomputable def cayleyCoordinate (t : ℝ) : ℂ :=
  ((t : ℂ) - Complex.I) / ((t : ℂ) + Complex.I)

theorem cayleyCoordinate_measurable : Measurable cayleyCoordinate := by
  exact (Complex.measurable_ofReal.sub measurable_const).div
    (Complex.measurable_ofReal.add measurable_const)

private theorem cayleyCoordinate_norm (t : ℝ) : ‖cayleyCoordinate t‖ = 1 := by
  rw [cayleyCoordinate, norm_div]
  have hden : ‖(t : ℂ) + Complex.I‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add,
      Complex.zero_im] at him
    exact one_ne_zero him
  rw [div_eq_one_iff_eq hden]
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
    Complex.I_re, sub_zero, Complex.sub_im, Complex.ofReal_im, Complex.I_im,
    zero_sub, mul_neg, neg_mul, neg_neg, Complex.add_re, add_zero,
    Complex.add_im, zero_add]

theorem cayleyCoordinate_bounded :
    ∃ C, ∀ t, ‖cayleyCoordinate t‖ ≤ C := by
  refine ⟨1, fun t => ?_⟩
  rw [cayleyCoordinate_norm]

private theorem cayleyCoordinate_relation (t : ℝ) :
    (t : ℂ) * (1 - cayleyCoordinate t) =
      Complex.I * (1 + cayleyCoordinate t) := by
  have hden : (t : ℂ) + Complex.I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im,
      zero_add, Complex.zero_im] at him
    exact one_ne_zero him
  rw [cayleyCoordinate]
  field_simp
  ring

private theorem inverseCayley_scalar_identity
    (U : E →L[ℂ] E) (hunit : U ∈ unitary (E →L[ℂ] E))
    (z : spectrum ℂ U) (hz : (z : ℂ) ≠ 1) :
    (1 - (z : ℂ)) * (inverseCayleyCoordinate z : ℂ) =
      Complex.I * (1 + (z : ℂ)) := by
  have hnorm : ‖(z : ℂ)‖ = 1 :=
    spectrum.norm_eq_one_of_unitary hunit z.property
  have hcircle : (z : ℂ).re * (z : ℂ).re +
      (z : ℂ).im * (z : ℂ).im = 1 := by
    calc
      (z : ℂ).re * (z : ℂ).re + (z : ℂ).im * (z : ℂ).im =
          Complex.normSq z := (Complex.normSq_apply z).symm
      _ = ‖(z : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq z
      _ = 1 := by rw [hnorm, one_pow]
  have hden : 1 - (z : ℂ).re ≠ 0 := by
    intro hzero
    have hre : (z : ℂ).re = 1 := (sub_eq_zero.mp hzero).symm
    have him : (z : ℂ).im = 0 := by
      rw [hre, one_mul] at hcircle
      nlinarith only [hcircle, sq_nonneg (z : ℂ).im]
    apply hz
    apply Complex.ext
    · simpa only [Complex.one_re] using hre
    · simpa only [Complex.one_im] using him
  apply Complex.ext
  · change (((1 : ℂ) - (z : ℂ)) *
        ((-((z : ℂ).im) / (1 - (z : ℂ).re) : ℝ) : ℂ)).re =
      (Complex.I * (1 + (z : ℂ))).re
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re,
      Complex.ofReal_re, Complex.sub_im, Complex.one_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
      zero_mul, one_mul, mul_zero, sub_zero, zero_sub]
    field_simp
    rw [zero_add]
  · change (((1 : ℂ) - (z : ℂ)) *
        ((-((z : ℂ).im) / (1 - (z : ℂ).re) : ℝ) : ℂ)).im =
      (Complex.I * (1 + (z : ℂ))).im
    simp only [Complex.mul_im, Complex.sub_re, Complex.one_re,
      Complex.ofReal_re, Complex.sub_im, Complex.one_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
      zero_mul, one_mul, mul_zero, zero_sub, zero_add]
    field_simp
    nlinarith only [hcircle]

private theorem cayleyCoordinate_inverseCayleyCoordinate
    (U : E →L[ℂ] E) (hunit : U ∈ unitary (E →L[ℂ] E))
    (z : spectrum ℂ U) (hz : (z : ℂ) ≠ 1) :
    cayleyCoordinate (inverseCayleyCoordinate z) = (z : ℂ) := by
  have hden : (inverseCayleyCoordinate z : ℂ) + Complex.I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im,
      zero_add, Complex.zero_im] at him
    exact one_ne_zero him
  rw [cayleyCoordinate, div_eq_iff hden]
  linear_combination inverseCayley_scalar_identity U hunit z hz

/-- The real PVM obtained from the normal CFC resolution using the inverse-Cayley coordinate. -/
noncomputable def inverseCayleyPVM
    (U : E →L[ℂ] E) (hU : IsStarNormal U) : PVM E :=
  normalCfcPVM U hU (fun z => inverseCayleyCoordinate z)
    (by exact inverseCayleyCoordinate_measurable.comp measurable_subtype_coe)

private theorem normalCfcScalarMeasure_unitPole_eq_zero
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (hNoFixed : ∀ x, U x = x → x = 0) (x : E) :
    normalCfcScalarMeasure U hU x (unitPole U) = 0 := by
  have hreal : (normalCfcScalarMeasure U hU x).real (unitPole U) = 0 := by
    have hinner := inner_normalCfcOperator_self U hU (unitPole U) x
    rw [normalCfcOperator_unitPole_eq_zero U hU hNoFixed,
      zero_apply, inner_zero_left] at hinner
    exact_mod_cast hinner.symm
  exact (measureReal_eq_zero_iff
    (measure_ne_top (normalCfcScalarMeasure U hU x) (unitPole U))).mp hreal

omit [CompleteSpace E] in
private theorem continuousLinearMap_eq_of_inner_self_eq_right
    (T S : E →L[ℂ] E)
    (h : ∀ x : E, @inner ℂ E _ x (T x) = @inner ℂ E _ x (S x)) :
    T = S := by
  apply continuousLinearMap_eq_of_inner_self_eq
  intro x
  rw [← inner_conj_symm (T x) x, ← inner_conj_symm (S x) x, h]

/-- Integrating the scalar Cayley coordinate against the inverse-Cayley PVM recovers the
unitary operator. -/
theorem inverseCayleyPVM_integral_cayleyCoordinate
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (hunit : U ∈ unitary (E →L[ℂ] E))
    (hNoFixed : ∀ x, U x = x → x = 0) :
    (inverseCayleyPVM U hU).integral cayleyCoordinate
      cayleyCoordinate_measurable cayleyCoordinate_bounded = U := by
  apply continuousLinearMap_eq_of_inner_self_eq_right
  intro x
  let mu := normalCfcScalarMeasure U hU x
  let coord : C(spectrum ℂ U, ℂ) :=
    (ContinuousMap.id ℂ).restrict (spectrum ℂ U)
  have hpole : mu (unitPole U) = 0 :=
    normalCfcScalarMeasure_unitPole_eq_zero U hU hNoFixed x
  have hae : ∀ᵐ z ∂mu, z ∉ unitPole U := by
    apply ae_iff.mpr
    rw [show {z : spectrum ℂ U | ¬z ∉ unitPole U} = unitPole U by
      ext z
      simp only [Set.mem_ofPred_eq, not_not]]
    exact hpole
  calc
    @inner ℂ E _ x
        ((inverseCayleyPVM U hU).integral cayleyCoordinate
          cayleyCoordinate_measurable cayleyCoordinate_bounded x) =
        ∫ t, cayleyCoordinate t ∂((inverseCayleyPVM U hU).scalarMeasure x) :=
      PVM.inner_integral_self _ _ _ _ x
    _ = ∫ t, cayleyCoordinate t ∂Measure.map
        (fun z : spectrum ℂ U => inverseCayleyCoordinate z) mu := by
      rw [inverseCayleyPVM, normalCfcPVM_scalarMeasure]
    _ = ∫ z, cayleyCoordinate (inverseCayleyCoordinate z) ∂mu := by
      have hgEq : (fun z : spectrum ℂ U => inverseCayleyCoordinate z) =
          inverseCayleyCoordinate ∘ Subtype.val := by
        funext z
        rfl
      rw [hgEq]
      exact integral_map
        (inverseCayleyCoordinate_measurable.comp
          measurable_subtype_coe).aemeasurable
        cayleyCoordinate_measurable.aestronglyMeasurable
    _ = ∫ z, (z : ℂ) ∂mu := by
      apply integral_congr_ae
      filter_upwards [hae] with z hz
      exact cayleyCoordinate_inverseCayleyCoordinate U hunit z hz
    _ = @inner ℂ E _ x ((cfcHom hU) coord x) := by
      exact integral_normalCfcScalarMeasure_complex U hU x coord
    _ = @inner ℂ E _ x (U x) := by
      rw [cfcHom_id]

/-- Every self-adjoint partial linear operator is the coordinate integral of a real PVM. -/
theorem spectral_theorem_existence
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ E_pvm : PVM E,
      E_pvm.unboundedIntegral ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable = A := by
  let U := cayleyTransform A hA
  have hunit : U ∈ unitary (E →L[ℂ] E) := cayleyTransform_unitary A hA
  have hU : IsStarNormal U :=
    (unitary_iff_isStarNormal_and_spectrum_subset_unitary.mp hunit).1
  have hNoFixed : ∀ x, U x = x → x = 0 :=
    one_not_mem_eigenvalues_cayleyTransform A hA
  let P := inverseCayleyPVM U hU
  let B := P.unboundedIntegral ((↑) : ℝ → ℂ)
    Complex.continuous_ofReal.measurable
  refine ⟨P, ?_⟩
  change B = A
  have hphase : P.integral cayleyCoordinate cayleyCoordinate_measurable
      cayleyCoordinate_bounded = U := by
    exact inverseCayleyPVM_integral_cayleyCoordinate U hU hunit hNoFixed
  have hle : A ≤ B := by
    exact P.selfAdjoint_le_coordinate_unboundedIntegral_of_cayley
      A hA cayleyCoordinate cayleyCoordinate_measurable
      cayleyCoordinate_bounded cayleyCoordinate_relation hphase
  have hsym : B.IsFormalAdjoint B :=
    P.coordinate_unboundedIntegral_isFormalAdjoint
  exact eq_of_selfAdjoint_le_formalSelfAdjoint A B hA hle hsym
