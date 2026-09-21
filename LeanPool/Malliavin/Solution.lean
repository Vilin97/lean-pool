/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.Malliavin.Malliavin

/-!
# Closability of the Malliavin derivative (Solution)

This module repeats the Mathlib-only statement boundary from `Challenge` and
discharges the advertised theorem using the development in `Malliavin`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Real Topology InnerProductSpace

/-- The Cameron–Martin Hilbert space: the closed first-chaos subspace of
centered continuous linear functionals in L²(μ). -/
noncomputable def CameronMartin.Space
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    (μ : Measure W) [IsGaussian μ] :
    Submodule ℝ (Lp ℝ 2 μ) :=
  (StrongDual.toLp μ 2 -
    (Lp.constL 2 μ ℝ).comp
      (ContinuousLinearMap.apply ℝ ℝ (∫ x, x ∂μ))).range.topologicalClosure

namespace CameronMartin

/-- The identity random variable centered by its Bochner mean. -/
noncomputable def centeredId
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W]
    (μ : Measure W) : W → W :=
  id - fun _ ↦ ∫ x, x ∂μ

/-- The centered identity is square-integrable under a Gaussian measure. -/
theorem memLp_centeredId
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ] : MemLp (centeredId μ) 2 μ := by
  have h_id : MemLp id 2 μ := IsGaussian.memLp_id μ 2 (by norm_num)
  have h_const : MemLp (fun _ : W ↦ ∫ x, x ∂μ) 2 μ :=
    memLp_const (∫ x, x ∂μ)
  exact h_id.sub h_const

/-- The centered identity as an element of `L²(μ; W)`. -/
noncomputable def centeredIdLp
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ] : Lp W 2 μ :=
  (memLp_centeredId μ).toLp (centeredId μ)

/-- The covariance map from scalar `L²(μ)` into the ambient Banach space. -/
noncomputable def covarianceMap
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ] : Lp ℝ 2 μ →L[ℝ] W :=
  ((ContinuousLinearMap.lsmul ℝ ℝ (E := W)).lpPairing μ 2 2).flip
    (centeredIdLp μ)

/-- The covariance embedding of the Cameron–Martin space into `W`. -/
noncomputable def inclusion
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ] : Space μ →L[ℝ] W :=
  (covarianceMap μ).domRestrict (Space μ)

/-- The Cameron–Martin space is complete because it is a closed subspace of `L²(μ)`. -/
instance instCompleteSpaceSpace
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    (μ : Measure W) [IsGaussian μ] : CompleteSpace (Space μ) :=
  inferInstanceAs (CompleteSpace
    ((StrongDual.toLp μ 2 -
      (Lp.constL 2 μ ℝ).comp
        (ContinuousLinearMap.apply ℝ ℝ (∫ x, x ∂μ))).range.topologicalClosure))

end CameronMartin

/-- The Malliavin derivative as the Riesz representative of differentiation
along the Cameron–Martin covariance embedding. -/
noncomputable def mderiv
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ] (F : W → ℝ) (x : W) : CameronMartin.Space μ :=
  (InnerProductSpace.toDual ℝ (CameronMartin.Space μ)).symm
    ((fderiv ℝ F x).comp (CameronMartin.inclusion μ))

/-- A bounded C¹ Fréchet functional with uniformly bounded derivative. -/
structure IsSmoothBounded {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : W → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 F
  bounded : ∃ C, ∀ x, |F x| ≤ C
  bounded_fderiv : ∃ C, ∀ x, ‖fderiv ℝ F x‖ ≤ C

namespace IsSmoothBounded

/-- A smooth bounded functional has a continuous Fréchet derivative. -/
theorem continuous_fderiv
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : W → ℝ} (hF : IsSmoothBounded F) : Continuous (fderiv ℝ F) :=
  hF.contDiff.continuous_fderiv one_ne_zero

/-- A smooth bounded functional belongs to every finite or infinite `Lᵖ` space. -/
theorem memLp
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {F : W → ℝ} (μ : Measure W) [IsGaussian μ]
    (hF : IsSmoothBounded F) (p : ℝ≥0∞) : MemLp F p μ := by
  obtain ⟨C, hC⟩ := hF.bounded
  exact MemLp.of_bound hF.contDiff.continuous.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x ↦ by
      simpa [Real.norm_eq_abs] using hC x)

/-- The Malliavin derivative of a smooth bounded functional is continuous. -/
theorem continuous_mderiv
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {F : W → ℝ} (μ : Measure W) [IsGaussian μ]
    (hF : IsSmoothBounded F) : Continuous (mderiv μ F) := by
  unfold mderiv
  exact (InnerProductSpace.toDual ℝ (CameronMartin.Space μ)).symm.continuous.comp
    (hF.continuous_fderiv.clm_comp continuous_const)

/-- The norm of the Malliavin derivative is uniformly bounded. -/
theorem exists_norm_mderiv_le
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {F : W → ℝ} (μ : Measure W) [IsGaussian μ]
    (hF : IsSmoothBounded F) : ∃ C, ∀ x, ‖mderiv μ F x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hF.bounded_fderiv
  refine ⟨C * ‖CameronMartin.inclusion μ‖, fun x ↦ ?_⟩
  unfold mderiv
  rw [LinearIsometryEquiv.norm_map]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hC x)
      (ContinuousLinearMap.opNorm_nonneg _))

/-- The Malliavin derivative of a smooth bounded functional belongs to `Lᵖ` for every `p`. -/
theorem memLp_mderiv
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {F : W → ℝ} (μ : Measure W) [IsGaussian μ]
    (hF : IsSmoothBounded F) (p : ℝ≥0∞) : MemLp (mderiv μ F) p μ := by
  obtain ⟨C, hC⟩ := hF.exists_norm_mderiv_le μ
  exact MemLp.of_bound (hF.continuous_mderiv μ).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

/-- The L²(μ) equivalence class of a smooth bounded functional. -/
noncomputable def toLp
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {F : W → ℝ} (μ : Measure W) [IsGaussian μ]
    (hF : IsSmoothBounded F) :
    Lp ℝ 2 μ :=
  (hF.memLp μ 2).toLp F

/-- The Malliavin derivative of a smooth bounded functional as an element
of L²(μ; H), where H is the Cameron–Martin space. -/
noncomputable def mderivLp
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {F : W → ℝ} (μ : Measure W) [IsGaussian μ]
    (hF : IsSmoothBounded F) :
    Lp (CameronMartin.Space μ) 2 μ :=
  (hF.memLp_mderiv μ 2).toLp (mderiv μ F)

end IsSmoothBounded

/-- Gaussian integration by parts: the mean directional Malliavin derivative
along a Cameron–Martin vector equals pairing against its first-chaos
representative. -/
theorem integral_inner_mderiv
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ]
    {F : W → ℝ} (hF : IsSmoothBounded F) (h : CameronMartin.Space μ) :
    ∫ x, ⟪mderiv μ F x, h⟫_ℝ ∂μ =
      ∫ x, F x * (h : Lp ℝ 2 μ) x ∂μ :=
  Malliavin.integral_inner_mderiv μ
    (Malliavin.IsSmoothBounded.mk
      hF.contDiff hF.bounded hF.bounded_fderiv)
    h

theorem mderiv_closable
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ]
    (F : ℕ → {F : W → ℝ // IsSmoothBounded F})
    {η : Lp (CameronMartin.Space μ) 2 μ}
    (hF : Tendsto (fun k ↦ (F k).2.toLp μ) atTop (𝓝 0))
    (hD : Tendsto (fun k ↦ (F k).2.mderivLp μ) atTop (𝓝 η)) :
    η = 0 :=
  Malliavin.mderiv_closable μ
    (fun k ↦ ⟨(F k).1, Malliavin.IsSmoothBounded.mk
      (F k).2.contDiff (F k).2.bounded (F k).2.bounded_fderiv⟩)
    hF hD

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
