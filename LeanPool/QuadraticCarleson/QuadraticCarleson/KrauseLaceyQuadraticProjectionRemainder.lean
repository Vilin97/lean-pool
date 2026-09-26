/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.HarmonicPhaseSum
public import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveragingAmplitude
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticSmoothProjection
public import LeanPool.QuadraticCarleson.QuadraticCarleson.HilbertRepresentativeBridge
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The smooth-projection remainder in the direct quadratic proof

This file formalizes the explicit normalized integral formula used for the
error kernel `(1 - P_R) κ_R`. The amplitude is the project's fixed positive
dyadic base, and the smoothing kernel is the inverse Fourier transform of the
concrete annular cutoff from `KrauseLaceyQuadraticSmoothProjection`.

The principal estimate is

`‖r_R x‖ ≤ C R⁻³ (1 + |x| / R)⁻²`, for `1 ≤ R`,

with a fixed, explicitly defined finite constant `C`. The last section
records the finite square-summation argument for the errors: the paper's
per-scale `L∞` and `L¹` bounds imply an `O(2⁻²ˢ V^(1/2))` `L²` sum.
-/

@[expose] public section

open Function MeasureTheory Set FourierTransform Metric Convolution
open scoped ENNReal NNReal ContDiff SchwartzMap ComplexConjugate

namespace QuadraticCarleson.KrauseLaceyQuadraticProjectionRemainder


noncomputable
section

/-- A one-sided cutoff which is one on `[1/8,2]` and supported in
`(1/16,33/16)`. In particular it is one on twice the support of the fixed
amplitude. -/
def remainderFrequencyCutoffData : ContDiffBump (17 / 16 : ℝ) :=
  ⟨15 / 16, 1, by norm_num, by norm_num⟩

/-- The complex-valued annular cutoff used to express the projection remainder. -/
def remainderFrequencyCutoff (ξ : ℝ) : ℂ :=
  (remainderFrequencyCutoffData ξ : ℂ)

/-- The cutoff used in the explicit kernel calculation is literally the
cutoff used by the project's `L²` annular projection. -/
theorem remainderFrequencyCutoff_eq_annularFrequencyCutoff :
    remainderFrequencyCutoff =
      KrauseLaceyQuadraticSmoothProjection.annularFrequencyCutoff := by
  funext ξ
  rfl

theorem contDiff_remainderFrequencyCutoff :
    ContDiff ℝ ∞ remainderFrequencyCutoff :=
  Complex.ofRealCLM.contDiff.comp remainderFrequencyCutoffData.contDiff

theorem hasCompactSupport_remainderFrequencyCutoff :
    HasCompactSupport remainderFrequencyCutoff :=
  remainderFrequencyCutoffData.hasCompactSupport.comp_left rfl

theorem remainderFrequencyCutoff_eq_one {ξ : ℝ}
    (hξ : ξ ∈ Icc (1 / 8 : ℝ) 2) :
    remainderFrequencyCutoff ξ = 1 := by
  have hmem : ξ ∈ closedBall (17 / 16 : ℝ) (15 / 16) := by
    rw [mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith [hξ.1, hξ.2]
  have hbump : remainderFrequencyCutoffData ξ = 1 :=
    remainderFrequencyCutoffData.one_of_mem_closedBall hmem
  change (remainderFrequencyCutoffData ξ : ℂ) = 1
  rw [hbump]
  norm_num

/-- The cutoff is one at the stationary frequency `2v` wherever the fixed
amplitude is nonzero. -/
theorem positiveDyadicBase_mul_remainderFrequencyCutoff_two (v : ℝ) :
    positiveDyadicBase v * remainderFrequencyCutoff (2 * v) =
      positiveDyadicBase v := by
  by_cases hv : positiveDyadicBase v = 0
  · simp [hv]
  · have hs := positiveDyadicBase_support_subset hv
    rw [remainderFrequencyCutoff_eq_one]
    · ring
    · constructor <;> linarith [hs.1, hs.2]

/-- The fixed cutoff bundled as a Schwartz function. -/
def remainderFrequencyCutoffSchwartz : SchwartzMap ℝ ℂ :=
  hasCompactSupport_remainderFrequencyCutoff.toSchwartzMap
    contDiff_remainderFrequencyCutoff

/-- The inverse Fourier transform of the fixed annular cutoff. -/
def projectionKernelSchwartz : SchwartzMap ℝ ℂ :=
  fourierInv remainderFrequencyCutoffSchwartz

theorem fourier_projectionKernelSchwartz :
    fourier projectionKernelSchwartz = remainderFrequencyCutoffSchwartz := by
  exact fourier_fourierInv_eq remainderFrequencyCutoffSchwartz

/-- The physical projection kernel at dyadic frequency radius `2^k`. -/
def scaledProjectionKernel (k : ℤ) (t : ℝ) : ℂ :=
  (((2 : ℝ) ^ k : ℝ) : ℂ) *
    projectionKernelSchwartz ((2 : ℝ) ^ k * t)

theorem integrable_scaledProjectionKernel (k : ℤ) :
    Integrable (scaledProjectionKernel k) := by
  have hk : (2 : ℝ) ^ k ≠ 0 := zpow_ne_zero _ (by norm_num)
  exact (projectionKernelSchwartz.integrable.comp_mul_left' hk).const_mul _

/-- The scaled physical kernel has exactly the cutoff used to define
`annularProjectionL2`. -/
theorem fourier_scaledProjectionKernel (k : ℤ) (ξ : ℝ) :
    𝓕 (scaledProjectionKernel k) ξ =
      KrauseLaceyQuadraticSmoothProjection.scaledAnnularFrequencyCutoff k ξ := by
  let R : ℝ := (2 : ℝ) ^ k
  have hR : 0 < R := by dsimp [R]; positivity
  let g : ℝ → ℂ := fun u ↦
    Complex.exp (((-2 * Real.pi * u * (ξ / R) : ℝ) : ℂ) * Complex.I) •
      projectionKernelSchwartz u
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hfun : (fun t : ℝ ↦
      Complex.exp (((-2 * Real.pi * t * ξ : ℝ) : ℂ) * Complex.I) •
        scaledProjectionKernel k t) =
      fun t ↦ (R : ℂ) * g (R * t) := by
    funext t
    unfold scaledProjectionKernel g
    simp only [R, smul_eq_mul]
    have hphase :
        (((-2 * Real.pi * t * ξ : ℝ) : ℂ) * Complex.I) =
          (((-2 * Real.pi * ((2 : ℝ) ^ k * t) *
            (ξ / (2 : ℝ) ^ k) : ℝ) : ℂ) * Complex.I) := by
      congr 1
      norm_cast
      field_simp
    rw [hphase]
    ring
  rw [hfun, MeasureTheory.integral_const_mul,
    Measure.integral_comp_mul_left]
  rw [abs_of_pos (inv_pos.mpr hR)]
  rw [Complex.real_smul]
  rw [← mul_assoc]
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ hR.ne']
  norm_num
  have hg : (∫ y : ℝ, g y) =
      𝓕 (projectionKernelSchwartz : ℝ → ℂ) (ξ / R) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
  rw [hg]
  rw [← SchwartzMap.fourier_coe]
  rw [fourier_projectionKernelSchwartz]
  unfold KrauseLaceyQuadraticSmoothProjection.scaledAnnularFrequencyCutoff
  rw [← remainderFrequencyCutoff_eq_annularFrequencyCutoff]
  rfl

/-- Convolution with the concrete physical projection kernel. -/
def scaledProjectionConvolution (k : ℤ) (f : ℝ → ℂ) : ℝ → ℂ :=
  scaledProjectionKernel k ⋆[ContinuousLinearMap.mul ℂ ℂ] f

/-- The Fourier-defined annular projection agrees in `L²` with convolution
by the concrete inverse-Fourier kernel. The only extra premise is that this
convolution belongs to `L²`; for the localized scale outputs this is supplied
by their already established `L²` estimate. -/
theorem annularProjectionL2_toLp_eq_scaledProjectionConvolution
    (k : ℤ) {f : ℝ → ℂ} (hf : Integrable f) (hf₂ : MemLp f 2 volume)
    (hconv₂ : MemLp (scaledProjectionConvolution k f) 2 volume) :
    KrauseLaceyQuadraticSmoothProjection.annularProjectionL2 k (hf₂.toLp f) =
      hconv₂.toLp (scaledProjectionConvolution k f) := by
  have hkernel := integrable_scaledProjectionKernel k
  have hconv : Integrable (scaledProjectionConvolution k f) := by
    exact hkernel.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [KrauseLaceyQuadraticSmoothProjection.fourier_annularProjectionL2]
  apply Lp.ext
  filter_upwards [
    (KrauseLaceyQuadraticSmoothProjection.memLp_annularFourierMultiplier
      k (hf₂.toLp f)).coeFn_toLp,
    HilbertRepresentativeBridge.fourier_toLp_ae_eq hf hf₂,
    HilbertRepresentativeBridge.fourier_toLp_ae_eq hconv hconv₂
  ] with ξ hmult hfourier hconvFourier
  have hmult' :
      (KrauseLaceyQuadraticSmoothProjection.annularMultiplierL2
        k (hf₂.toLp f) : ℝ → ℂ) ξ =
        KrauseLaceyQuadraticSmoothProjection.annularFourierMultiplier
          k (hf₂.toLp f) ξ := by
    simpa only [KrauseLaceyQuadraticSmoothProjection.annularMultiplierL2] using hmult
  rw [hmult', hconvFourier]
  unfold KrauseLaceyQuadraticSmoothProjection.annularFourierMultiplier
  rw [hfourier]
  change _ = 𝓕
    (scaledProjectionKernel k ⋆[ContinuousLinearMap.mul ℂ ℂ] f) ξ
  rw [Real.fourier_mul_convolution_eq hkernel hf,
    fourier_scaledProjectionKernel]

/-- Fourier inversion identifies the oscillatory integral of the smoothing
kernel with the concrete cutoff. -/
theorem integral_projectionKernel_mul_phase (v : ℝ) :
    (∫ u : ℝ, projectionKernelSchwartz u * phase (-2 * v * u)) =
      remainderFrequencyCutoff (2 * v) := by
  have h := congrArg (fun f : SchwartzMap ℝ ℂ ↦ f (2 * v))
    fourier_projectionKernelSchwartz
  change fourier (projectionKernelSchwartz : ℝ → ℂ) (2 * v) =
    remainderFrequencyCutoff (2 * v) at h
  rw [Real.fourier_eq] at h
  simpa [Circle.smul_def, Real.fourierChar_apply, phase,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- The exact cancellation identity used to insert the projection into the
kernel formula. -/
theorem positiveDyadicBase_eq_projectionKernel_integral (v : ℝ) :
    positiveDyadicBase v =
      ∫ u : ℝ, projectionKernelSchwartz u * phase (-2 * v * u) *
        positiveDyadicBase v := by
  calc
    positiveDyadicBase v =
        positiveDyadicBase v * remainderFrequencyCutoff (2 * v) :=
      (positiveDyadicBase_mul_remainderFrequencyCutoff_two v).symm
    _ = positiveDyadicBase v *
        (∫ u : ℝ, projectionKernelSchwartz u * phase (-2 * v * u)) := by
      rw [integral_projectionKernel_mul_phase]
    _ = ∫ u : ℝ, projectionKernelSchwartz u * phase (-2 * v * u) *
        positiveDyadicBase v := by
      rw [integral_mul_const]
      ring

/-- The bracket in the paper's explicit remainder formula. -/
def projectionRemainderBracket (R v u : ℝ) : ℂ :=
  positiveDyadicBase v -
    positiveDyadicBase (v - u / R ^ 2) * phase (u ^ 2 / R ^ 2)

/-- The normalized quadratic scale kernel `κ_R`. -/
def quadraticScaleKernel (R x : ℝ) : ℂ :=
  R⁻¹ * positiveDyadicBase (x / R) * phase (x ^ 2)

/-- At `R = 2^k`, the normalized kernel is the project's actual positive
dyadic quadratic kernel. -/
theorem quadraticScaleKernel_two_zpow (k : ℤ) (x : ℝ) :
    quadraticScaleKernel ((2 : ℝ) ^ k) x =
      annularQuadraticKernel (positiveDyadicAmplitude k) 1 x := by
  unfold quadraticScaleKernel annularQuadraticKernel positiveDyadicAmplitude
  simp only [one_mul, div_eq_inv_mul, inv_zpow]

/-- The normalized integral formula for the smooth projection `P_R κ_R`. -/
def smoothProjectedQuadraticScaleKernel (R x : ℝ) : ℂ :=
  R⁻¹ * phase (x ^ 2) *
    ∫ u : ℝ, projectionKernelSchwartz u * phase (-2 * (x / R) * u) *
      positiveDyadicBase (x / R - u / R ^ 2) * phase (u ^ 2 / R ^ 2)

/-- The explicit projected-kernel formula is exactly convolution with the
inverse-Fourier kernel at the same dyadic scale. -/
theorem scaledProjectionConvolution_quadraticScaleKernel_eq
    (k : ℤ) (x : ℝ) :
    scaledProjectionConvolution k
        (quadraticScaleKernel ((2 : ℝ) ^ k)) x =
      smoothProjectedQuadraticScaleKernel ((2 : ℝ) ^ k) x := by
  let R : ℝ := (2 : ℝ) ^ k
  have hR : 0 < R := by dsimp [R]; positivity
  let q : ℝ → ℂ := fun u ↦
    projectionKernelSchwartz u *
      positiveDyadicBase (x / R - u / R ^ 2) *
      phase ((x - u / R) ^ 2)
  have hrow : (fun t : ℝ ↦
      scaledProjectionKernel k t * quadraticScaleKernel R (x - t)) =
        fun t ↦ q (R * t) := by
    funext t
    unfold scaledProjectionKernel quadraticScaleKernel q
    change (R : ℂ) * projectionKernelSchwartz (R * t) *
        (((R⁻¹ : ℝ) : ℂ) * positiveDyadicBase ((x - t) / R) *
          phase ((x - t) ^ 2)) =
      projectionKernelSchwartz (R * t) *
        positiveDyadicBase (x / R - (R * t) / R ^ 2) *
          phase ((x - (R * t) / R) ^ 2)
    have hamp : (x - t) / R = x / R - (R * t) / R ^ 2 := by
      field_simp
    have harg : x - (R * t) / R = x - t := by
      field_simp
    rw [← hamp, harg]
    have hcancel : (R : ℂ) * ((R⁻¹ : ℝ) : ℂ) = 1 := by
      norm_cast
      exact mul_inv_cancel₀ hR.ne'
    calc
      _ = ((R : ℂ) * ((R⁻¹ : ℝ) : ℂ)) *
          projectionKernelSchwartz (R * t) *
            positiveDyadicBase ((x - t) / R) * phase ((x - t) ^ 2) := by ring
      _ = _ := by rw [hcancel]; ring
  have hq : (∫ u : ℝ, q u) = phase (x ^ 2) *
      ∫ u : ℝ, projectionKernelSchwartz u * phase (-2 * (x / R) * u) *
        positiveDyadicBase (x / R - u / R ^ 2) * phase (u ^ 2 / R ^ 2) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    unfold q
    have hsq : (x - u / R) ^ 2 =
        x ^ 2 + (-2 * (x / R) * u + u ^ 2 / R ^ 2) := by
      field_simp
      ring
    rw [hsq, phase_add, phase_add]
    ring
  unfold scaledProjectionConvolution
  rw [convolution_def]
  change (∫ t : ℝ,
    scaledProjectionKernel k t * quadraticScaleKernel R (x - t)) = _
  rw [hrow, Measure.integral_comp_mul_left]
  rw [abs_of_pos (inv_pos.mpr hR), Complex.real_smul, hq]
  unfold smoothProjectedQuadraticScaleKernel
  dsimp [R]
  ring

theorem continuous_quadraticScaleKernel_two_zpow (k : ℤ) :
    Continuous (quadraticScaleKernel ((2 : ℝ) ^ k)) := by
  have hamp : Continuous (positiveDyadicAmplitude k) :=
    continuous_iff_continuousAt.mpr
      (fun t ↦ (hasDerivAt_positiveDyadicAmplitude k t).continuousAt)
  have hkernel : Continuous
      (annularQuadraticKernel (positiveDyadicAmplitude k) 1) := by
    unfold annularQuadraticKernel phase
    fun_prop
  convert hkernel using 1
  funext x
  exact quadraticScaleKernel_two_zpow k x

theorem hasCompactSupport_quadraticScaleKernel_two_zpow (k : ℤ) :
    HasCompactSupport (quadraticScaleKernel ((2 : ℝ) ^ k)) := by
  let A : ℝ := (2 : ℝ) ^ (k - 1)
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (A / 4) A))
  intro x hx
  apply positiveDyadicAmplitude_support_subset k
  intro ha
  exact hx (by
    rw [quadraticScaleKernel_two_zpow]
    simp [annularQuadraticKernel, ha])

theorem integrable_quadraticScaleKernel_two_zpow (k : ℤ) :
    Integrable (quadraticScaleKernel ((2 : ℝ) ^ k)) :=
  (continuous_quadraticScaleKernel_two_zpow k).integrable_of_hasCompactSupport
    (hasCompactSupport_quadraticScaleKernel_two_zpow k)

theorem integrable_smoothProjectedQuadraticScaleKernel_two_zpow (k : ℤ) :
    Integrable (smoothProjectedQuadraticScaleKernel ((2 : ℝ) ^ k)) := by
  have heq : smoothProjectedQuadraticScaleKernel ((2 : ℝ) ^ k) =
      scaledProjectionConvolution k
        (quadraticScaleKernel ((2 : ℝ) ^ k)) := by
    funext x
    exact (scaledProjectionConvolution_quadraticScaleKernel_eq k x).symm
  rw [heq]
  exact (integrable_scaledProjectionKernel k).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_quadraticScaleKernel_two_zpow k)

theorem fourier_smoothProjectedQuadraticScaleKernel_two_zpow
    (k : ℤ) (ξ : ℝ) :
    𝓕 (smoothProjectedQuadraticScaleKernel ((2 : ℝ) ^ k)) ξ =
      KrauseLaceyQuadraticSmoothProjection.scaledAnnularFrequencyCutoff k ξ *
        𝓕 (quadraticScaleKernel ((2 : ℝ) ^ k)) ξ := by
  have heq : smoothProjectedQuadraticScaleKernel ((2 : ℝ) ^ k) =
      scaledProjectionConvolution k
        (quadraticScaleKernel ((2 : ℝ) ^ k)) := by
    funext x
    exact (scaledProjectionConvolution_quadraticScaleKernel_eq k x).symm
  rw [heq]
  change 𝓕
    (scaledProjectionKernel k ⋆[ContinuousLinearMap.mul ℂ ℂ]
      quadraticScaleKernel ((2 : ℝ) ^ k)) ξ = _
  rw [Real.fourier_mul_convolution_eq
    (integrable_scaledProjectionKernel k)
    (integrable_quadraticScaleKernel_two_zpow k),
    fourier_scaledProjectionKernel]

/-- The normalized explicit kernel formula for `(1-P_R)κ_R`. -/
def quadraticProjectionRemainder (R x : ℝ) : ℂ :=
  R⁻¹ * phase (x ^ 2) *
    ∫ u : ℝ, projectionKernelSchwartz u * phase (-2 * (x / R) * u) *
      projectionRemainderBracket R (x / R) u

/-- The fixed first weighted moment which controls the central remainder. -/
def projectionKernelFirstMoment : ℝ :=
  ∫ u : ℝ, ‖projectionKernelSchwartz u‖ * (|u| + u ^ 2)

/-- The fixed second weighted moment used for spatial decay. -/
def projectionKernelSecondMoment : ℝ :=
  ∫ u : ℝ, ‖projectionKernelSchwartz u‖ * u ^ 2

theorem projectionKernelFirstMoment_integrable :
    Integrable (fun u : ℝ ↦
      ‖projectionKernelSchwartz u‖ * (|u| + u ^ 2)) := by
  have h1 := projectionKernelSchwartz.integrable_pow_mul volume 1
  have h2 := projectionKernelSchwartz.integrable_pow_mul volume 2
  have h1' : Integrable (fun u : ℝ ↦ ‖projectionKernelSchwartz u‖ * |u|) := by
    simpa only [Real.norm_eq_abs, pow_one, mul_comm] using h1
  have h2' : Integrable (fun u : ℝ ↦ ‖projectionKernelSchwartz u‖ * u ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs, mul_comm] using h2
  have hsum : Integrable (fun u : ℝ ↦
      ‖projectionKernelSchwartz u‖ * |u| +
        ‖projectionKernelSchwartz u‖ * u ^ 2) := h1'.add h2'
  simpa only [mul_add] using hsum

theorem projectionKernelSecondMoment_integrable :
    Integrable (fun u : ℝ ↦ ‖projectionKernelSchwartz u‖ * u ^ 2) := by
  have h2 := projectionKernelSchwartz.integrable_pow_mul volume 2
  simpa only [Real.norm_eq_abs, sq_abs, mul_comm] using h2

theorem projectionKernelFirstMoment_nonneg : 0 ≤ projectionKernelFirstMoment := by
  exact integral_nonneg fun u ↦ mul_nonneg (norm_nonneg _) (by positivity)

theorem projectionKernelSecondMoment_nonneg : 0 ≤ projectionKernelSecondMoment := by
  exact integral_nonneg fun u ↦ mul_nonneg (norm_nonneg _) (sq_nonneg _)

/-- The displayed bracket formula is exactly the difference between the
scale kernel and its normalized smooth projection. -/
theorem quadraticProjectionRemainder_eq_sub (R x : ℝ) :
    quadraticProjectionRemainder R x =
      quadraticScaleKernel R x - smoothProjectedQuadraticScaleKernel R x := by
  let v : ℝ := x / R
  let f₀ : ℝ → ℂ := fun u ↦
    projectionKernelSchwartz u * phase (-2 * v * u) * positiveDyadicBase v
  let f₁ : ℝ → ℂ := fun u ↦
    projectionKernelSchwartz u * phase (-2 * v * u) *
      positiveDyadicBase (v - u / R ^ 2) * phase (u ^ 2 / R ^ 2)
  have hphase : Continuous phase := by
    unfold phase
    fun_prop
  have hamp : Continuous positiveDyadicBase := positiveDyadicBase_smooth.continuous
  have hfac₀ : AEStronglyMeasurable
      (fun u : ℝ ↦ phase (-2 * v * u) * positiveDyadicBase v) volume := by
    exact ((hphase.comp (continuous_const.mul continuous_id)).mul
      continuous_const).aestronglyMeasurable
  have hfac₁ : AEStronglyMeasurable
      (fun u : ℝ ↦ phase (-2 * v * u) *
        positiveDyadicBase (v - u / R ^ 2) * phase (u ^ 2 / R ^ 2)) volume := by
    exact (((hphase.comp (continuous_const.mul continuous_id)).mul
      (hamp.comp (continuous_const.sub
        (continuous_id.div_const (R ^ 2))))).mul
      (hphase.comp ((continuous_id.pow 2).div_const (R ^ 2)))).aestronglyMeasurable
  have hbound₀ : ∀ᵐ u : ℝ ∂volume,
      ‖phase (-2 * v * u) * positiveDyadicBase v‖ ≤
        positiveDyadicAmplitudeBound := by
    filter_upwards [] with u
    simpa only [norm_mul, norm_phase, one_mul] using norm_positiveDyadicBase_le v
  have hbound₁ : ∀ᵐ u : ℝ ∂volume,
      ‖phase (-2 * v * u) * positiveDyadicBase (v - u / R ^ 2) *
        phase (u ^ 2 / R ^ 2)‖ ≤ positiveDyadicAmplitudeBound := by
    filter_upwards [] with u
    simpa only [norm_mul, norm_phase, one_mul, mul_one] using
      norm_positiveDyadicBase_le (v - u / R ^ 2)
  have hf₀ : Integrable f₀ := by
    simpa only [f₀, mul_assoc] using
      projectionKernelSchwartz.integrable.mul_bdd hfac₀ hbound₀
  have hf₁ : Integrable f₁ := by
    simpa only [f₁, mul_assoc] using
      projectionKernelSchwartz.integrable.mul_bdd hfac₁ hbound₁
  have hintegral :
      (∫ u : ℝ, projectionKernelSchwartz u * phase (-2 * v * u) *
        projectionRemainderBracket R v u) =
        positiveDyadicBase v -
          ∫ u : ℝ, projectionKernelSchwartz u * phase (-2 * v * u) *
            positiveDyadicBase (v - u / R ^ 2) * phase (u ^ 2 / R ^ 2) := by
    calc
      _ = ∫ u : ℝ, f₀ u - f₁ u := by
        apply integral_congr_ae
        filter_upwards [] with u
        dsimp [f₀, f₁, projectionRemainderBracket]
        ring
      _ = (∫ u : ℝ, f₀ u) - ∫ u : ℝ, f₁ u := integral_sub hf₀ hf₁
      _ = positiveDyadicBase v - ∫ u : ℝ, f₁ u := by
        congr 1
        exact (positiveDyadicBase_eq_projectionKernel_integral v).symm
      _ = _ := rfl
  unfold quadraticProjectionRemainder quadraticScaleKernel
    smoothProjectedQuadraticScaleKernel
  change R⁻¹ * phase (x ^ 2) *
      (∫ u : ℝ, projectionKernelSchwartz u * phase (-2 * v * u) *
        projectionRemainderBracket R v u) = _
  rw [hintegral]
  dsimp [v]
  ring

theorem integrable_quadraticProjectionRemainder_two_zpow (k : ℤ) :
    Integrable (quadraticProjectionRemainder ((2 : ℝ) ^ k)) := by
  have heq : quadraticProjectionRemainder ((2 : ℝ) ^ k) =
      quadraticScaleKernel ((2 : ℝ) ^ k) -
        smoothProjectedQuadraticScaleKernel ((2 : ℝ) ^ k) := by
    funext x
    exact quadraticProjectionRemainder_eq_sub ((2 : ℝ) ^ k) x
  rw [heq]
  exact (integrable_quadraticScaleKernel_two_zpow k).sub
    (integrable_smoothProjectedQuadraticScaleKernel_two_zpow k)

theorem fourier_quadraticProjectionRemainder_two_zpow
    (k : ℤ) (ξ : ℝ) :
    𝓕 (quadraticProjectionRemainder ((2 : ℝ) ^ k)) ξ =
      (1 - KrauseLaceyQuadraticSmoothProjection.scaledAnnularFrequencyCutoff
        k ξ) * 𝓕 (quadraticScaleKernel ((2 : ℝ) ^ k)) ξ := by
  have heq : quadraticProjectionRemainder ((2 : ℝ) ^ k) =
      quadraticScaleKernel ((2 : ℝ) ^ k) -
        smoothProjectedQuadraticScaleKernel ((2 : ℝ) ^ k) := by
    funext x
    exact quadraticProjectionRemainder_eq_sub ((2 : ℝ) ^ k) x
  rw [heq]
  rw [Real.fourier_eq]
  simp only [Pi.sub_apply, smul_sub]
  rw [integral_sub]
  · change 𝓕 (quadraticScaleKernel ((2 : ℝ) ^ k)) ξ -
        𝓕 (smoothProjectedQuadraticScaleKernel ((2 : ℝ) ^ k)) ξ = _
    rw [fourier_smoothProjectedQuadraticScaleKernel_two_zpow]
    ring
  · rw [Real.fourierIntegral_convergent_iff]
    exact integrable_quadraticScaleKernel_two_zpow k
  · rw [Real.fourierIntegral_convergent_iff]
    exact integrable_smoothProjectedQuadraticScaleKernel_two_zpow k

/-- The genuine scale-`k` quadratic convolution output. -/
def quadraticScaleOutput (k : ℤ) (f : ℝ → ℂ) : ℝ → ℂ :=
  quadraticScaleKernel ((2 : ℝ) ^ k) ⋆[ContinuousLinearMap.mul ℂ ℂ] f

/-- The convolution output of the explicit projection remainder. -/
def quadraticProjectionRemainderOutput (k : ℤ) (f : ℝ → ℂ) : ℝ → ℂ :=
  quadraticProjectionRemainder ((2 : ℝ) ^ k) ⋆[ContinuousLinearMap.mul ℂ ℂ] f

/-- Adapter to the convolution orientation used by the localized quadratic
pieces in the direct proof. -/
theorem quadraticScaleOutput_eq_actual_convolution
    (k : ℤ) (f : ℝ → ℂ) (x : ℝ) :
    quadraticScaleOutput k f x =
      ∫ t, annularQuadraticKernel (positiveDyadicAmplitude k) 1 (x - t) * f t := by
  let F : ℝ → ℂ := fun t ↦
    quadraticScaleKernel ((2 : ℝ) ^ k) (x - t) * f t
  unfold quadraticScaleOutput
  rw [convolution_def]
  calc
    (∫ t, quadraticScaleKernel ((2 : ℝ) ^ k) t * f (x - t)) =
        ∫ t, F (x - t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      unfold F
      rw [show x - (x - t) = t by ring]
    _ = ∫ t, F t := MeasureTheory.integral_sub_left_eq_self F volume x
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      unfold F
      rw [quadraticScaleKernel_two_zpow]

theorem quadraticProjectionRemainderOutput_eq_actual_convolution
    (k : ℤ) (f : ℝ → ℂ) (x : ℝ) :
    quadraticProjectionRemainderOutput k f x =
      ∫ t, quadraticProjectionRemainder ((2 : ℝ) ^ k) (x - t) * f t := by
  let F : ℝ → ℂ := fun t ↦
    quadraticProjectionRemainder ((2 : ℝ) ^ k) (x - t) * f t
  unfold quadraticProjectionRemainderOutput
  rw [convolution_def]
  calc
    (∫ t, quadraticProjectionRemainder ((2 : ℝ) ^ k) t * f (x - t)) =
        ∫ t, F (x - t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      unfold F
      rw [show x - (x - t) = t by ring]
    _ = ∫ t, F t := MeasureTheory.integral_sub_left_eq_self F volume x
    _ = _ := rfl

theorem integrable_quadraticScaleOutput (k : ℤ) {f : ℝ → ℂ}
    (hf : Integrable f) : Integrable (quadraticScaleOutput k f) :=
  (integrable_quadraticScaleKernel_two_zpow k).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) hf

theorem integrable_quadraticProjectionRemainderOutput
    (k : ℤ) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (quadraticProjectionRemainderOutput k f) :=
  (integrable_quadraticProjectionRemainder_two_zpow k).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) hf

/-- Concrete `L²` projection-error identity for an actual scale output.
Both `MemLp` premises are properties of the displayed convolution outputs,
not abstract projection assumptions. -/
theorem quadraticScaleOutputL2_sub_annularProjectionL2_eq_remainderOutputL2
    (k : ℤ) {f : ℝ → ℂ} (hf : Integrable f)
    (hscale₂ : MemLp (quadraticScaleOutput k f) 2 volume)
    (hrem₂ : MemLp (quadraticProjectionRemainderOutput k f) 2 volume) :
    hscale₂.toLp (quadraticScaleOutput k f) -
        KrauseLaceyQuadraticSmoothProjection.annularProjectionL2 k
          (hscale₂.toLp (quadraticScaleOutput k f)) =
      hrem₂.toLp (quadraticProjectionRemainderOutput k f) := by
  have hscale₁ := integrable_quadraticScaleOutput k hf
  have hrem₁ := integrable_quadraticProjectionRemainderOutput k hf
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [map_sub,
    KrauseLaceyQuadraticSmoothProjection.fourier_annularProjectionL2]
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_sub
      (Lp.fourierTransformₗᵢ ℝ ℂ
        (hscale₂.toLp (quadraticScaleOutput k f)))
      (KrauseLaceyQuadraticSmoothProjection.annularMultiplierL2 k
        (hscale₂.toLp (quadraticScaleOutput k f))),
    HilbertRepresentativeBridge.fourier_toLp_ae_eq hscale₁ hscale₂,
    (KrauseLaceyQuadraticSmoothProjection.memLp_annularFourierMultiplier k
      (hscale₂.toLp (quadraticScaleOutput k f))).coeFn_toLp,
    HilbertRepresentativeBridge.fourier_toLp_ae_eq hrem₁ hrem₂
  ] with ξ hsubFourier hscaleFourier hmult hremFourier
  have hmult' :
      (KrauseLaceyQuadraticSmoothProjection.annularMultiplierL2 k
        (hscale₂.toLp (quadraticScaleOutput k f)) : ℝ → ℂ) ξ =
      KrauseLaceyQuadraticSmoothProjection.annularFourierMultiplier k
        (hscale₂.toLp (quadraticScaleOutput k f)) ξ := by
    simpa only [KrauseLaceyQuadraticSmoothProjection.annularMultiplierL2] using hmult
  rw [hsubFourier]
  change
    (Lp.fourierTransformₗᵢ ℝ ℂ
      (hscale₂.toLp (quadraticScaleOutput k f))) ξ -
      (KrauseLaceyQuadraticSmoothProjection.annularMultiplierL2 k
        (hscale₂.toLp (quadraticScaleOutput k f))) ξ =
    (Lp.fourierTransformₗᵢ ℝ ℂ
      (hrem₂.toLp (quadraticProjectionRemainderOutput k f))) ξ
  rw [hscaleFourier, hmult', hremFourier]
  unfold KrauseLaceyQuadraticSmoothProjection.annularFourierMultiplier
  rw [hscaleFourier]
  unfold quadraticScaleOutput quadraticProjectionRemainderOutput
  rw [Real.fourier_mul_convolution_eq
      (integrable_quadraticScaleKernel_two_zpow k) hf,
    Real.fourier_mul_convolution_eq
      (integrable_quadraticProjectionRemainder_two_zpow k) hf,
    fourier_quadraticProjectionRemainder_two_zpow]
  ring

/-- Representative form of the preceding identity. This is the a.e.
statement consumed by the a.e. prefix-control interface. -/
theorem quadraticScaleOutput_sub_annularProjection_ae
    (k : ℤ) {f : ℝ → ℂ} (hf : Integrable f)
    (hscale₂ : MemLp (quadraticScaleOutput k f) 2 volume)
    (hrem₂ : MemLp (quadraticProjectionRemainderOutput k f) 2 volume) :
    (fun x ↦ (hscale₂.toLp (quadraticScaleOutput k f)) x -
      (KrauseLaceyQuadraticSmoothProjection.annularProjectionL2 k
        (hscale₂.toLp (quadraticScaleOutput k f))) x) =ᵐ[volume]
      quadraticProjectionRemainderOutput k f := by
  have heq :=
    quadraticScaleOutputL2_sub_annularProjectionL2_eq_remainderOutputL2
      k hf hscale₂ hrem₂
  have hsub := Lp.coeFn_sub
    (hscale₂.toLp (quadraticScaleOutput k f))
    (KrauseLaceyQuadraticSmoothProjection.annularProjectionL2 k
      (hscale₂.toLp (quadraticScaleOutput k f)))
  filter_upwards [hsub, hrem₂.coeFn_toLp] with x hx hrem
  rw [← heq] at hrem
  exact hx.symm.trans hrem

/-- The fixed amplitude is globally Lipschitz with its already constructed
derivative bound. -/
theorem norm_positiveDyadicBase_sub_le (v w : ℝ) :
    ‖positiveDyadicBase v - positiveDyadicBase w‖ ≤
      positiveDyadicAmplitudeBound * |v - w| := by
  have hdiff : ∀ z : ℝ, DifferentiableAt ℝ positiveDyadicBase z :=
    fun z ↦ positiveDyadicBase_smooth.differentiable (by norm_num) z
  simpa only [Real.norm_eq_abs] using
    (convex_univ.norm_image_sub_le_of_norm_deriv_le
      (s := (Set.univ : Set ℝ)) (f := positiveDyadicBase)
      (C := positiveDyadicAmplitudeBound)
      (fun z _ ↦ hdiff z) (fun z _ ↦ norm_deriv_positiveDyadicBase_le z)
      (Set.mem_univ w) (Set.mem_univ v))

/-- The bracket gains the exact `R⁻²` factor required in the paper. -/
theorem norm_projectionRemainderBracket_le
    {R : ℝ} (hR : 1 ≤ R) (v u : ℝ) :
    ‖projectionRemainderBracket R v u‖ ≤
      (positiveDyadicAmplitudeBound * (1 + 2 * Real.pi)) / R ^ 2 *
        (|u| + u ^ 2) := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hRpos
  let w : ℝ := v - u / R ^ 2
  have hdiff : ‖positiveDyadicBase v - positiveDyadicBase w‖ ≤
      positiveDyadicAmplitudeBound * (|u| / R ^ 2) := by
    calc
      ‖positiveDyadicBase v - positiveDyadicBase w‖ ≤
          positiveDyadicAmplitudeBound * |v - w| :=
        norm_positiveDyadicBase_sub_le v w
      _ = positiveDyadicAmplitudeBound * (|u| / R ^ 2) := by
        dsimp [w]
        rw [show v - (v - u / R ^ 2) = u / R ^ 2 by ring,
          abs_div, abs_of_pos hR2]
  have hphase : ‖1 - phase (u ^ 2 / R ^ 2)‖ ≤
      2 * Real.pi * (u ^ 2 / R ^ 2) := by
    rw [norm_sub_rev]
    have h := norm_phase_sub_one_le (u ^ 2 / R ^ 2)
    simpa only [abs_div, abs_of_nonneg (sq_nonneg u), abs_of_pos hR2] using h
  have hamp : ‖positiveDyadicBase w‖ ≤ positiveDyadicAmplitudeBound :=
    norm_positiveDyadicBase_le w
  have hD : 0 ≤ positiveDyadicAmplitudeBound := positiveDyadicAmplitudeBound_nonneg
  calc
    ‖projectionRemainderBracket R v u‖ =
        ‖(positiveDyadicBase v - positiveDyadicBase w) +
          positiveDyadicBase w * (1 - phase (u ^ 2 / R ^ 2))‖ := by
      unfold projectionRemainderBracket
      dsimp [w]
      congr 1
      ring
    _ ≤ ‖positiveDyadicBase v - positiveDyadicBase w‖ +
        ‖positiveDyadicBase w * (1 - phase (u ^ 2 / R ^ 2))‖ := norm_add_le _ _
    _ ≤ positiveDyadicAmplitudeBound * (|u| / R ^ 2) +
        positiveDyadicAmplitudeBound * (2 * Real.pi * (u ^ 2 / R ^ 2)) := by
      gcongr
      rw [norm_mul]
      exact mul_le_mul hamp hphase (norm_nonneg _) hD
    _ ≤ (positiveDyadicAmplitudeBound * (1 + 2 * Real.pi)) / R ^ 2 *
        (|u| + u ^ 2) := by
      have huabs : 0 ≤ |u| := abs_nonneg u
      have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
      rw [show positiveDyadicAmplitudeBound * (|u| / R ^ 2) +
          positiveDyadicAmplitudeBound * (2 * Real.pi * (u ^ 2 / R ^ 2)) =
          (positiveDyadicAmplitudeBound / R ^ 2) *
            (|u| + 2 * Real.pi * u ^ 2) by field_simp]
      rw [show (positiveDyadicAmplitudeBound * (1 + 2 * Real.pi)) / R ^ 2 *
          (|u| + u ^ 2) = (positiveDyadicAmplitudeBound / R ^ 2) *
            ((1 + 2 * Real.pi) * (|u| + u ^ 2)) by ring]
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hD hR2.le)
      nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) huabs) zero_le_one]

/-- The constant in the uniform `R⁻³` estimate. -/
def projectionRemainderCentralConstant : ℝ :=
  positiveDyadicAmplitudeBound * (1 + 2 * Real.pi) *
    projectionKernelFirstMoment

theorem projectionRemainderCentralConstant_nonneg :
    0 ≤ projectionRemainderCentralConstant := by
  unfold projectionRemainderCentralConstant
  exact mul_nonneg
    (mul_nonneg positiveDyadicAmplitudeBound_nonneg (by positivity))
    projectionKernelFirstMoment_nonneg

/-- The first half of the remainder estimate: the explicit bracket gives a
uniform gain of two powers of the physical scale. -/
theorem norm_quadraticProjectionRemainder_le_central
    {R : ℝ} (hR : 1 ≤ R) (x : ℝ) :
    ‖quadraticProjectionRemainder R x‖ ≤
      projectionRemainderCentralConstant * R⁻¹ ^ 3 := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let C₀ : ℝ := positiveDyadicAmplitudeBound * (1 + 2 * Real.pi)
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    exact mul_nonneg positiveDyadicAmplitudeBound_nonneg (by positivity)
  have hmajorant : Integrable (fun u : ℝ ↦
      (C₀ / R ^ 2) *
        (‖projectionKernelSchwartz u‖ * (|u| + u ^ 2))) :=
    projectionKernelFirstMoment_integrable.const_mul (C₀ / R ^ 2)
  have hinner :
      ‖∫ u : ℝ, projectionKernelSchwartz u *
          phase (-2 * (x / R) * u) *
          projectionRemainderBracket R (x / R) u‖ ≤
        (C₀ / R ^ 2) * projectionKernelFirstMoment := by
    calc
      _ ≤ ∫ u : ℝ, (C₀ / R ^ 2) *
          (‖projectionKernelSchwartz u‖ * (|u| + u ^ 2)) := by
        apply norm_integral_le_of_norm_le hmajorant
        filter_upwards [] with u
        rw [norm_mul, norm_mul, norm_phase, mul_one]
        have hb := norm_projectionRemainderBracket_le hR (x / R) u
        change ‖projectionKernelSchwartz u‖ *
            ‖projectionRemainderBracket R (x / R) u‖ ≤ _
        calc
          _ ≤ ‖projectionKernelSchwartz u‖ *
              ((C₀ / R ^ 2) * (|u| + u ^ 2)) :=
            mul_le_mul_of_nonneg_left hb (norm_nonneg _)
          _ = _ := by ring
      _ = (C₀ / R ^ 2) * projectionKernelFirstMoment := by
        rw [integral_const_mul]
        rfl
  rw [quadraticProjectionRemainder, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_inv, abs_of_pos hRpos, norm_phase, mul_one]
  calc
    R⁻¹ * ‖∫ u : ℝ, projectionKernelSchwartz u *
        phase (-2 * (x / R) * u) *
        projectionRemainderBracket R (x / R) u‖ ≤
      R⁻¹ * ((C₀ / R ^ 2) * projectionKernelFirstMoment) :=
        mul_le_mul_of_nonneg_left hinner (inv_nonneg.mpr hRpos.le)
    _ = projectionRemainderCentralConstant * R⁻¹ ^ 3 := by
      dsimp [C₀, projectionRemainderCentralConstant]
      field_simp

theorem positiveDyadicBase_eq_zero_of_one_le_abs
    {v : ℝ} (hv : 1 ≤ |v|) : positiveDyadicBase v = 0 := by
  by_contra hne
  have hs := positiveDyadicBase_support_subset hne
  have hv0 : 0 ≤ v := by linarith [hs.1]
  rw [abs_of_nonneg hv0] at hv
  linarith [hs.2]

/-- Outside the fixed amplitude support, a nonzero translated amplitude
forces the integration variable to be large. -/
theorem scale_sq_mul_v_sq_le_four_mul_u_sq_of_translatedAmplitude_ne_zero
    {R v u : ℝ} (hR : 1 ≤ R) (hv : 1 ≤ |v|)
    (ha : positiveDyadicBase (v - u / R ^ 2) ≠ 0) :
    R ^ 4 * v ^ 2 ≤ 4 * u ^ 2 := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hRpos
  have hs := positiveDyadicBase_support_subset ha
  have hw0 : 0 ≤ v - u / R ^ 2 := by linarith [hs.1]
  have hwabs : |v - u / R ^ 2| ≤ 1 / 2 := by
    rw [abs_of_nonneg hw0]
    exact hs.2
  have htri : |v| ≤ |v - u / R ^ 2| + |u / R ^ 2| := by
    calc
      |v| = |(v - u / R ^ 2) + u / R ^ 2| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hhalf : |v| / 2 ≤ |u| / R ^ 2 := by
    rw [abs_div, abs_of_pos hR2] at htri
    linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ |v| / 2) hhalf 2
  rw [div_pow, div_pow, sq_abs, sq_abs] at hsq
  field_simp at hsq
  nlinarith

/-- The support geometry converts the crude amplitude bound into the
second-moment majorant used for spatial decay. -/
theorem norm_projectionRemainderBracket_le_tail
    {R v : ℝ} (hR : 1 ≤ R) (hv : 1 ≤ |v|) (u : ℝ) :
    ‖projectionRemainderBracket R v u‖ ≤
      (4 * positiveDyadicAmplitudeBound / (R ^ 4 * v ^ 2)) * u ^ 2 := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hvne : v ≠ 0 := by intro hv0; subst v; norm_num at hv
  have hvpos : 0 < v ^ 2 := sq_pos_of_ne_zero hvne
  have hden : 0 < R ^ 4 * v ^ 2 := mul_pos (pow_pos hRpos 4) hvpos
  have hz := positiveDyadicBase_eq_zero_of_one_le_abs hv
  by_cases ha : positiveDyadicBase (v - u / R ^ 2) = 0
  · rw [projectionRemainderBracket, hz, ha]
    simp only [zero_mul, sub_zero, norm_zero]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg)
        hden.le)
      (sq_nonneg u)
  · have hgeom :=
      scale_sq_mul_v_sq_le_four_mul_u_sq_of_translatedAmplitude_ne_zero hR hv ha
    have hfactor : 1 ≤ 4 * u ^ 2 / (R ^ 4 * v ^ 2) := by
      rw [le_div_iff₀ hden]
      simpa only [one_mul] using hgeom
    calc
      ‖projectionRemainderBracket R v u‖ =
          ‖positiveDyadicBase (v - u / R ^ 2)‖ := by
        rw [projectionRemainderBracket, hz, zero_sub, norm_neg, norm_mul,
          norm_phase, mul_one]
      _ ≤ positiveDyadicAmplitudeBound :=
        norm_positiveDyadicBase_le (v - u / R ^ 2)
      _ = positiveDyadicAmplitudeBound * 1 := by ring
      _ ≤ positiveDyadicAmplitudeBound *
          (4 * u ^ 2 / (R ^ 4 * v ^ 2)) :=
        mul_le_mul_of_nonneg_left hfactor positiveDyadicAmplitudeBound_nonneg
      _ = (4 * positiveDyadicAmplitudeBound / (R ^ 4 * v ^ 2)) * u ^ 2 := by
        field_simp

/-- The fixed constant in the spatial-tail estimate. -/
def projectionRemainderTailConstant : ℝ :=
  4 * positiveDyadicAmplitudeBound * projectionKernelSecondMoment

theorem projectionRemainderTailConstant_nonneg :
    0 ≤ projectionRemainderTailConstant := by
  unfold projectionRemainderTailConstant
  exact mul_nonneg
    (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg)
    projectionKernelSecondMoment_nonneg

/-- The support of the amplitude gives two powers of spatial decay. This
version retains the stronger `R⁻⁵` factor delivered by the proof. -/
theorem norm_quadraticProjectionRemainder_le_tail
    {R : ℝ} (hR : 1 ≤ R) {x : ℝ} (hx : 1 ≤ |x / R|) :
    ‖quadraticProjectionRemainder R x‖ ≤
      projectionRemainderTailConstant * R⁻¹ ^ 5 * (x / R)⁻¹ ^ 2 := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hvne : x / R ≠ 0 := by
    intro hv0
    rw [hv0, abs_zero] at hx
    norm_num at hx
  have hv2 : 0 < (x / R) ^ 2 := sq_pos_of_ne_zero hvne
  let C₁ : ℝ := 4 * positiveDyadicAmplitudeBound
  have hC₁ : 0 ≤ C₁ := by
    dsimp [C₁]
    exact mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg
  have hden : 0 < R ^ 4 * (x / R) ^ 2 :=
    mul_pos (pow_pos hRpos 4) hv2
  have hmajorant : Integrable (fun u : ℝ ↦
      (C₁ / (R ^ 4 * (x / R) ^ 2)) *
        (‖projectionKernelSchwartz u‖ * u ^ 2)) :=
    projectionKernelSecondMoment_integrable.const_mul
      (C₁ / (R ^ 4 * (x / R) ^ 2))
  have hinner :
      ‖∫ u : ℝ, projectionKernelSchwartz u *
          phase (-2 * (x / R) * u) *
          projectionRemainderBracket R (x / R) u‖ ≤
        (C₁ / (R ^ 4 * (x / R) ^ 2)) *
          projectionKernelSecondMoment := by
    calc
      _ ≤ ∫ u : ℝ, (C₁ / (R ^ 4 * (x / R) ^ 2)) *
          (‖projectionKernelSchwartz u‖ * u ^ 2) := by
        apply norm_integral_le_of_norm_le hmajorant
        filter_upwards [] with u
        rw [norm_mul, norm_mul, norm_phase, mul_one]
        have hb := norm_projectionRemainderBracket_le_tail hR hx u
        change ‖projectionKernelSchwartz u‖ *
            ‖projectionRemainderBracket R (x / R) u‖ ≤ _
        calc
          _ ≤ ‖projectionKernelSchwartz u‖ *
              ((C₁ / (R ^ 4 * (x / R) ^ 2)) * u ^ 2) :=
            mul_le_mul_of_nonneg_left hb (norm_nonneg _)
          _ = _ := by ring
      _ = (C₁ / (R ^ 4 * (x / R) ^ 2)) *
          projectionKernelSecondMoment := by
        rw [integral_const_mul]
        rfl
  rw [quadraticProjectionRemainder, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_inv, abs_of_pos hRpos, norm_phase, mul_one]
  calc
    R⁻¹ * ‖∫ u : ℝ, projectionKernelSchwartz u *
        phase (-2 * (x / R) * u) *
        projectionRemainderBracket R (x / R) u‖ ≤
      R⁻¹ * ((C₁ / (R ^ 4 * (x / R) ^ 2)) *
        projectionKernelSecondMoment) :=
      mul_le_mul_of_nonneg_left hinner (inv_nonneg.mpr hRpos.le)
    _ = projectionRemainderTailConstant * R⁻¹ ^ 5 * (x / R)⁻¹ ^ 2 := by
      dsimp [C₁, projectionRemainderTailConstant]
      field_simp

private theorem one_le_four_mul_one_add_abs_inv_sq_of_abs_le_one
    {v : ℝ} (hv : |v| ≤ 1) :
    1 ≤ 4 * (1 + |v|)⁻¹ ^ 2 := by
  have hp : 0 < 1 + |v| := by positivity
  rw [inv_pow]
  rw [le_mul_inv_iff₀ (pow_pos hp 2)]
  nlinarith [abs_nonneg v]

private theorem inv_sq_le_four_mul_one_add_abs_inv_sq_of_one_le_abs
    {v : ℝ} (hv : 1 ≤ |v|) :
    v⁻¹ ^ 2 ≤ 4 * (1 + |v|)⁻¹ ^ 2 := by
  have hvne : v ≠ 0 := by intro hv0; subst v; norm_num at hv
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hvne
  have hp : 0 < (1 + |v|) ^ 2 := pow_pos (by positivity) 2
  rw [inv_pow, inv_pow]
  rw [← mul_one (v ^ 2)⁻¹, inv_mul_le_iff₀ hv2]
  rw [show v ^ 2 * (4 * ((1 + |v|) ^ 2)⁻¹) =
      (4 * v ^ 2) * ((1 + |v|) ^ 2)⁻¹ by ring]
  rw [le_mul_inv_iff₀ hp]
  have hadd : 1 + |v| ≤ 2 * |v| := by linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |v|) hadd 2
  nlinarith [sq_abs v]

/-- A single fixed constant for the full spatially decaying estimate. -/
def projectionRemainderConstant : ℝ :=
  4 * max projectionRemainderCentralConstant projectionRemainderTailConstant

theorem projectionRemainderConstant_nonneg : 0 ≤ projectionRemainderConstant := by
  unfold projectionRemainderConstant
  exact mul_nonneg (by norm_num) <|
    projectionRemainderCentralConstant_nonneg.trans (le_max_left _ _)

/-- The explicit smooth-projection remainder bound from the direct
quadratic proof. -/
theorem norm_quadraticProjectionRemainder_le
    {R : ℝ} (hR : 1 ≤ R) (x : ℝ) :
    ‖quadraticProjectionRemainder R x‖ ≤
      projectionRemainderConstant * R⁻¹ ^ 3 *
        (1 + |x / R|)⁻¹ ^ 2 := by
  let v : ℝ := x / R
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr hRpos.le
  have hmax : 0 ≤ max projectionRemainderCentralConstant
      projectionRemainderTailConstant :=
    projectionRemainderCentralConstant_nonneg.trans (le_max_left _ _)
  rcases le_total |v| 1 with hv | hv
  · have hc := norm_quadraticProjectionRemainder_le_central hR x
    have hfac := one_le_four_mul_one_add_abs_inv_sq_of_abs_le_one hv
    calc
      ‖quadraticProjectionRemainder R x‖ ≤
          projectionRemainderCentralConstant * R⁻¹ ^ 3 := hc
      _ ≤ max projectionRemainderCentralConstant projectionRemainderTailConstant *
          R⁻¹ ^ 3 := by
        gcongr
        exact le_max_left _ _
      _ = (max projectionRemainderCentralConstant projectionRemainderTailConstant *
          R⁻¹ ^ 3) * 1 := by ring
      _ ≤ (max projectionRemainderCentralConstant projectionRemainderTailConstant *
          R⁻¹ ^ 3) * (4 * (1 + |v|)⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_left hfac (mul_nonneg hmax (pow_nonneg hRinv 3))
      _ = projectionRemainderConstant * R⁻¹ ^ 3 *
          (1 + |x / R|)⁻¹ ^ 2 := by
        dsimp [v, projectionRemainderConstant]
        ring
  · have ht := norm_quadraticProjectionRemainder_le_tail hR (x := x) hv
    have hscale : R⁻¹ ^ 5 ≤ R⁻¹ ^ 3 := by
      simpa only [inv_pow] using inv_pow_le_inv_pow_of_le hR (by omega : 3 ≤ 5)
    have hspace := inv_sq_le_four_mul_one_add_abs_inv_sq_of_one_le_abs hv
    calc
      ‖quadraticProjectionRemainder R x‖ ≤
          projectionRemainderTailConstant * R⁻¹ ^ 5 * v⁻¹ ^ 2 := by
        simpa only [v] using ht
      _ ≤ projectionRemainderTailConstant * R⁻¹ ^ 3 * v⁻¹ ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hscale projectionRemainderTailConstant_nonneg)
          (sq_nonneg v⁻¹)
      _ ≤ projectionRemainderTailConstant * R⁻¹ ^ 3 *
          (4 * (1 + |v|)⁻¹ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hspace
          (mul_nonneg projectionRemainderTailConstant_nonneg (pow_nonneg hRinv 3))
      _ ≤ max projectionRemainderCentralConstant projectionRemainderTailConstant *
          R⁻¹ ^ 3 * (4 * (1 + |v|)⁻¹ ^ 2) := by
        gcongr
        exact le_max_right _ _
      _ = projectionRemainderConstant * R⁻¹ ^ 3 *
          (1 + |x / R|)⁻¹ ^ 2 := by
        dsimp [v, projectionRemainderConstant]
        ring

/-- A Cauchy weight convenient for integrating the spatial remainder
decay. -/
def quadraticRemainderWeight (R x : ℝ) : ℝ :=
  (1 + (x / R) ^ 2)⁻¹

/-- Integrable Cauchy-weight form of the explicit pointwise remainder
estimate. -/
theorem norm_quadraticProjectionRemainder_le_weight
    {R : ℝ} (hR : 1 ≤ R) (x : ℝ) :
    ‖quadraticProjectionRemainder R x‖ ≤
      projectionRemainderConstant * R⁻¹ ^ 3 *
        quadraticRemainderWeight R x := by
  have hr := norm_quadraticProjectionRemainder_le hR x
  have hden : 1 + (x / R) ^ 2 ≤ (1 + |x / R|) ^ 2 := by
    nlinarith [abs_nonneg (x / R), sq_abs (x / R)]
  have hinv : (1 + |x / R|)⁻¹ ^ 2 ≤ (1 + (x / R) ^ 2)⁻¹ := by
    rw [inv_pow]
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hden
  exact hr.trans <| mul_le_mul_of_nonneg_left hinv <|
    mul_nonneg projectionRemainderConstant_nonneg (by positivity)

theorem integrable_quadraticRemainderWeight {R : ℝ} (hR : 0 < R) :
    Integrable (quadraticRemainderWeight R) := by
  change Integrable (fun x : ℝ ↦ (1 + (x / R) ^ 2)⁻¹)
  exact integrable_inv_one_add_sq.comp_div hR.ne'

theorem integrable_quadraticRemainderWeight_sub_left
    {R : ℝ} (hR : 0 < R) (x : ℝ) :
    Integrable (fun t ↦ quadraticRemainderWeight R (x - t)) := by
  exact (integrable_quadraticRemainderWeight hR).comp_sub_left x

theorem integral_quadraticRemainderWeight_sub_left
    {R : ℝ} (hR : 0 < R) (x : ℝ) :
    (∫ t : ℝ, quadraticRemainderWeight R (x - t)) = R * Real.pi := by
  rw [MeasureTheory.integral_sub_left_eq_self]
  change (∫ t : ℝ, (fun y : ℝ ↦ (1 + y ^ 2)⁻¹) (t / R)) =
    R * Real.pi
  calc
    (∫ t : ℝ, (fun y : ℝ ↦ (1 + y ^ 2)⁻¹) (t / R)) =
        |R| • ∫ y : ℝ, (1 + y ^ 2)⁻¹ :=
      Measure.integral_comp_div (fun y : ℝ ↦ (1 + y ^ 2)⁻¹) R
    _ = R * Real.pi := by
      rw [abs_of_pos hR, integral_univ_inv_one_add_sq]
      rfl

theorem quadraticRemainderWeight_sub_le_two_mul
    {R : ℝ} (hR : 1 ≤ R) {x t z : ℝ} (htz : |t - z| ≤ 1 / 2) :
    quadraticRemainderWeight R (x - t) ≤
      2 * quadraticRemainderWeight R (x - z) := by
  let a : ℝ := (x - t) / R
  let b : ℝ := (x - z) / R
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hd : |b - a| ≤ 1 / 2 := by
    dsimp [a, b]
    rw [show (x - z) / R - (x - t) / R = (t - z) / R by ring,
      abs_div, abs_of_pos hRpos]
    rw [div_le_iff₀ hRpos]
    nlinarith
  have hdsq : (b - a) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have hp := pow_le_pow_left₀ (abs_nonneg (b - a)) hd 2
    simpa only [sq_abs] using hp
  have hden : 1 + b ^ 2 ≤ 2 * (1 + a ^ 2) := by
    nlinarith [sq_nonneg (2 * a - b)]
  have ha : 0 < 1 + a ^ 2 := by positivity
  have hb : 0 < 1 + b ^ 2 := by positivity
  unfold quadraticRemainderWeight
  change (1 + a ^ 2)⁻¹ ≤ 2 * (1 + b ^ 2)⁻¹
  calc
    (1 + a ^ 2)⁻¹ = 1 / (1 + a ^ 2) := by rw [one_div]
    _ ≤ 2 / (1 + b ^ 2) :=
      (div_le_div_iff₀ ha hb).2 (by simpa using hden)
    _ = 2 * (1 + b ^ 2)⁻¹ := by ring

/-- Local mass on the centered unit interval, in the exact form supplied
by the direct quadratic decomposition. -/
def centeredUnitMass (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  ∫ t in Set.Icc (x - 1 / 2) (x + 1 / 2), ‖f t‖

/-- A Cauchy weight at scale `R ≥ 1` integrates against any input with
uniform centered-unit mass at most `M` with size `O(R M)`. -/
theorem integral_weight_mul_norm_le_of_centeredUnitMass
    {R : ℝ} (hR : 1 ≤ R) {f : ℝ → ℂ} (hf : Integrable f)
    {M : ℝ} (hlocal : ∀ z, centeredUnitMass f z ≤ M)
    (x : ℝ) :
    (∫ t : ℝ, quadraticRemainderWeight R (x - t) * ‖f t‖) ≤
      2 * (R * Real.pi) * M := by
  let q : ℝ → ℝ := fun z ↦ quadraticRemainderWeight R (x - z)
  let g : ℝ → ℝ := fun t ↦ ‖f t‖
  let S : Set (ℝ × ℝ) := {p | |p.1 - p.2| ≤ (1 / 2 : ℝ)}
  let H : ℝ × ℝ → ℝ := S.indicator (fun p ↦ q p.2 * g p.1)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hq : Integrable q := integrable_quadraticRemainderWeight_sub_left hRpos x
  have hg : Integrable g := hf.norm
  have hq_nonneg (z : ℝ) : 0 ≤ q z := by
    dsimp [q, quadraticRemainderWeight]
    positivity
  have hg_nonneg (t : ℝ) : 0 ≤ g t := norm_nonneg _
  have hq_norm_le_one (z : ℝ) : ‖q z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hq_nonneg z)]
    dsimp [q, quadraticRemainderWeight]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ((x - z) / R)])
  have hS : MeasurableSet S := by
    dsimp [S]
    exact isClosed_le (continuous_fst.sub continuous_snd).abs continuous_const |>.measurableSet
  have hprod : Integrable (fun p : ℝ × ℝ ↦ q p.2 * g p.1)
      (volume.prod volume) := by
    simpa only [mul_comm] using hg.mul_prod hq
  have hH : Integrable H (volume.prod volume) := by
    exact hprod.indicator hS
  have hinner_left (t : ℝ) :
      (∫ z : ℝ, H (t, z)) =
        ∫ z in Set.Icc (t - 1 / 2) (t + 1 / 2), q z * g t := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [] with z
    have heq : z ∈ Set.Icc (t - 1 / 2) (t + 1 / 2) ↔
        |t - z| ≤ (1 / 2 : ℝ) := by
      rw [Set.mem_Icc, abs_le]
      constructor <;> intro hz <;> constructor <;> linarith [hz.1, hz.2]
    simp only [H, S, g, Set.indicator_apply, Set.mem_ofPred_eq, heq]
  have hinner_right (z : ℝ) :
      (∫ t : ℝ, H (t, z)) = q z * centeredUnitMass f z := by
    rw [centeredUnitMass, ← integral_const_mul,
      ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [] with t
    have heq : t ∈ Set.Icc (z - 1 / 2) (z + 1 / 2) ↔
        |t - z| ≤ (1 / 2 : ℝ) := by
      rw [Set.mem_Icc, abs_le]
      constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]
    simp only [H, S, g, Set.indicator_apply, Set.mem_ofPred_eq, heq]
  have hfixed (t : ℝ) :
      q t * g t ≤ 2 * ∫ z : ℝ, H (t, z) := by
    have hright : IntegrableOn (fun z : ℝ ↦ 2 * q z * g t)
        (Set.Icc (t - 1 / 2) (t + 1 / 2)) := by
      have hi := hq.const_mul (2 * g t)
      apply Integrable.integrableOn
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hi
    calc
      q t * g t = ∫ _z : ℝ in Set.Icc (t - 1 / 2) (t + 1 / 2), q t * g t := by
        rw [setIntegral_const]
        change q t * g t =
          (volume (Set.Icc (t - 1 / 2) (t + 1 / 2))).toReal * (q t * g t)
        rw [Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num :
          0 ≤ t + 1 / 2 - (t - 1 / 2))]
        ring
      _ ≤ ∫ z : ℝ in Set.Icc (t - 1 / 2) (t + 1 / 2), 2 * q z * g t := by
        apply setIntegral_mono_on
          (integrableOn_const measure_Icc_lt_top.ne)
          hright measurableSet_Icc
        intro z hz
        have htz : |t - z| ≤ (1 / 2 : ℝ) := by
          rw [abs_le]
          constructor <;> linarith [hz.1, hz.2]
        exact mul_le_mul_of_nonneg_right
          (quadraticRemainderWeight_sub_le_two_mul hR htz) (hg_nonneg t)
      _ = 2 * ∫ z : ℝ in Set.Icc (t - 1 / 2) (t + 1 / 2), q z * g t := by
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      _ = 2 * ∫ z : ℝ, H (t, z) := by rw [hinner_left]
  have hqg : Integrable (fun t : ℝ ↦ q t * g t) := by
    have hi := hg.bdd_mul hq.aestronglyMeasurable
      (ae_of_all _ hq_norm_le_one)
    simpa only [mul_comm] using hi
  have hleftInner : Integrable (fun t : ℝ ↦ ∫ z : ℝ, H (t, z)) :=
    hH.integral_prod_left
  have hrightInner : Integrable (fun z : ℝ ↦ ∫ t : ℝ, H (t, z)) :=
    hH.integral_prod_right
  have hqmass : Integrable (fun z : ℝ ↦ q z * centeredUnitMass f z) := by
    apply hrightInner.congr
    filter_upwards [] with z
    exact hinner_right z
  have hqM : Integrable (fun z : ℝ ↦ q z * M) := hq.mul_const M
  calc
    (∫ t : ℝ, quadraticRemainderWeight R (x - t) * ‖f t‖) =
        ∫ t : ℝ, q t * g t := rfl
    _ ≤ ∫ t : ℝ, 2 * ∫ z : ℝ, H (t, z) :=
      integral_mono hqg (hleftInner.const_mul 2) hfixed
    _ = 2 * ∫ t : ℝ, ∫ z : ℝ, H (t, z) := integral_const_mul 2 _
    _ = 2 * ∫ z : ℝ, ∫ t : ℝ, H (t, z) := by
      congr 1
      exact integral_integral_swap (f := fun t z ↦ H (t, z)) hH
    _ = 2 * ∫ z : ℝ, q z * centeredUnitMass f z := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      exact hinner_right z
    _ ≤ 2 * ∫ z : ℝ, q z * M := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply integral_mono hqmass hqM
      intro z
      exact mul_le_mul_of_nonneg_left (hlocal z) (hq_nonneg z)
    _ = 2 * (M * ∫ z : ℝ, q z) := by
      rw [show (∫ z : ℝ, q z * M) = M * ∫ z : ℝ, q z by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with z
        ring]
    _ = 2 * (R * Real.pi) * M := by
      rw [show (∫ z : ℝ, q z) = R * Real.pi by
        exact integral_quadraticRemainderWeight_sub_left hRpos x]
      ring

/-- The pointwise kernel estimate integrates to the paper's `R⁻²` mass
bound at every nonnegative dyadic scale. -/
theorem integral_norm_quadraticProjectionRemainder_two_zpow_le
    {k : ℤ} (hk : 0 ≤ k) :
    (∫ x : ℝ, ‖quadraticProjectionRemainder ((2 : ℝ) ^ k) x‖) ≤
      Real.pi * projectionRemainderConstant * ((2 : ℝ) ^ k)⁻¹ ^ 2 := by
  let R : ℝ := (2 : ℝ) ^ k
  have hR : 1 ≤ R := by
    simpa only [R, zpow_zero] using
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let p : ℝ → ℝ := fun x ↦ (1 + (x / R) ^ 2)⁻¹
  have hp : Integrable p := by
    simpa only [p] using integrable_inv_one_add_sq.comp_div hRpos.ne'
  let A : ℝ := projectionRemainderConstant * R⁻¹ ^ 3
  have hA : 0 ≤ A :=
    mul_nonneg projectionRemainderConstant_nonneg (by positivity)
  have hmajorant : Integrable (fun x : ℝ ↦ A * p x) := hp.const_mul A
  have hpoint (x : ℝ) :
      ‖quadraticProjectionRemainder R x‖ ≤ A * p x := by
    have hr := norm_quadraticProjectionRemainder_le hR x
    have hden : 1 + (x / R) ^ 2 ≤ (1 + |x / R|) ^ 2 := by
      nlinarith [abs_nonneg (x / R), sq_abs (x / R)]
    have hinv : (1 + |x / R|)⁻¹ ^ 2 ≤ (1 + (x / R) ^ 2)⁻¹ := by
      rw [inv_pow]
      exact (inv_le_inv₀ (by positivity) (by positivity)).2 hden
    calc
      ‖quadraticProjectionRemainder R x‖ ≤
          projectionRemainderConstant * R⁻¹ ^ 3 *
            (1 + |x / R|)⁻¹ ^ 2 := hr
      _ ≤ projectionRemainderConstant * R⁻¹ ^ 3 *
          (1 + (x / R) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hA
      _ = A * p x := rfl
  calc
    (∫ x : ℝ, ‖quadraticProjectionRemainder R x‖) ≤
        ∫ x : ℝ, A * p x :=
      integral_mono (integrable_quadraticProjectionRemainder_two_zpow k).norm
        hmajorant hpoint
    _ = A * ∫ x : ℝ, p x := integral_const_mul A p
    _ = A * (R * Real.pi) := by
      congr 1
      unfold p
      change (∫ x : ℝ, (fun y : ℝ ↦ (1 + y ^ 2)⁻¹) (x / R)) =
        R * Real.pi
      calc
        (∫ x : ℝ, (fun y : ℝ ↦ (1 + y ^ 2)⁻¹) (x / R)) =
            |R| • ∫ y : ℝ, (1 + y ^ 2)⁻¹ :=
          Measure.integral_comp_div (fun y : ℝ ↦ (1 + y ^ 2)⁻¹) R
        _ = R * Real.pi := by
          rw [abs_of_pos hRpos, integral_univ_inv_one_add_sq]
          rfl
    _ = Real.pi * projectionRemainderConstant * R⁻¹ ^ 2 := by
      unfold A
      field_simp
    _ = _ := rfl

/-- The explicit remainder convolution is uniformly bounded by the
`R⁻³` kernel supremum times the `L¹` mass of its input. -/
theorem norm_quadraticProjectionRemainderOutput_le
    {k : ℤ} (hk : 0 ≤ k) {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    ‖quadraticProjectionRemainderOutput k f x‖ ≤
      projectionRemainderCentralConstant * ((2 : ℝ) ^ k)⁻¹ ^ 3 *
        ∫ y : ℝ, ‖f y‖ := by
  have hR : 1 ≤ (2 : ℝ) ^ k := by
    simpa only [zpow_zero] using
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
  have hmajorant : Integrable (fun y : ℝ ↦
      (projectionRemainderCentralConstant * ((2 : ℝ) ^ k)⁻¹ ^ 3) *
        ‖f y‖) :=
    hf.norm.const_mul
      (projectionRemainderCentralConstant * ((2 : ℝ) ^ k)⁻¹ ^ 3)
  rw [quadraticProjectionRemainderOutput_eq_actual_convolution]
  calc
    ‖∫ y : ℝ, quadraticProjectionRemainder ((2 : ℝ) ^ k) (x - y) * f y‖ ≤
        ∫ y : ℝ,
          (projectionRemainderCentralConstant * ((2 : ℝ) ^ k)⁻¹ ^ 3) *
            ‖f y‖ := by
      apply norm_integral_le_of_norm_le hmajorant
      filter_upwards [] with y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_quadraticProjectionRemainder_le_central hR (x - y))
        (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- The standard `L¹ * L¹ → L¹` estimate, specialized to the explicit
projection remainder and proved directly from convolution/Fubini. -/
theorem integral_norm_quadraticProjectionRemainderOutput_le
    (k : ℤ) {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ x : ℝ, ‖quadraticProjectionRemainderOutput k f x‖) ≤
      (∫ x : ℝ, ‖quadraticProjectionRemainder ((2 : ℝ) ^ k) x‖) *
        ∫ x : ℝ, ‖f x‖ := by
  let q : ℝ → ℝ := fun x ↦
    ‖quadraticProjectionRemainder ((2 : ℝ) ^ k) x‖
  let g : ℝ → ℝ := fun x ↦ ‖f x‖
  have hq : Integrable q :=
    (integrable_quadraticProjectionRemainder_two_zpow k).norm
  have hg : Integrable g := hf.norm
  have hqg : Integrable
      (q ⋆[ContinuousLinearMap.mul ℝ ℝ] g) :=
    hq.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hg
  have houtput := integrable_quadraticProjectionRemainderOutput k hf
  calc
    (∫ x : ℝ, ‖quadraticProjectionRemainderOutput k f x‖) ≤
        ∫ x : ℝ, (q ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x := by
      apply integral_mono houtput.norm hqg
      intro x
      change ‖∫ y : ℝ,
          quadraticProjectionRemainder ((2 : ℝ) ^ k) y * f (x - y)‖ ≤
        ∫ y : ℝ,
          ‖quadraticProjectionRemainder ((2 : ℝ) ^ k) y‖ * ‖f (x - y)‖
      simpa only [norm_mul] using
        (norm_integral_le_integral_norm
          (fun y : ℝ ↦
            quadraticProjectionRemainder ((2 : ℝ) ^ k) y * f (x - y)))
    _ = (∫ x : ℝ, q x) * ∫ x : ℝ, g x := by
      simpa using MeasureTheory.integral_convolution
        (ContinuousLinearMap.mul ℝ ℝ) hq hg
    _ = _ := rfl

/-- At nonnegative dyadic scales the remainder output has the paper's
`R⁻²` `L¹` bound. -/
theorem integral_norm_quadraticProjectionRemainderOutput_two_zpow_le
    {k : ℤ} (hk : 0 ≤ k) {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ x : ℝ, ‖quadraticProjectionRemainderOutput k f x‖) ≤
      Real.pi * projectionRemainderConstant * ((2 : ℝ) ^ k)⁻¹ ^ 2 *
        ∫ x : ℝ, ‖f x‖ := by
  calc
    (∫ x : ℝ, ‖quadraticProjectionRemainderOutput k f x‖) ≤
        (∫ x : ℝ, ‖quadraticProjectionRemainder ((2 : ℝ) ^ k) x‖) *
          ∫ x : ℝ, ‖f x‖ :=
      integral_norm_quadraticProjectionRemainderOutput_le k hf
    _ ≤ (Real.pi * projectionRemainderConstant * ((2 : ℝ) ^ k)⁻¹ ^ 2) *
          ∫ x : ℝ, ‖f x‖ :=
      mul_le_mul_of_nonneg_right
        (integral_norm_quadraticProjectionRemainder_two_zpow_le hk)
        (integral_nonneg fun _ ↦ norm_nonneg _)

/-- The local-unit-mass replacement for a pointwise input bound. At scale
`R = 2^k`, local mass `M` yields the uniform remainder bound
`2 π C M R⁻²`. -/
theorem norm_quadraticProjectionRemainderOutput_le_of_centeredUnitMass
    {k : ℤ} (hk : 0 ≤ k) {f : ℝ → ℂ} (hf : Integrable f)
    {M : ℝ} (hlocal : ∀ z, centeredUnitMass f z ≤ M)
    (x : ℝ) :
    ‖quadraticProjectionRemainderOutput k f x‖ ≤
      2 * Real.pi * projectionRemainderConstant * M *
        ((2 : ℝ) ^ k)⁻¹ ^ 2 := by
  let R : ℝ := (2 : ℝ) ^ k
  let A : ℝ := projectionRemainderConstant * R⁻¹ ^ 3
  have hR : 1 ≤ R := by
    simpa only [R, zpow_zero] using
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hA : 0 ≤ A := by
    unfold A
    exact mul_nonneg projectionRemainderConstant_nonneg (by positivity)
  have hw : Integrable (fun y : ℝ ↦
      quadraticRemainderWeight R (x - y)) :=
    integrable_quadraticRemainderWeight_sub_left hRpos x
  have hw_norm_le_one (y : ℝ) :
      ‖quadraticRemainderWeight R (x - y)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      unfold quadraticRemainderWeight
      positivity)]
    unfold quadraticRemainderWeight
    exact inv_le_one_of_one_le₀ (by
      nlinarith [sq_nonneg ((x - y) / R)])
  have hweighted : Integrable (fun y : ℝ ↦
      quadraticRemainderWeight R (x - y) * ‖f y‖) := by
    have hi := hf.norm.bdd_mul hw.aestronglyMeasurable
      (ae_of_all _ hw_norm_le_one)
    simpa only [mul_comm] using hi
  have hmajorant : Integrable (fun y : ℝ ↦
      A * (quadraticRemainderWeight R (x - y) * ‖f y‖)) :=
    hweighted.const_mul A
  rw [quadraticProjectionRemainderOutput_eq_actual_convolution]
  calc
    ‖∫ y : ℝ, quadraticProjectionRemainder R (x - y) * f y‖ ≤
        ∫ y : ℝ,
          A * (quadraticRemainderWeight R (x - y) * ‖f y‖) := by
      apply norm_integral_le_of_norm_le hmajorant
      filter_upwards [] with y
      rw [norm_mul]
      calc
        ‖quadraticProjectionRemainder R (x - y)‖ * ‖f y‖ ≤
            (projectionRemainderConstant * R⁻¹ ^ 3 *
              quadraticRemainderWeight R (x - y)) * ‖f y‖ :=
          mul_le_mul_of_nonneg_right
            (norm_quadraticProjectionRemainder_le_weight hR (x - y))
            (norm_nonneg (f y))
        _ = A * (quadraticRemainderWeight R (x - y) * ‖f y‖) := by
          unfold A
          ring
    _ = A * ∫ y : ℝ,
        quadraticRemainderWeight R (x - y) * ‖f y‖ :=
      integral_const_mul A _
    _ ≤ A * (2 * (R * Real.pi) * M) :=
      mul_le_mul_of_nonneg_left
        (integral_weight_mul_norm_le_of_centeredUnitMass
          hR hf hlocal x) hA
    _ = 2 * Real.pi * projectionRemainderConstant * M * R⁻¹ ^ 2 := by
      unfold A
      field_simp
    _ = _ := rfl

/-- If the input is bounded by `K`, the remainder output has the paper's
`K R⁻²` uniform bound. -/
theorem norm_quadraticProjectionRemainderOutput_le_of_bound
    {k : ℤ} (hk : 0 ≤ k) {f : ℝ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hfK : ∀ x, ‖f x‖ ≤ K) (x : ℝ) :
    ‖quadraticProjectionRemainderOutput k f x‖ ≤
      K * (Real.pi * projectionRemainderConstant *
        ((2 : ℝ) ^ k)⁻¹ ^ 2) := by
  let q : ℝ → ℝ := fun y ↦
    ‖quadraticProjectionRemainder ((2 : ℝ) ^ k) y‖
  have hq : Integrable q :=
    (integrable_quadraticProjectionRemainder_two_zpow k).norm
  have hmajorant : Integrable (fun y : ℝ ↦ K * q y) := hq.const_mul K
  unfold quadraticProjectionRemainderOutput
  rw [convolution_def]
  calc
    ‖∫ y : ℝ,
        quadraticProjectionRemainder ((2 : ℝ) ^ k) y * f (x - y)‖ ≤
        ∫ y : ℝ, K * q y := by
      apply norm_integral_le_of_norm_le hmajorant
      filter_upwards [] with y
      rw [norm_mul]
      calc
        ‖quadraticProjectionRemainder ((2 : ℝ) ^ k) y‖ * ‖f (x - y)‖ ≤
            ‖quadraticProjectionRemainder ((2 : ℝ) ^ k) y‖ * K :=
          mul_le_mul_of_nonneg_left (hfK (x - y)) (norm_nonneg _)
        _ = K * q y := by unfold q; ring
    _ = K * ∫ y : ℝ, q y := integral_const_mul K q
    _ ≤ K * (Real.pi * projectionRemainderConstant *
        ((2 : ℝ) ^ k)⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (integral_norm_quadraticProjectionRemainder_two_zpow_le hk) hK

/-- The interpolation step in squared form. It combines the concrete
`L∞` and `L¹` output estimates and already has scale decay `R⁻⁴`. -/
theorem integral_sq_norm_quadraticProjectionRemainderOutput_le
    {k : ℤ} (hk : 0 ≤ k) {f : ℝ → ℂ} (hf : Integrable f)
    {K : ℝ} (hK : 0 ≤ K) (hfK : ∀ x, ‖f x‖ ≤ K) :
    (∫ x : ℝ, ‖quadraticProjectionRemainderOutput k f x‖ ^ 2) ≤
      (Real.pi * projectionRemainderConstant *
          ((2 : ℝ) ^ k)⁻¹ ^ 2) ^ 2 * K * ∫ x : ℝ, ‖f x‖ := by
  let M : ℝ := Real.pi * projectionRemainderConstant *
    ((2 : ℝ) ^ k)⁻¹ ^ 2
  have hM : 0 ≤ M := by
    unfold M
    exact mul_nonneg
      (mul_nonneg Real.pi_pos.le projectionRemainderConstant_nonneg)
      (by positivity)
  have houtput := integrable_quadraticProjectionRemainderOutput k hf
  have hbound : ∀ᵐ x : ℝ ∂volume,
      ‖quadraticProjectionRemainderOutput k f x‖ ≤ K * M :=
    ae_of_all _ (norm_quadraticProjectionRemainderOutput_le_of_bound hk hK hfK)
  have hbound' : ∀ᵐ x : ℝ ∂volume,
      ‖‖quadraticProjectionRemainderOutput k f x‖‖ ≤ K * M := by
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hx
  have hsq : Integrable
      (fun x : ℝ ↦ ‖quadraticProjectionRemainderOutput k f x‖ ^ 2) :=
    by
      have hi := houtput.norm.bdd_mul houtput.norm.aestronglyMeasurable hbound'
      simpa only [pow_two] using hi
  have hmajorant : Integrable (fun x : ℝ ↦
      (K * M) * ‖quadraticProjectionRemainderOutput k f x‖) :=
    houtput.norm.const_mul (K * M)
  have hpoint (x : ℝ) :
      ‖quadraticProjectionRemainderOutput k f x‖ ^ 2 ≤
        (K * M) * ‖quadraticProjectionRemainderOutput k f x‖ := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right
      (norm_quadraticProjectionRemainderOutput_le_of_bound hk hK hfK x)
      (norm_nonneg _)
  calc
    (∫ x : ℝ, ‖quadraticProjectionRemainderOutput k f x‖ ^ 2) ≤
        ∫ x : ℝ, (K * M) *
          ‖quadraticProjectionRemainderOutput k f x‖ :=
      integral_mono hsq hmajorant hpoint
    _ = (K * M) *
        ∫ x : ℝ, ‖quadraticProjectionRemainderOutput k f x‖ :=
      integral_const_mul (K * M) _
    _ ≤ (K * M) * (M * ∫ x : ℝ, ‖f x‖) :=
      mul_le_mul_of_nonneg_left
        (integral_norm_quadraticProjectionRemainderOutput_two_zpow_le hk hf)
        (mul_nonneg hK hM)
    _ = M ^ 2 * K * ∫ x : ℝ, ‖f x‖ := by ring
    _ = _ := rfl

/-- `L²` interpolation using only the centered-unit mass hypothesis and
the total `L¹` mass. -/
theorem integral_sq_norm_quadraticProjectionRemainderOutput_le_of_centeredUnitMass
    {k : ℤ} (hk : 0 ≤ k) {f : ℝ → ℂ} (hf : Integrable f)
    {M : ℝ} (hM : 0 ≤ M) (hlocal : ∀ z, centeredUnitMass f z ≤ M) :
    (∫ x : ℝ, ‖quadraticProjectionRemainderOutput k f x‖ ^ 2) ≤
      2 * (Real.pi * projectionRemainderConstant *
          ((2 : ℝ) ^ k)⁻¹ ^ 2) ^ 2 * M * ∫ x : ℝ, ‖f x‖ := by
  let L : ℝ := Real.pi * projectionRemainderConstant *
    ((2 : ℝ) ^ k)⁻¹ ^ 2
  have hL : 0 ≤ L := by
    unfold L
    exact mul_nonneg
      (mul_nonneg Real.pi_pos.le projectionRemainderConstant_nonneg)
      (by positivity)
  have houtput := integrable_quadraticProjectionRemainderOutput k hf
  have hbound : ∀ᵐ x : ℝ ∂volume,
      ‖quadraticProjectionRemainderOutput k f x‖ ≤ 2 * M * L := by
    filter_upwards [] with x
    have hx := norm_quadraticProjectionRemainderOutput_le_of_centeredUnitMass
      hk hf hlocal x
    simpa only [L] using hx.trans_eq (by ring)
  have hbound' : ∀ᵐ x : ℝ ∂volume,
      ‖‖quadraticProjectionRemainderOutput k f x‖‖ ≤ 2 * M * L := by
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hx
  have hsq : Integrable
      (fun x : ℝ ↦ ‖quadraticProjectionRemainderOutput k f x‖ ^ 2) := by
    have hi := houtput.norm.bdd_mul houtput.norm.aestronglyMeasurable hbound'
    simpa only [pow_two] using hi
  have hmajorant : Integrable (fun x : ℝ ↦
      (2 * M * L) * ‖quadraticProjectionRemainderOutput k f x‖) :=
    houtput.norm.const_mul (2 * M * L)
  have hpoint (x : ℝ) :
      ‖quadraticProjectionRemainderOutput k f x‖ ^ 2 ≤
        (2 * M * L) * ‖quadraticProjectionRemainderOutput k f x‖ := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right
      (norm_quadraticProjectionRemainderOutput_le_of_centeredUnitMass
        hk hf hlocal x |>.trans_eq (by unfold L; ring))
      (norm_nonneg _)
  calc
    (∫ x : ℝ, ‖quadraticProjectionRemainderOutput k f x‖ ^ 2) ≤
        ∫ x : ℝ, (2 * M * L) *
          ‖quadraticProjectionRemainderOutput k f x‖ :=
      integral_mono hsq hmajorant hpoint
    _ = (2 * M * L) *
        ∫ x : ℝ, ‖quadraticProjectionRemainderOutput k f x‖ :=
      integral_const_mul (2 * M * L) _
    _ ≤ (2 * M * L) * (L * ∫ x : ℝ, ‖f x‖) :=
      mul_le_mul_of_nonneg_left
        (integral_norm_quadraticProjectionRemainderOutput_two_zpow_le hk hf)
        (mul_nonneg (mul_nonneg (by norm_num) hM) hL)
    _ = 2 * L ^ 2 * M * ∫ x : ℝ, ‖f x‖ := by ring
    _ = _ := rfl

/-- For nonnegative dyadic scales the actual projection-remainder output of
every integrable input has a canonical `L²` representative. -/
theorem memLp_two_quadraticProjectionRemainderOutput
    {k : ℤ} (hk : 0 ≤ k) {f : ℝ → ℂ} (hf : Integrable f) :
    MemLp (quadraticProjectionRemainderOutput k f) 2 volume := by
  have hconv := integrable_quadraticProjectionRemainderOutput k hf
  rw [memLp_two_iff_integrable_sq_norm hconv.aestronglyMeasurable]
  let B : ℝ := projectionRemainderCentralConstant * ((2 : ℝ) ^ k)⁻¹ ^ 3 *
    ∫ y : ℝ, ‖f y‖
  have hbound : ∀ᵐ x : ℝ ∂volume,
      ‖quadraticProjectionRemainderOutput k f x‖ ≤ B :=
    ae_of_all _ (norm_quadraticProjectionRemainderOutput_le hk hf)
  have hbound' : ∀ᵐ x : ℝ ∂volume,
      ‖‖quadraticProjectionRemainderOutput k f x‖‖ ≤ B := by
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hx
  have hi := hconv.norm.bdd_mul hconv.norm.aestronglyMeasurable hbound'
  simpa only [pow_two] using hi

/-- Quantitative `L²` interpolation for the concrete remainder output. This
is the per-scale estimate used in the final finite sum. -/
theorem norm_quadraticProjectionRemainderOutputL2_le
    {k : ℤ} (hk : 0 ≤ k) {f : ℝ → ℂ} (hf : Integrable f)
    {K : ℝ} (hK : 0 ≤ K) (hfK : ∀ x, ‖f x‖ ≤ K) :
    ‖(memLp_two_quadraticProjectionRemainderOutput hk hf).toLp
        (quadraticProjectionRemainderOutput k f)‖ ≤
      (Real.pi * projectionRemainderConstant *
          ((2 : ℝ) ^ k)⁻¹ ^ 2) *
        Real.sqrt K * Real.sqrt (∫ x : ℝ, ‖f x‖) := by
  let u : Lp (α := ℝ) ℂ 2 volume :=
    (memLp_two_quadraticProjectionRemainderOutput hk hf).toLp
      (quadraticProjectionRemainderOutput k f)
  let M : ℝ := Real.pi * projectionRemainderConstant *
    ((2 : ℝ) ^ k)⁻¹ ^ 2
  let m : ℝ := ∫ x : ℝ, ‖f x‖
  have hM : 0 ≤ M := by
    unfold M
    exact mul_nonneg
      (mul_nonneg Real.pi_pos.le projectionRemainderConstant_nonneg)
      (by positivity)
  have hm : 0 ≤ m := integral_nonneg fun _ ↦ norm_nonneg _
  have hu_sq : ‖u‖ ^ 2 =
      ∫ x : ℝ, ‖quadraticProjectionRemainderOutput k f x‖ ^ 2 := by
    have hinner : (∫ x : ℝ, ‖u x‖ ^ 2) = ‖u‖ ^ 2 := by
      simpa only [real_inner_self_eq_norm_sq] using
        (L2.inner_def (𝕜 := ℝ) u u).symm
    rw [← hinner]
    apply integral_congr_ae
    filter_upwards [
      (memLp_two_quadraticProjectionRemainderOutput hk hf).coeFn_toLp]
        with x hx
    rw [hx]
  refine (sq_le_sq₀ (norm_nonneg u)
    (mul_nonneg (mul_nonneg hM (Real.sqrt_nonneg K))
      (Real.sqrt_nonneg m))).mp ?_
  rw [hu_sq]
  calc
    (∫ x : ℝ, ‖quadraticProjectionRemainderOutput k f x‖ ^ 2) ≤
        M ^ 2 * K * m := by
      simpa only [M, m] using
        integral_sq_norm_quadraticProjectionRemainderOutput_le hk hf hK hfK
    _ = (M * Real.sqrt K * Real.sqrt m) ^ 2 := by
      unfold M
      simp only [mul_pow, Real.sq_sqrt hK, Real.sq_sqrt hm]
    _ = _ := rfl

/-- Quantitative `L²` remainder estimate from local unit-window mass and
total mass. -/
theorem norm_quadraticProjectionRemainderOutputL2_le_of_centeredUnitMass
    {k : ℤ} (hk : 0 ≤ k) {f : ℝ → ℂ} (hf : Integrable f)
    {M : ℝ} (hM : 0 ≤ M) (hlocal : ∀ z, centeredUnitMass f z ≤ M) :
    ‖(memLp_two_quadraticProjectionRemainderOutput hk hf).toLp
        (quadraticProjectionRemainderOutput k f)‖ ≤
      2 * (Real.pi * projectionRemainderConstant *
          ((2 : ℝ) ^ k)⁻¹ ^ 2) *
        Real.sqrt M * Real.sqrt (∫ x : ℝ, ‖f x‖) := by
  let u : Lp (α := ℝ) ℂ 2 volume :=
    (memLp_two_quadraticProjectionRemainderOutput hk hf).toLp
      (quadraticProjectionRemainderOutput k f)
  let L : ℝ := Real.pi * projectionRemainderConstant *
    ((2 : ℝ) ^ k)⁻¹ ^ 2
  let m : ℝ := ∫ x : ℝ, ‖f x‖
  have hL : 0 ≤ L := by
    unfold L
    exact mul_nonneg
      (mul_nonneg Real.pi_pos.le projectionRemainderConstant_nonneg)
      (by positivity)
  have hm : 0 ≤ m := integral_nonneg fun _ ↦ norm_nonneg _
  have hu_sq : ‖u‖ ^ 2 =
      ∫ x : ℝ, ‖quadraticProjectionRemainderOutput k f x‖ ^ 2 := by
    have hinner : (∫ x : ℝ, ‖u x‖ ^ 2) = ‖u‖ ^ 2 := by
      simpa only [real_inner_self_eq_norm_sq] using
        (L2.inner_def (𝕜 := ℝ) u u).symm
    rw [← hinner]
    apply integral_congr_ae
    filter_upwards [
      (memLp_two_quadraticProjectionRemainderOutput hk hf).coeFn_toLp]
        with x hx
    rw [hx]
  refine (sq_le_sq₀ (norm_nonneg u)
    (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hL) (Real.sqrt_nonneg M))
      (Real.sqrt_nonneg m))).mp ?_
  rw [hu_sq]
  calc
    (∫ x : ℝ, ‖quadraticProjectionRemainderOutput k f x‖ ^ 2) ≤
        2 * L ^ 2 * M * m := by
      simpa only [L, m] using
        integral_sq_norm_quadraticProjectionRemainderOutput_le_of_centeredUnitMass
          hk hf hM hlocal
    _ ≤ 4 * L ^ 2 * M * m := by
      have hLMm : 0 ≤ L ^ 2 * M * m := by positivity
      nlinarith
    _ = (2 * L * Real.sqrt M * Real.sqrt m) ^ 2 := by
      unfold L
      simp only [mul_pow, Real.sq_sqrt hM, Real.sq_sqrt hm]
      ring
    _ = _ := rfl

/-- Canonical `L²` remainder output at a natural-number dyadic scale. -/
noncomputable def nonnegativeDyadicProjectionRemainderOutputL2
    (k : ℕ) (f : ℝ → ℂ) (hf : Integrable f) :
    Lp (α := ℝ) ℂ 2 volume :=
  (memLp_two_quadraticProjectionRemainderOutput
      (k := (k : ℤ)) (by omega) hf).toLp
    (quadraticProjectionRemainderOutput (k : ℤ) f)

theorem norm_nonnegativeDyadicProjectionRemainderOutputL2_le
    (k : ℕ) {f : ℝ → ℂ} (hf : Integrable f)
    {K : ℝ} (hK : 0 ≤ K) (hfK : ∀ x, ‖f x‖ ≤ K) :
    ‖nonnegativeDyadicProjectionRemainderOutputL2 k f hf‖ ≤
      (Real.pi * projectionRemainderConstant *
          ((2 : ℝ) ^ k)⁻¹ ^ 2) *
        Real.sqrt K * Real.sqrt (∫ x : ℝ, ‖f x‖) := by
  unfold nonnegativeDyadicProjectionRemainderOutputL2
  simpa only [zpow_natCast] using
    norm_quadraticProjectionRemainderOutputL2_le
      (k := (k : ℤ)) (by omega) hf hK hfK

/-- Concrete `L²` projection-error identity with no remainder-space premise:
integrability of the input supplies it automatically. -/
theorem quadraticScaleOutputL2_sub_annularProjectionL2_eq_remainderOutputL2_of_nonneg
    {k : ℤ} (hk : 0 ≤ k) {f : ℝ → ℂ} (hf : Integrable f)
    (hscale₂ : MemLp (quadraticScaleOutput k f) 2 volume) :
    hscale₂.toLp (quadraticScaleOutput k f) -
        KrauseLaceyQuadraticSmoothProjection.annularProjectionL2 k
          (hscale₂.toLp (quadraticScaleOutput k f)) =
      (memLp_two_quadraticProjectionRemainderOutput hk hf).toLp
        (quadraticProjectionRemainderOutput k f) :=
  quadraticScaleOutputL2_sub_annularProjectionL2_eq_remainderOutputL2
    k hf hscale₂ (memLp_two_quadraticProjectionRemainderOutput hk hf)

/-- A.e. representative form of the concrete nonnegative-scale projection
error identity. -/
theorem quadraticScaleOutput_sub_annularProjection_ae_of_nonneg
    {k : ℤ} (hk : 0 ≤ k) {f : ℝ → ℂ} (hf : Integrable f)
    (hscale₂ : MemLp (quadraticScaleOutput k f) 2 volume) :
    (fun x ↦ (hscale₂.toLp (quadraticScaleOutput k f)) x -
      (KrauseLaceyQuadraticSmoothProjection.annularProjectionL2 k
        (hscale₂.toLp (quadraticScaleOutput k f))) x) =ᵐ[volume]
      quadraticProjectionRemainderOutput k f :=
  quadraticScaleOutput_sub_annularProjection_ae k hf hscale₂
    (memLp_two_quadraticProjectionRemainderOutput hk hf)

/-- Pointwise sum of the absolute values of finitely many projection-error
outputs. This dominates every partial sum and every finite tail, without
using cancellation between errors. -/
def finiteProjectionErrorMajorant
    (N : ℕ) (u : ℕ → ℝ → ℂ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, ‖u n x‖

theorem memLp_two_finiteProjectionErrorMajorant
    {N : ℕ} {u : ℕ → ℝ → ℂ} (hu : ∀ n, MemLp (u n) 2 volume) :
    MemLp (finiteProjectionErrorMajorant N u) 2 volume := by
  change MemLp (fun x ↦ ∑ n ∈ Finset.range N, ‖u n x‖) 2 volume
  exact memLp_finsetSum (Finset.range N) fun n _ ↦ (hu n).norm

/-- The square integral of the extended-nonnegative version of the finite
projection-error majorant is exactly the square of its real `L²` norm. -/
theorem lintegral_ofReal_finiteProjectionErrorMajorant_sq_eq
    {N : ℕ} {u : ℕ → ℝ → ℂ} (hu : ∀ n, MemLp (u n) 2 volume) :
    (∫⁻ x, ENNReal.ofReal (finiteProjectionErrorMajorant N u x) ^ 2) =
      ENNReal.ofReal
        (‖(memLp_two_finiteProjectionErrorMajorant hu).toLp
          (finiteProjectionErrorMajorant N u)‖ ^ 2) := by
  let F : ℝ → ℝ := finiteProjectionErrorMajorant N u
  have hF0 (x : ℝ) : 0 ≤ F x := by
    exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hIntegral :
      (∫⁻ x, ENNReal.ofReal (F x) ^ 2) = (∫⁻ x, ‖F x‖ₑ ^ 2) := by
    apply lintegral_congr
    intro x
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hF0 x)]
  change (∫⁻ x, ENNReal.ofReal (F x) ^ 2) = _
  rw [hIntegral, ← eLpNorm_two_sq_lintegral F
    (memLp_two_finiteProjectionErrorMajorant hu).aestronglyMeasurable,
    ← Lp.enorm_toLp (memLp_two_finiteProjectionErrorMajorant hu),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

private theorem toLp_finsetSum_eq_sum
    {ι E : Type*} [NormedAddCommGroup E]
    (S : Finset ι) {u : ι → ℝ → E}
    (hu : ∀ i, MemLp (u i) 2 volume) :
    (memLp_finsetSum' S (fun i _ ↦ hu i)).toLp (∑ i ∈ S, u i) =
      ∑ i ∈ S, (hu i).toLp (u i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact MemLp.toLp_zero _
  | @insert a S ha ih =>
      have hadd := MemLp.toLp_add (hu a)
        (memLp_finsetSum' S (fun i _ ↦ hu i))
      simpa only [Finset.sum_insert ha, ih] using hadd

/-- The `L²` norm of the pointwise finite error majorant is bounded by the
sum of the individual error norms. -/
theorem norm_finiteProjectionErrorMajorantL2_le
    {N : ℕ} {u : ℕ → ℝ → ℂ} (hu : ∀ n, MemLp (u n) 2 volume) :
    ‖(memLp_two_finiteProjectionErrorMajorant hu).toLp
        (finiteProjectionErrorMajorant N u)‖ ≤
      ∑ n ∈ Finset.range N, ‖(hu n).toLp (u n)‖ := by
  let v : ℕ → ℝ → ℝ := fun n x ↦ ‖u n x‖
  have hv : ∀ n, MemLp (v n) 2 volume := fun n ↦ (hu n).norm
  have hfun : finiteProjectionErrorMajorant N u =
      ∑ n ∈ Finset.range N, v n := by
    funext x
    simp only [finiteProjectionErrorMajorant, Finset.sum_apply, v]
  have hsum : MemLp (∑ n ∈ Finset.range N, v n) 2 volume :=
    memLp_finsetSum' (Finset.range N) fun n _ ↦ hv n
  have htoLp :
      (memLp_two_finiteProjectionErrorMajorant hu).toLp
          (finiteProjectionErrorMajorant N u) =
        ∑ n ∈ Finset.range N, (hv n).toLp (v n) :=
    (MemLp.toLp_congr (memLp_two_finiteProjectionErrorMajorant hu) hsum
      (ae_of_all _ fun x ↦ congrFun hfun x)).trans
        (toLp_finsetSum_eq_sum (Finset.range N) hv)
  rw [htoLp]
  calc
    ‖∑ n ∈ Finset.range N, (hv n).toLp (v n)‖ ≤
        ∑ n ∈ Finset.range N, ‖(hv n).toLp (v n)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.range N, ‖(hu n).toLp (u n)‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm (u n) (hu n).aestronglyMeasurable]

/-- A finite pointwise remainder majorant is controlled in `L²` by the sum
of the centered-unit-mass bounds for its individual scale outputs. This is
the abstract bridge needed by the direct quadratic residue families; unlike
the earlier bounded-input route, it assumes no pointwise bound on the inputs.
-/
theorem norm_finiteProjectionErrorMajorantL2_le_of_centeredUnitMass
    {N : ℕ} {k : ℕ → ℤ} (hk : ∀ n, 0 ≤ k n)
    {f : ℕ → ℝ → ℂ} (hf : ∀ n, Integrable (f n))
    {M : ℕ → ℝ} (hM : ∀ n, 0 ≤ M n)
    (hlocal : ∀ n z, centeredUnitMass (f n) z ≤ M n) :
    let u : ℕ → ℝ → ℂ := fun n ↦
      quadraticProjectionRemainderOutput (k n) (f n)
    let hu : ∀ n, MemLp (u n) 2 volume := fun n ↦
      memLp_two_quadraticProjectionRemainderOutput (hk n) (hf n)
    ‖(memLp_two_finiteProjectionErrorMajorant hu).toLp
        (finiteProjectionErrorMajorant N u)‖ ≤
      ∑ n ∈ Finset.range N,
        2 * (Real.pi * projectionRemainderConstant *
            ((2 : ℝ) ^ (k n))⁻¹ ^ 2) *
          Real.sqrt (M n) * Real.sqrt (∫ x : ℝ, ‖f n x‖) := by
  dsimp only
  calc
    ‖(memLp_two_finiteProjectionErrorMajorant fun n ↦
        memLp_two_quadraticProjectionRemainderOutput (hk n) (hf n)).toLp
          (finiteProjectionErrorMajorant N fun n ↦
            quadraticProjectionRemainderOutput (k n) (f n))‖ ≤
        ∑ n ∈ Finset.range N,
          ‖(memLp_two_quadraticProjectionRemainderOutput
              (hk n) (hf n)).toLp
            (quadraticProjectionRemainderOutput (k n) (f n))‖ :=
      norm_finiteProjectionErrorMajorantL2_le
        (N := N) (fun n ↦
          memLp_two_quadraticProjectionRemainderOutput (hk n) (hf n))
    _ ≤ ∑ n ∈ Finset.range N,
        2 * (Real.pi * projectionRemainderConstant *
            ((2 : ℝ) ^ (k n))⁻¹ ^ 2) *
          Real.sqrt (M n) * Real.sqrt (∫ x : ℝ, ‖f n x‖) := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_quadraticProjectionRemainderOutputL2_le_of_centeredUnitMass
        (hk n) (hf n) (hM n) (hlocal n)

/-- Pointwise absolute-error majorant for the consecutive nonnegative
dyadic scales `s + j₀, ..., s + j₀ + N - 1`. -/
def finiteDyadicProjectionRemainderMajorant
    (N s j₀ : ℕ) (f : ℕ → ℝ → ℂ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    ‖quadraticProjectionRemainderOutput ((s + j₀ + n : ℕ) : ℤ) (f n) x‖

theorem memLp_two_finiteDyadicProjectionRemainderMajorant
    (N s j₀ : ℕ) {f : ℕ → ℝ → ℂ} (hf : ∀ n, Integrable (f n)) :
    MemLp (finiteDyadicProjectionRemainderMajorant N s j₀ f) 2 volume := by
  unfold finiteDyadicProjectionRemainderMajorant
  apply memLp_finsetSum
  intro n hn
  exact (memLp_two_quadraticProjectionRemainderOutput
    (k := ((s + j₀ + n : ℕ) : ℤ)) (by omega) (hf n)).norm

/-- Cancellation-free `L²` estimate for the concrete pointwise finite
error majorant. -/
theorem norm_finiteDyadicProjectionRemainderMajorantL2_le
    (N s j₀ : ℕ) {f : ℕ → ℝ → ℂ} (hf : ∀ n, Integrable (f n)) :
    ‖(memLp_two_finiteDyadicProjectionRemainderMajorant N s j₀ hf).toLp
        (finiteDyadicProjectionRemainderMajorant N s j₀ f)‖ ≤
      ∑ n ∈ Finset.range N,
        ‖(memLp_two_quadraticProjectionRemainderOutput
            (k := ((s + j₀ + n : ℕ) : ℤ)) (by omega) (hf n)).toLp
          (quadraticProjectionRemainderOutput
            ((s + j₀ + n : ℕ) : ℤ) (f n))‖ := by
  let u : ℕ → ℝ → ℂ := fun n ↦
    quadraticProjectionRemainderOutput ((s + j₀ + n : ℕ) : ℤ) (f n)
  let hu : ∀ n, MemLp (u n) 2 volume := fun n ↦
    memLp_two_quadraticProjectionRemainderOutput
      (k := ((s + j₀ + n : ℕ) : ℤ)) (by omega) (hf n)
  have hfun : finiteDyadicProjectionRemainderMajorant N s j₀ f =
      finiteProjectionErrorMajorant N u := by
    funext x
    simp only [finiteDyadicProjectionRemainderMajorant,
      finiteProjectionErrorMajorant, u]
  have htoLp :
      (memLp_two_finiteDyadicProjectionRemainderMajorant N s j₀ hf).toLp
          (finiteDyadicProjectionRemainderMajorant N s j₀ f) =
        (memLp_two_finiteProjectionErrorMajorant hu).toLp
          (finiteProjectionErrorMajorant N u) :=
    MemLp.toLp_congr _ _ (ae_of_all _ fun x ↦ congrFun hfun x)
  rw [htoLp]
  calc
    ‖(memLp_two_finiteProjectionErrorMajorant hu).toLp
        (finiteProjectionErrorMajorant N u)‖ ≤
        ∑ n ∈ Finset.range N, ‖(hu n).toLp (u n)‖ :=
      norm_finiteProjectionErrorMajorantL2_le (N := N) hu
    _ = ∑ n ∈ Finset.range N,
        ‖(memLp_two_quadraticProjectionRemainderOutput
            (k := ((s + j₀ + n : ℕ) : ℤ)) (by omega) (hf n)).toLp
          (quadraticProjectionRemainderOutput
            ((s + j₀ + n : ℕ) : ℤ) (f n))‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Lp.norm_toLp]

private theorem sum_sixteenth_shift_le
    (N s j₀ : ℕ) :
    (∑ n ∈ Finset.range N,
        (1 / 16 : ℝ) ^ (s + j₀ + n)) ≤
      2 * (1 / 16 : ℝ) ^ s := by
  have hbasepow : (1 / 16 : ℝ) ^ (s + j₀) ≤ (1 / 16 : ℝ) ^ s := by
    rw [pow_add]
    calc
      (1 / 16 : ℝ) ^ s * (1 / 16 : ℝ) ^ j₀ ≤
          (1 / 16 : ℝ) ^ s * 1 := by
        gcongr
        exact pow_le_one₀ (by norm_num) (by norm_num)
      _ = _ := by ring
  have hgeom : (∑ n ∈ Finset.range N, (1 / 16 : ℝ) ^ n) ≤ 2 := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n := by
        exact Finset.sum_le_sum fun n _ ↦
          pow_le_pow_left₀ (by norm_num : 0 ≤ (1 / 16 : ℝ))
            (by norm_num : (1 / 16 : ℝ) ≤ 1 / 2) n
      _ ≤ 2 := sum_geometric_two_le N
  simp_rw [show ∀ n : ℕ, (1 / 16 : ℝ) ^ (s + j₀ + n) =
      (1 / 16 : ℝ) ^ (s + j₀) * (1 / 16 : ℝ) ^ n by
        intro n; rw [pow_add]]
  rw [← Finset.mul_sum]
  calc
    (1 / 16 : ℝ) ^ (s + j₀) *
        (∑ n ∈ Finset.range N, (1 / 16 : ℝ) ^ n) ≤
      (1 / 16 : ℝ) ^ s *
        (∑ n ∈ Finset.range N, (1 / 16 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_right hbasepow
        (Finset.sum_nonneg fun _ _ ↦ by positivity)
    _ ≤ (1 / 16 : ℝ) ^ s * 2 :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 2 * (1 / 16 : ℝ) ^ s := by ring

private theorem sqrt_sum_sixteenth_shift_le
    (N s j₀ : ℕ) :
    Real.sqrt (∑ n ∈ Finset.range N,
        (1 / 16 : ℝ) ^ (s + j₀ + n)) ≤
      2 * (1 / 4 : ℝ) ^ s := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have h := sum_sixteenth_shift_le N s j₀
    have hpow : ((1 / 4 : ℝ) ^ s) ^ 2 = (1 / 16 : ℝ) ^ s := by
      rw [pow_two, ← mul_pow]
      norm_num
    rw [mul_pow, hpow]
    nlinarith [show 0 ≤ (1 / 16 : ℝ) ^ s by positivity]

/-- Finite `L²` summation of projection errors. The hypothesis is exactly
the per-scale bound obtained by interpolating the paper's
`‖r_R * F_j‖∞ ≲ K R⁻²` and `‖r_R * F_j‖₁ ≲ R⁻² m_j` estimates. The result is
cardinality-free and has the required `(1/4)^s = 2^(-2s)` decay. -/
theorem norm_finset_sum_projectionErrors_le
    (N s j₀ : ℕ) {K V C : ℝ}
    (_hK : 0 ≤ K) (_hV : 0 ≤ V) (hC : 0 ≤ C)
    (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n)
    (hmass : (∑ n ∈ Finset.range N, m n) ≤ V)
    (g : ℕ → Lp (α := ℝ) ℂ 2 volume)
    (hg : ∀ n ∈ Finset.range N,
      ‖g n‖ ≤ C * Real.sqrt K *
        Real.sqrt ((1 / 16 : ℝ) ^ (s + j₀ + n)) * Real.sqrt (m n)) :
    ‖∑ n ∈ Finset.range N, g n‖ ≤
      2 * C * Real.sqrt K * (1 / 4 : ℝ) ^ s * Real.sqrt V := by
  have hCK : 0 ≤ C * Real.sqrt K :=
    mul_nonneg hC (Real.sqrt_nonneg _)
  have hCS := Real.sum_sqrt_mul_sqrt_le
    (f := fun n ↦ (1 / 16 : ℝ) ^ (s + j₀ + n)) (g := m)
    (Finset.range N)
    (fun n ↦ pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16) _)
    hm
  have hmassSqrt :
      Real.sqrt (∑ n ∈ Finset.range N, m n) ≤ Real.sqrt V :=
    Real.sqrt_le_sqrt hmass
  have hweightSqrt := sqrt_sum_sixteenth_shift_le N s j₀
  calc
    ‖∑ n ∈ Finset.range N, g n‖ ≤
        ∑ n ∈ Finset.range N, ‖g n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N,
        C * Real.sqrt K *
          Real.sqrt ((1 / 16 : ℝ) ^ (s + j₀ + n)) * Real.sqrt (m n) :=
      Finset.sum_le_sum fun n hn ↦ hg n hn
    _ = (C * Real.sqrt K) *
        ∑ n ∈ Finset.range N,
          Real.sqrt ((1 / 16 : ℝ) ^ (s + j₀ + n)) * Real.sqrt (m n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ (C * Real.sqrt K) *
        (Real.sqrt (∑ n ∈ Finset.range N,
          (1 / 16 : ℝ) ^ (s + j₀ + n)) *
            Real.sqrt (∑ n ∈ Finset.range N, m n)) :=
      mul_le_mul_of_nonneg_left hCS hCK
    _ ≤ (C * Real.sqrt K) *
        ((2 * (1 / 4 : ℝ) ^ s) * Real.sqrt V) := by
      apply mul_le_mul_of_nonneg_left _ hCK
      exact mul_le_mul hweightSqrt hmassSqrt
        (Real.sqrt_nonneg _) (by positivity)
    _ = 2 * C * Real.sqrt K * (1 / 4 : ℝ) ^ s * Real.sqrt V := by ring

private theorem inv_two_pow_sq_eq_sqrt_sixteenth_pow (q : ℕ) :
    ((2 : ℝ) ^ q)⁻¹ ^ 2 = Real.sqrt ((1 / 16 : ℝ) ^ q) := by
  have hquarter : ((2 : ℝ) ^ q)⁻¹ ^ 2 = (1 / 4 : ℝ) ^ q := by
    rw [← inv_pow]
    rw [pow_two, ← mul_pow]
    norm_num
  have hsixteenth : ((1 / 4 : ℝ) ^ q) ^ 2 = (1 / 16 : ℝ) ^ q := by
    rw [pow_two, ← mul_pow]
    norm_num
  rw [hquarter, ← hsixteenth, Real.sqrt_sq (by positivity)]

/-- Fully concrete finite summation of the actual remainder convolutions.
The inputs may vary with the scale, are bounded by `K`, and their `L¹`
masses sum to at most `V`. No cardinality factor remains. -/
theorem norm_finset_sum_nonnegativeDyadicProjectionRemainderOutputL2_le
    (N s j₀ : ℕ) {K V : ℝ} (hK : 0 ≤ K) (hV : 0 ≤ V)
    (f : ℕ → ℝ → ℂ) (hf : ∀ n, Integrable (f n))
    (hfK : ∀ n x, ‖f n x‖ ≤ K)
    (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n)
    (hfmass : ∀ n, (∫ x : ℝ, ‖f n x‖) ≤ m n)
    (hmass : (∑ n ∈ Finset.range N, m n) ≤ V) :
    ‖∑ n ∈ Finset.range N,
        nonnegativeDyadicProjectionRemainderOutputL2
          (s + j₀ + n) (f n) (hf n)‖ ≤
      2 * (Real.pi * projectionRemainderConstant) * Real.sqrt K *
        (1 / 4 : ℝ) ^ s * Real.sqrt V := by
  let g : ℕ → Lp (α := ℝ) ℂ 2 volume := fun n ↦
    nonnegativeDyadicProjectionRemainderOutputL2
      (s + j₀ + n) (f n) (hf n)
  apply norm_finset_sum_projectionErrors_le N s j₀ hK hV
    (mul_nonneg Real.pi_pos.le projectionRemainderConstant_nonneg)
    m hm hmass g
  intro n hn
  have hnorm := norm_nonnegativeDyadicProjectionRemainderOutputL2_le
    (s + j₀ + n) (hf n) hK (hfK n)
  have hsqrtMass : Real.sqrt (∫ x : ℝ, ‖f n x‖) ≤ Real.sqrt (m n) :=
    Real.sqrt_le_sqrt (hfmass n)
  have hcoefficient :
      0 ≤ (Real.pi * projectionRemainderConstant *
          ((2 : ℝ) ^ (s + j₀ + n))⁻¹ ^ 2) * Real.sqrt K := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg Real.pi_pos.le projectionRemainderConstant_nonneg)
        (by positivity))
      (Real.sqrt_nonneg _)
  calc
    ‖g n‖ ≤
        (Real.pi * projectionRemainderConstant *
            ((2 : ℝ) ^ (s + j₀ + n))⁻¹ ^ 2) *
          Real.sqrt K * Real.sqrt (∫ x : ℝ, ‖f n x‖) := hnorm
    _ ≤ (Real.pi * projectionRemainderConstant *
            ((2 : ℝ) ^ (s + j₀ + n))⁻¹ ^ 2) *
          Real.sqrt K * Real.sqrt (m n) :=
      mul_le_mul_of_nonneg_left hsqrtMass hcoefficient
    _ = (Real.pi * projectionRemainderConstant) * Real.sqrt K *
          Real.sqrt ((1 / 16 : ℝ) ^ (s + j₀ + n)) * Real.sqrt (m n) := by
      rw [inv_two_pow_sq_eq_sqrt_sixteenth_pow]
      ring


end
end QuadraticCarleson.KrauseLaceyQuadraticProjectionRemainder
