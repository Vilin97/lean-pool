/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWsp
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.SmoothRepresentative
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Diagonal convex smoothing of fractional kernels

The inward convex smoother acts on a fractional difference quotient by
sampling both variables with the same affine map.  This module records that
operator separately from the source-facing fractional Sobolev API.  Its
measure estimates are the analytic input for smooth density on cubes.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Apply one inward affine sample map simultaneously to both arguments of a
fractional kernel. -/
def diagonalConvexApproxSample {d : ℕ} (x0 z : Vec d) (r ε : ℝ) :
    Vec d × Vec d → Vec d × Vec d :=
  fun xy => (convexApproxSample x0 z r ε xy.1,
    convexApproxSample x0 z r ε xy.2)

@[simp] theorem diagonalConvexApproxSample_apply {d : ℕ} (x0 z : Vec d)
    (r ε : ℝ) (xy : Vec d × Vec d) :
    diagonalConvexApproxSample x0 z r ε xy =
      (convexApproxSample x0 z r ε xy.1,
        convexApproxSample x0 z r ε xy.2) := rfl

/-- Average a vector-valued Gagliardo kernel along the diagonal inward affine
samples.  This is deliberately an internal analytic operator, not a new
fractional-Sobolev norm. -/
noncomputable def diagonalConvexApproxAverage {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : Vec d → ℝ) (H : Vec d × Vec d → E) (x0 : Vec d) (r ε : ℝ)
    (xy : Vec d × Vec d) : E :=
  ∫ z in tsupport ρ, ρ z • H (diagonalConvexApproxSample x0 z r ε xy)

/-- The probability measure associated with a nonnegative unit-mass convex
approximation kernel. -/
noncomputable def convexApproxKernelMeasure {d : ℕ} (ρ : Vec d → ℝ) :
    Measure (Vec d) :=
  volume.withDensity fun z => ENNReal.ofReal (ρ z)

theorem isProbabilityMeasure_convexApproxKernelMeasure {d : ℕ}
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ) :
    IsProbabilityMeasure (convexApproxKernelMeasure ρ) := by
  apply isProbabilityMeasure_withDensity_ofReal hρ.nonneg
  · exact (hρ.continuous.integrable_of_hasCompactSupport hρ.compactSupport)
  · rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => image_eq_zero_of_notMem_tsupport hz)]
    exact hρ.setIntegral_one

@[simp] theorem diagonalConvexApproxAverage_apply {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : Vec d → ℝ) (H : Vec d × Vec d → E) (x0 : Vec d) (r ε : ℝ)
    (xy : Vec d × Vec d) :
    diagonalConvexApproxAverage ρ H x0 r ε xy =
      ∫ z in tsupport ρ, ρ z • H (diagonalConvexApproxSample x0 z r ε xy) := rfl

/-- Recast a kernel-weighted set integral as a Bochner integral against the
probability measure carried by the smoothing kernel. -/
theorem setIntegral_smul_eq_integral_convexApproxKernelMeasure {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    (G : Vec d → E) :
    (∫ z in tsupport ρ, ρ z • G z) = ∫ z, G z
        ∂convexApproxKernelMeasure ρ := by
  symm
  have hmeasure :
      (fun z => ENNReal.ofReal (ρ z)) =
        fun z => (Real.toNNReal (ρ z) : ℝ≥0∞) := by
    funext z
    rw [ENNReal.ofReal_eq_coe_nnreal (hρ.nonneg z),
      Real.toNNReal_of_nonneg (hρ.nonneg z)]
  rw [convexApproxKernelMeasure, hmeasure,
    integral_withDensity_eq_integral_smul₀
      hρ.continuous.measurable.real_toNNReal.aemeasurable]
  have hzero : ∀ z ∉ tsupport ρ,
      Real.toNNReal (ρ z) • G z = 0 := by
    intro z hz
    simp [image_eq_zero_of_notMem_tsupport hz]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  apply MeasureTheory.setIntegral_congr_fun (isClosed_tsupport ρ).measurableSet
  intro z hz
  change (Real.toNNReal (ρ z) : ℝ) •
      G z = ρ z • G z
  rw [Real.coe_toNNReal _ (hρ.nonneg z)]

/-- Recast the diagonal average as a Bochner integral against the probability
measure carried by the smoothing kernel. -/
theorem diagonalConvexApproxAverage_eq_integral_kernelMeasure {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    (H : Vec d × Vec d → E) (x0 : Vec d) (r ε : ℝ) (xy : Vec d × Vec d) :
    diagonalConvexApproxAverage ρ H x0 r ε xy =
      ∫ z, H (diagonalConvexApproxSample x0 z r ε xy)
        ∂convexApproxKernelMeasure ρ := by
  exact setIntegral_smul_eq_integral_convexApproxKernelMeasure hρ
    (fun z => H (diagonalConvexApproxSample x0 z r ε xy))

/-- The simultaneous affine sampling map contracts Euclidean pair distances by
the scalar factor `1 - ε`. -/
theorem euclideanDist_convexApproxSample {d : ℕ} (x0 z : Vec d) (r ε : ℝ)
    (hε : ε < 1) (x y : Vec d) :
    euclideanDist (convexApproxSample x0 z r ε x)
      (convexApproxSample x0 z r ε y) =
      (1 - ε) * euclideanDist x y := by
  have hrewrite :
      convexApproxSample x0 z r ε x - convexApproxSample x0 z r ε y =
        (1 - ε) • (x - y) := by
    unfold convexApproxSample
    module
  rw [euclideanDist, hrewrite, euclideanNorm_smul,
    abs_of_pos (sub_pos.mpr hε)]
  rfl

/-- Pulling a Euclidean fractional kernel through one diagonal affine sample
has the exact scaling dictated by the fractional order. -/
theorem cubeEuclideanWspKernel_comp_diagonalConvexApproxSample {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) (F : Vec d → Vec d)
    (x0 z : Vec d) (r ε : ℝ) (hε : ε < 1) (xy : Vec d × Vec d) :
    cubeEuclideanWspKernel s p
        (fun x => F (convexApproxSample x0 z r ε x)) xy =
      ((1 - ε) ^ (s.1 + (d : ℝ) / p.exponent.toReal)) •
        cubeEuclideanWspKernel s p F
          (diagonalConvexApproxSample x0 z r ε xy) := by
  rcases xy with ⟨x, y⟩
  simp only [cubeEuclideanWspKernel_apply, diagonalConvexApproxSample_apply]
  have hscale : 0 < 1 - ε := sub_pos.mpr hε
  rw [euclideanDist_convexApproxSample x0 z r ε hε x y,
    Real.mul_rpow hscale.le (euclideanDist_nonneg x y), smul_smul]
  have hpow :
      (1 - ε) ^ (s.1 + (d : ℝ) / p.exponent.toReal) *
        (1 - ε) ^ (-(s.1 + (d : ℝ) / p.exponent.toReal)) = 1 := by
    rw [← Real.rpow_add hscale]
    ring_nf
    rw [Real.rpow_zero]
  rw [← mul_assoc, hpow, one_mul]

/-- The diagonal affine sampling map transports a product of restricted volume
measures with one Jacobian factor for each cube variable. -/
theorem map_prod_restrict_diagonalConvexApproxSample
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    (x0 z : Vec d) (r ε : ℝ) (hε : ε < 1) :
    Measure.map (diagonalConvexApproxSample x0 z r ε)
        ((volume.restrict U).prod (volume.restrict U)) =
      (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ 2) •
        ((volume.restrict (convexApproxSample x0 z r ε '' U)).prod
          (volume.restrict (convexApproxSample x0 z r ε '' U))) := by
  have hdiag : diagonalConvexApproxSample x0 z r ε =
      Prod.map (convexApproxSample x0 z r ε) (convexApproxSample x0 z r ε) := by
    funext xy
    rfl
  rw [hdiag, ← Measure.map_prod_map (volume.restrict U) (volume.restrict U)
    (measurableEmbedding_convexApproxSample x0 z r ε hε).measurable
    (measurableEmbedding_convexApproxSample x0 z r ε hε).measurable]
  rw [map_restrict_convexApproxSample hU x0 z r ε hε,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, pow_two]

/-- The corresponding transport formula for the normalized-first-variable
Gagliardo measure.  The cube normalization is unchanged; the two affine
Jacobians are explicit. -/
theorem map_gagliardoCubeMeasure_diagonalConvexApproxSample {d : ℕ}
    (Q : TriadicCube d) (x0 z : Vec d) (r ε : ℝ) (hε : ε < 1) :
    Measure.map (diagonalConvexApproxSample x0 z r ε)
        (Gagliardo.gagliardoCubeMeasure Q) =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) •
        ((ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ 2) •
          ((volume.restrict (convexApproxSample x0 z r ε '' cubeSet Q)).prod
            (volume.restrict (convexApproxSample x0 z r ε '' cubeSet Q)))) := by
  have hmeas : Measurable (diagonalConvexApproxSample x0 z r ε) :=
    ((measurableEmbedding_convexApproxSample x0 z r ε hε).measurable.prodMap
      (measurableEmbedding_convexApproxSample x0 z r ε hε).measurable)
  rw [Gagliardo.gagliardoCubeMeasure, normalizedCubeMeasure, cubeMeasure,
    Measure.prod_smul_left, Measure.map_smul _ hmeas.aemeasurable]
  exact congrArg (ENNReal.ofReal ((cubeVolume Q)⁻¹) • ·)
    (map_prod_restrict_diagonalConvexApproxSample (measurableSet_cubeSet Q)
      x0 z r ε hε)

/-- The `p`-th power of the norm is convex for the finite exponents used by
the fractional theory. -/
theorem convexOn_norm_rpow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℝ} (hq : 1 ≤ q) :
    ConvexOn ℝ Set.univ (fun v : E => ‖v‖ ^ q) := by
  constructor
  · exact convex_univ
  intro x _ y _ a b ha hb hab
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  have hnorm : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    simpa [smul_eq_mul] using
      (convexOn_univ_norm.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab)
  calc
    ‖a • x + b • y‖ ^ q ≤ (a * ‖x‖ + b * ‖y‖) ^ q :=
      Real.rpow_le_rpow (norm_nonneg _) hnorm hq0
    _ ≤ a * ‖x‖ ^ q + b * ‖y‖ ^ q := by
      simpa [smul_eq_mul] using
        ((convexOn_rpow hq).2 (show ‖x‖ ∈ Set.Ici (0 : ℝ) by exact norm_nonneg _)
          (show ‖y‖ ∈ Set.Ici (0 : ℝ) by exact norm_nonneg _) ha hb hab)

/-- Pointwise vector Jensen followed by Tonelli.  The averaging variable is
kept scalar, which avoids any measurable `Lp`-valued section construction.
This is the finite-`p` estimate used by diagonal Gagliardo averaging. -/
theorem lintegral_enorm_rpow_integral_le_lintegral_lintegral
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [IsProbabilityMeasure ν]
    {H : β → α → E} {q : ℝ} (hq : 1 ≤ q)
    (hsection : ∀ᵐ x ∂μ, Integrable (fun z => H z x) ν)
    (hsectionpow : ∀ᵐ x ∂μ, Integrable (fun z => ‖H z x‖ ^ q) ν)
    (hpow_meas : AEMeasurable (fun xz : α × β => ‖H xz.2 xz.1‖ₑ ^ q) (μ.prod ν)) :
    ∫⁻ x, ‖∫ z, H z x ∂ν‖ₑ ^ q ∂μ ≤
      ∫⁻ z, ∫⁻ x, ‖H z x‖ₑ ^ q ∂μ ∂ν := by
  have hjensen : ∀ᵐ x ∂μ,
      ‖∫ z, H z x ∂ν‖ₑ ^ q ≤ ∫⁻ z, ‖H z x‖ₑ ^ q ∂ν := by
    filter_upwards [hsection, hsectionpow] with x hx hxp
    have hq0 : 0 ≤ q := le_trans zero_le_one hq
    have hreal :
        ‖∫ z, H z x ∂ν‖ ^ q ≤ ∫ z, ‖H z x‖ ^ q ∂ν := by
      have hconv : ConvexOn ℝ Set.univ (fun v : E => ‖v‖ ^ q) :=
        convexOn_norm_rpow hq
      have hcont : ContinuousOn (fun v : E => ‖v‖ ^ q) Set.univ := by
        exact (continuous_norm.rpow_const fun _ => Or.inr hq0).continuousOn
      exact hconv.map_integral_le hcont isClosed_univ
        (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hx hxp
    have hpow_eq :
        ∫ z, ‖H z x‖ ^ q ∂ν = (∫⁻ z, ‖H z x‖ₑ ^ q ∂ν).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae]
      · congr 1
        apply lintegral_congr
        intro z
        rw [← ofReal_norm,
          ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0]
      · exact Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _
      · exact hxp.aestronglyMeasurable
    calc
      ‖∫ z, H z x ∂ν‖ₑ ^ q = ENNReal.ofReal (‖∫ z, H z x ∂ν‖ ^ q) := by
        rw [← ofReal_norm,
          ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0]
      _ ≤ ENNReal.ofReal (∫ z, ‖H z x‖ ^ q ∂ν) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (∫⁻ z, ‖H z x‖ₑ ^ q ∂ν).toReal := by rw [hpow_eq]
      _ ≤ ∫⁻ z, ‖H z x‖ₑ ^ q ∂ν := ENNReal.ofReal_toReal_le
  calc
    ∫⁻ x, ‖∫ z, H z x ∂ν‖ₑ ^ q ∂μ ≤
        ∫⁻ x, ∫⁻ z, ‖H z x‖ₑ ^ q ∂ν ∂μ := by
      exact lintegral_mono_ae hjensen
    _ = ∫⁻ z, ∫⁻ x, ‖H z x‖ₑ ^ q ∂μ ∂ν :=
      lintegral_lintegral_swap hpow_meas

/-- Powered `L^p` control of an average against the convex kernel measure.
The three section hypotheses are analytic integrability obligations; later
transport lemmas discharge them from `MemLp` of a Gagliardo kernel. -/
theorem lintegral_convexApproxKernelAverage_rpow_le
    {d : ℕ} {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) [SFinite μ] {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    (H : Vec d → α → E) {q : ℝ} (hq : 1 ≤ q)
    (hsection : ∀ᵐ x ∂μ, Integrable (fun z => H z x) (convexApproxKernelMeasure ρ))
    (hsectionpow : ∀ᵐ x ∂μ, Integrable (fun z => ‖H z x‖ ^ q)
      (convexApproxKernelMeasure ρ))
    (hpow_meas : AEMeasurable (fun xz : α × Vec d => ‖H xz.2 xz.1‖ₑ ^ q)
      (μ.prod (convexApproxKernelMeasure ρ))) :
    ∫⁻ x, ‖∫ z in tsupport ρ, ρ z • H z x‖ₑ ^ q ∂μ ≤
      ∫⁻ z, ∫⁻ x, ‖H z x‖ₑ ^ q ∂μ ∂convexApproxKernelMeasure ρ := by
  let : IsProbabilityMeasure (convexApproxKernelMeasure ρ) :=
    isProbabilityMeasure_convexApproxKernelMeasure hρ
  have hintegral : ∀ x,
      (∫ z in tsupport ρ, ρ z • H z x) =
        ∫ z, H z x ∂convexApproxKernelMeasure ρ := by
    intro x
    exact setIntegral_smul_eq_integral_convexApproxKernelMeasure hρ (fun z => H z x)
  simp_rw [hintegral]
  exact lintegral_enorm_rpow_integral_le_lintegral_lintegral μ
    (convexApproxKernelMeasure ρ) hq hsection hsectionpow hpow_meas

/-- The preceding Jensen--Tonelli estimate specialized to diagonal affine
sampling of a fractional kernel. -/
theorem lintegral_diagonalConvexApproxAverage_rpow_le
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (μ : Measure (Vec d × Vec d)) [SFinite μ]
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    (K : Vec d × Vec d → E) (x0 : Vec d) (r ε : ℝ) {q : ℝ} (hq : 1 ≤ q)
    (hsection : ∀ᵐ xy ∂μ, Integrable
      (fun z => K (diagonalConvexApproxSample x0 z r ε xy))
      (convexApproxKernelMeasure ρ))
    (hsectionpow : ∀ᵐ xy ∂μ, Integrable
      (fun z => ‖K (diagonalConvexApproxSample x0 z r ε xy)‖ ^ q)
      (convexApproxKernelMeasure ρ))
    (hpow_meas : AEMeasurable
      (fun xyz : (Vec d × Vec d) × Vec d =>
        ‖K (diagonalConvexApproxSample x0 xyz.2 r ε xyz.1)‖ₑ ^ q)
      (μ.prod (convexApproxKernelMeasure ρ))) :
    ∫⁻ xy, ‖diagonalConvexApproxAverage ρ K x0 r ε xy‖ₑ ^ q ∂μ ≤
      ∫⁻ z, ∫⁻ xy,
        ‖K (diagonalConvexApproxSample x0 z r ε xy)‖ₑ ^ q ∂μ
          ∂convexApproxKernelMeasure ρ := by
  let : IsProbabilityMeasure (convexApproxKernelMeasure ρ) :=
    isProbabilityMeasure_convexApproxKernelMeasure hρ
  have haverage : ∀ xy,
      diagonalConvexApproxAverage ρ K x0 r ε xy =
        ∫ z, K (diagonalConvexApproxSample x0 z r ε xy)
          ∂convexApproxKernelMeasure ρ := by
    intro xy
    exact diagonalConvexApproxAverage_eq_integral_kernelMeasure hρ K x0 r ε xy
  simp_rw [haverage]
  exact lintegral_enorm_rpow_integral_le_lintegral_lintegral μ
    (convexApproxKernelMeasure ρ) hq hsection hsectionpow hpow_meas

end

end Homogenization
