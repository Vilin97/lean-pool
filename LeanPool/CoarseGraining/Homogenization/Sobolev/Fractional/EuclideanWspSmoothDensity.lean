/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ConvexApproxGagliardoLpBound
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspSmoothDual
public import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpCoordinate
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLp
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Convergence
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Smooth density for Euclidean fractional Sobolev fields

This module is the source-facing smooth-density layer for the Euclidean
fractional full norm on a triadic cube.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem cubeEuclideanWspField_component_memLpOn {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanWspField Q s p) (i : Fin d) :
    MemLpOn (openCubeSet Q) p.exponent (fun x => F.toField x i) := by
  rw [MemLpOn]
  have hcomponent : MemLp (fun x => F.toField x i) p.exponent
      (normalizedCubeMeasure Q) := by
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using
      F.euclideanMemLp.eval_piLp i
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at hcomponent
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹)
  have hc0 : c ≠ 0 := by
    dsimp only [c]
    exact ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (cubeVolume_pos Q))
  have hctop : c ≠ ⊤ := by
    dsimp only [c]
    exact ENNReal.ofReal_ne_top
  apply MemLp.of_measure_le_smul (μ := c • volume.restrict (openCubeSet Q))
    (c := c⁻¹) (ENNReal.inv_ne_top.2 hc0)
  · simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul] using
      (le_refl (volume.restrict (openCubeSet Q)))
  · simpa only [c] using hcomponent

/-- The global componentwise convex smoothing representative of a Euclidean
fractional field. -/
private noncomputable def cubeEuclideanWspConvexApproxSmoothField {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanWspField Q s p) (x0 : Vec d) (r ε : ℝ) : Vec d → Vec d :=
  fun x i => convexApproxSmoothRepresentative (openCubeSet Q)
    (unitConvexApproxKernel (d := d)) (fun y => F.toField y i) x0 r ε x

private theorem contDiff_cubeEuclideanWspConvexApproxSmoothField {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanWspField Q s p) (x0 : Vec d) {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞)
      (cubeEuclideanWspConvexApproxSmoothField F x0 r ε) := by
  rw [contDiff_pi]
  intro i
  exact contDiff_convexApproxSmoothRepresentative
    (isOpen_openCubeSet Q).measurableSet
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)) p.one_lt.le
    (cubeEuclideanWspField_component_memLpOn F i) hr hε

private noncomputable def cubeEuclideanWspConvexApproxSmoothTest {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanWspField Q s p) (x0 : Vec d) {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) : CubeEuclideanWspSmoothTest Q s p where
  toField := cubeEuclideanWspConvexApproxSmoothField F x0 r ε
  contDiff := contDiff_cubeEuclideanWspConvexApproxSmoothField F x0 hr hε

private theorem closedBall_halfCubeRadius_subset_openCubeSet {d : ℕ}
    (Q : TriadicCube d) :
    Metric.closedBall (cubeCenter Q) (cubeRadius Q / 2) ⊆ openCubeSet Q := by
  rw [← ball_cubeCenter_eq_openCubeSet]
  exact Metric.closedBall_subset_ball (half_lt_self (cubeRadius_pos Q))

private theorem tendsto_diagonalConvexApproxSample_atTop {d : ℕ}
    (Q : TriadicCube d) {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 ≤ r)
    (xy : Vec d × Vec d) (hxy : xy ∈ (openCubeSet Q) ×ˢ (openCubeSet Q))
    (z : Vec d) (hz : z ∈ tsupport (unitConvexApproxKernel (d := d))) :
    Filter.Tendsto
      (fun n : ℕ => diagonalConvexApproxSample x0 z r
        (unitConvexApproxScale n) xy)
      Filter.atTop (nhds xy) := by
  have hz_norm : ‖z‖ ≤ 1 := by
    have hzball := (isConvexApproxKernel_unitConvexApproxKernel (d := d)).support_subset_closedBall hz
    simpa only [Metric.mem_closedBall, dist_zero_right] using hzball
  have hε0 : ∀ n : ℕ, 0 ≤ unitConvexApproxScale n :=
    unitConvexApproxScale_nonneg
  have hbound : ∀ n : ℕ,
      dist (diagonalConvexApproxSample x0 z r (unitConvexApproxScale n) xy) xy ≤
        unitConvexApproxScale n *
          (2 * Classical.choose (isOpenBoundedConvexDomain_openCubeSet Q).isBoundedDomain) := by
    intro n
    rw [Prod.dist_eq]
    apply max_le
    · simpa only [dist_eq_norm_sub, diagonalConvexApproxSample_apply] using
        (norm_convexApproxSample_sub_le_two_mul_choose_of_isOpenBoundedConvexDomain
          (isOpenBoundedConvexDomain_openCubeSet Q) hxy.1 hball hr hz_norm (hε0 n))
    · simpa only [dist_eq_norm_sub, diagonalConvexApproxSample_apply] using
        (norm_convexApproxSample_sub_le_two_mul_choose_of_isOpenBoundedConvexDomain
          (isOpenBoundedConvexDomain_openCubeSet Q) hxy.2 hball hr hz_norm (hε0 n))
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hscaled : Filter.Tendsto
      (fun n : ℕ => unitConvexApproxScale n *
        (2 * Classical.choose (isOpenBoundedConvexDomain_openCubeSet Q).isBoundedDomain))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_unitConvexApproxScale_zero.mul_const
      (2 * Classical.choose (isOpenBoundedConvexDomain_openCubeSet Q).isBoundedDomain)
  have hC0 : 0 ≤ 2 * Classical.choose
      (isOpenBoundedConvexDomain_openCubeSet Q).isBoundedDomain := by
    exact mul_nonneg (by norm_num)
      (le_of_lt (Classical.choose_spec
        (isOpenBoundedConvexDomain_openCubeSet Q).isBoundedDomain).1)
  have hchoose0 : 0 ≤ Classical.choose
      (isOpenBoundedConvexDomain_openCubeSet Q).isBoundedDomain :=
    le_of_lt (Classical.choose_spec
      (isOpenBoundedConvexDomain_openCubeSet Q).isBoundedDomain).1
  filter_upwards [Metric.tendsto_nhds.mp hscaled δ hδ] with n hn
  exact lt_of_le_of_lt (hbound n) (by
    simpa [abs_of_nonneg (hε0 n), abs_of_nonneg hchoose0, Real.dist_eq] using hn)

private theorem tendsto_diagonalConvexApproxAverage_apply_of_boundedContinuous
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (Q : TriadicCube d)
    (G : BoundedContinuousFunction (Vec d × Vec d) E)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 ≤ r)
    (xy : Vec d × Vec d) (hxy : xy ∈ (openCubeSet Q) ×ˢ (openCubeSet Q)) :
    Filter.Tendsto
      (fun n : ℕ => diagonalConvexApproxAverage
        (unitConvexApproxKernel (d := d)) G x0 r (unitConvexApproxScale n) xy)
      Filter.atTop (nhds (G xy)) := by
  let ν := convexApproxKernelMeasure (unitConvexApproxKernel (d := d))
  let : IsProbabilityMeasure ν := by
    simpa only [ν] using
      isProbabilityMeasure_convexApproxKernelMeasure
        (isConvexApproxKernel_unitConvexApproxKernel (d := d))
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun z : Vec d => G (diagonalConvexApproxSample x0 z r
        (unitConvexApproxScale n) xy)) ν := by
    intro n
    exact (G.continuous.comp (by
      change Continuous (fun z : Vec d =>
        ((1 - unitConvexApproxScale n) • xy.1 +
          unitConvexApproxScale n • (x0 - r • z),
         (1 - unitConvexApproxScale n) • xy.2 +
          unitConvexApproxScale n • (x0 - r • z)))
      fun_prop)).aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ z ∂ν,
      ‖G (diagonalConvexApproxSample x0 z r (unitConvexApproxScale n) xy)‖ ≤ ‖G‖ := by
    intro n
    exact Filter.Eventually.of_forall fun z => G.norm_coe_le_norm _
  have hlim : ∀ᵐ z ∂ν,
      Filter.Tendsto
        (fun n : ℕ => G (diagonalConvexApproxSample x0 z r
          (unitConvexApproxScale n) xy))
        Filter.atTop (nhds (G xy)) := by
    filter_upwards [ae_mem_tsupport_convexApproxKernelMeasure
      (ρ := unitConvexApproxKernel (d := d))] with z hz
    exact (G.continuous.tendsto xy).comp
      (tendsto_diagonalConvexApproxSample_atTop Q hball hr xy hxy z hz)
  have hint : Filter.Tendsto
      (fun n : ℕ => ∫ z, G (diagonalConvexApproxSample x0 z r
        (unitConvexApproxScale n) xy) ∂ν)
      Filter.atTop (nhds (∫ _z, G xy ∂ν)) := by
    exact tendsto_integral_of_dominated_convergence (fun _ => ‖G‖)
      hmeas (integrable_const ‖G‖) hbound hlim
  rw [show (fun n : ℕ => diagonalConvexApproxAverage
      (unitConvexApproxKernel (d := d)) G x0 r (unitConvexApproxScale n) xy) =
      fun n : ℕ => ∫ z, G (diagonalConvexApproxSample x0 z r
        (unitConvexApproxScale n) xy) ∂ν by
      funext n
      simpa only [ν] using
        (diagonalConvexApproxAverage_eq_integral_kernelMeasure
          (isConvexApproxKernel_unitConvexApproxKernel (d := d)) G x0 r
          (unitConvexApproxScale n) xy)]
  simpa using hint

private theorem aestronglyMeasurable_diagonalConvexApproxAverage_of_boundedContinuous
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (Q : TriadicCube d)
    (G : BoundedContinuousFunction (Vec d × Vec d) E)
    (x0 : Vec d) (r ε : ℝ) :
    AEStronglyMeasurable
      (diagonalConvexApproxAverage (unitConvexApproxKernel (d := d)) G x0 r ε)
      (Gagliardo.gagliardoCubeMeasure Q) := by
  let μ := Gagliardo.gagliardoCubeMeasure Q
  let ν := convexApproxKernelMeasure (unitConvexApproxKernel (d := d))
  let : IsProbabilityMeasure ν := by
    simpa only [ν] using
      isProbabilityMeasure_convexApproxKernelMeasure
        (isConvexApproxKernel_unitConvexApproxKernel (d := d))
  have hjoint : AEStronglyMeasurable
      (fun xyz : (Vec d × Vec d) × Vec d =>
        G (diagonalConvexApproxSample x0 xyz.2 r ε xyz.1)) (μ.prod ν) := by
    exact (G.continuous.comp (by
      change Continuous (fun xyz : (Vec d × Vec d) × Vec d =>
        ((1 - ε) • xyz.1.1 + ε • (x0 - r • xyz.2),
         (1 - ε) • xyz.1.2 + ε • (x0 - r • xyz.2)))
      fun_prop)).aestronglyMeasurable
  have havg : AEStronglyMeasurable
      (fun xy => ∫ z, G (diagonalConvexApproxSample x0 z r ε xy) ∂ν) μ :=
    hjoint.integral_prod_right'
  simpa only [ν] using havg.congr
    (Filter.Eventually.of_forall fun xy =>
      (diagonalConvexApproxAverage_eq_integral_kernelMeasure
        (isConvexApproxKernel_unitConvexApproxKernel (d := d)) G x0 r ε xy).symm)

private theorem ae_mem_openCubeProduct_gagliardoCubeMeasure {d : ℕ}
    (Q : TriadicCube d) :
    ∀ᵐ xy ∂Gagliardo.gagliardoCubeMeasure Q,
      xy ∈ (openCubeSet Q) ×ˢ (openCubeSet Q) := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹)
  let μ := (volume.restrict (openCubeSet Q)).prod
    (volume.restrict (openCubeSet Q))
  have hμ : ∀ᵐ xy ∂μ, xy ∈ (openCubeSet Q) ×ˢ (openCubeSet Q) := by
    rw [MeasureTheory.ae_iff]
    change μ ((openCubeSet Q) ×ˢ (openCubeSet Q))ᶜ = 0
    dsimp only [μ]
    rw [Measure.prod_restrict]
    rw [Measure.restrict_apply
      ((isOpen_openCubeSet Q).measurableSet.prod (isOpen_openCubeSet Q).measurableSet).compl]
    rw [Set.compl_inter_self, MeasureTheory.measure_empty]
  rw [Gagliardo.gagliardoCubeMeasure, normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet, Measure.prod_smul_left]
  change ∀ᵐ xy ∂c • μ, xy ∈ (openCubeSet Q) ×ˢ (openCubeSet Q)
  exact Measure.ae_smul_measure hμ c

private theorem norm_diagonalConvexApproxAverage_le_norm_boundedContinuous
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : BoundedContinuousFunction (Vec d × Vec d) E)
    (x0 : Vec d) (r ε : ℝ) (xy : Vec d × Vec d) :
    ‖diagonalConvexApproxAverage (unitConvexApproxKernel (d := d)) G x0 r ε xy‖ ≤
      ‖G‖ := by
  let ν := convexApproxKernelMeasure (unitConvexApproxKernel (d := d))
  let : IsProbabilityMeasure ν := by
    simpa only [ν] using
      isProbabilityMeasure_convexApproxKernelMeasure
        (isConvexApproxKernel_unitConvexApproxKernel (d := d))
  rw [diagonalConvexApproxAverage_eq_integral_kernelMeasure
    (isConvexApproxKernel_unitConvexApproxKernel (d := d))]
  simpa only [MeasureTheory.measureReal_def, MeasureTheory.measure_univ,
    ENNReal.toReal_one, mul_one] using
    (norm_integral_le_of_norm_le_const
      (μ := ν) (Filter.Eventually.of_forall fun z => G.norm_coe_le_norm _))

private theorem tendsto_eLpNorm_diagonalConvexApproxAverage_sub_zero_of_boundedContinuous
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (Q : TriadicCube d) (p : FiniteLpExponent)
    (G : BoundedContinuousFunction (Vec d × Vec d) E)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 ≤ r) :
    Filter.Tendsto
      (fun n : ℕ => eLpNorm
        (fun xy => diagonalConvexApproxAverage
          (unitConvexApproxKernel (d := d)) G x0 r
            (unitConvexApproxScale n) xy - G xy)
        p.exponent (Gagliardo.gagliardoCubeMeasure Q))
      Filter.atTop (nhds 0) := by
  let μ := Gagliardo.gagliardoCubeMeasure Q
  let q := p.exponent.toReal
  let C : ℝ≥0∞ := ENNReal.ofReal (2 * ‖G‖) ^ q
  have hqpos : 0 < q := by
    dsimp only [q]
    exact ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun xy => ‖diagonalConvexApproxAverage
          (unitConvexApproxKernel (d := d)) G x0 r
            (unitConvexApproxScale n) xy - G xy‖ₑ ^ q) μ := by
    intro n
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((aestronglyMeasurable_diagonalConvexApproxAverage_of_boundedContinuous
        Q G x0 r (unitConvexApproxScale n)).sub
          G.continuous.aestronglyMeasurable).enorm
  have hbound : ∀ n : ℕ, (fun xy => ‖diagonalConvexApproxAverage
        (unitConvexApproxKernel (d := d)) G x0 r
          (unitConvexApproxScale n) xy - G xy‖ₑ ^ q) ≤ᵐ[μ]
      fun _ => C := by
    intro n
    filter_upwards with xy
    have havg : ‖diagonalConvexApproxAverage
        (unitConvexApproxKernel (d := d)) G x0 r
          (unitConvexApproxScale n) xy‖ ≤ ‖G‖ :=
      norm_diagonalConvexApproxAverage_le_norm_boundedContinuous G x0 r
        (unitConvexApproxScale n) xy
    have hnorm : ‖diagonalConvexApproxAverage
        (unitConvexApproxKernel (d := d)) G x0 r
          (unitConvexApproxScale n) xy - G xy‖ ≤ 2 * ‖G‖ := by
      calc
        ‖diagonalConvexApproxAverage
            (unitConvexApproxKernel (d := d)) G x0 r
              (unitConvexApproxScale n) xy - G xy‖ ≤
            ‖diagonalConvexApproxAverage
              (unitConvexApproxKernel (d := d)) G x0 r
                (unitConvexApproxScale n) xy‖ + ‖G xy‖ := norm_sub_le _ _
        _ ≤ ‖G‖ + ‖G‖ := add_le_add havg (G.norm_coe_le_norm _)
        _ = 2 * ‖G‖ := by ring
    exact ENNReal.rpow_le_rpow (by
      simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hnorm) hq0
  have hfin : ∫⁻ _xy, C ∂μ ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hq0 ENNReal.ofReal_ne_top)
      (MeasureTheory.measure_lt_top μ Set.univ).ne
  have hlim : ∀ᵐ xy ∂μ, Filter.Tendsto
      (fun n : ℕ => ‖diagonalConvexApproxAverage
          (unitConvexApproxKernel (d := d)) G x0 r
            (unitConvexApproxScale n) xy - G xy‖ₑ ^ q)
        Filter.atTop (nhds 0) := by
    filter_upwards [ae_mem_openCubeProduct_gagliardoCubeMeasure Q] with xy hxy
    have hpoint := tendsto_diagonalConvexApproxAverage_apply_of_boundedContinuous
      Q G hball hr xy hxy
    have hsub : Filter.Tendsto
        (fun n : ℕ => diagonalConvexApproxAverage
          (unitConvexApproxKernel (d := d)) G x0 r
            (unitConvexApproxScale n) xy - G xy)
        Filter.atTop (nhds 0) := by
      have hconst : Filter.Tendsto (fun _n : ℕ => G xy)
          Filter.atTop (nhds (G xy)) := tendsto_const_nhds
      simpa using hpoint.sub hconst
    have henorm := (continuous_enorm.tendsto (0 : E)).comp hsub
    have henorm' : Filter.Tendsto
        (fun n : ℕ => ‖diagonalConvexApproxAverage
          (unitConvexApproxKernel (d := d)) G x0 r
            (unitConvexApproxScale n) xy - G xy‖ₑ)
        Filter.atTop (nhds 0) := by
      simpa only [Function.comp_apply, enorm_zero] using! henorm
    have hrpow := ((ENNReal.continuous_rpow_const (y := q)).tendsto
      (0 : ℝ≥0∞)).comp henorm'
    simpa only [Function.comp_apply, enorm_zero, ENNReal.zero_rpow_of_pos hqpos] using! hrpow
  have hpower : Filter.Tendsto
      (fun n : ℕ => ∫⁻ xy, ‖diagonalConvexApproxAverage
          (unitConvexApproxKernel (d := d)) G x0 r
            (unitConvexApproxScale n) xy - G xy‖ₑ ^ q ∂μ)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence'
      (fun _ => C) hmeas hbound hfin hlim
  rw [show (fun n : ℕ => eLpNorm
      (fun xy => diagonalConvexApproxAverage
        (unitConvexApproxKernel (d := d)) G x0 r
          (unitConvexApproxScale n) xy - G xy)
      p.exponent μ) = fun n : ℕ =>
        (∫⁻ xy, ‖diagonalConvexApproxAverage
          (unitConvexApproxKernel (d := d)) G x0 r
            (unitConvexApproxScale n) xy - G xy‖ₑ ^ q ∂μ) ^ (1 / q) by
      funext n
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne]]
  have hrpow : Filter.Tendsto
      (fun n : ℕ => (∫⁻ xy, ‖diagonalConvexApproxAverage
        (unitConvexApproxKernel (d := d)) G x0 r
          (unitConvexApproxScale n) xy - G xy‖ₑ ^ q ∂μ) ^ (1 / q))
      Filter.atTop (nhds 0) :=
    by
      have hraw := ((ENNReal.continuous_rpow_const (y := 1 / q)).tendsto
        (0 : ℝ≥0∞)).comp hpower
      have hzero : (0 : ℝ≥0∞) ^ (1 / q) = 0 :=
        by simpa only [one_div] using ENNReal.zero_rpow_of_pos (inv_pos.mpr hqpos)
      simpa only [Function.comp_apply, hzero] using! hraw
  simpa only [Function.comp_apply, ENNReal.zero_rpow_of_pos (inv_pos.mpr hqpos)] using hrpow

private theorem memLp_comp_diagonalConvexApproxJointSample {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [TopologicalSpace E] [ContinuousENorm E]
    (Q : TriadicCube d) (p : FiniteLpExponent) (K : Vec d × Vec d → E)
    (hK : MemLp K p.exponent (Gagliardo.gagliardoCubeMeasure Q))
    {x0 : Vec d} {r ε : ℝ} (hε : ε < 1)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    MemLp
      (K ∘ diagonalConvexApproxJointSample x0 r ε)
      p.exponent
      ((Gagliardo.gagliardoCubeMeasure Q).prod
        (convexApproxKernelMeasure (unitConvexApproxKernel (d := d))) ) := by
  let μ := Gagliardo.gagliardoCubeMeasure Q
  let ν := convexApproxKernelMeasure (unitConvexApproxKernel (d := d))
  let J : ℝ≥0∞ := ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ 2
  let T := diagonalConvexApproxJointSample x0 r ε
  let : IsProbabilityMeasure ν := by
    simpa only [ν] using isProbabilityMeasure_convexApproxKernelMeasure
      (isConvexApproxKernel_unitConvexApproxKernel (d := d))
  have hmap : Measure.map T (μ.prod ν) ≤ J • μ := by
    simpa only [μ, ν, J, T] using
      (map_diagonalConvexApproxJointSample_le Q
        (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hε hball hr hε0 hε1)
  have hJtop : J ≠ ⊤ := by
    dsimp only [J]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hKmap : MemLp K p.exponent (Measure.map T (μ.prod ν)) :=
    MemLp.of_measure_le_smul hJtop hmap hK
  exact (memLp_map_measure_iff hKmap.aestronglyMeasurable
    (measurable_diagonalConvexApproxJointSample x0 r ε).aemeasurable).mp hKmap

private theorem ae_diagonalConvexApproxAverage_sub {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) (p : FiniteLpExponent)
    (K L : Vec d × Vec d → E)
    (hK : MemLp K p.exponent (Gagliardo.gagliardoCubeMeasure Q))
    (hL : MemLp L p.exponent (Gagliardo.gagliardoCubeMeasure Q))
    {x0 : Vec d} {r ε : ℝ} (hε : ε < 1)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (fun xy => diagonalConvexApproxAverage
        (unitConvexApproxKernel (d := d)) (K - L) x0 r ε xy) =ᵐ[
          Gagliardo.gagliardoCubeMeasure Q]
      fun xy => diagonalConvexApproxAverage
          (unitConvexApproxKernel (d := d)) K x0 r ε xy -
        diagonalConvexApproxAverage
          (unitConvexApproxKernel (d := d)) L x0 r ε xy := by
  let μ := Gagliardo.gagliardoCubeMeasure Q
  let ν := convexApproxKernelMeasure (unitConvexApproxKernel (d := d))
  let : IsProbabilityMeasure ν := by
    simpa only [ν] using isProbabilityMeasure_convexApproxKernelMeasure
      (isConvexApproxKernel_unitConvexApproxKernel (d := d))
  let : SFinite ν := inferInstance
  let : IsFiniteMeasure μ := inferInstance
  let : IsFiniteMeasure (μ.prod ν) := inferInstance
  have hKjoint := memLp_comp_diagonalConvexApproxJointSample
    Q p K hK hε hball hr hε0 hε1
  have hLjoint := memLp_comp_diagonalConvexApproxJointSample
    Q p L hL hε hball hr hε0 hε1
  have hKsection : ∀ᵐ xy ∂μ, Integrable
      (fun z => K (diagonalConvexApproxSample x0 z r ε xy)) ν := by
    simpa only [Function.comp_apply, diagonalConvexApproxJointSample] using
      (hKjoint.integrable p.one_lt.le).prod_right_ae
  have hLsection : ∀ᵐ xy ∂μ, Integrable
      (fun z => L (diagonalConvexApproxSample x0 z r ε xy)) ν := by
    simpa only [Function.comp_apply, diagonalConvexApproxJointSample] using
      (hLjoint.integrable p.one_lt.le).prod_right_ae
  filter_upwards [hKsection, hLsection] with xy hKxy hLxy
  rw [diagonalConvexApproxAverage_eq_integral_kernelMeasure
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)) (K - L) x0 r ε xy,
    diagonalConvexApproxAverage_eq_integral_kernelMeasure
      (isConvexApproxKernel_unitConvexApproxKernel (d := d)) K x0 r ε xy,
    diagonalConvexApproxAverage_eq_integral_kernelMeasure
      (isConvexApproxKernel_unitConvexApproxKernel (d := d)) L x0 r ε xy]
  exact integral_sub hKxy hLxy

private theorem aestronglyMeasurable_diagonalConvexApproxAverage_of_memLp
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (Q : TriadicCube d) (p : FiniteLpExponent)
    (K : Vec d × Vec d → E)
    (hK : MemLp K p.exponent (Gagliardo.gagliardoCubeMeasure Q))
    {x0 : Vec d} {r ε : ℝ} (hε : ε < 1)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    AEStronglyMeasurable
      (diagonalConvexApproxAverage (unitConvexApproxKernel (d := d)) K x0 r ε)
      (Gagliardo.gagliardoCubeMeasure Q) := by
  let μ := Gagliardo.gagliardoCubeMeasure Q
  let ν := convexApproxKernelMeasure (unitConvexApproxKernel (d := d))
  let : IsProbabilityMeasure ν := by
    simpa only [ν] using isProbabilityMeasure_convexApproxKernelMeasure
      (isConvexApproxKernel_unitConvexApproxKernel (d := d))
  have hjoint := memLp_comp_diagonalConvexApproxJointSample
    Q p K hK hε hball hr hε0 hε1
  have havg : AEStronglyMeasurable
      (fun xy => ∫ z, K (diagonalConvexApproxSample x0 z r ε xy) ∂ν) μ := by
    exact hjoint.aestronglyMeasurable.integral_prod_right'
  simpa only [μ, ν] using havg.congr
    (Filter.Eventually.of_forall fun xy =>
      (diagonalConvexApproxAverage_eq_integral_kernelMeasure
        (isConvexApproxKernel_unitConvexApproxKernel (d := d)) K x0 r ε xy).symm)

private theorem tendsto_eLpNorm_diagonalConvexApproxAverage_sub_zero_of_memLp
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (Q : TriadicCube d) (p : FiniteLpExponent)
    (K : Vec d × Vec d → E)
    (hK : MemLp K p.exponent (Gagliardo.gagliardoCubeMeasure Q))
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 ≤ r) :
    Filter.Tendsto
      (fun n : ℕ => eLpNorm
        (fun xy => diagonalConvexApproxAverage
          (unitConvexApproxKernel (d := d)) K x0 r
            (unitConvexApproxScale n) xy - K xy)
        p.exponent (Gagliardo.gagliardoCubeMeasure Q))
      Filter.atTop (nhds 0) := by
  let μ := Gagliardo.gagliardoCubeMeasure Q
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  by_cases hηtop : η = ⊤
  · exact Filter.Eventually.of_forall (fun n => by simp [hηtop])
  obtain ⟨η₁, hη₁_pos, hη₁⟩ :=
    MeasureTheory.exists_Lp_half (μ := μ) (ε := E) (p := p.exponent) hη.ne'
  obtain ⟨η₂, hη₂_pos, hη₂⟩ :=
    MeasureTheory.exists_Lp_half (μ := μ) (ε := E) (p := p.exponent) hη₁_pos.ne'
  have hevent_pos : ∀ᶠ n : ℕ in Filter.atTop,
      0 < unitConvexApproxScale n :=
    Filter.Eventually.of_forall (fun n => by
      dsimp [unitConvexApproxScale]
      positivity)
  have hevent_half : ∀ᶠ n : ℕ in Filter.atTop,
      unitConvexApproxScale n < (1 / 2 : ℝ) :=
    (tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 _ (by positivity)
  let C : ℝ≥0∞ :=
    (ENNReal.ofReal (((1 / 2 : ℝ) ^ d)⁻¹) ^ 2) ^ (1 / p.exponent).toReal
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have hC_ne_zero : C ≠ 0 := ne_of_gt hC_pos
  have hC_ne_top : C ≠ ⊤ := by
    dsimp [C]
    exact (ENNReal.rpow_lt_top_of_nonneg (by positivity)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).ne
  let δ : ℝ≥0∞ := min η₂ (η₁ / C)
  have hδ_pos : 0 < δ := by
    have hdiv : 0 < η₁ / C := ENNReal.div_pos hη₁_pos.ne' hC_ne_top
    dsimp only [δ]
    exact lt_min hη₂_pos hdiv
  obtain ⟨G, happrox, hG⟩ :=
    hK.exists_boundedContinuous_eLpNorm_sub_le p.lt_top.ne (ε := δ) hδ_pos.ne'
  have hdiff : MemLp (K - (G : Vec d × Vec d → E)) p.exponent μ := hK.sub hG
  have hthird : eLpNorm ((G : Vec d × Vec d → E) - K) p.exponent μ ≤ η₂ := by
    calc
      eLpNorm ((G : Vec d × Vec d → E) - K) p.exponent μ =
          eLpNorm (K - (G : Vec d × Vec d → E)) p.exponent μ := by
        rw [← eLpNorm_neg]
        apply eLpNorm_congr_ae
        filter_upwards with xy
        simp only [Pi.sub_apply, neg_sub]
      _ ≤ δ := happrox
      _ ≤ η₂ := min_le_left _ _
  have hmiddle_tendsto :=
    tendsto_eLpNorm_diagonalConvexApproxAverage_sub_zero_of_boundedContinuous
      Q p G hball hr
  have hmiddle_eventually : ∀ᶠ n : ℕ in Filter.atTop,
      eLpNorm (fun xy => diagonalConvexApproxAverage
        (unitConvexApproxKernel (d := d)) G x0 r
          (unitConvexApproxScale n) xy - G xy) p.exponent μ ≤ η₂ :=
    ENNReal.tendsto_nhds_zero.1 hmiddle_tendsto η₂ hη₂_pos
  have hfirst_eventually : ∀ᶠ n : ℕ in Filter.atTop,
      eLpNorm (fun xy => diagonalConvexApproxAverage
        (unitConvexApproxKernel (d := d)) K x0 r
          (unitConvexApproxScale n) xy - diagonalConvexApproxAverage
            (unitConvexApproxKernel (d := d)) G x0 r
              (unitConvexApproxScale n) xy) p.exponent μ ≤ η₁ := by
    filter_upwards [hevent_pos, hevent_half] with n hεpos hεhalf
    have hfactor :
        (ENNReal.ofReal (((1 - unitConvexApproxScale n) ^ d)⁻¹) ^ 2) ^
            (1 / p.exponent).toReal ≤ C := by
      have hhalf : (1 / 2 : ℝ) ≤ 1 - unitConvexApproxScale n := by linarith
      have hpow : (1 / 2 : ℝ) ^ d ≤ (1 - unitConvexApproxScale n) ^ d :=
        pow_le_pow_left₀ (by positivity) hhalf d
      have hhalf_pos : 0 < (1 / 2 : ℝ) ^ d := by positivity
      have hinv : ((1 - unitConvexApproxScale n) ^ d)⁻¹ ≤
          ((1 / 2 : ℝ) ^ d)⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hhalf_pos hpow
      exact ENNReal.rpow_le_rpow
        (pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal hinv) 2) (by positivity)
    have hεlt : unitConvexApproxScale n < 1 := by linarith
    have hrewrite := ae_diagonalConvexApproxAverage_sub
      Q p K G hK hG hεlt hball hr hεpos.le (by linarith)
    calc
      eLpNorm (fun xy => diagonalConvexApproxAverage
          (unitConvexApproxKernel (d := d)) K x0 r
            (unitConvexApproxScale n) xy - diagonalConvexApproxAverage
              (unitConvexApproxKernel (d := d)) G x0 r
                (unitConvexApproxScale n) xy) p.exponent μ
        = eLpNorm (diagonalConvexApproxAverage
          (unitConvexApproxKernel (d := d)) (K - (G : Vec d × Vec d → E)) x0 r
            (unitConvexApproxScale n)) p.exponent μ := by
              apply eLpNorm_congr_ae
              exact hrewrite.symm
      _ ≤ (ENNReal.ofReal (((1 - unitConvexApproxScale n) ^ d)⁻¹) ^ 2) ^
            (1 / p.exponent).toReal * eLpNorm (K - (G : Vec d × Vec d → E)) p.exponent μ := by
              exact eLpNorm_diagonalConvexApproxAverage_le_of_memLp Q p
                (K - (G : Vec d × Vec d → E)) hdiff
                (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hεlt hball hr
                hεpos.le (by linarith)
      _ ≤ (ENNReal.ofReal (((1 - unitConvexApproxScale n) ^ d)⁻¹) ^ 2) ^
            (1 / p.exponent).toReal * δ := by gcongr
      _ ≤ C * δ := by gcongr
      _ ≤ C * (η₁ / C) := by
        gcongr
        exact min_le_right _ _
      _ = η₁ := ENNReal.mul_div_cancel hC_ne_zero hC_ne_top
  filter_upwards [hevent_pos, hevent_half, hfirst_eventually, hmiddle_eventually] with
      n hεpos hεhalf hfirst hmiddle
  let A : Vec d × Vec d → E := fun xy => diagonalConvexApproxAverage
    (unitConvexApproxKernel (d := d)) K x0 r (unitConvexApproxScale n) xy -
      diagonalConvexApproxAverage (unitConvexApproxKernel (d := d)) G x0 r
        (unitConvexApproxScale n) xy
  let B : Vec d × Vec d → E := fun xy =>
    (diagonalConvexApproxAverage (unitConvexApproxKernel (d := d)) G x0 r
      (unitConvexApproxScale n) xy - G xy) + (G xy - K xy)
  have hAmeas : AEStronglyMeasurable A μ := by
    dsimp only [A]
    exact (aestronglyMeasurable_diagonalConvexApproxAverage_of_memLp Q p K hK
      (by linarith) hball hr hεpos.le (by linarith)).sub
        (aestronglyMeasurable_diagonalConvexApproxAverage_of_boundedContinuous Q G x0 r
          (unitConvexApproxScale n))
  have hBmeas : AEStronglyMeasurable B μ := by
    dsimp only [B]
    exact
      ((aestronglyMeasurable_diagonalConvexApproxAverage_of_boundedContinuous Q G x0 r
        (unitConvexApproxScale n)).sub G.continuous.aestronglyMeasurable).add
        (hG.aestronglyMeasurable.sub hK.aestronglyMeasurable)
  have hBnorm : eLpNorm B p.exponent μ < η₁ :=
    hη₂ _ _
      ((aestronglyMeasurable_diagonalConvexApproxAverage_of_boundedContinuous Q G x0 r
        (unitConvexApproxScale n)).sub G.continuous.aestronglyMeasurable)
      (hG.aestronglyMeasurable.sub hK.aestronglyMeasurable)
      hmiddle hthird
  have hsum : eLpNorm (A + B) p.exponent μ < η :=
    hη₁ _ _ hAmeas hBmeas hfirst hBnorm.le
  calc
    eLpNorm (fun xy => diagonalConvexApproxAverage
        (unitConvexApproxKernel (d := d)) K x0 r
          (unitConvexApproxScale n) xy - K xy) p.exponent μ
      = eLpNorm (A + B) p.exponent μ := by
          apply eLpNorm_congr_ae
          filter_upwards with xy
          change diagonalConvexApproxAverage (unitConvexApproxKernel (d := d)) K x0 r
              (unitConvexApproxScale n) xy - K xy =
            (diagonalConvexApproxAverage (unitConvexApproxKernel (d := d)) K x0 r
                (unitConvexApproxScale n) xy - diagonalConvexApproxAverage
                  (unitConvexApproxKernel (d := d)) G x0 r (unitConvexApproxScale n) xy) +
              ((diagonalConvexApproxAverage (unitConvexApproxKernel (d := d)) G x0 r
                (unitConvexApproxScale n) xy - G xy) + (G xy - K xy))
          abel
    _ ≤ η := hsum.le

private theorem cubeEuclideanWspKernel_convexApproxSmoothField_eq_scaled_average_of_integrable
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanWspField Q s p) (x0 : Vec d) (r ε : ℝ)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 < r)
    (hε0 : 0 < ε) (hε1 : ε < 1) (xy : Vec d × Vec d)
    (hxy : xy ∈ (openCubeSet Q) ×ˢ (openCubeSet Q))
    (hint : ∀ i : Fin d,
      Integrable (fun z : Vec d => F.toField
        (convexApproxSample x0 z r ε xy.1) i)
          (convexApproxKernelMeasure (unitConvexApproxKernel (d := d))) ∧
      Integrable (fun z : Vec d => F.toField
        (convexApproxSample x0 z r ε xy.2) i)
          (convexApproxKernelMeasure (unitConvexApproxKernel (d := d)))) :
    cubeEuclideanWspKernel s p
        (cubeEuclideanWspConvexApproxSmoothField F x0 r ε) xy =
      ((1 - ε) ^ (s.1 + (d : ℝ) / p.exponent.toReal)) •
        diagonalConvexApproxAverage (unitConvexApproxKernel (d := d))
          (cubeEuclideanWspKernel s p F.toField) x0 r ε xy := by
  let ν := convexApproxKernelMeasure (unitConvexApproxKernel (d := d))
  let S := cubeEuclideanWspConvexApproxSmoothField F x0 r ε
  have hρ : IsConvexApproxKernel (unitConvexApproxKernel (d := d)) :=
    isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hS : S xy.1 - S xy.2 = ∫ z, F.toField
      (convexApproxSample x0 z r ε xy.1) - F.toField
        (convexApproxSample x0 z r ε xy.2) ∂ν := by
    ext i
    rw [eval_integral]
    · simp only [Pi.sub_apply]
      rw [integral_sub (hint i).1 (hint i).2]
      simp only [S, cubeEuclideanWspConvexApproxSmoothField]
      rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
          (isOpenBoundedConvexDomain_openCubeSet Q) hρ hxy.1 hball hr hε0 hε1,
        convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
          (isOpenBoundedConvexDomain_openCubeSet Q) hρ hxy.2 hball hr hε0 hε1]
      rw [convexApproxSmoothing_apply, convexApproxSmoothing_apply]
      simp only [convexApproxIntegrand_apply]
      change (∫ z in tsupport (unitConvexApproxKernel (d := d)),
          (unitConvexApproxKernel (d := d)) z • F.toField
            (convexApproxSample x0 z r ε xy.1) i) -
          ∫ z in tsupport (unitConvexApproxKernel (d := d)),
            (unitConvexApproxKernel (d := d)) z • F.toField
              (convexApproxSample x0 z r ε xy.2) i = _
      rw [setIntegral_smul_eq_integral_convexApproxKernelMeasure hρ,
        setIntegral_smul_eq_integral_convexApproxKernelMeasure hρ]
    · intro j
      exact (hint j).1.sub (hint j).2
  have hinter : Integrable (fun z : Vec d => F.toField
      (convexApproxSample x0 z r ε xy.1) - F.toField
        (convexApproxSample x0 z r ε xy.2)) ν := by
    apply Integrable.of_eval
    intro i
    simpa only [Pi.sub_apply] using! (hint i).1.sub (hint i).2
  rw [show cubeEuclideanWspConvexApproxSmoothField F x0 r ε = S by rfl,
    cubeEuclideanWspKernel_apply, hS]
  change (euclideanDist xy.1 xy.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal))) •
      (HilbertVec.ofVecL d) (∫ z, F.toField
        (convexApproxSample x0 z r ε xy.1) - F.toField
          (convexApproxSample x0 z r ε xy.2) ∂ν) = _
  rw [← (HilbertVec.ofVecL d).integral_comp_comm hinter,
    ← integral_smul,
    diagonalConvexApproxAverage_eq_integral_kernelMeasure hρ]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with z
  simpa only [S, cubeEuclideanWspConvexApproxSmoothField,
    HilbertVec.ofVecL_apply, cubeEuclideanWspKernel_apply, Pi.sub_apply] using
    (cubeEuclideanWspKernel_comp_diagonalConvexApproxSample s p F.toField
      x0 z r ε hε1 xy)

private theorem cubeEuclideanWspField_component_comp_fst_memLpGagliardo
    {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanWspField Q s p) (i : Fin d) :
    MemLp (fun xy : Vec d × Vec d => F.toField xy.1 i) p.exponent
      (Gagliardo.gagliardoCubeMeasure Q) := by
  let ν := volume.restrict (cubeSet Q)
  let : IsFiniteMeasure ν := by
    simpa only [ν, ← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hcomponent : MemLp (fun x => F.toField x i) p.exponent
      (normalizedCubeMeasure Q) := by
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using
      F.euclideanMemLp.eval_piLp i
  simpa only [ν, Gagliardo.gagliardoCubeMeasure] using! hcomponent.comp_fst ν

private theorem cubeEuclideanWspField_component_comp_snd_memLpGagliardo
    {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanWspField Q s p) (i : Fin d) :
    MemLp (fun xy : Vec d × Vec d => F.toField xy.2 i) p.exponent
      (Gagliardo.gagliardoCubeMeasure Q) := by
  let μ := normalizedCubeMeasure Q
  let : IsFiniteMeasure μ := inferInstance
  have hcomponent : MemLp (fun x => F.toField x i) p.exponent
      (volume.restrict (cubeSet Q)) := by
    simpa only [MemLpOn, ← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
      cubeEuclideanWspField_component_memLpOn F i
  simpa only [μ, Gagliardo.gagliardoCubeMeasure] using! hcomponent.comp_snd μ

private theorem ae_integrable_diagonalConvexApproxSample_components
    {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanWspField Q s p) (x0 : Vec d) (r ε : ℝ)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    ∀ᵐ xy ∂Gagliardo.gagliardoCubeMeasure Q, ∀ i : Fin d,
      Integrable (fun z : Vec d => F.toField
        (convexApproxSample x0 z r ε xy.1) i)
          (convexApproxKernelMeasure (unitConvexApproxKernel (d := d))) ∧
      Integrable (fun z : Vec d => F.toField
        (convexApproxSample x0 z r ε xy.2) i)
          (convexApproxKernelMeasure (unitConvexApproxKernel (d := d))) := by
  let μ := Gagliardo.gagliardoCubeMeasure Q
  let ν := convexApproxKernelMeasure (unitConvexApproxKernel (d := d))
  let : IsFiniteMeasure μ := inferInstance
  let : IsProbabilityMeasure ν := by
    simpa only [ν] using isProbabilityMeasure_convexApproxKernelMeasure
      (isConvexApproxKernel_unitConvexApproxKernel (d := d))
  let : IsFiniteMeasure (μ.prod ν) := inferInstance
  have hfst : ∀ i : Fin d, MemLp
      ((fun xy : Vec d × Vec d => F.toField xy.1 i) ∘
        diagonalConvexApproxJointSample x0 r ε) p.exponent
      (μ.prod ν) := by
    intro i
    exact memLp_comp_diagonalConvexApproxJointSample Q p _
      (cubeEuclideanWspField_component_comp_fst_memLpGagliardo F i) hε1 hball hr hε0 hε1.le
  have hsnd : ∀ i : Fin d, MemLp
      ((fun xy : Vec d × Vec d => F.toField xy.2 i) ∘
        diagonalConvexApproxJointSample x0 r ε) p.exponent
      (μ.prod ν) := by
    intro i
    exact memLp_comp_diagonalConvexApproxJointSample Q p _
      (cubeEuclideanWspField_component_comp_snd_memLpGagliardo F i) hε1 hball hr hε0 hε1.le
  have hfst' : ∀ i : Fin d, ∀ᵐ xy ∂Gagliardo.gagliardoCubeMeasure Q,
      Integrable (fun z : Vec d => F.toField
        (convexApproxSample x0 z r ε xy.1) i)
          (convexApproxKernelMeasure (unitConvexApproxKernel (d := d))) := by
    intro i
    simpa only [μ, ν, Function.comp_apply, diagonalConvexApproxJointSample] using!
      (hfst i).integrable p.one_lt.le |>.prod_right_ae
  have hsnd' : ∀ i : Fin d, ∀ᵐ xy ∂Gagliardo.gagliardoCubeMeasure Q,
      Integrable (fun z : Vec d => F.toField
        (convexApproxSample x0 z r ε xy.2) i)
          (convexApproxKernelMeasure (unitConvexApproxKernel (d := d))) := by
    intro i
    simpa only [μ, ν, Function.comp_apply, diagonalConvexApproxJointSample] using!
      (hsnd i).integrable p.one_lt.le |>.prod_right_ae
  have hall : ∀ᵐ xy ∂Gagliardo.gagliardoCubeMeasure Q, ∀ i : Fin d,
      Integrable (fun z : Vec d => F.toField
        (convexApproxSample x0 z r ε xy.1) i)
          (convexApproxKernelMeasure (unitConvexApproxKernel (d := d))) ∧
      Integrable (fun z : Vec d => F.toField
        (convexApproxSample x0 z r ε xy.2) i)
          (convexApproxKernelMeasure (unitConvexApproxKernel (d := d))) := by
    exact ae_all_iff.2 fun i => (hfst' i).and (hsnd' i)
  exact hall

private theorem ae_cubeEuclideanWspKernel_convexApproxSmoothField_eq_scaled_average
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanWspField Q s p) (x0 : Vec d) (r ε : ℝ)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 < r)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    cubeEuclideanWspKernel s p
        (cubeEuclideanWspConvexApproxSmoothField F x0 r ε) =ᵐ[
          Gagliardo.gagliardoCubeMeasure Q]
      ((1 - ε) ^ (s.1 + (d : ℝ) / p.exponent.toReal)) •
        diagonalConvexApproxAverage (unitConvexApproxKernel (d := d))
          (cubeEuclideanWspKernel s p F.toField) x0 r ε := by
  filter_upwards [ae_mem_openCubeProduct_gagliardoCubeMeasure Q,
    ae_integrable_diagonalConvexApproxSample_components F x0 r ε hball hr.le hε0.le hε1] with
      xy hxy hint
  exact cubeEuclideanWspKernel_convexApproxSmoothField_eq_scaled_average_of_integrable
    Q s p F x0 r ε hball hr hε0 hε1 xy hxy hint

private theorem tendsto_fractional_diagonal_scale_one {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) :
    Filter.Tendsto
      (fun n : ℕ => (1 - unitConvexApproxScale n) ^
        (s.1 + (d : ℝ) / p.exponent.toReal))
      Filter.atTop (nhds 1) := by
  have hbase : Filter.Tendsto (fun n : ℕ => 1 - unitConvexApproxScale n)
      Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub tendsto_unitConvexApproxScale_zero
  have hpow := (Real.continuousAt_rpow_const 1
      (s.1 + (d : ℝ) / p.exponent.toReal) (Or.inl one_ne_zero)).tendsto.comp hbase
  simpa using! hpow

private theorem tendsto_cubeEuclideanWspESeminorm_convexApproxSmoothField_sub_zero
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanWspField Q s p) (x0 : Vec d) (r : ℝ)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 < r) :
    Filter.Tendsto
      (fun n : ℕ => cubeEuclideanWspESeminorm Q s p
        (fun x => cubeEuclideanWspConvexApproxSmoothField F x0 r
          (unitConvexApproxScale n) x - F.toField x))
      Filter.atTop (nhds 0) := by
  let μ := Gagliardo.gagliardoCubeMeasure Q
  let K := cubeEuclideanWspKernel s p F.toField
  let c : ℕ → ℝ := fun n => (1 - unitConvexApproxScale n) ^
    (s.1 + (d : ℝ) / p.exponent.toReal)
  have haverage : Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun xy => diagonalConvexApproxAverage
        (unitConvexApproxKernel (d := d)) K x0 r (unitConvexApproxScale n) xy - K xy)
        p.exponent μ) Filter.atTop (nhds 0) := by
    simpa only [μ, K] using
      tendsto_eLpNorm_diagonalConvexApproxAverage_sub_zero_of_memLp
        Q p K F.euclideanMemWsp hball hr.le
  have hc : Filter.Tendsto c Filter.atTop (nhds 1) := by
    simpa only [c] using tendsto_fractional_diagonal_scale_one (d := d) s p
  have hcnorm : Filter.Tendsto (fun n : ℕ => ‖c n‖ₑ)
      Filter.atTop (nhds 1) := by
    simpa using! (continuous_enorm.tendsto (1 : ℝ)).comp hc
  have hdiffnorm : Filter.Tendsto (fun n : ℕ => ‖c n - 1‖ₑ)
      Filter.atTop (nhds 0) := by
    have hreal : Filter.Tendsto (fun n : ℕ => c n - 1)
        Filter.atTop (nhds 0) := by
      simpa using hc.sub (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1))
    simpa using! (continuous_enorm.tendsto (0 : ℝ)).comp hreal
  have hfirst : Filter.Tendsto (fun n : ℕ => eLpNorm (fun xy => c n •
      (diagonalConvexApproxAverage (unitConvexApproxKernel (d := d)) K x0 r
        (unitConvexApproxScale n) xy - K xy)) p.exponent μ)
      Filter.atTop (nhds 0) := by
    change Filter.Tendsto (fun n : ℕ => eLpNorm (c n • fun xy =>
      diagonalConvexApproxAverage (unitConvexApproxKernel (d := d)) K x0 r
        (unitConvexApproxScale n) xy - K xy) p.exponent μ) Filter.atTop (nhds 0)
    simpa only [eLpNorm_const_smul, one_mul] using
      ENNReal.Tendsto.mul hcnorm (Or.inl one_ne_zero) haverage (Or.inr ENNReal.one_ne_top)
  have hKtop : eLpNorm K p.exponent μ ≠ ⊤ := F.euclideanMemWsp.eLpNorm_lt_top.ne
  have hsecond : Filter.Tendsto (fun n : ℕ => eLpNorm (fun xy =>
      (c n - 1) • K xy) p.exponent μ) Filter.atTop (nhds 0) := by
    change Filter.Tendsto (fun n : ℕ => eLpNorm ((c n - 1) • K)
      p.exponent μ) Filter.atTop (nhds 0)
    simpa only [eLpNorm_const_smul, zero_mul] using
      ENNReal.Tendsto.mul_const hdiffnorm (Or.inr hKtop)
  have hsum : Filter.Tendsto (fun n : ℕ => eLpNorm (fun xy => c n •
      (diagonalConvexApproxAverage (unitConvexApproxKernel (d := d)) K x0 r
        (unitConvexApproxScale n) xy - K xy)) p.exponent μ +
        eLpNorm (fun xy => (c n - 1) • K xy) p.exponent μ)
      Filter.atTop (nhds 0) := by simpa using hfirst.add hsecond
  have hevent_lt : ∀ᶠ n : ℕ in Filter.atTop, unitConvexApproxScale n < 1 :=
    (tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one
  let T : ℕ → ℝ≥0∞ := fun n => cubeEuclideanWspESeminorm Q s p
    (fun x => cubeEuclideanWspConvexApproxSmoothField F x0 r
      (unitConvexApproxScale n) x - F.toField x)
  let T' : ℕ → ℝ≥0∞ := fun n => if unitConvexApproxScale n < 1 then T n else 0
  have hT' : Filter.Tendsto T' Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => bot_le) ?_
    intro n
    by_cases hε : unitConvexApproxScale n < 1
    · have hεpos : 0 < unitConvexApproxScale n := by
        dsimp [unitConvexApproxScale]
        positivity
      have hkernel := ae_cubeEuclideanWspKernel_convexApproxSmoothField_eq_scaled_average
        Q s p F x0 r (unitConvexApproxScale n) hball hr hεpos hε
      have hfirstmeas : AEStronglyMeasurable (fun xy => c n •
          (diagonalConvexApproxAverage (unitConvexApproxKernel (d := d)) K x0 r
            (unitConvexApproxScale n) xy - K xy)) μ := by
        exact (aestronglyMeasurable_diagonalConvexApproxAverage_of_memLp Q p K
          F.euclideanMemWsp hε hball hr.le hεpos.le hε.le).sub
            F.euclideanMemWsp.aestronglyMeasurable |>.const_smul (c n)
      have hsecondmeas : AEStronglyMeasurable (fun xy => (c n - 1) • K xy) μ :=
        by simpa only [μ, K] using! F.euclideanMemWsp.aestronglyMeasurable.const_smul (c n - 1)
      simp only [T', if_pos hε]
      change T n ≤ _
      rw [show T n = eLpNorm (cubeEuclideanWspKernel s p (fun x =>
        cubeEuclideanWspConvexApproxSmoothField F x0 r
          (unitConvexApproxScale n) x - F.toField x)) p.exponent μ by rfl]
      calc
        eLpNorm (cubeEuclideanWspKernel s p (fun x =>
            cubeEuclideanWspConvexApproxSmoothField F x0 r
              (unitConvexApproxScale n) x - F.toField x)) p.exponent μ
          = eLpNorm (fun xy => c n •
              (diagonalConvexApproxAverage (unitConvexApproxKernel (d := d)) K x0 r
                (unitConvexApproxScale n) xy - K xy) + (c n - 1) • K xy)
              p.exponent μ := by
                apply eLpNorm_congr_ae
                filter_upwards [hkernel] with xy hxy
                have hlinear : cubeEuclideanWspKernel s p (fun x =>
                    cubeEuclideanWspConvexApproxSmoothField F x0 r
                      (unitConvexApproxScale n) x - F.toField x) xy =
                    cubeEuclideanWspKernel s p
                      (cubeEuclideanWspConvexApproxSmoothField F x0 r
                        (unitConvexApproxScale n)) xy - K xy := by
                  dsimp only [K]
                  rw [cubeEuclideanWspKernel_apply, cubeEuclideanWspKernel_apply,
                    cubeEuclideanWspKernel_apply]
                  change _ • (HilbertVec.ofVecL d)
                    ((cubeEuclideanWspConvexApproxSmoothField F x0 r
                      (unitConvexApproxScale n) xy.1 - F.toField xy.1) -
                      (cubeEuclideanWspConvexApproxSmoothField F x0 r
                        (unitConvexApproxScale n) xy.2 - F.toField xy.2)) = _
                  have hvec :
                      (cubeEuclideanWspConvexApproxSmoothField F x0 r
                        (unitConvexApproxScale n) xy.1 - F.toField xy.1) -
                        (cubeEuclideanWspConvexApproxSmoothField F x0 r
                          (unitConvexApproxScale n) xy.2 - F.toField xy.2) =
                      (cubeEuclideanWspConvexApproxSmoothField F x0 r
                        (unitConvexApproxScale n) xy.1 -
                        cubeEuclideanWspConvexApproxSmoothField F x0 r
                          (unitConvexApproxScale n) xy.2) -
                        (F.toField xy.1 - F.toField xy.2) := by
                    abel
                  rw [hvec, (HilbertVec.ofVecL d).map_sub, smul_sub]
                  rfl
                have hxy' : cubeEuclideanWspKernel s p
                    (cubeEuclideanWspConvexApproxSmoothField F x0 r
                      (unitConvexApproxScale n)) xy = c n •
                    diagonalConvexApproxAverage (unitConvexApproxKernel (d := d)) K x0 r
                      (unitConvexApproxScale n) xy := by
                  simpa only [K, c, Pi.smul_apply] using hxy
                rw [hlinear, hxy']
                module
        _ ≤ _ := eLpNorm_add_le hfirstmeas hsecondmeas p.one_lt.le
    · simp [T', hε]
  apply Filter.Tendsto.congr' ?_ hT'
  filter_upwards [hevent_lt] with n hn
  simp [T', hn, T]

private theorem tendsto_eLpNorm_component_convexApproxSmoothField_sub_zero
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanWspField Q s p) (x0 : Vec d) (r : ℝ)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 < r) (i : Fin d) :
    Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun x =>
        cubeEuclideanWspConvexApproxSmoothField F x0 r (unitConvexApproxScale n) x i -
          F.toField x i) p.exponent (normalizedCubeMeasure Q))
      Filter.atTop (nhds 0) := by
  let U := openCubeSet Q
  let ρ := unitConvexApproxKernel (d := d)
  let f : Vec d → ℝ := fun x => F.toField x i
  let μ := volume.restrict U
  let c := ENNReal.ofReal ((cubeVolume Q)⁻¹)
  have hU : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_openCubeSet Q
  have hρ : IsConvexApproxKernel ρ := by
    simpa only [ρ] using isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hf : MemLpOn U p.exponent f := by
    simpa only [U, f] using cubeEuclideanWspField_component_memLpOn F i
  have hεpos : ∀ᶠ n : ℕ in Filter.atTop, 0 < unitConvexApproxScale n :=
    Filter.Eventually.of_forall fun n => by
      dsimp [unitConvexApproxScale]
      positivity
  have hεlt : ∀ᶠ n : ℕ in Filter.atTop, unitConvexApproxScale n < 1 :=
    (tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one
  have hsmoothing : Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun x => convexApproxSmoothing ρ f x0 r
        (unitConvexApproxScale n) x - f x) p.exponent μ)
      Filter.atTop (nhds 0) := by
    exact tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
      hU hρ p.one_lt.le p.lt_top.ne hf hball hr tendsto_unitConvexApproxScale_zero
      hεpos hεlt
  have hrep : Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun x =>
        cubeEuclideanWspConvexApproxSmoothField F x0 r (unitConvexApproxScale n) x i -
          F.toField x i) p.exponent μ)
      Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.congr' ?_ hsmoothing
    filter_upwards [hεpos, hεlt] with n hpos hlt
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    simp only [cubeEuclideanWspConvexApproxSmoothField, f, ρ]
    rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      hU hρ hx hball hr hpos hlt]
  have hmeasure : normalizedCubeMeasure Q = c • μ := by
    simp only [normalizedCubeMeasure, cubeMeasure, c, μ, U,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  have hctop : c ^ (1 / p.exponent).toReal ≠ ⊤ := by
    dsimp only [c]
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  apply Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => by
    rw [hmeasure, eLpNorm_smul_measure_of_ne_top p.lt_top.ne])
  simpa using ENNReal.Tendsto.const_mul hrep (Or.inr hctop)

private theorem tendsto_normalizedEuclideanLpENorm_convexApproxSmoothField_sub_zero
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanWspField Q s p) (x0 : Vec d) (r : ℝ)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 < r) :
    Filter.Tendsto
      (fun n : ℕ => (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
        p.exponent (fun x => cubeEuclideanWspConvexApproxSmoothField F x0 r
          (unitConvexApproxScale n) x - F.toField x))
      Filter.atTop (nhds 0) := by
  let μ := normalizedCubeMeasure Q
  let V : ℕ → Vec d → Vec d := fun n x =>
    cubeEuclideanWspConvexApproxSmoothField F x0 r (unitConvexApproxScale n) x - F.toField x
  have hcoord : ∀ i : Fin d, Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun x => V n x i) p.exponent μ)
      Filter.atTop (nhds 0) := by
    intro i
    simpa only [V, μ] using!
      tendsto_eLpNorm_component_convexApproxSmoothField_sub_zero
        Q s p F x0 r hball hr i
  have hsum : Filter.Tendsto
      (fun n : ℕ => ∑ i : Fin d, eLpNorm (fun x => V n x i) p.exponent μ)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hcoord i)
  have hdimtop : ‖(d : ℝ)‖ₑ ≠ ⊤ := enorm_ne_top
  have hbound : Filter.Tendsto (fun n : ℕ => ‖(d : ℝ)‖ₑ *
      ∑ i : Fin d, eLpNorm (fun x => V n x i) p.exponent μ)
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hsum (Or.inr hdimtop)
  have hmeas : ∀ n : ℕ, ∀ i : Fin d,
      AEStronglyMeasurable (fun x => V n x i) μ := by
    intro n i
    dsimp only [V]
    have hpos : 0 < unitConvexApproxScale n := by
      dsimp [unitConvexApproxScale]
      positivity
    exact ((continuous_apply i).comp
      (contDiff_cubeEuclideanWspConvexApproxSmoothField F x0 hr hpos).continuous).aestronglyMeasurable.sub
      (F.euclideanMemLp.eval_piLp i).aestronglyMeasurable
  have hvec : Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun x => HilbertVec.ofVec (V n x)) p.exponent μ)
      Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
      (fun _ => bot_le) ?_
    intro n
    exact euclidean_eLpNorm_le_dimension_mul_sum_coordinates μ p (V n) (hmeas n)
  simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
    BoundedMeasurableDomain.normalizedLpENorm,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    euclideanNorm_eq_norm_ofVec, eLpNorm_norm] using hvec

private theorem tendsto_cubeEuclideanWspFullENorm_convexApproxSmoothField_sub_zero
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanWspField Q s p) (x0 : Vec d) (r : ℝ)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 < r) :
    Filter.Tendsto
      (fun n : ℕ => cubeEuclideanWspFullENorm Q s p
        (fun x => cubeEuclideanWspConvexApproxSmoothField F x0 r
          (unitConvexApproxScale n) x - F.toField x))
      Filter.atTop (nhds 0) := by
  let L : ℕ → ℝ≥0∞ := fun n =>
    (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.exponent
      (fun x => cubeEuclideanWspConvexApproxSmoothField F x0 r
        (unitConvexApproxScale n) x - F.toField x)
  let S : ℕ → ℝ≥0∞ := fun n => cubeEuclideanWspESeminorm Q s p
    (fun x => cubeEuclideanWspConvexApproxSmoothField F x0 r
      (unitConvexApproxScale n) x - F.toField x)
  let W := cubeEuclideanWspScalePowerWeight Q s p
  let q := p.exponent.toReal
  have hqpos : 0 < q :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have hL : Filter.Tendsto L Filter.atTop (nhds 0) := by
    simpa only [L] using tendsto_normalizedEuclideanLpENorm_convexApproxSmoothField_sub_zero
      Q s p F x0 r hball hr
  have hS : Filter.Tendsto S Filter.atTop (nhds 0) := by
    simpa only [S] using tendsto_cubeEuclideanWspESeminorm_convexApproxSmoothField_sub_zero
      Q s p F x0 r hball hr
  have hLpow : Filter.Tendsto (fun n : ℕ => L n ^ q) Filter.atTop (nhds 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := q)).tendsto (0 : ℝ≥0∞)).comp hL
    simpa only [ENNReal.zero_rpow_of_pos hqpos] using! h
  have hSpow : Filter.Tendsto (fun n : ℕ => S n ^ q) Filter.atTop (nhds 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := q)).tendsto (0 : ℝ≥0∞)).comp hS
    simpa only [ENNReal.zero_rpow_of_pos hqpos] using! h
  have hWtop : W ≠ ⊤ := (cubeEuclideanWspScalePowerWeight_lt_top Q s p).ne
  have hWpow : Filter.Tendsto (fun n : ℕ => W * L n ^ q)
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hLpow (Or.inr hWtop)
  have hsum : Filter.Tendsto (fun n : ℕ => W * L n ^ q + S n ^ q)
      Filter.atTop (nhds 0) := by
    simpa using hWpow.add hSpow
  have hinvpos : 0 < q⁻¹ := inv_pos.mpr hqpos
  have hfinal := ((ENNReal.continuous_rpow_const (y := q⁻¹)).tendsto
    (0 : ℝ≥0∞)).comp hsum
  simpa only [cubeEuclideanWspFullENorm, L, S, W, q,
    ENNReal.zero_rpow_of_pos hinvpos] using! hfinal

/-- Componentwise `L^p` convergence of the explicit convex smoothing sequence,
from a supplied normalized `L^p` bound.  This is kept separate from the
fractional carrier so that the same smooth approximants work simultaneously in
the full fractional topology and in `L²`. -/
private theorem tendsto_eLpNorm_component_convexApproxSmoothField_sub_zero_of_memLp
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder)
    {q p : FiniteLpExponent} (F : CubeEuclideanWspField Q s q)
    (x0 : Vec d) (r : ℝ)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 < r) (i : Fin d)
    (hF : MemLp (fun x => F.toField x i) p.exponent (normalizedCubeMeasure Q)) :
    Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun x =>
        cubeEuclideanWspConvexApproxSmoothField F x0 r (unitConvexApproxScale n) x i -
          F.toField x i) p.exponent (normalizedCubeMeasure Q))
      Filter.atTop (nhds 0) := by
  let U := openCubeSet Q
  let ρ := unitConvexApproxKernel (d := d)
  let f : Vec d → ℝ := fun x => F.toField x i
  let μ := volume.restrict U
  let c := ENNReal.ofReal ((cubeVolume Q)⁻¹)
  have hU : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_openCubeSet Q
  have hρ : IsConvexApproxKernel ρ := by
    simpa only [ρ] using isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hf : MemLpOn U p.exponent f := by
    rw [MemLpOn]
    rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at hF
    let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹)
    have hc0 : c ≠ 0 := by
      dsimp only [c]
      exact ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (cubeVolume_pos Q))
    have hctop : c ≠ ⊤ := by
      dsimp only [c]
      exact ENNReal.ofReal_ne_top
    apply MemLp.of_measure_le_smul (μ := c • volume.restrict (openCubeSet Q))
      (c := c⁻¹) (ENNReal.inv_ne_top.2 hc0)
    · simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul] using
        (le_refl (volume.restrict (openCubeSet Q)))
    · simpa only [c] using hF
  have hεpos : ∀ᶠ n : ℕ in Filter.atTop, 0 < unitConvexApproxScale n :=
    Filter.Eventually.of_forall fun n => by
      dsimp [unitConvexApproxScale]
      positivity
  have hεlt : ∀ᶠ n : ℕ in Filter.atTop, unitConvexApproxScale n < 1 :=
    (tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one
  have hsmoothing : Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun x => convexApproxSmoothing ρ f x0 r
        (unitConvexApproxScale n) x - f x) p.exponent μ)
      Filter.atTop (nhds 0) := by
    exact tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
      hU hρ p.one_lt.le p.lt_top.ne hf hball hr tendsto_unitConvexApproxScale_zero
      hεpos hεlt
  have hrep : Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun x =>
        cubeEuclideanWspConvexApproxSmoothField F x0 r (unitConvexApproxScale n) x i -
          F.toField x i) p.exponent μ)
      Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.congr' ?_ hsmoothing
    filter_upwards [hεpos, hεlt] with n hpos hlt
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    simp only [cubeEuclideanWspConvexApproxSmoothField, f, ρ]
    rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      hU hρ hx hball hr hpos hlt]
  have hmeasure : normalizedCubeMeasure Q = c • μ := by
    simp only [normalizedCubeMeasure, cubeMeasure, c, μ, U,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  have hctop : c ^ (1 / p.exponent).toReal ≠ ⊤ := by
    dsimp only [c]
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  apply Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => by
    rw [hmeasure, eLpNorm_smul_measure_of_ne_top p.lt_top.ne])
  simpa using ENNReal.Tendsto.const_mul hrep (Or.inr hctop)

private theorem tendsto_eLpNorm_two_convexApproxSmoothField_sub_zero
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (q : FiniteLpExponent)
    (F : CubeEuclideanWspL2Field Q s q) (x0 : Vec d) (r : ℝ)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 < r) :
    Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun x => HilbertVec.ofVec
        (cubeEuclideanWspConvexApproxSmoothField F.toCubeEuclideanWspField x0 r
          (unitConvexApproxScale n) x - F.toField x)) 2
        (normalizedCubeMeasure Q))
      Filter.atTop (nhds 0) := by
  let V : ℕ → Vec d → Vec d := fun n x =>
    cubeEuclideanWspConvexApproxSmoothField F.toCubeEuclideanWspField x0 r
      (unitConvexApproxScale n) x - F.toField x
  have hcoord : ∀ i : Fin d, Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun x => V n x i) 2 (normalizedCubeMeasure Q))
      Filter.atTop (nhds 0) := by
    intro i
    simpa only [V] using!
      (tendsto_eLpNorm_component_convexApproxSmoothField_sub_zero_of_memLp
        (p := FiniteLpExponent.two) Q s F.toCubeEuclideanWspField x0 r hball hr i
        (by
          simpa only [FiniteLpExponent.two, HilbertVec.ofVec, PiLp.toLp_apply] using
            F.euclideanMemL2.eval_piLp i))
  have hsum : Filter.Tendsto
      (fun n : ℕ => ∑ i : Fin d,
        eLpNorm (fun x => V n x i) 2 (normalizedCubeMeasure Q))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hcoord i)
  have hdimtop : ‖(d : ℝ)‖ₑ ≠ ⊤ := enorm_ne_top
  have hbound : Filter.Tendsto (fun n : ℕ => ‖(d : ℝ)‖ₑ *
      ∑ i : Fin d, eLpNorm (fun x => V n x i) 2 (normalizedCubeMeasure Q))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hsum (Or.inr hdimtop)
  have hmeas : ∀ n : ℕ, ∀ i : Fin d,
      AEStronglyMeasurable (fun x => V n x i) (normalizedCubeMeasure Q) := by
    intro n i
    dsimp only [V]
    have hpos : 0 < unitConvexApproxScale n := by
      dsimp [unitConvexApproxScale]
      positivity
    exact ((continuous_apply i).comp
      (contDiff_cubeEuclideanWspConvexApproxSmoothField F.toCubeEuclideanWspField
        x0 hr hpos).continuous).aestronglyMeasurable.sub
      (F.euclideanMemL2.eval_piLp i).aestronglyMeasurable
  have hvec : Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun x => HilbertVec.ofVec (V n x)) 2
        (normalizedCubeMeasure Q))
      Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
      (fun _ => bot_le) ?_
    intro n
    exact euclidean_eLpNorm_le_dimension_mul_sum_coordinates
      (normalizedCubeMeasure Q) FiniteLpExponent.two (V n) (hmeas n)
  simpa only [V] using hvec

private theorem eventually_lt_of_tendsto_ennreal_zero {f : ℕ → ℝ≥0∞}
    (hf : Filter.Tendsto f Filter.atTop (nhds 0))
    {epsilon : ℝ≥0∞} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in Filter.atTop, f n < epsilon := by
  by_cases hepsilon_top : epsilon = ⊤
  · have hle := ENNReal.tendsto_nhds_zero.1 hf (1 : ℝ≥0∞) zero_lt_one
    filter_upwards [hle] with n hn
    simpa only [hepsilon_top] using hn.trans_lt ENNReal.one_lt_top
  · have hhalf_pos : 0 < epsilon / 2 :=
      ENNReal.div_pos hepsilon.ne' (by norm_num)
    have hhalf_lt : epsilon / 2 < epsilon :=
      ENNReal.half_lt_self hepsilon.ne' hepsilon_top
    have hle := ENNReal.tendsto_nhds_zero.1 hf (epsilon / 2) hhalf_pos
    filter_upwards [hle] with n hn
    exact hn.trans_lt hhalf_lt

/-- A single explicit convex smoothing approximant is simultaneously close in
the full fractional norm and in normalized `L²`. -/
theorem exists_cubeEuclideanWspSmoothTest_fullENorm_and_l2_sub_lt {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {q : FiniteLpExponent}
    (G : CubeEuclideanWspL2Field Q s q) {epsilon : ℝ≥0∞}
    (hepsilon : 0 < epsilon) :
    ∃ h : CubeEuclideanWspSmoothTest Q s q,
      cubeEuclideanWspFullENorm Q s q
          (fun x => h.toField x - G.toField x) < epsilon ∧
        eLpNorm (fun x => HilbertVec.ofVec (h.toField x - G.toField x)) 2
          (normalizedCubeMeasure Q) < epsilon := by
  let x0 := cubeCenter Q
  let r := cubeRadius Q / 2
  have hr : 0 < r := by
    dsimp only [r]
    exact half_pos (cubeRadius_pos Q)
  have hball : Metric.closedBall x0 r ⊆ openCubeSet Q := by
    simpa only [x0, r] using closedBall_halfCubeRadius_subset_openCubeSet Q
  have hfull := tendsto_cubeEuclideanWspFullENorm_convexApproxSmoothField_sub_zero
    Q s q G.toCubeEuclideanWspField x0 r hball hr
  have hl2 := tendsto_eLpNorm_two_convexApproxSmoothField_sub_zero
    Q s q G x0 r hball hr
  rcases (eventually_lt_of_tendsto_ennreal_zero hfull hepsilon).and
      (eventually_lt_of_tendsto_ennreal_zero hl2 hepsilon) |>.exists with
    ⟨n, hnfull, hnl2⟩
  refine ⟨cubeEuclideanWspConvexApproxSmoothTest G.toCubeEuclideanWspField x0
    (r := r) (ε := unitConvexApproxScale n) hr
    (by
      dsimp [unitConvexApproxScale]
      positivity), ?_, ?_⟩
  · simpa only [cubeEuclideanWspConvexApproxSmoothTest,
      cubeEuclideanWspConvexApproxSmoothField] using hnfull
  · simpa only [cubeEuclideanWspConvexApproxSmoothTest,
      cubeEuclideanWspConvexApproxSmoothField] using hnl2

theorem exists_cubeEuclideanWspSmoothTest_fullENorm_sub_lt {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanWspField Q s p) {epsilon : ℝ≥0∞}
    (hepsilon : 0 < epsilon) :
    ∃ h : CubeEuclideanWspSmoothTest Q s p,
      cubeEuclideanWspFullENorm Q s p
        (fun x => h.toField x - F.toField x) < epsilon := by
  let x0 := cubeCenter Q
  let r := cubeRadius Q / 2
  have hr : 0 < r := by
    dsimp only [r]
    exact half_pos (cubeRadius_pos Q)
  have hball : Metric.closedBall x0 r ⊆ openCubeSet Q := by
    simpa only [x0, r] using closedBall_halfCubeRadius_subset_openCubeSet Q
  have hconv := tendsto_cubeEuclideanWspFullENorm_convexApproxSmoothField_sub_zero
    Q s p F x0 r hball hr
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      cubeEuclideanWspFullENorm Q s p
        (fun x => cubeEuclideanWspConvexApproxSmoothField F x0 r
          (unitConvexApproxScale n) x - F.toField x) < epsilon := by
    by_cases hepsilon_top : epsilon = ⊤
    · have hle := ENNReal.tendsto_nhds_zero.1 hconv (1 : ℝ≥0∞) zero_lt_one
      filter_upwards [hle] with n hn
      simpa only [hepsilon_top] using hn.trans_lt ENNReal.one_lt_top
    · have hhalf_pos : 0 < epsilon / 2 :=
        ENNReal.div_pos hepsilon.ne' (by norm_num)
      have hhalf_lt : epsilon / 2 < epsilon :=
        ENNReal.half_lt_self hepsilon.ne' hepsilon_top
      have hle := ENNReal.tendsto_nhds_zero.1 hconv (epsilon / 2) hhalf_pos
      filter_upwards [hle] with n hn
      exact hn.trans_lt hhalf_lt
  rcases hsmall.exists with ⟨n, hn⟩
  refine ⟨cubeEuclideanWspConvexApproxSmoothTest F x0 (r := r)
    (ε := unitConvexApproxScale n) hr
    (by
      dsimp [unitConvexApproxScale]
      positivity), ?_⟩
  simpa only [cubeEuclideanWspConvexApproxSmoothTest,
    cubeEuclideanWspConvexApproxSmoothField] using hn

end

end Homogenization
