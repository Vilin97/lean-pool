/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ConvexApproxGagliardoSmoothing
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.PointwiseBounds

/-!
# Finite-`p` bounds for diagonal Gagliardo smoothing

This module begins the measure-transport layer needed to turn the diagonal
Jensen estimate into an unconditional fractional-kernel bound.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem gagliardoCubeMeasure_eq_openCubeProduct {d : ℕ}
    (Q : TriadicCube d) :
    Gagliardo.gagliardoCubeMeasure Q =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) •
        ((volume.restrict (openCubeSet Q)).prod
          (volume.restrict (openCubeSet Q))) := by
  rw [Gagliardo.gagliardoCubeMeasure, normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
    Measure.prod_smul_left]

private theorem finiteLpExponent_one_le (p : FiniteLpExponent) : 1 ≤ p.exponent :=
  p.one_lt.le

private theorem finiteLpExponent_ne_zero (p : FiniteLpExponent) : p.exponent ≠ 0 :=
  (zero_lt_one.trans p.one_lt).ne'

private theorem finiteLpExponent_ne_top (p : FiniteLpExponent) : p.exponent ≠ ∞ :=
  p.lt_top.ne

/-- The kernel probability measure is concentrated on the topological support
of its density. -/
theorem ae_mem_tsupport_convexApproxKernelMeasure {d : ℕ} {ρ : Vec d → ℝ}
    : ∀ᵐ z ∂convexApproxKernelMeasure ρ, z ∈ tsupport ρ := by
  rw [ae_iff]
  change convexApproxKernelMeasure ρ (tsupport ρ)ᶜ = 0
  rw [convexApproxKernelMeasure,
    withDensity_apply _ (isClosed_tsupport ρ).isOpen_compl.measurableSet]
  rw [← lintegral_zero (μ := volume.restrict (tsupport ρ)ᶜ)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (isClosed_tsupport ρ).isOpen_compl.measurableSet]
    with z hz
  rw [image_eq_zero_of_notMem_tsupport hz]
  simp

/-- The joint map used when Fubini interchanges the cube variables and the
kernel variable in diagonal smoothing. -/
def diagonalConvexApproxJointSample {d : ℕ} (x0 : Vec d) (r ε : ℝ) :
    (Vec d × Vec d) × Vec d → Vec d × Vec d :=
  fun xyz => diagonalConvexApproxSample x0 xyz.2 r ε xyz.1

theorem measurable_diagonalConvexApproxJointSample {d : ℕ} (x0 : Vec d)
    (r ε : ℝ) : Measurable (diagonalConvexApproxJointSample x0 r ε) := by
  unfold diagonalConvexApproxJointSample diagonalConvexApproxSample convexApproxSample
  fun_prop

/-- On the support of the convex kernel, simultaneous inward sampling maps the
open cube product into itself. -/
theorem diagonalConvexApproxSample_mapsTo_openCubeProduct {d : ℕ}
    (Q : TriadicCube d) {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 ≤ r)
    (hz : z ∈ tsupport ρ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Set.MapsTo (diagonalConvexApproxSample x0 z r ε)
      ((openCubeSet Q) ×ˢ (openCubeSet Q))
      ((openCubeSet Q) ×ˢ (openCubeSet Q)) := by
  intro xy hxy
  rcases hxy with ⟨hx, hy⟩
  constructor
  · exact convexApproxSample_mem_of_tsupport_subset_closedBall
      (isOpenBoundedConvexDomain_openCubeSet Q) hx hball
      hρ.support_subset_closedBall hz hr hε0 hε1
  · exact convexApproxSample_mem_of_tsupport_subset_closedBall
      (isOpenBoundedConvexDomain_openCubeSet Q) hy hball
      hρ.support_subset_closedBall hz hr hε0 hε1

/-- The pushed-forward Gagliardo measure of a fixed supported diagonal sample
is bounded by its two-Jacobian factor times the original measure. -/
theorem map_gagliardoCubeMeasure_diagonalConvexApproxSample_le {d : ℕ}
    (Q : TriadicCube d) {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {x0 z : Vec d} {r ε : ℝ} (hε : ε < 1)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 ≤ r)
    (hz : z ∈ tsupport ρ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Measure.map (diagonalConvexApproxSample x0 z r ε)
        (Gagliardo.gagliardoCubeMeasure Q) ≤
      (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ 2) •
        Gagliardo.gagliardoCubeMeasure Q := by
  let U := openCubeSet Q
  let J : ℝ≥0∞ := ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ 2
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹)
  have himage : convexApproxSample x0 z r ε '' U ⊆ U := by
    exact Set.image_subset_iff.mpr
      (fun x hx =>
        convexApproxSample_mem_of_tsupport_subset_closedBall
          (isOpenBoundedConvexDomain_openCubeSet Q) hx hball
          hρ.support_subset_closedBall hz hr hε0 hε1)
  have hprod :
      (volume.restrict (convexApproxSample x0 z r ε '' U)).prod
        (volume.restrict (convexApproxSample x0 z r ε '' U)) ≤
      (volume.restrict U).prod (volume.restrict U) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    exact Measure.restrict_mono_set volume (Set.prod_mono himage himage)
  have hmeas : Measurable (diagonalConvexApproxSample x0 z r ε) :=
    ((measurableEmbedding_convexApproxSample x0 z r ε hε).prodMap
      (measurableEmbedding_convexApproxSample x0 z r ε hε)).measurable
  rw [gagliardoCubeMeasure_eq_openCubeProduct Q,
    Measure.map_smul _ hmeas.aemeasurable,
    map_prod_restrict_diagonalConvexApproxSample
      (isOpen_openCubeSet Q).measurableSet x0 z r ε hε]
  change c • (J •
      ((volume.restrict (convexApproxSample x0 z r ε '' U)).prod
        (volume.restrict (convexApproxSample x0 z r ε '' U)))) ≤
    J • (c • ((volume.restrict U).prod (volume.restrict U)))
  rw [smul_smul, smul_smul, mul_comm J c]
  apply Measure.le_iff'.2
  intro s
  rw [Measure.smul_apply, Measure.smul_apply]
  exact mul_le_mul_right (hprod s) (c * J)

/-- A fixed supported diagonal affine sample is bounded on finite-
`L^p` Gagliardo kernels by the explicit two-Jacobian factor. -/
theorem eLpNorm_comp_diagonalConvexApproxSample_le {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [TopologicalSpace E] [ContinuousENorm E]
    (Q : TriadicCube d) (p : FiniteLpExponent) (K : Vec d × Vec d → E)
    (hK : MemLp K p.exponent (Gagliardo.gagliardoCubeMeasure Q))
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {x0 z : Vec d} {r ε : ℝ} (hε : ε < 1)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 ≤ r)
    (hz : z ∈ tsupport ρ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    eLpNorm (fun xy => K (diagonalConvexApproxSample x0 z r ε xy)) p.exponent
        (Gagliardo.gagliardoCubeMeasure Q) ≤
      (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ 2) ^ (1 / p.exponent).toReal *
        eLpNorm K p.exponent (Gagliardo.gagliardoCubeMeasure Q) := by
  let J : ℝ≥0∞ := ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ 2
  let A := diagonalConvexApproxSample x0 z r ε
  have hJtop : J ≠ ⊤ := by
    dsimp only [J]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hmap : Measure.map A (Gagliardo.gagliardoCubeMeasure Q) ≤
      J • Gagliardo.gagliardoCubeMeasure Q := by
    simpa only [A, J] using
      (map_gagliardoCubeMeasure_diagonalConvexApproxSample_le Q hρ hε hball hr hz hε0 hε1)
  have hKmap : MemLp K p.exponent (Measure.map A (Gagliardo.gagliardoCubeMeasure Q)) :=
    MemLp.of_measure_le_smul hJtop hmap hK
  have hAembedding : MeasurableEmbedding A := by
    dsimp only [A, diagonalConvexApproxSample]
    exact (measurableEmbedding_convexApproxSample x0 z r ε hε).prodMap
      (measurableEmbedding_convexApproxSample x0 z r ε hε)
  calc
    eLpNorm (fun xy => K (A xy)) p.exponent (Gagliardo.gagliardoCubeMeasure Q) =
        eLpNorm K p.exponent (Measure.map A (Gagliardo.gagliardoCubeMeasure Q)) := by
      symm
      exact hAembedding.eLpNorm_map_measure
    _ ≤ eLpNorm K p.exponent (J • Gagliardo.gagliardoCubeMeasure Q) :=
      eLpNorm_mono_measure K hmap
    _ = J ^ (1 / p.exponent).toReal *
        eLpNorm K p.exponent (Gagliardo.gagliardoCubeMeasure Q) := by
      rw [eLpNorm_smul_measure_of_ne_top p.lt_top.ne K J hK.aestronglyMeasurable]
      rfl

/-- The joint diagonal sampling map is quasi-measure-preserving with exactly
the two-Jacobian loss.  This is the missing bridge from fixed-sample bounds to
Fubini section statements. -/
theorem map_diagonalConvexApproxJointSample_le {d : ℕ}
    (Q : TriadicCube d) {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ} (hε : ε < 1)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Measure.map (diagonalConvexApproxJointSample x0 r ε)
        ((Gagliardo.gagliardoCubeMeasure Q).prod (convexApproxKernelMeasure ρ)) ≤
      (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ 2) •
        Gagliardo.gagliardoCubeMeasure Q := by
  let μ := Gagliardo.gagliardoCubeMeasure Q
  let ν := convexApproxKernelMeasure ρ
  let J : ℝ≥0∞ := ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ 2
  let T := diagonalConvexApproxJointSample x0 r ε
  let : IsProbabilityMeasure ν := by
    simpa only [ν] using isProbabilityMeasure_convexApproxKernelMeasure hρ
  let : SFinite ν := inferInstance
  have hT : Measurable T := by
    exact measurable_diagonalConvexApproxJointSample x0 r ε
  apply Measure.le_iff.2
  intro s hs
  rw [Measure.map_apply hT hs]
  have hpre : MeasurableSet (T ⁻¹' s) := hT hs
  rw [← lintegral_indicator_one hpre]
  let f : (Vec d × Vec d) × Vec d → ℝ≥0∞ :=
    fun xyz => Set.indicator s (fun _ => (1 : ℝ≥0∞)) (T xyz)
  have hf : Measurable f := by
    exact (measurable_const.indicator hs).comp hT
  change ∫⁻ xyz, f xyz ∂μ.prod ν ≤ (J • μ) s
  rw [lintegral_prod f hf.aemeasurable]
  rw [lintegral_lintegral_swap hf.aemeasurable]
  have hfixed : ∀ᵐ z ∂ν,
      (∫⁻ xy, f (xy, z) ∂μ) ≤ J * μ s := by
    filter_upwards [ae_mem_tsupport_convexApproxKernelMeasure (ρ := ρ)] with z hz
    let A := diagonalConvexApproxSample x0 z r ε
    have hA : Measurable A :=
      (measurableEmbedding_convexApproxSample x0 z r ε hε).prodMap
        (measurableEmbedding_convexApproxSample x0 z r ε hε) |>.measurable
    have hmap : Measure.map A μ ≤ J • μ := by
      simpa only [μ, J] using
        (map_gagliardoCubeMeasure_diagonalConvexApproxSample_le Q hρ hε
          hball hr hz hε0 hε1)
    have hrewrite : (fun xy => f (xy, z)) =
        (A ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext xy
      simpa only [f, T, A, diagonalConvexApproxJointSample, Function.comp_apply] using!
        (Set.indicator_comp_right A (g := fun _ => (1 : ℝ≥0∞)) (x := xy)).symm
    rw [hrewrite]
    calc
      ∫⁻ xy, (A ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) xy ∂μ = μ (A ⁻¹' s) :=
        lintegral_indicator_one (hA hs)
      _ = Measure.map A μ s := (Measure.map_apply hA hs).symm
      _ ≤ (J • μ) s := hmap s
      _ = J * μ s := by
        rw [Measure.smul_apply, smul_eq_mul]
  calc
    ∫⁻ z, ∫⁻ xy, f (xy, z) ∂μ ∂ν ≤ ∫⁻ z, J * μ s ∂ν :=
      lintegral_mono_ae hfixed
    _ = J * μ s * ν Set.univ := by
      rw [lintegral_const]
    _ = J * μ s := by
      rw [MeasureTheory.measure_univ, mul_one]
    _ = (J • μ) s := by rw [Measure.smul_apply, smul_eq_mul]

/-- The diagonal convex average satisfies the powered finite-`L^p` Gagliardo
bound without caller-supplied Fubini section hypotheses. -/
theorem lintegral_diagonalConvexApproxAverage_rpow_le_of_memLp
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (Q : TriadicCube d) (p : FiniteLpExponent)
    (K : Vec d × Vec d → E)
    (hK : MemLp K p.exponent (Gagliardo.gagliardoCubeMeasure Q))
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ} (hε : ε < 1)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∫⁻ xy, ‖diagonalConvexApproxAverage ρ K x0 r ε xy‖ₑ ^ p.exponent.toReal
        ∂Gagliardo.gagliardoCubeMeasure Q ≤
      (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ 2) *
        ∫⁻ xy, ‖K xy‖ₑ ^ p.exponent.toReal
          ∂Gagliardo.gagliardoCubeMeasure Q := by
  let μ := Gagliardo.gagliardoCubeMeasure Q
  let ν := convexApproxKernelMeasure ρ
  let J : ℝ≥0∞ := ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ 2
  let T := diagonalConvexApproxJointSample x0 r ε
  let : IsProbabilityMeasure ν := by
    simpa only [ν] using isProbabilityMeasure_convexApproxKernelMeasure hρ
  let : SFinite ν := inferInstance
  let : IsFiniteMeasure ν := inferInstance
  let : IsFiniteMeasure μ := inferInstance
  let : IsFiniteMeasure (μ.prod ν) := inferInstance
  have hT : Measurable T := measurable_diagonalConvexApproxJointSample x0 r ε
  have hmap : Measure.map T (μ.prod ν) ≤ J • μ := by
    simpa only [μ, ν, J, T] using
      (map_diagonalConvexApproxJointSample_le Q hρ hε hball hr hε0 hε1)
  have hJtop : J ≠ ⊤ := by
    dsimp only [J]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hKmap : MemLp K p.exponent (Measure.map T (μ.prod ν)) :=
    MemLp.of_measure_le_smul hJtop hmap hK
  have hKT : MemLp (K ∘ T) p.exponent (μ.prod ν) :=
    (memLp_map_measure_iff hKmap.aestronglyMeasurable hT.aemeasurable).mp hKmap
  have hsection : ∀ᵐ xy ∂μ, Integrable
      (fun z => K (diagonalConvexApproxSample x0 z r ε xy)) ν := by
    simpa only [T, diagonalConvexApproxJointSample, Function.comp_apply] using
      (hKT.integrable (finiteLpExponent_one_le p)).prod_right_ae
  have hsectionpow : ∀ᵐ xy ∂μ, Integrable
      (fun z => ‖K (diagonalConvexApproxSample x0 z r ε xy)‖ ^ p.exponent.toReal) ν := by
    simpa only [T, diagonalConvexApproxJointSample, Function.comp_apply] using
      (hKT.integrable_norm_rpow (finiteLpExponent_ne_zero p)
        (finiteLpExponent_ne_top p)).prod_right_ae
  have hpow_meas : AEMeasurable
      (fun xyz : (Vec d × Vec d) × Vec d =>
        ‖K (diagonalConvexApproxSample x0 xyz.2 r ε xyz.1)‖ₑ ^ p.exponent.toReal)
      (μ.prod ν) := by
    simpa only [T, diagonalConvexApproxJointSample, Function.comp_apply] using!
      (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        hKT.aestronglyMeasurable.enorm)
  have hp_one_le_toReal : 1 ≤ p.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_le_toReal (by norm_num) (finiteLpExponent_ne_top p)).mpr
      (finiteLpExponent_one_le p)
  calc
    ∫⁻ xy, ‖diagonalConvexApproxAverage ρ K x0 r ε xy‖ₑ ^ p.exponent.toReal ∂μ ≤
        ∫⁻ z, ∫⁻ xy,
          ‖K (diagonalConvexApproxSample x0 z r ε xy)‖ₑ ^ p.exponent.toReal ∂μ ∂ν :=
      lintegral_diagonalConvexApproxAverage_rpow_le μ hρ K x0 r ε
        hp_one_le_toReal
        hsection hsectionpow hpow_meas
    _ = ∫⁻ xyz, ‖K (T xyz)‖ₑ ^ p.exponent.toReal ∂μ.prod ν := by
      calc
        ∫⁻ z, ∫⁻ xy,
            ‖K (diagonalConvexApproxSample x0 z r ε xy)‖ₑ ^ p.exponent.toReal ∂μ ∂ν =
            ∫⁻ xy, ∫⁻ z,
              ‖K (diagonalConvexApproxSample x0 z r ε xy)‖ₑ ^ p.exponent.toReal ∂ν ∂μ := by
          exact (lintegral_lintegral_swap hpow_meas).symm
        _ = ∫⁻ xyz, ‖K (T xyz)‖ₑ ^ p.exponent.toReal ∂μ.prod ν := by
          symm
          exact lintegral_prod _ hpow_meas
    _ = ∫⁻ xy, ‖K xy‖ₑ ^ p.exponent.toReal ∂Measure.map T (μ.prod ν) := by
      symm
      exact lintegral_map'
        (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
          hKmap.aestronglyMeasurable.enorm) hT.aemeasurable
    _ ≤ ∫⁻ xy, ‖K xy‖ₑ ^ p.exponent.toReal ∂J • μ :=
      lintegral_mono' hmap le_rfl
    _ = J * ∫⁻ xy, ‖K xy‖ₑ ^ p.exponent.toReal ∂μ := by
      rw [lintegral_smul_measure, smul_eq_mul]

private theorem diagonalConvexApproxAverage_aestronglyMeasurable
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) (p : FiniteLpExponent) (K : Vec d × Vec d → E)
    (hK : MemLp K p.exponent (Gagliardo.gagliardoCubeMeasure Q))
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ} (hε : ε < 1)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    AEStronglyMeasurable (diagonalConvexApproxAverage ρ K x0 r ε)
      (Gagliardo.gagliardoCubeMeasure Q) := by
  let μ := Gagliardo.gagliardoCubeMeasure Q
  let ν := convexApproxKernelMeasure ρ
  let J : ℝ≥0∞ := ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ 2
  let T := diagonalConvexApproxJointSample x0 r ε
  let : IsProbabilityMeasure ν := by
    simpa only [ν] using isProbabilityMeasure_convexApproxKernelMeasure hρ
  let : SFinite ν := inferInstance
  let : IsFiniteMeasure ν := inferInstance
  let : IsFiniteMeasure μ := inferInstance
  let : IsFiniteMeasure (μ.prod ν) := inferInstance
  have hT : Measurable T := measurable_diagonalConvexApproxJointSample x0 r ε
  have hmap : Measure.map T (μ.prod ν) ≤ J • μ := by
    simpa only [μ, ν, J, T] using
      (map_diagonalConvexApproxJointSample_le Q hρ hε hball hr hε0 hε1)
  have hJtop : J ≠ ⊤ := by
    dsimp only [J]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hKmap : MemLp K p.exponent (Measure.map T (μ.prod ν)) :=
    MemLp.of_measure_le_smul hJtop hmap hK
  have hKT : MemLp (K ∘ T) p.exponent (μ.prod ν) :=
    (memLp_map_measure_iff hKmap.aestronglyMeasurable hT.aemeasurable).mp hKmap
  have haverage : diagonalConvexApproxAverage ρ K x0 r ε =
      fun xy => ∫ z, (K ∘ T) (xy, z) ∂ν := by
    funext xy
    exact diagonalConvexApproxAverage_eq_integral_kernelMeasure hρ K x0 r ε xy
  rw [haverage]
  exact hKT.aestronglyMeasurable.integral_prod_right'

/-- The unconditional finite-`L^p` norm form of the diagonal Gagliardo
average bound. -/
theorem eLpNorm_diagonalConvexApproxAverage_le_of_memLp
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (Q : TriadicCube d) (p : FiniteLpExponent)
    (K : Vec d × Vec d → E)
    (hK : MemLp K p.exponent (Gagliardo.gagliardoCubeMeasure Q))
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {x0 : Vec d} {r ε : ℝ} (hε : ε < 1)
    (hball : Metric.closedBall x0 r ⊆ openCubeSet Q) (hr : 0 ≤ r)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    eLpNorm (diagonalConvexApproxAverage ρ K x0 r ε) p.exponent
        (Gagliardo.gagliardoCubeMeasure Q) ≤
      (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ 2) ^ (1 / p.exponent).toReal *
        eLpNorm K p.exponent (Gagliardo.gagliardoCubeMeasure Q) := by
  let J : ℝ≥0∞ := ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ 2
  have hpow := lintegral_diagonalConvexApproxAverage_rpow_le_of_memLp
    Q p K hK hρ hε hball hr hε0 hε1
  have hp_inv : (1 / p.exponent).toReal = 1 / p.exponent.toReal := by
    simpa only [one_div] using ENNReal.toReal_inv p.exponent
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (finiteLpExponent_ne_zero p)
      (finiteLpExponent_ne_top p)
      (diagonalConvexApproxAverage_aestronglyMeasurable Q p K hK hρ hε hball hr hε0 hε1),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (finiteLpExponent_ne_zero p)
      (finiteLpExponent_ne_top p) hK.aestronglyMeasurable]
  rw [← hp_inv, ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  exact ENNReal.rpow_le_rpow hpow (by positivity)

end

end Homogenization
