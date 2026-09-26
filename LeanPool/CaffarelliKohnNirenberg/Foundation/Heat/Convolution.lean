/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Bounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Ambient.Euclidean
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.PeakFunction

/-!
# Heat-kernel convolution

This file records the scalar convolution interface used by the heat-kernel
route to the Newtonian kernel.  The heat kernel is the left factor and the
compactly supported function is the right factor, so Mathlib's right-factor
regularity and derivative-transport theorems apply directly.
-/

public section

open scoped Convolution
open scoped BigOperators
open scoped Topology

open MeasureTheory MeasureTheory.Measure
open Filter


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/-- Spatial convolution of the heat kernel with a scalar function. -/
@[expose] noncomputable def heatConv (t : ℝ) (u : Vec3 → ℝ) : Vec3 → ℝ :=
  MeasureTheory.convolution (fun y : Vec3 => heatKernel y t) u
    (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- Pointwise integral form of `heatConv`. -/
theorem heatConv_eq_integral (t : ℝ) (u : Vec3 → ℝ) (x : Vec3) :
    heatConv t u x = ∫ y : Vec3, heatKernel y t * u (x - y) := by
  rw [heatConv, MeasureTheory.convolution_lsmul]
  rfl

/-- Heat-kernel scaling in the spatial variable. -/
theorem heatKernel_scaling {x : Vec3} {t : ℝ} (ht : 0 < t) :
    heatKernel x t = (Real.sqrt t)⁻¹ ^ (3 : ℕ) *
      heatKernel ((Real.sqrt t)⁻¹ • x) 1 := by
  rw [heatKernel_eq_formula_sum ht, heatKernel_eq_formula_sum zero_lt_one]
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsum : ∑ i, ((Real.sqrt t)⁻¹ • x) i ^ 2 =
      (Real.sqrt t)⁻¹ ^ 2 * ∑ i, x i ^ 2 := by
    simp only [Pi.smul_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  have hpow : (Real.sqrt t)⁻¹ ^ (3 : ℕ) = t ^ (-(3 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, Real.inv_rpow hsqrt.le, ← Real.rpow_neg hsqrt.le]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
    norm_num
  have hbase : 4 * Real.pi * t = (4 * Real.pi) * t := by ring
  rw [hbase, Real.mul_rpow (by positivity) ht.le]
  rw [hpow]
  have hbase' : (4 * Real.pi) ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2) =
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) := by
    rw [← Real.mul_rpow (by positivity) ht.le]
  simp only [mul_one]
  have hinv : (Real.sqrt t)⁻¹ ^ 2 = t⁻¹ := by
    field_simp [hsqrt.ne', Real.sq_sqrt ht.le]
    exact (Real.sq_sqrt ht.le).symm
  have hexp : -(∑ i, x i ^ 2) / (4 * t) =
      -((Real.sqrt t)⁻¹ ^ 2 * ∑ i, x i ^ 2) / (4 * 1) := by
    rw [hinv]
    field_simp [ht.ne']
  rw [hexp]
  rw [hbase']
  rw [← hbase']
  ring_nf

/-- The Gaussian profile has vanishing polynomially weighted tails. -/
theorem heatKernel_profile_tendsto_zero_cobounded :
    Tendsto (fun z : Vec3 => ‖z‖ ^ (3 : ℝ) * heatKernel z 1)
      (Bornology.cobounded Vec3) (𝓝 0) := by
  have hs : Tendsto (fun z : Vec3 => vec3EuclideanNorm z)
      (Bornology.cobounded Vec3) atTop := by
    apply Filter.tendsto_atTop_mono' (Bornology.cobounded Vec3)
      (Filter.Eventually.of_forall (fun z => by
        exact CKN.space_norm_le_euclideanNorm z))
    exact tendsto_norm_cobounded_atTop
  have hknown := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (3 : ℝ) (1 / 4 : ℝ) (by norm_num)
  have hknown' := hknown.comp hs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hknown'
  · exact Filter.Eventually.of_forall fun z =>
      mul_nonneg (Real.rpow_nonneg (norm_nonneg z) _) (heatKernel_nonneg z 1)
  · filter_upwards [eventually_cobounded_le_norm 1] with z hz
    let s : ℝ := vec3EuclideanNorm z
    have hs1 : 1 ≤ s := hz.trans (CKN.space_norm_le_euclideanNorm z)
    have hsnonneg : 0 ≤ s := vec3EuclideanNorm_nonneg z
    have hconst : (4 * Real.pi) ^ (-(3 : ℝ) / 2) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · nlinarith only [Real.two_le_pi]
      · norm_num
    have hsq : s ≤ s ^ 2 := by nlinarith only [hs1, hsnonneg]
    have hexp : Real.exp (-s ^ 2 / 4) ≤ Real.exp (-s / 4) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hsq]
    rw [heatKernel_eq_formula_sum (by norm_num : (0 : ℝ) < 1)]
    simp only [Function.comp_apply]
    change ‖z‖ ^ (3 : ℝ) *
      ((4 * Real.pi * 1) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i, z i ^ 2) / (4 * 1))) ≤
      vec3EuclideanNorm z ^ (3 : ℝ) *
        Real.exp (-(1 / 4 : ℝ) * vec3EuclideanNorm z)
    rw [show ∑ i, z i ^ 2 = s ^ 2 by exact (vec3EuclideanNorm_sq z).symm]
    simp only [mul_one]
    calc
      ‖z‖ ^ (3 : ℝ) * ((4 * Real.pi) ^ (-(3 : ℝ) / 2) *
          Real.exp (-s ^ 2 / 4)) ≤
          s ^ (3 : ℝ) * ((4 * Real.pi) ^ (-(3 : ℝ) / 2) *
            Real.exp (-s ^ 2 / 4)) := by
        gcongr
        simpa [s, CKN.spaceEuclideanNorm, vec3EuclideanNorm] using
          CKN.space_norm_le_euclideanNorm z
      _ ≤ s ^ (3 : ℝ) * (1 * Real.exp (-s ^ 2 / 4)) := by
        gcongr
      _ ≤ s ^ (3 : ℝ) * (1 * Real.exp (-s / 4)) := by
        gcongr
      _ = s ^ (3 : ℝ) * Real.exp (-(1 / 4 : ℝ) * s) := by ring_nf

/-- The heat-kernel profile tail in the natural-number power form. -/
theorem heatKernel_profile_tendsto_zero_cobounded_nat :
    Tendsto (fun z : Vec3 => ‖z‖ ^ (3 : ℕ) * heatKernel z 1)
      (Bornology.cobounded Vec3) (𝓝 0) := by
  convert heatKernel_profile_tendsto_zero_cobounded using 1
  norm_num [Real.rpow_natCast]

/-- Compactly supported heat convolution converges pointwise to its input at
positive times tending to zero. -/
theorem heatConv_tendsto_self_nhdsWithin_zero_smooth {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huSupport : HasCompactSupport u) (x : Vec3) :
    Tendsto (fun t : ℝ => heatConv t u x) (𝓝[>] 0) (𝓝 (u x)) := by
  have hc : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) (𝓝[>] 0) atTop := by
    apply tendsto_inv_nhdsGT_zero.comp
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa only [Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Real.sqrt_pos.2 ht
  have hpeak :
      Tendsto (fun c : ℝ => ∫ y : Vec3,
        (c ^ Module.finrank ℝ Vec3 * heatKernel (c • (x - y)) 1) • u y)
        atTop (𝓝 (u x)) := by
    apply tendsto_integral_comp_smul_smul_of_integrable'
      (μ := volume) (φ := fun z : Vec3 => heatKernel z 1)
    · exact fun z => heatKernel_nonneg z 1
    · simpa using heatKernel_integral (1 : ℝ) (by norm_num)
    · simpa only [Module.finrank_fin_fun] using
        heatKernel_profile_tendsto_zero_cobounded_nat
    · exact hu.continuous.integrable_of_hasCompactSupport huSupport
    · exact hu.continuous.continuousAt
  have hpeak' := hpeak.comp hc
  apply (tendsto_congr' ?_).2 hpeak'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change heatConv t u x = ∫ y : Vec3,
    ((Real.sqrt t)⁻¹ ^ Module.finrank ℝ Vec3 *
      heatKernel ((Real.sqrt t)⁻¹ • (x - y)) 1) • u y
  rw [heatConv, MeasureTheory.convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [heatKernel_scaling (x := x - y) ht]
  simp only [Module.finrank_fin_fun]

/-- Time differentiation of heat convolution under the spatial integral. -/
theorem heatConv_hasDerivAt_integral_smooth {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huSupport : HasCompactSupport u)
    {t : ℝ} (ht : 0 < t) (x : Vec3) :
    HasDerivAt (fun s : ℝ => heatConv s u x)
      (∫ y : Vec3, heatKernelTimeDerivative y t * u (x - y)) t := by
  let g : Vec3 → ℝ := fun y => u (x - y)
  have hgc : Continuous g := by
    dsimp [g]
    fun_prop
  have hgs : HasCompactSupport g := by
    dsimp [g]
    exact huSupport.comp_homeomorph (Homeomorph.subLeft x)
  have hgi : Integrable (fun y : Vec3 => ‖g y‖) volume :=
    hgc.norm.integrable_of_hasCompactSupport hgs.norm
  have hkernel_cont : ∀ s : ℝ, Continuous (fun y : Vec3 => heatKernel y s) := by
    intro s
    by_cases hs : 0 < s
    · rw [show (fun y : Vec3 => heatKernel y s) = fun y : Vec3 =>
          (4 * Real.pi * s) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(vec3EuclideanNorm y) ^ 2 / (4 * s)) by
          funext y
          exact heatKernel_eq_formula hs]
      simp only [vec3EuclideanNorm]
      fun_prop (disch := positivity)
    · have hzero : (fun y : Vec3 => heatKernel y s) = 0 := by
        funext y
        exact heatKernel_eq_zero_of_nonpos (le_of_not_gt hs)
      rw [hzero]
      fun_prop
  let F : ℝ → Vec3 → ℝ := fun s y => heatKernel y s * g y
  let F' : ℝ → Vec3 → ℝ := fun s y => heatKernelTimeDerivative y s * g y
  have hset : Set.Ioo (t / 2) (2 * t) ∈ 𝓝 t := by
    rw [Metric.mem_nhds_iff]
    use t / 2
    constructor
    · positivity
    · intro s hs
      rw [Metric.mem_ball, Real.dist_eq] at hs
      rcases abs_lt.mp hs with ⟨hslo, hshi⟩
      constructor
      · nlinarith only [ht, hslo]
      · nlinarith only [ht, hshi]
  have hF_meas : ∀ᶠ s : ℝ in 𝓝 t,
      AEStronglyMeasurable (F s) volume := by
    filter_upwards [] with s
    have hcont : Continuous (F s) := by
      dsimp [F]
      exact (hkernel_cont s).mul hgc
    exact hcont.aestronglyMeasurable
  have hF_int : Integrable (F t) volume := by
    dsimp [F]
    exact ((hkernel_cont t).mul hgc).integrable_of_hasCompactSupport
      (hgs.mul_left)
  have hF'_meas : AEStronglyMeasurable (F' t) volume := by
    have hcont : Continuous (F' t) := by
      dsimp [F, F']
      rw [show (fun y : Vec3 => heatKernelTimeDerivative y t * g y) =
          fun y : Vec3 =>
            ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
              Real.exp (-(∑ i, y i ^ 2) / (4 * t))) *
              ((∑ i, y i ^ 2) / (4 * t ^ 2) - (3 : ℝ) / (2 * t)) * g y by
          funext y
          rw [heatKernelTimeDerivative, ite_eq_left ht,
            heatKernel_eq_formula_sum ht]]
      fun_prop (disch := positivity)
    exact hcont.aestronglyMeasurable
  let bound : Vec3 → ℝ :=
    fun y => (10000000 / (Real.sqrt (t / 2)) ^ 5) * ‖g y‖
  have hbound_integrable : Integrable bound volume := by
    dsimp [bound]
    exact hgi.const_mul _
  have h_bound : ∀ᵐ y : Vec3 ∂volume, ∀ s ∈ Set.Ioo (t / 2) (2 * t),
      ‖F' s y‖ ≤ bound y := by
    filter_upwards [] with y
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs.1.le
    have hsqrt : Real.sqrt (t / 2) ≤ Real.sqrt s :=
      Real.sqrt_le_sqrt hs.1.le
    have hrho : Real.sqrt (t / 2) ≤ rhoTwo y s := by
      calc
        Real.sqrt (t / 2) ≤ Real.sqrt s := hsqrt
        _ ≤ vec3EuclideanNorm y + Real.sqrt s :=
          le_add_of_nonneg_left (vec3EuclideanNorm_nonneg y)
    have hpow : (Real.sqrt (t / 2)) ^ 5 ≤ (rhoTwo y s) ^ 5 := by
      gcongr
    have hkernel_bound :
        |heatKernelTimeDerivative y s| ≤
          10000000 / (Real.sqrt (t / 2)) ^ 5 := by
      calc
        |heatKernelTimeDerivative y s| ≤ 10000000 / (rhoTwo y s) ^ 5 :=
          heatKernelTimeDerivative_le_rho_inv_five hspos
        _ ≤ 10000000 / (Real.sqrt (t / 2)) ^ 5 := by
          gcongr
    dsimp [F', bound]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hkernel_bound (abs_nonneg _)
  have h_diff : ∀ᵐ y : Vec3 ∂volume, ∀ s ∈ Set.Ioo (t / 2) (2 * t),
      HasDerivAt (fun s => F s y) (F' s y) s := by
    filter_upwards [] with y
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs.1.le
    dsimp [F, F']
    have hderiv := (heatKernel_time_differentiableAt (x := y) hspos).hasDerivAt
    rw [heatKernel_time_deriv (x := y) hspos] at hderiv
    exact hderiv.mul_const (g y)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') hset hF_meas hF_int hF'_meas h_bound
    hbound_integrable h_diff
  have hresult := hmain.2
  dsimp [F, F'] at hresult ⊢
  simpa only [heatConv_eq_integral, g] using hresult

/-- The time derivative is the spatial-Laplacian integral of the heat kernel. -/
theorem heatConv_hasDerivAt_laplacianIntegral_smooth {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huSupport : HasCompactSupport u)
    {t : ℝ} (ht : 0 < t) (x : Vec3) :
    HasDerivAt (fun s : ℝ => heatConv s u x)
      (∫ y : Vec3, heatKernelLaplacian y t * u (x - y)) t := by
  convert heatConv_hasDerivAt_integral_smooth hu huSupport ht x using 1
  apply integral_congr_ae
  filter_upwards [] with y
  rw [heatKernel_heat_equation ht]

/-- The heat kernel is bounded by its spatially constant prefactor. -/
theorem heatKernel_le_prefactor {y : Vec3} {t : ℝ} (ht : 0 < t) :
    heatKernel y t ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) := by
  rw [heatKernel_eq_formula_sum ht]
  have hsum : 0 ≤ ∑ i : Fin 3, y i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (y i)
  have harg : -(∑ i, y i ^ 2) / (4 * t) ≤ 0 := by
    rw [neg_div]
    exact neg_nonpos.mpr (div_nonneg hsum (by positivity))
  calc
    (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i, y i ^ 2) / (4 * t)) ≤
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr harg)
        (by positivity : 0 ≤ (4 * Real.pi * t) ^ (-(3 : ℝ) / 2))
    _ = (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) := by ring

/-- A compactly supported convolution has the standard large-time bound. -/
theorem heatConv_abs_le_prefactor_mul_integral_smooth {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huSupport : HasCompactSupport u) {t : ℝ}
    (ht : 0 < t) (x : Vec3) :
    |heatConv t u x| ≤
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * ∫ y : Vec3, ‖u y‖ := by
  have hui : Integrable u volume :=
    hu.continuous.integrable_of_hasCompactSupport huSupport
  have hcomp : Integrable (fun y : Vec3 => heatKernel (x - y) t * u y) volume := by
    have hcont : Continuous (fun y : Vec3 => heatKernel (x - y) t * u y) := by
      have hkernel : Continuous (fun y : Vec3 => heatKernel (x - y) t) := by
        rw [show (fun y : Vec3 => heatKernel (x - y) t) =
            fun y : Vec3 => (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
              Real.exp (-(vec3EuclideanNorm (x - y)) ^ 2 / (4 * t)) by
          funext y
          exact heatKernel_eq_formula ht]
        simp only [vec3EuclideanNorm]
        fun_prop (disch := positivity)
      exact hkernel.mul hu.continuous
    have hsupport : HasCompactSupport
        (fun y : Vec3 => heatKernel (x - y) t * u y) :=
      huSupport.mul_left
    exact hcont.integrable_of_hasCompactSupport hsupport
  have hbound : ∀ y : Vec3,
      ‖heatKernel (x - y) t * u y‖ ≤
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * ‖u y‖ := by
    intro y
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg _ _)]
    exact mul_le_mul_of_nonneg_right
      (heatKernel_le_prefactor ht) (norm_nonneg _)
  rw [show heatConv t u x = ∫ y : Vec3, heatKernel (x - y) t * u y by
    rw [heatConv, MeasureTheory.convolution_eq_swap]
    rfl]
  calc
    |∫ y : Vec3, heatKernel (x - y) t * u y| ≤
        ∫ y : Vec3, ‖heatKernel (x - y) t * u y‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (fun y : Vec3 => heatKernel (x - y) t * u y))
    _ ≤ ∫ y : Vec3,
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * ‖u y‖ := by
      exact integral_mono_ae hcomp.norm (hui.norm.const_mul _)
        (Filter.Eventually.of_forall hbound)
    _ = (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * ∫ y : Vec3, ‖u y‖ := by
      rw [integral_const_mul]

/-- The heat kernel tends pointwise to zero at large time. -/
theorem heatKernel_tendsto_zero_atTop (y : Vec3) :
    Tendsto (fun t : ℝ => heatKernel y t) atTop (𝓝 0) := by
  have hbase : Tendsto (fun t : ℝ => 4 * Real.pi * t) atTop atTop := by
    simpa only [id, mul_assoc] using
      ((tendsto_const_mul_atTop_of_pos (f := id) (l := atTop)
        (show 0 < 4 * Real.pi by positivity)).2 tendsto_id)
  have hpref : Tendsto (fun t : ℝ => (4 * Real.pi * t) ^ (-(3 : ℝ) / 2)) atTop
      (𝓝 0) := by
    have hpow := tendsto_rpow_neg_atTop (show 0 < (3 / 2 : ℝ) by norm_num)
    convert hpow.comp hbase using 1
    ext t
    congr 1
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0)) hpref
  · exact Filter.Eventually.of_forall fun t => heatKernel_nonneg y t
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [heatKernel_eq_formula ht]
    calc
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(vec3EuclideanNorm y) ^ 2 / (4 * t)) ≤
          (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * 1 := by
        gcongr
        apply Real.exp_le_one_iff.mpr
        rw [neg_div]
        apply neg_nonpos.mpr
        exact div_nonneg (sq_nonneg _) (by positivity)
      _ = (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) := by ring

/-- Heat convolution of a compactly supported continuous function vanishes at
large time. -/
theorem heatConv_tendsto_zero_atTop_smooth {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huSupport : HasCompactSupport u) (x : Vec3) :
    Tendsto (fun t : ℝ => heatConv t u x) atTop (𝓝 0) := by
  let g : Vec3 → ℝ := fun y => u (x - y)
  have hgc : Continuous g := by
    dsimp [g]
    fun_prop
  have hgs : HasCompactSupport g := by
    dsimp [g]
    exact huSupport.comp_homeomorph (Homeomorph.subLeft x)
  have hgi : Integrable (fun y : Vec3 => ‖g y‖) volume :=
    hgc.norm.integrable_of_hasCompactSupport hgs.norm
  have hmeas : ∀ᶠ t : ℝ in atTop,
      AEStronglyMeasurable (fun y : Vec3 => heatKernel y t * g y) volume := by
    filter_upwards [] with t
    have hcont : Continuous (fun y : Vec3 => heatKernel y t * g y) := by
      by_cases ht : 0 < t
      · have hGcont : Continuous (fun y : Vec3 => heatKernel y t) := by
          rw [show (fun y : Vec3 => heatKernel y t) = fun y : Vec3 =>
            (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
              Real.exp (-(vec3EuclideanNorm y) ^ 2 / (4 * t)) by
            funext y
            exact heatKernel_eq_formula ht]
          simp only [vec3EuclideanNorm]
          fun_prop (disch := positivity)
        exact hGcont.mul hgc
      · have hzero : (fun y : Vec3 => heatKernel y t) = 0 := by
          funext y
          exact heatKernel_eq_zero_of_nonpos (le_of_not_gt ht)
        have hzero' : Continuous (fun y : Vec3 => heatKernel y t) := by
          rw [hzero]
          fun_prop
        exact hzero'.mul hgc
    exact hcont.aestronglyMeasurable
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ᵐ y : Vec3 ∂volume,
      ‖heatKernel y t * g y‖ ≤ ‖g y‖ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    filter_upwards [] with y
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have hbase : 1 ≤ 4 * Real.pi * t := by
      calc
        (1 : ℝ) ≤ 4 * Real.pi := by nlinarith only [Real.two_le_pi]
        _ = (4 * Real.pi) * 1 := by ring
        _ ≤ 4 * Real.pi * t := by
          exact mul_le_mul_of_nonneg_left ht (by positivity)
    have hkernel : heatKernel y t ≤ 1 := by
      rw [heatKernel_eq_formula htpos]
      calc
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
              Real.exp (-(vec3EuclideanNorm y) ^ 2 / (4 * t)) ≤
            1 * Real.exp (-(vec3EuclideanNorm y) ^ 2 / (4 * t)) := by
          gcongr
          exact Real.rpow_le_one_of_one_le_of_nonpos hbase (by norm_num)
        _ ≤ 1 := by
          simpa only [one_mul] using
            (Real.exp_le_one_iff.mpr (by
              rw [neg_div]
              apply neg_nonpos.mpr
              exact div_nonneg (sq_nonneg _) (by positivity)))
        _ = 1 := by ring
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg y t)]
    calc
      heatKernel y t * ‖g y‖ ≤ 1 * ‖g y‖ :=
        mul_le_mul_of_nonneg_right hkernel (norm_nonneg _)
      _ = ‖g y‖ := by ring
  have hlim : ∀ᵐ y : Vec3 ∂volume,
      Tendsto (fun t : ℝ => heatKernel y t * g y) atTop (𝓝 0) := by
    filter_upwards [] with y
    simpa only [zero_mul] using
      (heatKernel_tendsto_zero_atTop y).mul tendsto_const_nhds
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (fun y : Vec3 => ‖g y‖) hmeas hbound hgi hlim
  simpa only [heatConv_eq_integral, g, integral_zero] using hDCT

end CKN.Foundation.Heat
