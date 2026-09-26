/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.ParametricIntegral

/-!
# Holomorphic parameters in compact contour integrals

A jointly holomorphic kernel can be integrated over a fixed compact parameter set, after a
continuous parametrization and multiplication by a fixed integrable weight. The weight need not
be holomorphic. In the circle specialization it includes the contour derivative and a continuous
boundary function.

This is simplex-independent infrastructure for continued Cauchy representations. It does not
assert a Jordan-curve theorem or homotopy invariance of contours.

## Main results

`analyticOnNhd_integral_smul_compact_kernel` gives analytic dependence for Banach-valued kernels;
`analyticOnNhd_integral_mul_compact_kernel` is its scalar specialization. Compactness supplies
derivative bounds and separable images, with no second-countability assumption on the parameter
space. `analyticOnNhd_circleIntegral_kernel_mul` is the scalar circle specialization.
-/

open Complex MeasureTheory Filter Metric Set
open scoped Topology
public section
variable {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [MeasurableSpace α] [TopologicalSpace α]
  [BorelSpace α] [T2Space α]

/-- A compact integral of a jointly analytic Banach-valued kernel, with a fixed integrable scalar
weight, is analytic in its parameters. -/
theorem analyticOnNhd_integral_smul_compact_kernel
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {μ : Measure α} {K : Set α} (hK : IsCompact K)
    {g : α → ℂ} (hg : IntegrableOn g K μ)
    {γ : α → ℂ} (hγ : ContinuousOn γ K)
    {U : Set E} (hU : IsOpen U) {W : Set (E × ℂ)}
    {H : E × ℂ → F} (hH : AnalyticOnNhd ℂ H W)
    (hW : ∀ x ∈ U, ∀ t ∈ K, (x, γ t) ∈ W) :
    AnalyticOnNhd ℂ (fun x => ∫ t in K, g t • H (x, γ t) ∂μ) U := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  let D := fun (x : E) (t : α) =>
    (fderiv ℂ H (x, γ t)).comp (ContinuousLinearMap.inl ℂ E ℂ)
  have hc : ContinuousOn (fun p : E × α => H (p.1, γ p.2)) (U ×ˢ K) :=
    hH.continuousOn.comp
      (continuousOn_fst.prodMk (hγ.comp continuousOn_snd (fun _ hp => hp.2)))
      (fun p hp => hW p.1 hp.1 p.2 hp.2)
  have hD : ContinuousOn (fun p : E × α => D p.1 p.2) (U ×ˢ K) :=
    (hH.fderiv.continuousOn.comp
      (continuousOn_fst.prodMk (hγ.comp continuousOn_snd (fun _ hp => hp.2)))
      (fun p hp => hW p.1 hp.1 p.2 hp.2)).clm_comp continuousOn_const
  have hslice {x : E} (hx : x ∈ U) : ContinuousOn (fun t => H (x, γ t)) K :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hx, ht⟩)
  apply DifferentiableOn.analyticOnNhd_of_finiteDimensional _ hU
  intro x hx
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall x r).prod hK).bddAbove_image
    (hD.mono (Set.prod_mono hball Subset.rfl)).norm
  apply (hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ.restrict K) (F := fun x t => g t • H (x, γ t))
    (F' := fun x t => g t • D x t) (bound := fun t => ‖g t‖ * M)
    (closedBall_mem_nhds x hr) ?_ (hg.smul_continuousOn_of_isCompact (hslice hx) hK) ?_ ?_
    (hg.norm.mul_const M) ?_).differentiableAt.differentiableWithinAt
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (hg.smul_continuousOn_of_isCompact (hslice hy) hK).aestronglyMeasurable
  · exact hg.aestronglyMeasurable.smul
      ((hD.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => ⟨hx, ht⟩)).aestronglyMeasurable_of_isCompact hK hK.measurableSet)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    intro y hy
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hM ⟨(y, t), ⟨hy, ht⟩, rfl⟩) (norm_nonneg _)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    intro y hy
    exact (((hH _ (hW y (hball hy) t ht)).differentiableAt.hasFDerivAt).comp y
      (hasFDerivAt_prodMk_left (𝕜 := ℂ) y (γ t))).const_smul (g t)

/-- Holomorphic dependence of a compact weighted integral of a jointly holomorphic kernel. Only the
parametrization, not the weight, must be continuous. -/
theorem analyticOnNhd_integral_mul_compact_kernel
    {μ : Measure α} {K : Set α} (hK : IsCompact K)
    {g : α → ℂ} (hg : IntegrableOn g K μ)
    {γ : α → ℂ} (hγ : ContinuousOn γ K)
    {U : Set E} (hU : IsOpen U) {W : Set (E × ℂ)}
    {H : E × ℂ → ℂ} (hH : AnalyticOnNhd ℂ H W)
    (hW : ∀ x ∈ U, ∀ t ∈ K, (x, γ t) ∈ W) :
    AnalyticOnNhd ℂ (fun x => ∫ t in K, g t * H (x, γ t) ∂μ) U := by
  simpa only [smul_eq_mul] using
    analyticOnNhd_integral_smul_compact_kernel hK hg hγ hU hH hW

omit [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α] [T2Space α] in
/-- Integrating a holomorphic parameter-dependent kernel against a continuous boundary function on a
fixed circle preserves holomorphy in all parameters. -/
theorem analyticOnNhd_circleIntegral_kernel_mul
    {U : Set E} (hU : IsOpen U) {W : Set (E × ℂ)}
    {H : E × ℂ → ℂ} (hH : AnalyticOnNhd ℂ H W)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ}
    (hf : ContinuousOn f (sphere c R))
    (hW : ∀ x ∈ U, ∀ s ∈ sphere c R, (x, s) ∈ W) :
    AnalyticOnNhd ℂ (fun x => ∮ s in C(c, R), H (x, s) * f s) U := by
  have hg : ContinuousOn (fun t : ℝ => deriv (circleMap c R) t * f (circleMap c R t))
      (Icc 0 (2 * Real.pi)) := by
    apply ContinuousOn.mul
    · change ContinuousOn (fun t : ℝ => deriv (circleMap c R) t) _
      simp only [deriv_circleMap]
      fun_prop
    · exact hf.comp (continuous_circleMap c R).continuousOn
        (fun t _ => circleMap_mem_sphere c hR t)
  have h := analyticOnNhd_integral_mul_compact_kernel (μ := volume) isCompact_Icc
    (hg.integrableOn_compact isCompact_Icc) (continuous_circleMap c R).continuousOn hU hH
    (fun x hx t _ => hW x hx _ (circleMap_mem_sphere c hR t))
  simpa only [circleIntegral_def_Icc, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
