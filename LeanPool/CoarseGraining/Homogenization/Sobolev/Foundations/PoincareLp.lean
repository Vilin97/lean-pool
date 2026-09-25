/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareLpIntegral
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareLpKernel
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareLpSmooth
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Poincare Lp -/

@[expose] public section

namespace Homogenization

/-!
# Finite-`p` convex-domain Poincare scaffolding

This wrapper module will be the stable import target for the future bounded
open convex domain `L^p` Poincare theorem family. For now it re-exports the
first two implementation layers:

- segment geometry and smooth FTC along affine segments;
- the mean-minus-average integral identity.

The eventual theorem surface should live here once the nested integral estimates
and the final convex-domain `L^p` bound are in place.
-/

private theorem continuous_integral_norm_fderiv_along_segment
    {d : ℕ} {u : Vec d → ℝ} (huDiff : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec d) :
    Continuous (fun y : Vec d => ∫ t in (0 : ℝ)..1,
      ‖fderiv ℝ u (segmentBlend x t y)‖ ∂MeasureTheory.volume) := by
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := huDiff.of_le (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hseg_cont : Continuous (fun p : Vec d × ℝ => segmentBlend x p.2 p.1) := by
    simpa [segmentBlend, AffineMap.lineMap_apply_module', add_comm] using
      (show Continuous (fun p : Vec d × ℝ => p.1 + p.2 • (x - p.1)) from
        (continuous_fst.add
          (continuous_snd.smul
            ((show Continuous (fun _ : Vec d × ℝ => x) from continuous_const).sub
              continuous_fst))))
  have hkernel :
      Continuous (fun p : Vec d × ℝ => ‖fderiv ℝ u (segmentBlend x p.2 p.1)‖) :=
    continuous_norm.comp (hfderiv_cont.comp hseg_cont)
  simpa using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume)
      (f := fun y t => ‖fderiv ℝ u (segmentBlend x t y)‖)
      hkernel (0 : ℝ) 1)

private theorem continuous_integral_norm_fderiv_mul_norm_sub_along_segment
    {d : ℕ} {u : Vec d → ℝ} (huDiff : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec d) :
    Continuous (fun y : Vec d => ∫ t in (0 : ℝ)..1,
      ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume) := by
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := huDiff.of_le (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hseg_cont : Continuous (fun p : Vec d × ℝ => segmentBlend x p.2 p.1) := by
    simpa [segmentBlend, AffineMap.lineMap_apply_module', add_comm] using
      (show Continuous (fun p : Vec d × ℝ => p.1 + p.2 • (x - p.1)) from
        (continuous_fst.add
          (continuous_snd.smul
            ((show Continuous (fun _ : Vec d × ℝ => x) from continuous_const).sub
              continuous_fst))))
  have hkernel :
      Continuous (fun p : Vec d × ℝ =>
        ‖fderiv ℝ u (segmentBlend x p.2 p.1)‖ * ‖x - p.1‖) := by
    exact
      (continuous_norm.comp (hfderiv_cont.comp hseg_cont)).mul
        (continuous_norm.comp
          ((show Continuous (fun p : Vec d × ℝ => x - p.1) from
              (show Continuous (fun _ : Vec d × ℝ => x) from continuous_const).sub
                continuous_fst)))
  simpa using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume)
      (f := fun y t => ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖)
      hkernel (0 : ℝ) 1)

private theorem integrableOn_norm_fderiv_mul_norm_sub_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    {u : Vec d → ℝ} (huDiff : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec d) :
    MeasureTheory.IntegrableOn
      (fun z : Vec d => ‖fderiv ℝ u z‖ * ‖x - z‖)
      U := by
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := huDiff.of_le (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hcont : Continuous (fun z : Vec d => ‖fderiv ℝ u z‖ * ‖x - z‖) :=
    (continuous_norm.comp hfderiv_cont).mul
      (continuous_norm.comp ((show Continuous (fun z : Vec d => x - z) from
        (show Continuous (fun _ : Vec d => x) from continuous_const).sub continuous_id)))
  have hcompact : IsCompact (closure U) := hU.isBoundedDomain.isBounded.isCompact_closure
  exact (hcont.continuousOn.integrableOn_compact hcompact).mono_set subset_closure

private theorem integrableOn_norm_fderiv_mul_rieszKernel_of_isSobolevRegularDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    {u : Vec d → ℝ} (huDiff : ContDiff ℝ (⊤ : ℕ∞) u) {x : Vec d} (hx : x ∈ U) :
    MeasureTheory.IntegrableOn
      (fun z : Vec d => ‖fderiv ℝ u z‖ * rieszKernel x z)
      U := by
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := huDiff.of_le (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hcompact : IsCompact (closure U) := hU.isBoundedDomain.isBounded.isCompact_closure
  have hkernel_int :
      MeasureTheory.IntegrableOn (fun z : Vec d => rieszKernel x z) U MeasureTheory.volume :=
    hU.isBoundedDomain.integrableOn_rieszKernel hx
  have hcontOn : ContinuousOn (fun z : Vec d => ‖fderiv ℝ u z‖) (closure U) :=
    (continuous_norm.comp hfderiv_cont).continuousOn
  simpa [mul_comm] using
    hkernel_int.mul_continuousOn_of_subset hcontOn hU.measurableSet hcompact subset_closure

private theorem integrable_segmentBlend_norm_fderiv_mul_norm_sub_prod_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    {u : Vec d → ℝ} (huDiff : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec d) :
    MeasureTheory.Integrable
      (fun p : ℝ × Vec d => ‖fderiv ℝ u (segmentBlend x p.1 p.2)‖ * ‖x - p.2‖)
      ((MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (MeasureTheory.volume.restrict U)) := by
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := huDiff.of_le (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hseg_cont : Continuous (fun p : ℝ × Vec d => segmentBlend x p.1 p.2) := by
    simpa [segmentBlend, AffineMap.lineMap_apply_module', add_comm] using
      (show Continuous (fun p : ℝ × Vec d => p.2 + p.1 • (x - p.2)) from
        continuous_snd.add
          (continuous_fst.smul
            ((show Continuous (fun _ : ℝ × Vec d => x) from continuous_const).sub
              continuous_snd)))
  have hcont :
      Continuous
        (fun p : ℝ × Vec d => ‖fderiv ℝ u (segmentBlend x p.1 p.2)‖ * ‖x - p.2‖) := by
    exact
      (continuous_norm.comp (hfderiv_cont.comp hseg_cont)).mul
        (continuous_norm.comp
          ((show Continuous (fun p : ℝ × Vec d => x - p.2) from
              (show Continuous (fun _ : ℝ × Vec d => x) from continuous_const).sub
                continuous_snd)))
  have hcompact :
      IsCompact ((Set.Icc (0 : ℝ) 1) ×ˢ closure U) :=
    isCompact_Icc.prod hU.isBoundedDomain.isBounded.isCompact_closure
  have hprod_int :
      MeasureTheory.IntegrableOn
        (fun p : ℝ × Vec d => ‖fderiv ℝ u (segmentBlend x p.1 p.2)‖ * ‖x - p.2‖)
        ((Set.Icc (0 : ℝ) 1) ×ˢ closure U)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
    hcont.continuousOn.integrableOn_compact hcompact
  have hsub :
      (Set.Ioc (0 : ℝ) 1) ×ˢ U ⊆ (Set.Icc (0 : ℝ) 1) ×ˢ closure U := by
    intro p hp
    exact ⟨Set.Ioc_subset_Icc_self hp.1, subset_closure hp.2⟩
  simpa [MeasureTheory.IntegrableOn, MeasureTheory.Measure.prod_restrict] using
    hprod_int.mono_set hsub

theorem integrableOn_integral_norm_fderiv_along_segment_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    {u : Vec d → ℝ} (huDiff : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec d) :
    MeasureTheory.IntegrableOn
      (fun y : Vec d => ∫ t in (0 : ℝ)..1,
        ‖fderiv ℝ u (segmentBlend x t y)‖ ∂MeasureTheory.volume)
      U := by
  have hcont : Continuous (fun y : Vec d => ∫ t in (0 : ℝ)..1,
      ‖fderiv ℝ u (segmentBlend x t y)‖ ∂MeasureTheory.volume) :=
    continuous_integral_norm_fderiv_along_segment huDiff x
  have hcompact : IsCompact (closure U) := hU.isBoundedDomain.isBounded.isCompact_closure
  exact (hcont.continuousOn.integrableOn_compact hcompact).mono_set subset_closure

theorem integrableOn_integral_norm_fderiv_mul_norm_sub_along_segment_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    {u : Vec d → ℝ} (huDiff : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec d) :
    MeasureTheory.IntegrableOn
      (fun y : Vec d => ∫ t in (0 : ℝ)..1,
        ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume)
      U := by
  have hcont : Continuous (fun y : Vec d => ∫ t in (0 : ℝ)..1,
      ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume) :=
    continuous_integral_norm_fderiv_mul_norm_sub_along_segment huDiff x
  have hcompact : IsCompact (closure U) := hU.isBoundedDomain.isBounded.isCompact_closure
  exact (hcont.continuousOn.integrableOn_compact hcompact).mono_set subset_closure

theorem norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_norm_sub_along_segment
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {u : Vec d → ℝ} (hu : MeasureTheory.IntegrableOn u U)
    (huDiff : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec d)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (hsegment :
      MeasureTheory.IntegrableOn
        (fun y => ∫ t in (0 : ℝ)..1,
          ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖)
        U) :
    ‖u x - integralAverage U u‖ ≤
      (MeasureTheory.volume U).toReal⁻¹ *
        ∫ y in U, ∫ t in (0 : ℝ)..1,
          ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume := by
  have hμinv_nonneg : 0 ≤ (MeasureTheory.volume U).toReal⁻¹ := by
    positivity
  have hconstInt : MeasureTheory.IntegrableOn (fun _ : Vec d => u x) U := by
    simp [MeasureTheory.IntegrableOn]
  have hsubInt : MeasureTheory.IntegrableOn (fun y => u x - u y) U := by
    simpa using! hconstInt.sub hu
  have hleftInt : MeasureTheory.IntegrableOn (fun y => ‖u x - u y‖) U := hsubInt.norm
  have hmono :
      (fun y => ‖u x - u y‖) ≤ᵐ[volumeMeasureOn U]
        (fun y => ∫ t in (0 : ℝ)..1,
          ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume) := by
    filter_upwards [] with y
    exact norm_sub_le_integral_norm_fderiv_mul_norm_sub_along_segment huDiff x y
  have hint :
      ∫ y in U, ‖u x - u y‖ ∂MeasureTheory.volume ≤
        ∫ y in U, ∫ t in (0 : ℝ)..1,
          ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
      (MeasureTheory.integral_mono_ae hleftInt hsegment hmono)
  calc
    ‖u x - integralAverage U u‖ ≤
        (MeasureTheory.volume U).toReal⁻¹ *
          ∫ y in U, ‖u x - u y‖ ∂MeasureTheory.volume :=
      norm_sub_integralAverage_le_volumeAverage_integral_norm_sub hu x hvol
    _ ≤ (MeasureTheory.volume U).toReal⁻¹ *
        ∫ y in U, ∫ t in (0 : ℝ)..1,
          ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
            exact mul_le_mul_of_nonneg_left hint hμinv_nonneg

theorem norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_norm_sub_along_segment_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) {u : Vec d → ℝ}
    (hu : MeasureTheory.IntegrableOn u U) (huDiff : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec d)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    ‖u x - integralAverage U u‖ ≤
      (MeasureTheory.volume U).toReal⁻¹ *
        ∫ y in U, ∫ t in (0 : ℝ)..1,
          ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume
          ∂MeasureTheory.volume :=
  norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_norm_sub_along_segment
    hu huDiff x hvol
    (integrableOn_integral_norm_fderiv_mul_norm_sub_along_segment_of_isSobolevRegularDomain
      hU huDiff x)

private theorem setIntegral_intervalIntegral_norm_fderiv_mul_norm_sub_along_segment_swap
    {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    {u : Vec d → ℝ} (huDiff : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec d) :
    ∫ y in U, ∫ t in (0 : ℝ)..1,
      ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume
        ∂MeasureTheory.volume
      =
      ∫ t in (0 : ℝ)..1, ∫ y in U,
        ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
  have hprod_int :
      MeasureTheory.Integrable
        (fun p : ℝ × Vec d => ‖fderiv ℝ u (segmentBlend x p.1 p.2)‖ * ‖x - p.2‖)
        ((MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
          (MeasureTheory.volume.restrict U)) :=
    integrable_segmentBlend_norm_fderiv_mul_norm_sub_prod_of_isSobolevRegularDomain
      hU huDiff x
  have hprod_int' :
      MeasureTheory.Integrable
        (Function.uncurry fun t y =>
          ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖)
        ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
          (MeasureTheory.volume.restrict U)) := by
    simpa [Function.uncurry, Set.uIoc_of_le zero_le_one] using! hprod_int
  simpa [Set.uIoc_of_le zero_le_one] using
    (MeasureTheory.intervalIntegral_integral_swap
      (μ := MeasureTheory.volume.restrict U)
      (a := (0 : ℝ)) (b := 1)
      (f := fun t y => ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖)
      hprod_int').symm

theorem intervalIntegral_setIntegral_norm_fderiv_mul_norm_sub_along_segment_le_rieszKernel_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} (huDiff : ContDiff ℝ (⊤ : ℕ∞) u) {x : Vec d} (hx : x ∈ U) :
    ∫ t in (0 : ℝ)..1, ∫ y in U,
      ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume
        ∂MeasureTheory.volume
      ≤
      (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ)) *
        ∫ z in U, ‖fderiv ℝ u z‖ * rieszKernel x z ∂MeasureTheory.volume := by
  let φ : Vec d → ℝ := fun z => ‖fderiv ℝ u z‖
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := huDiff.of_le (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hφ_nonneg : ∀ z, 0 ≤ φ z := by
    intro z
    exact norm_nonneg _
  have hφ_meas : AEMeasurable φ (MeasureTheory.volume.restrict U) :=
    hfderiv_cont.norm.measurable.aemeasurable
  have hφ_int :
      MeasureTheory.IntegrableOn (fun z => φ z * ‖x - z‖) U MeasureTheory.volume := by
    simpa [φ] using
      integrableOn_norm_fderiv_mul_norm_sub_of_isSobolevRegularDomain
        hU.isSobolevRegularDomain huDiff x
  have hφK_int :
      MeasureTheory.IntegrableOn (fun z => φ z * rieszKernel x z) U MeasureTheory.volume := by
    simpa [φ] using
      integrableOn_norm_fderiv_mul_rieszKernel_of_isSobolevRegularDomain
        (d := d) hU.isSobolevRegularDomain huDiff hx
  have hR : 0 < 2 * Classical.choose hU.isBoundedDomain := by
    have hchoose_pos : 0 < Classical.choose hU.isBoundedDomain :=
      (Classical.choose_spec hU.isBoundedDomain).1
    linarith
  have hleft_int :
      IntervalIntegrable
        (fun t =>
          ∫ y in U, φ (segmentBlend x t y) * ‖x - y‖ ∂MeasureTheory.volume)
        MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    simpa [MeasureTheory.IntegrableOn, MeasureTheory.Measure.prod_restrict, φ] using
      (integrable_segmentBlend_norm_fderiv_mul_norm_sub_prod_of_isSobolevRegularDomain
        hU.isSobolevRegularDomain huDiff x).integral_prod_left
  have hright_int :
      IntervalIntegrable
        (fun t =>
          ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
            ∫ z in U ∩
              Metric.closedBall x ((1 - t) * (2 * Classical.choose hU.isBoundedDomain)),
              φ z * ‖x - z‖ ∂MeasureTheory.volume)
        MeasureTheory.volume 0 1 :=
    intervalIntegrable_inv_pow_setIntegral_inter_closedBall
      (d := d) hU.isOpen.measurableSet hR hφ_nonneg hφ_meas hφK_int
  have hpointwise :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        ∫ y in U, φ (segmentBlend x t y) * ‖x - y‖ ∂MeasureTheory.volume
          ≤
          ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
            ∫ z in U ∩
              Metric.closedBall x ((1 - t) * (2 * Classical.choose hU.isBoundedDomain)),
              φ z * ‖x - z‖ ∂MeasureTheory.volume := by
    intro t ht
    exact
      setIntegral_segmentBlend_mul_norm_sub_le_inv_pow_mul_setIntegral_inter_closedBall
        hU hx ht.1.le ht.2 hφ_int hφ_nonneg
  calc
    ∫ t in (0 : ℝ)..1, ∫ y in U,
        φ (segmentBlend x t y) * ‖x - y‖ ∂MeasureTheory.volume
          ∂MeasureTheory.volume
      ≤
        ∫ t in (0 : ℝ)..1,
          ((1 - t) ^ (d + 1 : ℕ))⁻¹ *
            ∫ z in U ∩
              Metric.closedBall x ((1 - t) * (2 * Classical.choose hU.isBoundedDomain)),
              φ z * ‖x - z‖ ∂MeasureTheory.volume
            ∂MeasureTheory.volume := by
            exact
              intervalIntegral.integral_mono_on_of_le_Ioo
                zero_le_one hleft_int hright_int hpointwise
    _ ≤ (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ)) *
          ∫ z in U, φ z * rieszKernel x z ∂MeasureTheory.volume := by
            exact
              intervalIntegral_inv_pow_setIntegral_inter_closedBall_le_rieszKernel
                (d := d) hU.isOpen.measurableSet hR hφ_nonneg hφ_meas hφK_int
    _ = (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ)) *
          ∫ z in U, ‖fderiv ℝ u z‖ * rieszKernel x z ∂MeasureTheory.volume := by
            simp [φ]

theorem setIntegral_intervalIntegral_norm_fderiv_mul_norm_sub_along_segment_le_rieszKernel_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} (huDiff : ContDiff ℝ (⊤ : ℕ∞) u) {x : Vec d} (hx : x ∈ U) :
    ∫ y in U, ∫ t in (0 : ℝ)..1,
      ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume
        ∂MeasureTheory.volume
      ≤
      (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ)) *
        ∫ z in U, ‖fderiv ℝ u z‖ * rieszKernel x z ∂MeasureTheory.volume := by
  rw [setIntegral_intervalIntegral_norm_fderiv_mul_norm_sub_along_segment_swap
    hU.isSobolevRegularDomain huDiff x]
  exact
    intervalIntegral_setIntegral_norm_fderiv_mul_norm_sub_along_segment_le_rieszKernel_of_isOpenBoundedConvexDomain
      (d := d) hU huDiff hx

theorem norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_rieszKernel_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) {u : Vec d → ℝ}
    (hu : MeasureTheory.IntegrableOn u U) (huDiff : ContDiff ℝ (⊤ : ℕ∞) u)
    {x : Vec d} (hx : x ∈ U)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    ‖u x - integralAverage U u‖ ≤
      (MeasureTheory.volume U).toReal⁻¹ *
        ((((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ)) *
          ∫ z in U, ‖fderiv ℝ u z‖ * rieszKernel x z ∂MeasureTheory.volume) := by
  have hμinv_nonneg : 0 ≤ (MeasureTheory.volume U).toReal⁻¹ := by
    positivity
  calc
    ‖u x - integralAverage U u‖ ≤
        (MeasureTheory.volume U).toReal⁻¹ *
          ∫ y in U, ∫ t in (0 : ℝ)..1,
            ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume
              ∂MeasureTheory.volume :=
      norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_norm_sub_along_segment_of_isSobolevRegularDomain
        hU.isSobolevRegularDomain hu huDiff x hvol
    _ ≤ (MeasureTheory.volume U).toReal⁻¹ *
        ((((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ)) *
          ∫ z in U, ‖fderiv ℝ u z‖ * rieszKernel x z ∂MeasureTheory.volume) := by
            exact mul_le_mul_of_nonneg_left
              (setIntegral_intervalIntegral_norm_fderiv_mul_norm_sub_along_segment_le_rieszKernel_of_isOpenBoundedConvexDomain
                (d := d) hU huDiff hx)
              hμinv_nonneg

private theorem integrableOn_norm_fderiv_rpow_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    {u : Vec d → ℝ} (huDiff : ContDiff ℝ (⊤ : ℕ∞) u)
    {p : ℝ} (hp : 0 < p) :
    MeasureTheory.IntegrableOn
      (fun z : Vec d => ‖fderiv ℝ u z‖ ^ p)
      U := by
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := huDiff.of_le (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hp_nonneg : 0 ≤ p := le_of_lt hp
  have hcont : Continuous (fun z : Vec d => ‖fderiv ℝ u z‖ ^ p) :=
    (continuous_norm.comp hfderiv_cont).rpow_const (fun _ => Or.inr hp_nonneg)
  have hcompact : IsCompact (closure U) := hU.isBoundedDomain.isBounded.isCompact_closure
  exact (hcont.continuousOn.integrableOn_compact hcompact).mono_set subset_closure

private theorem integrableOn_prod_norm_fderiv_rpow_mul_rieszKernel_of_isSobolevRegularDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    {u : Vec d → ℝ} (huDiff : ContDiff ℝ (⊤ : ℕ∞) u)
    {p : ℝ} (hp : 0 < p) :
    MeasureTheory.IntegrableOn
      (fun z : Vec d × Vec d => (‖fderiv ℝ u z.2‖ ^ p) * rieszKernel z.1 z.2)
      (U ×ˢ U) (MeasureTheory.volume.prod MeasureTheory.volume) := by
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := huDiff.of_le (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hp_nonneg : 0 ≤ p := le_of_lt hp
  have hkernel_int :
      MeasureTheory.IntegrableOn
        (fun z : Vec d × Vec d => rieszKernel z.1 z.2)
        (U ×ˢ U) (MeasureTheory.volume.prod MeasureTheory.volume) :=
    integrableOn_prod_rieszKernel_of_isSobolevRegularDomain (d := d) hU
  have hcontOn :
      ContinuousOn
        (fun z : Vec d × Vec d => ‖fderiv ℝ u z.2‖ ^ p)
        (closure U ×ˢ closure U) := by
    have hcont : Continuous (fun z : Vec d × Vec d => ‖fderiv ℝ u z.2‖ ^ p) :=
      (continuous_norm.comp (hfderiv_cont.comp continuous_snd)).rpow_const
        (fun _ => Or.inr hp_nonneg)
    exact hcont.continuousOn
  have hcompact : IsCompact (closure U ×ˢ closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure.prod
      hU.isBoundedDomain.isBounded.isCompact_closure
  have hsub : U ×ˢ U ⊆ closure U ×ˢ closure U := by
    intro z hz
    exact ⟨subset_closure hz.1, subset_closure hz.2⟩
  simpa [mul_comm] using
    hkernel_int.mul_continuousOn_of_subset hcontOn
      (hU.measurableSet.prod hU.measurableSet) hcompact hsub

private theorem integrableOn_norm_sub_integralAverage_rpow_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) {u : Vec d → ℝ}
    (huDiff : ContDiff ℝ (⊤ : ℕ∞) u)
    {p : ℝ} (hp : 0 < p) :
    MeasureTheory.IntegrableOn
      (fun x : Vec d => ‖u x - integralAverage U u‖ ^ p)
      U := by
  have hp_nonneg : 0 ≤ p := le_of_lt hp
  have hu_cont : Continuous u := huDiff.continuous
  have hcont : Continuous (fun x : Vec d => ‖u x - integralAverage U u‖ ^ p) :=
    (continuous_norm.comp (hu_cont.sub continuous_const)).rpow_const
      (fun _ => Or.inr hp_nonneg)
  have hcompact : IsCompact (closure U) := hU.isBoundedDomain.isBounded.isCompact_closure
  exact (hcont.continuousOn.integrableOn_compact hcompact).mono_set subset_closure

theorem integral_rpow_norm_sub_integralAverage_le_bound_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) {u : Vec d → ℝ}
    (hu : MeasureTheory.IntegrableOn u U) (huDiff : ContDiff ℝ (⊤ : ℕ∞) u)
    {p : ℝ} (hp : 1 < p) (hvol : 0 < (MeasureTheory.volume U).toReal) :
    ∫ x in U, ‖u x - integralAverage U u‖ ^ p ∂MeasureTheory.volume ≤
      (((MeasureTheory.volume U).toReal⁻¹ *
          (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ))) ^ p) *
        ((((d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
            (4 * Classical.choose hU.isBoundedDomain)) ^ p) *
          ∫ y in U, ‖fderiv ℝ u y‖ ^ p ∂MeasureTheory.volume) := by
  let μU : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict U
  let B : ℝ :=
    (MeasureTheory.volume U).toReal⁻¹ *
      (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ))
  let M : ℝ :=
    (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
      (4 * Classical.choose hU.isBoundedDomain)
  let g : Vec d → ℝ := fun y => ‖fderiv ℝ u y‖
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hchoose_pos : 0 < Classical.choose hU.isBoundedDomain :=
    (Classical.choose_spec hU.isBoundedDomain).1
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hg_nonneg : ∀ y, 0 ≤ g y := by
    intro y
    exact norm_nonneg _
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := huDiff.of_le (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hg_meas : AEMeasurable g μU :=
    hfderiv_cont.norm.measurable.aemeasurable
  have hgK_prod_int :
      MeasureTheory.IntegrableOn
        (fun z : Vec d × Vec d => g z.2 * rieszKernel z.1 z.2)
        (U ×ˢ U) (MeasureTheory.volume.prod MeasureTheory.volume) := by
    simpa [g] using
      integrableOn_prod_norm_fderiv_rpow_mul_rieszKernel_of_isSobolevRegularDomain
        (d := d) hU.isSobolevRegularDomain huDiff (p := (1 : ℝ)) zero_lt_one
  have hgp_int :
      MeasureTheory.IntegrableOn
        (fun y => (g y) ^ p) U MeasureTheory.volume := by
    simpa [g] using
      integrableOn_norm_fderiv_rpow_of_isSobolevRegularDomain
        hU.isSobolevRegularDomain huDiff hp_pos
  have hgpK_prod_int :
      MeasureTheory.IntegrableOn
        (fun z : Vec d × Vec d => (g z.2) ^ p * rieszKernel z.1 z.2)
        (U ×ˢ U) (MeasureTheory.volume.prod MeasureTheory.volume) := by
    simpa [g] using
      integrableOn_prod_norm_fderiv_rpow_mul_rieszKernel_of_isSobolevRegularDomain
        (d := d) hU.isSobolevRegularDomain huDiff hp_pos
  have hleft_int :
      MeasureTheory.Integrable
        (fun x => ‖u x - integralAverage U u‖ ^ p) μU := by
    simpa [μU, MeasureTheory.IntegrableOn] using
      integrableOn_norm_sub_integralAverage_rpow_of_isSobolevRegularDomain
        hU.isSobolevRegularDomain huDiff hp_pos
  have hkernel_pow_int :
      MeasureTheory.Integrable
        (fun x => (∫ y, g y * rieszKernel x y ∂μU) ^ p)
        μU :=
    integrable_rpow_integral_mul_rieszKernel_of_isSobolevRegularDomain
      hU.isSobolevRegularDomain hp hg_nonneg hg_meas hgK_prod_int hgpK_prod_int
  have hright_int :
      MeasureTheory.Integrable
        (fun x => (B * ∫ y, g y * rieszKernel x y ∂μU) ^ p)
        μU := by
    have htmp :
        MeasureTheory.Integrable
          (fun x => B ^ p * (∫ y, g y * rieszKernel x y ∂μU) ^ p)
          μU := hkernel_pow_int.const_mul (B ^ p)
    refine htmp.congr ?_
    filter_upwards with x
    have hinner_nonneg : 0 ≤ ∫ y, g y * rieszKernel x y ∂μU := by
      exact MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall
          (fun y => mul_nonneg (hg_nonneg y) (rieszKernel_nonneg x y)))
    rw [Real.mul_rpow hB_nonneg hinner_nonneg]
  have hpointwise :
      (fun x => ‖u x - integralAverage U u‖ ^ p) ≤ᵐ[μU]
        (fun x => (B * ∫ y, g y * rieszKernel x y ∂μU) ^ p) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU.isOpen.measurableSet] with x hx
    have hbase :
        ‖u x - integralAverage U u‖ ≤
          B * ∫ z in U, ‖fderiv ℝ u z‖ * rieszKernel x z ∂MeasureTheory.volume := by
      simpa [B, g, μU, mul_assoc] using
        norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_rieszKernel_of_isOpenBoundedConvexDomain
          (d := d) hU hu huDiff hx hvol
    have hright_nonneg : 0 ≤
        B * ∫ y, g y * rieszKernel x y ∂μU := by
      have hinner_nonneg : 0 ≤ ∫ y, g y * rieszKernel x y ∂μU := by
        exact MeasureTheory.integral_nonneg_of_ae
          (Filter.Eventually.of_forall
            (fun y => mul_nonneg (hg_nonneg y) (rieszKernel_nonneg x y)))
      exact mul_nonneg hB_nonneg hinner_nonneg
    exact Real.rpow_le_rpow (norm_nonneg _) hbase hp_nonneg
  have hBpow_nonneg : 0 ≤ B ^ p := Real.rpow_nonneg hB_nonneg _
  calc
    ∫ x in U, ‖u x - integralAverage U u‖ ^ p ∂MeasureTheory.volume
        = ∫ x, ‖u x - integralAverage U u‖ ^ p ∂μU := by
            rfl
    _ ≤ ∫ x, (B * ∫ y, g y * rieszKernel x y ∂μU) ^ p ∂μU := by
          exact MeasureTheory.integral_mono_ae hleft_int hright_int hpointwise
    _ = ∫ x, B ^ p * (∫ y, g y * rieszKernel x y ∂μU) ^ p ∂μU := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          have hinner_nonneg : 0 ≤ ∫ y, g y * rieszKernel x y ∂μU := by
            exact MeasureTheory.integral_nonneg_of_ae
              (Filter.Eventually.of_forall
                (fun y => mul_nonneg (hg_nonneg y) (rieszKernel_nonneg x y)))
          rw [Real.mul_rpow hB_nonneg hinner_nonneg]
    _ = B ^ p * ∫ x, (∫ y, g y * rieszKernel x y ∂μU) ^ p ∂μU := by
          rw [MeasureTheory.integral_const_mul]
    _ ≤ B ^ p *
        ((((d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
            (4 * Classical.choose hU.isBoundedDomain)) ^ p) *
          ∫ y in U, (g y) ^ p ∂MeasureTheory.volume) := by
            apply mul_le_mul_of_nonneg_left ?_ hBpow_nonneg
            simpa [μU, M] using
              integral_rpow_integral_mul_rieszKernel_le_bound_of_isSobolevRegularDomain
                hU.isSobolevRegularDomain hp hg_nonneg hg_meas hgK_prod_int hgp_int hgpK_prod_int
    _ = (((MeasureTheory.volume U).toReal⁻¹ *
          (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ))) ^ p) *
        ((((d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
            (4 * Classical.choose hU.isBoundedDomain)) ^ p) *
          ∫ y in U, ‖fderiv ℝ u y‖ ^ p ∂MeasureTheory.volume) := by
            simp [B, g]

theorem norm_sub_integralAverage_le_two_mul_choose_mul_volumeAverage_integral_norm_fderiv_along_segment
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) {u : Vec d → ℝ}
    (hu : MeasureTheory.IntegrableOn u U) (huDiff : ContDiff ℝ (⊤ : ℕ∞) u)
    {x : Vec d} (hx : x ∈ U)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (hsegmentMul :
      MeasureTheory.IntegrableOn
        (fun y => ∫ t in (0 : ℝ)..1,
          ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume)
        U)
    (hsegment :
      MeasureTheory.IntegrableOn
        (fun y => ∫ t in (0 : ℝ)..1,
          ‖fderiv ℝ u (segmentBlend x t y)‖ ∂MeasureTheory.volume)
        U) :
    ‖u x - integralAverage U u‖ ≤
      (MeasureTheory.volume U).toReal⁻¹ *
        ((2 * Classical.choose hU.isBoundedDomain) *
          ∫ y in U, ∫ t in (0 : ℝ)..1,
            ‖fderiv ℝ u (segmentBlend x t y)‖ ∂MeasureTheory.volume
            ∂MeasureTheory.volume) := by
  have hμinv_nonneg : 0 ≤ (MeasureTheory.volume U).toReal⁻¹ := by
    positivity
  have houterScaled :
      MeasureTheory.IntegrableOn
        (fun y => (2 * Classical.choose hU.isBoundedDomain) *
          ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u (segmentBlend x t y)‖ ∂MeasureTheory.volume)
        U := by
    simpa [MeasureTheory.IntegrableOn, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      hsegment.integrable.const_mul (2 * Classical.choose hU.isBoundedDomain)
  have hmono :
      (fun y => ∫ t in (0 : ℝ)..1,
        ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume) ≤ᵐ[volumeMeasureOn U]
        (fun y => (2 * Classical.choose hU.isBoundedDomain) *
          ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u (segmentBlend x t y)‖ ∂MeasureTheory.volume) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU.measurableSet] with y hy
    exact
      integral_norm_fderiv_mul_norm_sub_along_segment_le_two_mul_choose_mul_integral_norm_fderiv_along_segment
        hU.isBoundedDomain huDiff hx hy
  have houter_le :
      ∫ y in U, ∫ t in (0 : ℝ)..1,
        ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume
          ∂MeasureTheory.volume ≤
        ∫ y in U, (2 * Classical.choose hU.isBoundedDomain) *
          ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u (segmentBlend x t y)‖
            ∂MeasureTheory.volume ∂MeasureTheory.volume := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
      (MeasureTheory.integral_mono_ae hsegmentMul houterScaled hmono)
  calc
    ‖u x - integralAverage U u‖ ≤
        (MeasureTheory.volume U).toReal⁻¹ *
          ∫ y in U, ∫ t in (0 : ℝ)..1,
            ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖ ∂MeasureTheory.volume
            ∂MeasureTheory.volume :=
      norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_norm_sub_along_segment
        hu huDiff x hvol hsegmentMul
    _ ≤ (MeasureTheory.volume U).toReal⁻¹ *
        ∫ y in U, (2 * Classical.choose hU.isBoundedDomain) *
          ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u (segmentBlend x t y)‖
            ∂MeasureTheory.volume ∂MeasureTheory.volume := by
              exact mul_le_mul_of_nonneg_left houter_le hμinv_nonneg
    _ = (MeasureTheory.volume U).toReal⁻¹ *
        ((2 * Classical.choose hU.isBoundedDomain) *
          ∫ y in U, ∫ t in (0 : ℝ)..1,
            ‖fderiv ℝ u (segmentBlend x t y)‖ ∂MeasureTheory.volume
            ∂MeasureTheory.volume) := by
              rw [MeasureTheory.integral_const_mul]

theorem norm_sub_integralAverage_le_two_mul_choose_mul_volumeAverage_integral_norm_fderiv_along_segment_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) {u : Vec d → ℝ}
    (hu : MeasureTheory.IntegrableOn u U) (huDiff : ContDiff ℝ (⊤ : ℕ∞) u)
    {x : Vec d} (hx : x ∈ U)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    ‖u x - integralAverage U u‖ ≤
      (MeasureTheory.volume U).toReal⁻¹ *
        ((2 * Classical.choose hU.isBoundedDomain) *
          ∫ y in U, ∫ t in (0 : ℝ)..1,
            ‖fderiv ℝ u (segmentBlend x t y)‖ ∂MeasureTheory.volume
            ∂MeasureTheory.volume) := by
  exact
    norm_sub_integralAverage_le_two_mul_choose_mul_volumeAverage_integral_norm_fderiv_along_segment
      hU hu huDiff hx hvol
      (integrableOn_integral_norm_fderiv_mul_norm_sub_along_segment_of_isSobolevRegularDomain
        hU huDiff x)
      (integrableOn_integral_norm_fderiv_along_segment_of_isSobolevRegularDomain
        hU huDiff x)

end Homogenization
