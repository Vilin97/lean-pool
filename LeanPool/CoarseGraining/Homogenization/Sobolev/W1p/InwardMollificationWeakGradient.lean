/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.GlobalAffineLp
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.InwardMollificationGeometry
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvolutionLp

/-!
# Weak gradient of inward mollification

This file identifies the classical coordinate derivative of the inward
mollification of an `H10Function` with the correspondingly mollified global
zero extension of its weak gradient.  The proof first establishes the global
convolution identity by closing the identities for the supported smooth
approximants built into `H10Function`, and then applies the affine chain rule.
-/

namespace Homogenization

open Function MeasureTheory _root_.Filter Set Topology
open scoped ENNReal Convolution Pointwise

noncomputable section

private theorem H10Function.approx_sub_zeroExtension_eq_indicator_sub
    {d : ℕ} {U : Set (Vec d)} (u : H10Function U) (n : ℕ) :
    (fun x => u.approx n x - u.zeroExtension x) =
      Set.indicator U (fun x => u.approx n x - u.toH1Function.toFun x) := by
  funext x
  by_cases hx : x ∈ U
  · simp only [Set.indicator_of_mem hx, u.zeroExtension_apply_of_mem hx]
  · have hzero : u.approx n x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun hx_support => hx (u.approx_support_subset n hx_support)
    rw [Set.indicator_of_notMem hx, u.zeroExtension_apply_of_not_mem hx, sub_zero, hzero]

private theorem H10Function.fderiv_approx_sub_zeroExtensionGrad_eq_indicator_sub
    {d : ℕ} {U : Set (Vec d)} (u : H10Function U) (n : ℕ) (i : Fin d) :
    (fun x =>
      (fderiv ℝ (u.approx n) x) (basisVec i) - u.zeroExtensionGrad x i) =
      Set.indicator U
        (fun x =>
          (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i) := by
  funext x
  by_cases hx : x ∈ U
  · simp only [Set.indicator_of_mem hx, u.zeroExtensionGrad_apply_of_mem hx]
  · have hx_support : x ∉ tsupport (u.approx n) :=
      fun hx_support => hx (u.approx_support_subset n hx_support)
    have hzero : u.approx n =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := u.approx n)).isOpen_compl.eventually_mem hx_support |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    have hderiv_zero : (fderiv ℝ (u.approx n) x) (basisVec i) = 0 := by
      rw [hzero.fderiv_eq]
      simp only [fderiv_zero, Pi.zero_apply, zero_apply]
    rw [Set.indicator_of_notMem hx, u.zeroExtensionGrad_apply_of_not_mem hx,
      Pi.zero_apply, sub_zero, hderiv_zero]

private theorem memLp_convolution_scaledConvexApproxKernel
    {d : ℕ} {g : Vec d → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hg : MemLp g p volume) {a : ℝ} (ha : 0 < a) :
    MemLp
      (scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] g)
      p volume := by
  let k : Vec d → ℝ :=
    scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a
  have hρ : IsConvexApproxKernel (unitConvexApproxKernel (d := d)) :=
    isConvexApproxKernel_unitConvexApproxKernel
  have hk_compact : HasCompactSupport k :=
    hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport ha
  have hk_cont : Continuous k :=
    continuous_scaledConvexApproxKernel hρ.continuous a
  have hconv_cont : Continuous
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) :=
    hk_compact.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hk_cont (hg.locallyIntegrable hp)
  refine ⟨hconv_cont.aestronglyMeasurable, ?_⟩
  exact (young_convolution_nonneg_integral_one_of_aemeasurable hp hp_top
    (scaledConvexApproxKernel_nonneg hρ ha)
    (integrable_scaledConvexApproxKernel hρ ha)
    (integral_scaledConvexApproxKernel hρ ha)
    (measurable_scaledConvexApproxKernel hρ.continuous a)
    hg.aemeasurable).trans_lt hg.2

private theorem convolution_sub_eq_sub_convolution
    {d : ℕ} {k f g : Vec d → ℝ}
    (hkf : ConvolutionExists k f (ContinuousLinearMap.lsmul ℝ ℝ) volume)
    (hkg : ConvolutionExists k g (ContinuousLinearMap.lsmul ℝ ℝ) volume) :
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun x => f x - g x) =
      (fun x =>
        (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
          (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) := by
  funext x
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
    mul_sub]
  exact integral_sub (hkf x) (hkg x)

private theorem H10Function.hasWeakPartialDerivOn_convolution_zeroExtension
    {d : ℕ} {U : Set (Vec d)} (u : H10Function U) (hU : MeasurableSet U)
    {a : ℝ} (ha : 0 < a) (i : Fin d) :
    HasWeakPartialDerivOn Set.univ i
      (scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] u.zeroExtension)
      (scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume]
          fun x => u.zeroExtensionGrad x i) := by
  let k : Vec d → ℝ :=
    scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a
  let un : ℕ → Vec d → ℝ := fun n =>
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u.approx n
  let gn : ℕ → Vec d → ℝ := fun n =>
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      fun x => (fderiv ℝ (u.approx n) x) (basisVec i)
  have hρ : IsConvexApproxKernel (unitConvexApproxKernel (d := d)) :=
    isConvexApproxKernel_unitConvexApproxKernel
  have hk_compact : HasCompactSupport k :=
    hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport ha
  have hk_smooth : ContDiff ℝ (⊤ : ℕ∞) k :=
    contDiff_scaledConvexApproxKernel hρ a
  have hk_cont : Continuous k := hk_smooth.continuous
  have hk_int : Integrable k volume := integrable_scaledConvexApproxKernel hρ ha
  have hk_loc : LocallyIntegrable k volume := hk_int.locallyIntegrable
  have hu_mem : MemLp u.zeroExtension 2 volume :=
    u.memLp_zeroExtension hU u.toH1Function.memL2
  have hgi_mem : MemLp (fun x => u.zeroExtensionGrad x i) 2 volume := by
    have hmem := u.gradMemLp_zeroExtensionGrad hU u.toH1Function.gradMemL2 i
    change MemLp (fun x => u.zeroExtensionGrad x i) 2
      (volume.restrict Set.univ) at hmem
    simpa only [Measure.restrict_univ] using hmem
  have hu_conv_mem : MemLp
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u.zeroExtension) 2 volume :=
    memLp_convolution_scaledConvexApproxKernel (by norm_num) (by norm_num) hu_mem ha
  have hgi_conv_mem : MemLp
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun x => u.zeroExtensionGrad x i) 2 volume :=
    memLp_convolution_scaledConvexApproxKernel (by norm_num) (by norm_num) hgi_mem ha
  have hu_n_mem : ∀ n, MemLp (u.approx n) 2 volume := by
    intro n
    exact (u.approx_smooth n).continuous.memLp_of_hasCompactSupport
      (u.approx_hasCompactSupport n)
  have hgn_base_mem : ∀ n, MemLp
      (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) 2 volume := by
    intro n
    have hcont : Continuous (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) :=
      ((u.approx_smooth n).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hsupp : HasCompactSupport
        (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) := by
      simpa only using (u.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact hcont.memLp_of_hasCompactSupport hsupp
  have hun_mem : ∀ n, MemLp (un n) 2 volume := by
    intro n
    exact memLp_convolution_scaledConvexApproxKernel (by norm_num) (by norm_num)
      (hu_n_mem n) ha
  have hgn_mem : ∀ n, MemLp (gn n) 2 volume := by
    intro n
    exact memLp_convolution_scaledConvexApproxKernel (by norm_num) (by norm_num)
      (hgn_base_mem n) ha
  have hweak_n : ∀ n, HasWeakPartialDerivOn Set.univ i (un n) (gn n) := by
    intro n
    have hu_n_loc : LocallyIntegrable (u.approx n) volume :=
      (hu_n_mem n).locallyIntegrable (by norm_num)
    have hconv_smooth : ContDiff ℝ 1 (un n) := by
      exact hk_compact.contDiff_convolution_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) (hk_smooth.of_le (by norm_num)) hu_n_loc
    have hclass : HasWeakPartialDerivOn Set.univ i (un n)
        (fun x => (fderiv ℝ (un n) x) (basisVec i)) :=
      HasWeakPartialDerivOn.of_contDiff hconv_smooth
    have hgrad_eq :
        (fun x => (fderiv ℝ (un n) x) (basisVec i)) = gn n := by
      funext x
      have hfd := (u.approx_hasCompactSupport n).hasFDerivAt_convolution_right
        (ContinuousLinearMap.lsmul ℝ ℝ) hk_loc
        ((u.approx_smooth n).of_le (by norm_num)) x
      change (fderiv ℝ
        (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u.approx n) x)
          (basisVec i) =
        (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          fun y => (fderiv ℝ (u.approx n) y) (basisVec i)) x
      rw [hfd.fderiv]
      exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hk_loc
        ((u.approx_hasCompactSupport n).fderiv ℝ)
        ((u.approx_smooth n).continuous_fderiv (by norm_num)) x (basisVec i)
    rw [← hgrad_eq]
    exact hclass
  have hu_tend : Filter.Tendsto
      (fun n => eLpNorm (fun x => u.approx n x - u.zeroExtension x) 2 volume)
      Filter.atTop (nhds 0) := by
    refine u.tendsto_approx.congr (fun n => ?_)
    rw [u.approx_sub_zeroExtension_eq_indicator_sub n,
      eLpNorm_indicator_eq_eLpNorm_restrict hU]
  have hgi_tend : Filter.Tendsto
      (fun n => eLpNorm
        (fun x =>
          (fderiv ℝ (u.approx n) x) (basisVec i) - u.zeroExtensionGrad x i)
        2 volume)
      Filter.atTop (nhds 0) := by
    refine (u.tendsto_approx_grad i).congr (fun n => ?_)
    rw [u.fderiv_approx_sub_zeroExtensionGrad_eq_indicator_sub n i,
      eLpNorm_indicator_eq_eLpNorm_restrict hU]
  have hun_tend : Filter.Tendsto
      (fun n => eLpNorm
        (fun x => un n x -
          (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u.zeroExtension) x)
        2 volume)
      Filter.atTop (nhds 0) := by
    have hconv_exists_n : ∀ n,
        ConvolutionExists k (u.approx n) (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      fun n => hk_compact.convolutionExists_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont
        ((hu_n_mem n).locallyIntegrable (by norm_num))
    have hconv_exists_u :
        ConvolutionExists k u.zeroExtension (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont
        (hu_mem.locallyIntegrable (by norm_num))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu_tend
    · intro n
      exact bot_le
    · intro n
      change eLpNorm
        (fun x =>
          (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u.approx n) x -
            (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u.zeroExtension) x)
        2 volume ≤ _
      rw [← convolution_sub_eq_sub_convolution (hconv_exists_n n) hconv_exists_u]
      exact young_convolution_nonneg_integral_one_of_aemeasurable (by norm_num) (by norm_num)
        (scaledConvexApproxKernel_nonneg hρ ha) hk_int
        (integral_scaledConvexApproxKernel hρ ha)
        (measurable_scaledConvexApproxKernel hρ.continuous a)
        ((hu_n_mem n).sub hu_mem).aemeasurable
  have hgn_tend : Filter.Tendsto
      (fun n => eLpNorm
        (fun x => gn n x -
          (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            fun y => u.zeroExtensionGrad y i) x)
        2 volume)
      Filter.atTop (nhds 0) := by
    have hconv_exists_n : ∀ n,
        ConvolutionExists k
          (fun x => (fderiv ℝ (u.approx n) x) (basisVec i))
          (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      fun n => hk_compact.convolutionExists_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont
        ((hgn_base_mem n).locallyIntegrable (by norm_num))
    have hconv_exists_g :
        ConvolutionExists k (fun x => u.zeroExtensionGrad x i)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont
        (hgi_mem.locallyIntegrable (by norm_num))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgi_tend
    · intro n
      exact bot_le
    · intro n
      change eLpNorm
        (fun x =>
          (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            fun y => (fderiv ℝ (u.approx n) y) (basisVec i)) x -
            (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
              fun y => u.zeroExtensionGrad y i) x)
        2 volume ≤ _
      rw [← convolution_sub_eq_sub_convolution (hconv_exists_n n) hconv_exists_g]
      exact young_convolution_nonneg_integral_one_of_aemeasurable (by norm_num) (by norm_num)
        (scaledConvexApproxKernel_nonneg hρ ha) hk_int
        (integral_scaledConvexApproxKernel hρ ha)
        (measurable_scaledConvexApproxKernel hρ.continuous a)
        ((hgn_base_mem n).sub hgi_mem).aemeasurable
  apply HasWeakPartialDerivOn.of_tendsto_eLpNorm_finiteLp FiniteLpExponent.two
    (by simpa only [FiniteLpExponent.two_exponent, Measure.restrict_univ] using hu_conv_mem)
    (by simpa only [FiniteLpExponent.two_exponent, Measure.restrict_univ] using hgi_conv_mem)
    (by simpa only [FiniteLpExponent.two_exponent, Measure.restrict_univ] using hun_mem)
    (by simpa only [FiniteLpExponent.two_exponent, Measure.restrict_univ] using hgn_mem)
    hweak_n
  · simpa only [FiniteLpExponent.two_exponent, Measure.restrict_univ] using hun_tend
  · simpa only [FiniteLpExponent.two_exponent, Measure.restrict_univ] using hgn_tend

private theorem H10Function.ae_eq_fderiv_convolution_zeroExtension_apply_basisVec
    {d : ℕ} {U : Set (Vec d)} (u : H10Function U) (hU : MeasurableSet U)
    {a : ℝ} (ha : 0 < a) (i : Fin d) :
    (fun x =>
      (fderiv ℝ
        (scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, volume] u.zeroExtension) x)
        (basisVec i)) =ᵐ[volume]
      fun x =>
        (scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, volume]
            fun y => u.zeroExtensionGrad y i) x := by
  let k : Vec d → ℝ :=
    scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a
  have hρ : IsConvexApproxKernel (unitConvexApproxKernel (d := d)) :=
    isConvexApproxKernel_unitConvexApproxKernel
  have hk_compact : HasCompactSupport k :=
    hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport ha
  have hk_smooth : ContDiff ℝ (⊤ : ℕ∞) k :=
    contDiff_scaledConvexApproxKernel hρ a
  have hu_mem : MemLp u.zeroExtension 2 volume :=
    u.memLp_zeroExtension hU u.toH1Function.memL2
  have hgi_mem : MemLp (fun x => u.zeroExtensionGrad x i) 2 volume := by
    have hmem := u.gradMemLp_zeroExtensionGrad hU u.toH1Function.gradMemL2 i
    change MemLp (fun x => u.zeroExtensionGrad x i) 2
      (volume.restrict Set.univ) at hmem
    simpa only [Measure.restrict_univ] using hmem
  have hsmooth : ContDiff ℝ 1
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u.zeroExtension) :=
    hk_compact.contDiff_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (hk_smooth.of_le (by norm_num))
      (hu_mem.locallyIntegrable (by norm_num))
  have hclass : HasWeakPartialDerivOn Set.univ i
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u.zeroExtension)
      (fun x =>
        (fderiv ℝ
          (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u.zeroExtension) x)
          (basisVec i)) :=
    HasWeakPartialDerivOn.of_contDiff hsmooth
  have hrough := u.hasWeakPartialDerivOn_convolution_zeroExtension hU ha i
  have hclass_loc : LocallyIntegrable
      (fun x =>
        (fderiv ℝ
          (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u.zeroExtension) x)
          (basisVec i)) volume :=
    ((hsmooth.continuous_fderiv (by norm_num)).clm_apply continuous_const).locallyIntegrable
  have hrough_loc : LocallyIntegrable
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun x => u.zeroExtensionGrad x i) volume := by
    exact (memLp_convolution_scaledConvexApproxKernel (by norm_num) (by norm_num)
      hgi_mem ha).locallyIntegrable (by norm_num)
  have hae := HasWeakPartialDerivOn.ae_eq isOpen_univ
    (hclass_loc.locallyIntegrableOn Set.univ)
    (hrough_loc.locallyIntegrableOn Set.univ) hclass hrough
  simpa only [k, Measure.restrict_univ] using hae

namespace H10Function

/-- The classical coordinate derivative of the inward mollification of an
`H¹₀` zero extension is the outward-affine pullback of the mollified weak
gradient, including the exact chain-rule factor `1 + ε`. -/
theorem ae_eq_fderiv_inwardMollification_unit_apply_basisVec
    {d : ℕ} {U : Set (Vec d)} (u : H10Function U) (hU : MeasurableSet U)
    {x0 : Vec d} {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (i : Fin d) :
    (fun x =>
      (fderiv ℝ
        (inwardMollification (unitConvexApproxKernel (d := d))
          u.zeroExtension x0 r ε) x) (basisVec i)) =ᵐ[volume]
      fun x => (1 + ε) *
        (scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) (ε * r) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, volume]
            fun y => u.zeroExtensionGrad y i) (globalAffineExpansion x0 ε x) := by
  let k : Vec d → ℝ :=
    scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) (ε * r)
  let v : Vec d → ℝ :=
    k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u.zeroExtension
  have hscale : 0 < ε * r := mul_pos hε hr
  have hρ : IsConvexApproxKernel (unitConvexApproxKernel (d := d)) :=
    isConvexApproxKernel_unitConvexApproxKernel
  have hk_compact : HasCompactSupport k :=
    hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport hscale
  have hk_smooth : ContDiff ℝ (⊤ : ℕ∞) k :=
    contDiff_scaledConvexApproxKernel hρ (ε * r)
  have hu_mem : MemLp u.zeroExtension 2 volume :=
    u.memLp_zeroExtension hU u.toH1Function.memL2
  have hv_smooth : ContDiff ℝ 1 v :=
    hk_compact.contDiff_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (hk_smooth.of_le (by norm_num))
      (hu_mem.locallyIntegrable (by norm_num))
  have hconv := u.ae_eq_fderiv_convolution_zeroExtension_apply_basisVec hU hscale i
  have hconv_comp :=
    Filter.EventuallyEq.comp_globalAffineExpansion hconv x0 hε.le
  change (fun x =>
    (fderiv ℝ (v ∘ globalAffineExpansion x0 ε) x) (basisVec i)) =ᵐ[volume]
      fun x => (1 + ε) *
        (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          fun y => u.zeroExtensionGrad y i) (globalAffineExpansion x0 ε x)
  filter_upwards [hconv_comp] with x hx
  have haff : HasFDerivAt (globalAffineExpansion x0 ε)
      ((1 + ε) • ContinuousLinearMap.id ℝ (Vec d)) x := by
    simpa [globalAffineExpansion, sub_eq_add_neg] using
      (((1 + ε) • ContinuousLinearMap.id ℝ (Vec d)).hasFDerivAt.add_const
        (-ε • x0))
  have hv_deriv : HasFDerivAt v (fderiv ℝ v (globalAffineExpansion x0 ε x))
      (globalAffineExpansion x0 ε x) :=
    hv_smooth.differentiable (by simp) |>.differentiableAt.hasFDerivAt
  have hcomp := hv_deriv.comp x haff
  have hpoint :
      (fderiv ℝ (v ∘ globalAffineExpansion x0 ε) x) (basisVec i) =
        (1 + ε) * (fderiv ℝ v (globalAffineExpansion x0 ε x)) (basisVec i) := by
    rw [hcomp.fderiv]
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  have hx' :
      (fderiv ℝ v (globalAffineExpansion x0 ε x)) (basisVec i) =
        (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          fun y => u.zeroExtensionGrad y i) (globalAffineExpansion x0 ε x) := by
    simpa only [Function.comp_apply, v, k] using hx
  rw [hpoint, hx']

end H10Function

end

end Homogenization
