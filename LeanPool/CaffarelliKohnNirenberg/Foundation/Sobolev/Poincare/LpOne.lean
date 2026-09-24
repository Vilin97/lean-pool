/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.Lp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Lp One

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

namespace CKN

private theorem integrableOn_norm_fderiv_mul_rieszKernel
    {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {u : Vec d → ℝ}
    (huDiff : ContDiff ℝ 1 u) :
    MeasureTheory.IntegrableOn
      (fun z : Vec d × Vec d => ‖fderiv ℝ u z.2‖ * rieszKernel z.1 z.2)
      (U ×ˢ U) (MeasureTheory.volume.prod MeasureTheory.volume) := by
  have hkernel :
      MeasureTheory.IntegrableOn
        (fun z : Vec d × Vec d => rieszKernel z.1 z.2)
        (U ×ˢ U) (MeasureTheory.volume.prod MeasureTheory.volume) :=
    integrableOn_prod_rieszKernel_of_isSobolevRegularDomain
      hU.isSobolevRegularDomain
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := huDiff.of_le (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hmult_cont :
      ContinuousOn (fun z : Vec d × Vec d => ‖fderiv ℝ u z.2‖)
        (closure (U ×ˢ U)) :=
    (continuous_norm.comp (hfderiv_cont.comp continuous_snd)).continuousOn
  have hcompact : IsCompact (closure (U ×ˢ U)) := by
    have hprodcompact :=
      hU.isBoundedDomain.isBounded.isCompact_closure.prod
        hU.isBoundedDomain.isBounded.isCompact_closure
    apply hprodcompact.of_isClosed_subset isClosed_closure
    exact closure_minimal
      (fun z hz => ⟨subset_closure hz.1, subset_closure hz.2⟩) hprodcompact.isClosed
  have hsub : U ×ˢ U ⊆ closure (U ×ˢ U) := subset_closure
  simpa [mul_comm] using
    hkernel.mul_continuousOn_of_subset hmult_cont
      (hU.measurableSet.prod hU.measurableSet) hcompact hsub

private theorem integral_norm_sub_integralAverage_le_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) {u : Vec d → ℝ}
    (hu : MeasureTheory.IntegrableOn u U)
    (huDiff : ContDiff ℝ 1 u)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    ∫ x in U, ‖u x - integralAverage U u‖ ∂MeasureTheory.volume ≤
      (((MeasureTheory.volume U).toReal⁻¹ *
          (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ))) *
        ((d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
          (4 * Classical.choose hU.isBoundedDomain))) *
        ∫ y in U, ‖fderiv ℝ u y‖ ∂MeasureTheory.volume := by
  let μU : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict U
  let B : ℝ :=
    (MeasureTheory.volume U).toReal⁻¹ *
      (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ))
  let M : ℝ :=
    (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
      (4 * Classical.choose hU.isBoundedDomain)
  let g : Vec d → ℝ := fun y => ‖fderiv ℝ u y‖
  have hB_nonneg : 0 ≤ B := by
    have hchoose_pos : 0 < Classical.choose hU.isBoundedDomain :=
      (Classical.choose_spec hU.isBoundedDomain).1
    have hd_pos : 0 < (d : ℝ) := by
      exact_mod_cast (NeZero.pos d)
    dsimp [B]
    positivity
  have hM_nonneg : 0 ≤ M := by
    have hchoose_pos : 0 < Classical.choose hU.isBoundedDomain :=
      (Classical.choose_spec hU.isBoundedDomain).1
    have hd_pos : 0 < (d : ℝ) := by
      exact_mod_cast (NeZero.pos d)
    dsimp [M]
    positivity
  have hg_nonneg : ∀ y, 0 ≤ g y := fun y => norm_nonneg _
  have hfderiv_cont : Continuous (fderiv ℝ u) := by
    have h1 : ContDiff ℝ 1 u := huDiff.of_le (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hg_int : MeasureTheory.IntegrableOn g U MeasureTheory.volume := by
    have hcompact : IsCompact (closure U) :=
      hU.isBoundedDomain.isBounded.isCompact_closure
    exact ((continuous_norm.comp hfderiv_cont).continuousOn.integrableOn_compact
      hcompact).mono_set subset_closure
  have hprod :
      MeasureTheory.Integrable
        (fun z : Vec d × Vec d => g z.2 * rieszKernel z.1 z.2) (μU.prod μU) := by
    have hprod' := integrableOn_norm_fderiv_mul_rieszKernel hU huDiff
    simpa [g, μU, MeasureTheory.IntegrableOn, MeasureTheory.Measure.prod_restrict] using hprod'
  have hleft_int :
      MeasureTheory.Integrable
        (fun x => ‖u x - integralAverage U u‖) μU := by
    have hcont : Continuous (fun x => ‖u x - integralAverage U u‖) :=
      continuous_norm.comp (huDiff.continuous.sub continuous_const)
    have hcompact : IsCompact (closure U) :=
      hU.isBoundedDomain.isBounded.isCompact_closure
    simpa [μU, MeasureTheory.IntegrableOn] using
      (hcont.continuousOn.integrableOn_compact hcompact).mono_set subset_closure
  have hinner_int :
      MeasureTheory.Integrable
        (fun x => ∫ y, g y * rieszKernel x y ∂μU) μU :=
    hprod.integral_prod_left
  have hright_int :
      MeasureTheory.Integrable
        (fun x => B * ∫ y, g y * rieszKernel x y ∂μU) μU :=
    hinner_int.const_mul B
  have hpointwise :
      (fun x => ‖u x - integralAverage U u‖) ≤ᵐ[μU]
        (fun x => B * ∫ y, g y * rieszKernel x y ∂μU) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU.measurableSet] with x hx
    have hbase :=
      norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_rieszKernel_of_isOpenBoundedConvexDomain
        hU hu huDiff hx hvol
    have hinner_nonneg : 0 ≤ ∫ y, g y * rieszKernel x y ∂μU := by
      exact MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall
          (fun y => mul_nonneg (hg_nonneg y) (rieszKernel_nonneg x y)))
    simpa [B, g, μU, mul_assoc] using hbase
  have hleft_le :
      ∫ x, ‖u x - integralAverage U u‖ ∂μU ≤
        ∫ x, B * ∫ y, g y * rieszKernel x y ∂μU ∂μU :=
    MeasureTheory.integral_mono_ae hleft_int hright_int hpointwise
  have hswap :
      (∫ x, ∫ y, g y * rieszKernel x y ∂μU ∂μU) =
        ∫ y, ∫ x, g y * rieszKernel x y ∂μU ∂μU :=
    MeasureTheory.integral_integral_swap hprod
  have hkernel_bound :
      ∀ᵐ y ∂μU,
        ∫ x, rieszKernel x y ∂μU ≤ M := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU.measurableSet] with y hy
    simpa [M, μU, MeasureTheory.IntegrableOn] using
      hU.isBoundedDomain.integral_rieszKernel_right_le hy
  have hinner_prod_int :
      MeasureTheory.Integrable
        (fun y => ∫ x, g y * rieszKernel x y ∂μU) μU :=
    hprod.integral_prod_right
  have houter_bound_int :
      MeasureTheory.Integrable (fun y => M * g y) μU := by
    simpa [μU, MeasureTheory.IntegrableOn, mul_comm] using hg_int.integrable.const_mul M
  have hinner_mono :
      (fun y => ∫ x, g y * rieszKernel x y ∂μU) ≤ᵐ[μU]
        (fun y => M * g y) := by
    filter_upwards [hkernel_bound] with y hy
    rw [MeasureTheory.integral_const_mul]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hy (hg_nonneg y)
  have houter_le :
      (∫ y, ∫ x, g y * rieszKernel x y ∂μU ∂μU) ≤
        ∫ y, M * g y ∂μU :=
    MeasureTheory.integral_mono_ae hinner_prod_int houter_bound_int hinner_mono
  have hmain :
      ∫ x, B * ∫ y, g y * rieszKernel x y ∂μU ∂μU ≤ B * M * ∫ y, g y ∂μU := by
    rw [MeasureTheory.integral_const_mul, hswap]
    calc
      B * (∫ y, ∫ x, g y * rieszKernel x y ∂μU ∂μU) ≤
          B * ∫ y, M * g y ∂μU := mul_le_mul_of_nonneg_left houter_le hB_nonneg
      _ = B * M * ∫ y, g y ∂μU := by
        rw [MeasureTheory.integral_const_mul]
        ring
  calc
    ∫ x in U, ‖u x - integralAverage U u‖ ∂MeasureTheory.volume =
        ∫ x, ‖u x - integralAverage U u‖ ∂μU := rfl
    _ ≤ ∫ x, B * ∫ y, g y * rieszKernel x y ∂μU ∂μU := hleft_le
    _ ≤ B * M * ∫ y, g y ∂μU := hmain
    _ = (B * M) * ∫ y in U, ‖fderiv ℝ u y‖ ∂MeasureTheory.volume := by
      simp [g, B, M, μU]

theorem integral_norm_sub_integralAverage_le_bound_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) {u : Vec d → ℝ}
    (hu : MeasureTheory.IntegrableOn u U)
    (huDiff : ContDiff ℝ 1 u)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    ∫ x in U, ‖u x - integralAverage U u‖ ∂MeasureTheory.volume ≤
      ((MeasureTheory.volume U).toReal⁻¹ *
          (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ))) *
        ((d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
          (4 * Classical.choose hU.isBoundedDomain)) *
        ∫ y in U, ‖fderiv ℝ u y‖ ∂MeasureTheory.volume :=
  integral_norm_sub_integralAverage_le_of_isOpenBoundedConvexDomain
    hU hu huDiff hvol

end CKN
