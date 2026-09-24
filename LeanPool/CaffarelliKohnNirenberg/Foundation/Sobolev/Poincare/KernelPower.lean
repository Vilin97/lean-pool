/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.KernelTime

/-!
# Kernel Power

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

namespace CKN

open MeasureTheory Metric
open scoped ENNReal NNReal Pointwise

/-!
# Weighted and Riesz power-mean bounds for the Poincare kernel integrand

First: a Hölder-type weighted power-mean inequality used to convert the
interval integral into an `L^p` bound.
Second: the final convex-domain Riesz-kernel bounds used by the Poincare
estimates.
-/

section WeightedPowerMean

theorem weighted_power_mean_setIntegral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s)
    {p : ℝ} (hp : 1 < p)
    {f w : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hw : ∀ x, 0 ≤ w x)
    (hf_meas : AEMeasurable f (μ.restrict s))
    (hwi : MeasureTheory.IntegrableOn w s μ)
    (hfpwi : MeasureTheory.IntegrableOn (fun x => (f x) ^ p * w x) s μ) :
    (∫ x in s, f x * w x ∂μ) ^ p ≤
      (∫ x in s, w x ∂μ) ^ (p - 1) * ∫ x in s, (f x) ^ p * w x ∂μ := by
  set μs : Measure α := μ.restrict s
  set ρ : α → ℝ≥0∞ := fun x => ENNReal.ofReal (w x)
  set ν : Measure α := μs.withDensity ρ
  let q : ℝ := p / (p - 1)
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hpq : p.HolderConjugate q := by
    dsimp [q]
    exact Real.HolderConjugate.conjExponent hp
  have hρ_aemeas : AEMeasurable ρ μs := by
    simpa [ρ, μs] using hwi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hρ_lt_top : ∀ᵐ x ∂μs, ρ x < ⊤ := by
    filter_upwards with x
    simp [ρ]
  have hρ_lint_ne_top : ∫⁻ x, ρ x ∂μs ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hwi (ae_of_all _ fun x => hw x)]
    simp
  have : MeasureTheory.IsFiniteMeasure ν := MeasureTheory.isFiniteMeasure_withDensity hρ_lint_ne_top
  have hf_meas_ν : AEMeasurable f ν := by
    exact hf_meas.mono_ac (MeasureTheory.withDensity_absolutelyContinuous _ _)
  have hpow_int_base : MeasureTheory.Integrable (fun x => (ρ x).toReal • (‖f x‖ ^ p)) μs := by
    refine hfpwi.congr ?_
    filter_upwards with x
    rw [smul_eq_mul, ENNReal.toReal_ofReal (hw x), Real.norm_of_nonneg (hf x)]
    ring
  have hpow_int : MeasureTheory.Integrable (fun x => ‖f x‖ ^ p) ν := by
    rw [show ν = μs.withDensity ρ by rfl]
    exact
      (MeasureTheory.integrable_withDensity_iff_integrable_smul₀'
        (μ := μs) hρ_aemeas hρ_lt_top).2 hpow_int_base
  have hf_mem : MeasureTheory.MemLp f (ENNReal.ofReal p) ν := by
    exact
      (MeasureTheory.integrable_norm_rpow_iff
        (μ := ν) hf_meas_ν.aestronglyMeasurable
        (by simp [hp_pos]) ENNReal.ofReal_ne_top).1 <| by
          simpa [ENNReal.toReal_ofReal hp_nonneg] using hpow_int
  have h_one_mem : MeasureTheory.MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal q) ν := by
    simpa [q] using
      (MeasureTheory.memLp_const (μ := ν) (p := ENNReal.ofReal q) (1 : ℝ))
  have hHolder :
      ∫ x, f x * (1 : ℝ) ∂ν ≤
        (∫ x, (f x) ^ p ∂ν) ^ (1 / p : ℝ) *
          (∫ x, (1 : ℝ) ^ q ∂ν) ^ (1 / q : ℝ) := by
    exact MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := ν) hpq
      (ae_of_all _ fun x => hf x)
      (ae_of_all _ fun _ => by positivity)
      hf_mem h_one_mem
  have hleft_eq : ∫ x, f x ∂ν = ∫ x in s, f x * w x ∂μ := by
    rw [show ν = μs.withDensity ρ by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀
      (μ := μs) hρ_aemeas hρ_lt_top]
    simp [μs, ρ, smul_eq_mul, ENNReal.toReal_ofReal, hw, mul_comm]
  have hpow_eq : ∫ x, (f x) ^ p ∂ν = ∫ x in s, (f x) ^ p * w x ∂μ := by
    rw [show ν = μs.withDensity ρ by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀
      (μ := μs) hρ_aemeas hρ_lt_top]
    simp [μs, ρ, smul_eq_mul, ENNReal.toReal_ofReal, hw, mul_comm]
  have hone_eq : ∫ x, (1 : ℝ) ^ q ∂ν = ∫ x in s, w x ∂μ := by
    rw [show ν = μs.withDensity ρ by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀
      (μ := μs) hρ_aemeas hρ_lt_top]
    simp [μs, ρ, q, smul_eq_mul, ENNReal.toReal_ofReal, hw]
  set A := ∫ x in s, f x * w x ∂μ
  set I := ∫ x in s, (f x) ^ p * w x ∂μ
  set W := ∫ x in s, w x ∂μ
  have hA_nonneg : 0 ≤ A := by
    exact MeasureTheory.setIntegral_nonneg hs (fun x _ => mul_nonneg (hf x) (hw x))
  have hI_nonneg : 0 ≤ I := by
    exact MeasureTheory.setIntegral_nonneg hs (fun x _ =>
      mul_nonneg (Real.rpow_nonneg (hf x) _) (hw x))
  have hW_nonneg : 0 ≤ W := by
    exact MeasureTheory.setIntegral_nonneg hs (fun x _ => hw x)
  by_cases hW_zero : ∫ x in s, w x ∂μ = 0
  · have hfw_nonneg : 0 ≤ ∫ x in s, f x * w x ∂μ :=
      MeasureTheory.setIntegral_nonneg hs (fun x _ => mul_nonneg (hf x) (hw x))
    have hfw_zero : ∫ x in s, f x * w x ∂μ ≤ 0 := by
      by_cases hfwi : MeasureTheory.IntegrableOn (fun x => f x * w x) s μ
      · have hw_ae : w =ᵐ[μ.restrict s] 0 := by
          rwa [MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae
            (MeasureTheory.ae_restrict_of_ae (ae_of_all _ (fun x => hw x))) hwi] at hW_zero
        have : (fun x => f x * w x) =ᵐ[μ.restrict s] 0 :=
          hw_ae.mono (fun x hx => by simp [hx])
        rw [MeasureTheory.integral_congr_ae this]
        simp
      · simp [MeasureTheory.integral_undef hfwi]
    have h0 := le_antisymm hfw_zero hfw_nonneg
    simpa [A, I, W, h0, hW_zero] using
      (show A ^ p ≤ W ^ (p - 1) * I by
        simp [A, I, W, h0, hW_zero,
          mul_nonneg (Real.rpow_nonneg (le_refl _) _)
            (MeasureTheory.setIntegral_nonneg hs
              (fun x _ => mul_nonneg (Real.rpow_nonneg (hf x) _) (hw x))),
          Real.zero_rpow (ne_of_gt hp_pos)])
  · have hHolder' : A ≤ W ^ (1 / q : ℝ) * I ^ (1 / p : ℝ) := by
      have hνreal_eq : ν.real Set.univ = W := by
        calc
          ν.real Set.univ = ∫ x, (1 : ℝ) ∂ν := by
            rw [integral_const]
            simp [Measure.real]
          _ = ∫ x, (1 : ℝ) ^ q ∂ν := by simp [q]
          _ = W := hone_eq
      simpa [A, I, W, hleft_eq, hpow_eq, hνreal_eq, one_div, mul_comm, mul_left_comm, mul_assoc]
        using hHolder
    have hpow :=
      Real.rpow_le_rpow hA_nonneg hHolder' (le_of_lt hp_pos)
    have hWroot_nonneg : 0 ≤ W ^ (1 / q : ℝ) := Real.rpow_nonneg hW_nonneg _
    have hIroot_nonneg : 0 ≤ I ^ (1 / p : ℝ) := Real.rpow_nonneg hI_nonneg _
    have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
    have hrhs :
        (W ^ (1 / q : ℝ) * I ^ (1 / p : ℝ)) ^ p = W ^ (p - 1) * I := by
      rw [Real.mul_rpow hWroot_nonneg hIroot_nonneg]
      rw [← Real.rpow_mul hW_nonneg, ← Real.rpow_mul hI_nonneg]
      have hWq : (1 / q : ℝ) * p = p - 1 := by
        dsimp [q]
        field_simp [hp_ne_zero, show p - 1 ≠ 0 by exact ne_of_gt (sub_pos.mpr hp)]
      have hIp : (1 / p : ℝ) * p = 1 := by
        field_simp [hp_ne_zero]
      rw [hWq, hIp, Real.rpow_one]
    simpa [A, I, W] using hpow.trans_eq hrhs

end WeightedPowerMean

section RieszPowerMean

variable {d : ℕ} [NeZero d]

/-- Cache `Nontrivial (Vec d)` once per section. -/
instance instNontrivialVecRiesz : Nontrivial (Vec d) := inferInstance

theorem integral_mul_rieszKernel_rpow_le_of_isSobolevRegularDomain
    {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    {p : ℝ} (hp : 1 < p)
    {g : Vec d → ℝ} (hg_nonneg : ∀ y, 0 ≤ g y)
    (hg_meas : AEMeasurable g (MeasureTheory.volume.restrict U))
    {x : Vec d} (hx : x ∈ U)
    (hgpK_int :
      MeasureTheory.IntegrableOn
        (fun y => (g y) ^ p * rieszKernel x y) U MeasureTheory.volume) :
    (∫ y in U, g y * rieszKernel x y ∂MeasureTheory.volume) ^ p ≤
      (∫ y in U, rieszKernel x y ∂MeasureTheory.volume) ^ (p - 1) *
        ∫ y in U, (g y) ^ p * rieszKernel x y ∂MeasureTheory.volume := by
  exact weighted_power_mean_setIntegral hU.measurableSet hp
    hg_nonneg (fun y => rieszKernel_nonneg x y) hg_meas
    (hU.isBoundedDomain.integrableOn_rieszKernel hx) hgpK_int

theorem integral_mul_rieszKernel_rpow_le_bound_of_isSobolevRegularDomain
    {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    {p : ℝ} (hp : 1 < p)
    {g : Vec d → ℝ} (hg_nonneg : ∀ y, 0 ≤ g y)
    (hg_meas : AEMeasurable g (MeasureTheory.volume.restrict U))
    {x : Vec d} (hx : x ∈ U)
    (hgpK_int :
      MeasureTheory.IntegrableOn
        (fun y => (g y) ^ p * rieszKernel x y) U MeasureTheory.volume) :
    (∫ y in U, g y * rieszKernel x y ∂MeasureTheory.volume) ^ p ≤
      (((d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
          (4 * Classical.choose hU.isBoundedDomain)) ^ (p - 1)) *
        ∫ y in U, (g y) ^ p * rieszKernel x y ∂MeasureTheory.volume := by
  set W := ∫ y in U, rieszKernel x y ∂MeasureTheory.volume
  set I := ∫ y in U, (g y) ^ p * rieszKernel x y ∂MeasureTheory.volume
  set M : ℝ :=
    (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
      (4 * Classical.choose hU.isBoundedDomain)
  have hW_nonneg : 0 ≤ W := by
    exact MeasureTheory.setIntegral_nonneg hU.measurableSet
      (fun y _ => rieszKernel_nonneg x y)
  have hW_le_M : W ≤ M := by
    simpa [W, M] using hU.isBoundedDomain.integral_rieszKernel_le (x := x) hx
  have hI_nonneg : 0 ≤ I := by
    exact MeasureTheory.setIntegral_nonneg hU.measurableSet
      (fun y _ => mul_nonneg (Real.rpow_nonneg (hg_nonneg y) _) (rieszKernel_nonneg x y))
  calc
    (∫ y in U, g y * rieszKernel x y ∂MeasureTheory.volume) ^ p
        ≤ W ^ (p - 1) * I := by
            simpa [W, I] using
              integral_mul_rieszKernel_rpow_le_of_isSobolevRegularDomain
                hU hp hg_nonneg hg_meas hx hgpK_int
    _ ≤ M ^ (p - 1) * I := by
          apply mul_le_mul_of_nonneg_right ?_ hI_nonneg
          exact Real.rpow_le_rpow hW_nonneg hW_le_M (sub_nonneg.mpr (le_of_lt hp))
    _ = (((d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
          (4 * Classical.choose hU.isBoundedDomain)) ^ (p - 1)) *
        ∫ y in U, (g y) ^ p * rieszKernel x y ∂MeasureTheory.volume := by
          simp [I, M]

theorem integrable_rpow_integral_mul_rieszKernel_of_isSobolevRegularDomain
    {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    {p : ℝ} (hp : 1 < p)
    {g : Vec d → ℝ} (hg_nonneg : ∀ y, 0 ≤ g y)
    (hg_meas : AEMeasurable g (MeasureTheory.volume.restrict U))
    (hgK_prod_int :
      MeasureTheory.IntegrableOn
        (fun z : Vec d × Vec d => g z.2 * rieszKernel z.1 z.2)
        (U ×ˢ U) (MeasureTheory.volume.prod MeasureTheory.volume))
    (hgpK_prod_int :
      MeasureTheory.IntegrableOn
        (fun z : Vec d × Vec d => (g z.2) ^ p * rieszKernel z.1 z.2)
        (U ×ˢ U) (MeasureTheory.volume.prod MeasureTheory.volume)) :
    MeasureTheory.Integrable
      (fun x => (∫ y in U, g y * rieszKernel x y ∂MeasureTheory.volume) ^ p)
      (MeasureTheory.volume.restrict U) := by
  let μU : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict U
  set M : ℝ :=
    (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
      (4 * Classical.choose hU.isBoundedDomain)
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hchoose_pos : 0 < Classical.choose hU.isBoundedDomain :=
    (Classical.choose_spec hU.isBoundedDomain).1
  have hM_nonneg : 0 ≤ M := by
    have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
    have hball_nonneg :
        0 ≤ (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal :=
      ENNReal.toReal_nonneg
    have hchoose_nonneg : 0 ≤ (4 * Classical.choose hU.isBoundedDomain : ℝ) := by
      exact mul_nonneg (by norm_num) hchoose_pos.le
    dsimp [M]
    exact mul_nonneg (mul_nonneg hd_nonneg hball_nonneg) hchoose_nonneg
  have hgK_prod_int' :
      MeasureTheory.Integrable
        (fun z : Vec d × Vec d => g z.2 * rieszKernel z.1 z.2)
        (μU.prod μU) := by
    simpa [μU, MeasureTheory.IntegrableOn, MeasureTheory.Measure.prod_restrict] using hgK_prod_int
  have hgpK_prod_int' :
      MeasureTheory.Integrable
        (fun z : Vec d × Vec d => (g z.2) ^ p * rieszKernel z.1 z.2)
        (μU.prod μU) := by
    simpa [μU, MeasureTheory.IntegrableOn, MeasureTheory.Measure.prod_restrict] using hgpK_prod_int
  have hright_int :
      MeasureTheory.Integrable
        (fun x => M ^ (p - 1) * ∫ y, (g y) ^ p * rieszKernel x y ∂μU)
        μU := by
    simpa [M] using
      (hgpK_prod_int'.integral_prod_left.const_mul (M ^ (p - 1)))
  have hpointwise :
      (fun x => (∫ y, g y * rieszKernel x y ∂μU) ^ p) ≤ᵐ[μU]
        (fun x => M ^ (p - 1) * ∫ y, (g y) ^ p * rieszKernel x y ∂μU) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU.measurableSet, hgpK_prod_int'.prod_right_ae] with
      x hx hxgpK
    simpa [μU, M, MeasureTheory.IntegrableOn] using
      (integral_mul_rieszKernel_rpow_le_bound_of_isSobolevRegularDomain
        hU hp hg_nonneg hg_meas hx hxgpK)
  have hinner_meas :
      AEStronglyMeasurable
        (fun x => ∫ y, g y * rieszKernel x y ∂μU)
        μU :=
    hgK_prod_int'.aestronglyMeasurable.integral_prod_right'
  have hleft_ae :
      AEStronglyMeasurable
        (fun x => (∫ y, g y * rieszKernel x y ∂μU) ^ p)
        μU := by
    let hpow_meas : Measurable (fun t : ℝ => t ^ p) :=
      (continuous_id.rpow_const fun _ => Or.inr hp_nonneg).measurable
    exact (hpow_meas.comp_aemeasurable hinner_meas.aemeasurable).aestronglyMeasurable
  have hleft_bound :
      ∀ᵐ x ∂μU, ‖(∫ y, g y * rieszKernel x y ∂μU) ^ p‖ ≤
        M ^ (p - 1) * ∫ y, (g y) ^ p * rieszKernel x y ∂μU := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU.measurableSet, hgK_prod_int'.prod_right_ae,
      hpointwise] with x hx hxgK hxbound
    have hinner_nonneg : 0 ≤ ∫ y, g y * rieszKernel x y ∂μU := by
      exact MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall
          (fun y => mul_nonneg (hg_nonneg y) (rieszKernel_nonneg x y)))
    have hpow_nonneg : 0 ≤ (∫ y, g y * rieszKernel x y ∂μU) ^ p :=
      Real.rpow_nonneg hinner_nonneg _
    simpa [Real.norm_of_nonneg hpow_nonneg] using hxbound
  exact hright_int.mono' hleft_ae hleft_bound

theorem integral_rpow_integral_mul_rieszKernel_le_bound_of_isSobolevRegularDomain
    {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)
    {p : ℝ} (hp : 1 < p)
    {g : Vec d → ℝ} (hg_nonneg : ∀ y, 0 ≤ g y)
    (hg_meas : AEMeasurable g (MeasureTheory.volume.restrict U))
    (hgK_prod_int :
      MeasureTheory.IntegrableOn
        (fun z : Vec d × Vec d => g z.2 * rieszKernel z.1 z.2)
        (U ×ˢ U) (MeasureTheory.volume.prod MeasureTheory.volume))
    (hgp_int :
      MeasureTheory.IntegrableOn
        (fun y => (g y) ^ p) U MeasureTheory.volume)
    (hgpK_prod_int :
      MeasureTheory.IntegrableOn
        (fun z : Vec d × Vec d => (g z.2) ^ p * rieszKernel z.1 z.2)
        (U ×ˢ U) (MeasureTheory.volume.prod MeasureTheory.volume)) :
    ∫ x in U, (∫ y in U, g y * rieszKernel x y ∂MeasureTheory.volume) ^ p ∂MeasureTheory.volume ≤
      (((d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
          (4 * Classical.choose hU.isBoundedDomain)) ^ p) *
        ∫ y in U, (g y) ^ p ∂MeasureTheory.volume := by
  let μU : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict U
  set M : ℝ :=
    (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
      (4 * Classical.choose hU.isBoundedDomain)
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hchoose_pos : 0 < Classical.choose hU.isBoundedDomain :=
    (Classical.choose_spec hU.isBoundedDomain).1
  have hM_nonneg : 0 ≤ M := by
    have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
    have hball_nonneg :
        0 ≤ (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal :=
      ENNReal.toReal_nonneg
    have hchoose_nonneg : 0 ≤ (4 * Classical.choose hU.isBoundedDomain : ℝ) := by
      exact mul_nonneg (by norm_num) hchoose_pos.le
    dsimp [M]
    exact mul_nonneg (mul_nonneg hd_nonneg hball_nonneg) hchoose_nonneg
  have hgK_prod_int' :
      MeasureTheory.Integrable
        (fun z : Vec d × Vec d => g z.2 * rieszKernel z.1 z.2)
        (μU.prod μU) := by
    simpa [μU, MeasureTheory.IntegrableOn, MeasureTheory.Measure.prod_restrict] using hgK_prod_int
  have hgpK_prod_int' :
      MeasureTheory.Integrable
        (fun z : Vec d × Vec d => (g z.2) ^ p * rieszKernel z.1 z.2)
        (μU.prod μU) := by
    simpa [μU, MeasureTheory.IntegrableOn, MeasureTheory.Measure.prod_restrict] using hgpK_prod_int
  have hright_int :
      MeasureTheory.Integrable
        (fun x => M ^ (p - 1) * ∫ y, (g y) ^ p * rieszKernel x y ∂μU)
        μU := by
    simpa [M] using
      (hgpK_prod_int'.integral_prod_left.const_mul (M ^ (p - 1)))
  have hpointwise :
      (fun x => (∫ y, g y * rieszKernel x y ∂μU) ^ p) ≤ᵐ[μU]
        (fun x => M ^ (p - 1) * ∫ y, (g y) ^ p * rieszKernel x y ∂μU) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU.measurableSet, hgpK_prod_int'.prod_right_ae] with
      x hx hxgpK
    simpa [μU, M, MeasureTheory.IntegrableOn] using
      (integral_mul_rieszKernel_rpow_le_bound_of_isSobolevRegularDomain
        hU hp hg_nonneg hg_meas hx hxgpK)
  have hinner_meas :
      AEStronglyMeasurable
        (fun x => ∫ y, g y * rieszKernel x y ∂μU)
        μU :=
    hgK_prod_int'.aestronglyMeasurable.integral_prod_right'
  have hleft_ae :
      AEStronglyMeasurable
        (fun x => (∫ y, g y * rieszKernel x y ∂μU) ^ p)
        μU := by
    let hpow_meas : Measurable (fun t : ℝ => t ^ p) :=
      (continuous_id.rpow_const fun _ => Or.inr hp_nonneg).measurable
    exact (hpow_meas.comp_aemeasurable hinner_meas.aemeasurable).aestronglyMeasurable
  have hleft_bound :
      ∀ᵐ x ∂μU, ‖(∫ y, g y * rieszKernel x y ∂μU) ^ p‖ ≤
        M ^ (p - 1) * ∫ y, (g y) ^ p * rieszKernel x y ∂μU := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU.measurableSet, hgK_prod_int'.prod_right_ae,
      hpointwise] with x hx hxgK hxbound
    have hinner_nonneg : 0 ≤ ∫ y, g y * rieszKernel x y ∂μU := by
      exact MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall
          (fun y => mul_nonneg (hg_nonneg y) (rieszKernel_nonneg x y)))
    have hpow_nonneg : 0 ≤ (∫ y, g y * rieszKernel x y ∂μU) ^ p :=
      Real.rpow_nonneg hinner_nonneg _
    simpa [Real.norm_of_nonneg hpow_nonneg] using hxbound
  have hleft_int :
      MeasureTheory.Integrable
        (fun x => (∫ y, g y * rieszKernel x y ∂μU) ^ p)
        μU := by
    exact hright_int.mono' hleft_ae hleft_bound
  have hswap_int :
      MeasureTheory.Integrable
        (fun y => ∫ x, (g y) ^ p * rieszKernel x y ∂μU)
        μU :=
    hgpK_prod_int'.integral_prod_right
  have hgp_int' :
      MeasureTheory.Integrable
        (fun y => (g y) ^ p) μU := by
    simpa [μU, MeasureTheory.IntegrableOn] using hgp_int
  have hscaled_int :
      MeasureTheory.Integrable
        (fun y => (g y) ^ p * M)
        μU := by
    have htmp := hgp_int'.const_mul M
    simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
  have hswap_bound :
      (fun y => ∫ x, (g y) ^ p * rieszKernel x y ∂μU) ≤ᵐ[μU]
        (fun y => (g y) ^ p * M) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU.measurableSet] with y hy
    have hgy_nonneg : 0 ≤ (g y) ^ p :=
      Real.rpow_nonneg (hg_nonneg y) _
    have hk_le :
        ∫ x, rieszKernel x y ∂μU ≤ M := by
      simpa [μU, M] using hU.isBoundedDomain.integral_rieszKernel_right_le hy
    calc
      ∫ x, (g y) ^ p * rieszKernel x y ∂μU
          = (g y) ^ p * ∫ x, rieszKernel x y ∂μU := by
              rw [MeasureTheory.integral_const_mul]
      _ ≤ (g y) ^ p * M := by
            exact mul_le_mul_of_nonneg_left hk_le hgy_nonneg
  have hMp : M ^ (p - 1) * M = M ^ p := by
    by_cases hM_zero : M = 0
    · have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
      have hp_sub_ne_zero : p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
      simp [hM_zero, Real.zero_rpow hp_ne_zero, Real.zero_rpow hp_sub_ne_zero]
    · have hM_pos : 0 < M := lt_of_le_of_ne hM_nonneg (by simpa [eq_comm] using hM_zero)
      simpa using (Real.rpow_add hM_pos (p - 1) 1).symm
  calc
    ∫ x, (∫ y, g y * rieszKernel x y ∂μU) ^ p ∂μU
        ≤ ∫ x, M ^ (p - 1) * ∫ y, (g y) ^ p * rieszKernel x y ∂μU ∂μU := by
            exact MeasureTheory.integral_mono_ae hleft_int hright_int hpointwise
    _ = M ^ (p - 1) * ∫ x, ∫ y, (g y) ^ p * rieszKernel x y ∂μU ∂μU := by
          rw [MeasureTheory.integral_const_mul]
    _ = M ^ (p - 1) * ∫ y, ∫ x, (g y) ^ p * rieszKernel x y ∂μU ∂μU := by
          congr 1
          exact MeasureTheory.integral_integral_swap hgpK_prod_int'
    _ ≤ M ^ (p - 1) * ∫ y, (g y) ^ p * M ∂μU := by
          apply mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hM_nonneg _)
          exact MeasureTheory.integral_mono_ae hswap_int hscaled_int hswap_bound
    _ = (M ^ (p - 1) * M) * ∫ y, (g y) ^ p ∂μU := by
          have hscaled :
              ∫ y, (g y) ^ p * M ∂μU = M * ∫ y, (g y) ^ p ∂μU := by
            have hmul :
                (fun y => (g y) ^ p * M) = fun y => M * (g y) ^ p := by
              funext y
              ring
            rw [hmul, MeasureTheory.integral_const_mul]
          rw [hscaled]
          ring
    _ = M ^ p * ∫ y, (g y) ^ p ∂μU := by
          rw [hMp]
    _ = (((d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
          (4 * Classical.choose hU.isBoundedDomain)) ^ p) *
        ∫ y, (g y) ^ p ∂μU := by
          simp [M]
end RieszPowerMean

end CKN
