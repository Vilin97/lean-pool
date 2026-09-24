/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliAssembly

/-!
# Caccioppoli Energy

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat


noncomputable section

namespace CKN

theorem caccioppoli_heat_cutoff_lower
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2)
    {z : ParabolicPoint} (hz : z ∈ parabolicCylinder x₀ t₀ r) :
    1 / (2000 * r) ≤
      backwardHeat_cutoff (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε)
        x₀ t₀ r z := by
  have hzmem := mem_parabolicCylinder.mp hz
  have hx : z.1 ∈ vec3Ball x₀ (ρ / 2) := by
    rw [mem_vec3Ball]
    exact hzmem.1.trans_le hscale
  have hη := caccioppoli_heat_cutoff_eq_one_on x₀ t₀ ρ ε r hρ hε hr hscale
    hx ⟨hzmem.2.1, by linarith only [hzmem.2.2, hε]⟩
  have htime : z.2 - t₀ < r ^ 2 := by
    exact lt_of_le_of_lt (by linarith only [hzmem.2.2])
      (sq_pos_of_pos hr)
  have hψ := centeredBackwardHeatTest_lower_on_cylinder hr hz
  have hψ' : 1 / (2000 * r) ≤
      backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) := by
    simpa only [centeredBackwardHeatTest] using hψ
  unfold backwardHeat_cutoff
  simp only [ite_eq_left htime, hη, one_mul]
  exact hψ'

theorem caccioppoli_cutoff_norm_measurable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I) :
    AEMeasurable (fun z => ENNReal.ofReal (vec3EuclideanNorm (u z)))
        (volume.restrict (parabolicCylinder x₀ t₀ ρ)) ∧
      AEMeasurable (fun z => ENNReal.ofReal |p z|)
        (volume.restrict (parabolicCylinder x₀ t₀ ρ)) ∧
      AEMeasurable (fun z => ENNReal.ofReal (vec3EuclideanNorm (f z)))
        (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := by
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hU0 : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet Ω' J)) := hdata.1
  have hP0 : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet Ω' J)) := hdata.2.2.1
  have hF0 : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet Ω' J)) := hdata.2.2.2.1
  have hU : AEMeasurable (fun z => ENNReal.ofReal (vec3EuclideanNorm (u z)))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact ((ENNReal.continuous_ofReal.comp hc).comp_aestronglyMeasurable hU0)
      |>.aemeasurable.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have hP : AEMeasurable (fun z => ENNReal.ofReal |p z|)
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := by
    have hc : Continuous (fun v : ℝ => |v|) := continuous_abs
    exact ((ENNReal.continuous_ofReal.comp hc).comp_aestronglyMeasurable hP0)
      |>.aemeasurable.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have hF : AEMeasurable (fun z => ENNReal.ofReal (vec3EuclideanNorm (f z)))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact ((ENNReal.continuous_ofReal.comp hc).comp_aestronglyMeasurable hF0)
      |>.aemeasurable.mono_measure (Measure.restrict_mono hcyl le_rfl)
  exact ⟨hU, hP, hF⟩

theorem caccioppoli_nested_integral_eq
    {Ω : Set Vec3} {T : Set ℝ} {g : ParabolicPoint → ℝ}
    (hg : IntegrableOn g (Ω ×ˢ T) ((volume : Measure Vec3).prod volume)) :
    ∫ s in T, ∫ x in Ω, g (x, s) =
      ∫ z in Ω ×ˢ T, g z ∂((volume : Measure Vec3).prod volume) := by
  have hswap : IntegrableOn (fun z : ℝ × Vec3 =>
      g (show ParabolicPoint from z.swap))
      (T ×ˢ Ω) ((volume : Measure ℝ).prod volume) := hg.swap
  calc
    ∫ s in T, ∫ x in Ω, g (show ParabolicPoint from (x, s)) =
        ∫ z in T ×ˢ Ω, g (show ParabolicPoint from z.swap)
          ∂((volume : Measure ℝ).prod volume) := by
          have hp := setIntegral_prod
            (f := fun z : ℝ × Vec3 =>
              g (show ParabolicPoint from z.swap)) hswap
          convert hp.symm using 1
          rfl
    _ = ∫ z in Ω ×ˢ T, g z ∂((volume : Measure Vec3).prod volume) := by
      simpa using
        (setIntegral_prod_swap T Ω (fun z : ℝ × Vec3 =>
          g (show ParabolicPoint from z.swap))).symm

theorem caccioppoli_lower_from_slice_bounds
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {x₀ : Vec3} {t₀ r S : ℝ} (hr : 0 < r)
    (hS : 0 ≤ S)
    (hE : ∀ᵐ t ∂volume.restrict (Ioc (t₀ - r ^ 2) t₀),
      (∫⁻ x in vec3Ball x₀ r,
        ENNReal.ofReal ((vec3EuclideanNorm (u (x, t))) ^ 2)) ≤
        ENNReal.ofReal (2000 * r * S))
    (hG : (∫⁻ z in parabolicCylinder x₀ t₀ r,
      ENNReal.ofReal (spatialGradientSq u Du z)) ≤
        ENNReal.ofReal (1000 * r * S)) :
    (alpha u (x₀, t₀) r + beta u Du (x₀, t₀) r) ^ 2 ≤ 6000 * S := by
  have hess : essSup (fun t =>
      ∫⁻ x in vec3Ball x₀ r,
        ENNReal.ofReal ((vec3EuclideanNorm (u (x, t))) ^ 2))
    (volume.restrict (Ioc (t₀ - r ^ 2) t₀)) ≤
      ENNReal.ofReal (2000 * r * S) := by
    let _ : (ae (volume.restrict (Ioc (t₀ - r ^ 2) t₀))).NeBot := by
      rw [MeasureTheory.ae_restrict_neBot]
      rw [Real.volume_Ioc]
      rw [sub_sub_cancel]
      exact (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hr)).ne'
    exact essSup_le_of_ae_le _ hE
      (isCoboundedUnder_le_of_eventually_le _
        (Filter.Eventually.of_forall fun _ => bot_le))
  have hα : alpha u (x₀, t₀) r ^ 2 ≤ 2000 * S := by
    rw [alpha_sq_eq u (x₀, t₀) r hr]
    have hess' : timeSliceEnergyEssSup x₀ t₀ r
        (fun w => vec3EuclideanNorm (u w)) ≤
        ENNReal.ofReal (2000 * r * S) := by
      have hfun : (fun t => ∫⁻ x in vec3Ball x₀ r,
          ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ (2 : ℝ)) =
          (fun t => ∫⁻ x in vec3Ball x₀ r,
            ENNReal.ofReal ((vec3EuclideanNorm (u (x, t))) ^ 2)) := by
        funext t
        apply lintegral_congr
        intro x
        rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _),
          ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _)
            (by norm_num)]
        norm_num [Real.rpow_natCast]
      simp only [timeSliceEnergyEssSup, timeSliceBallEnergy]
      rw [hfun]
      exact hess
    have hright : ENNReal.ofReal (2000 * r * S) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    have hreal := ENNReal.toReal_mono hright hess'
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2000 * r * S)] at hreal
    calc
      r⁻¹ * (timeSliceEnergyEssSup x₀ t₀ r
          (fun w => vec3EuclideanNorm (u w))).toReal ≤
          r⁻¹ * (2000 * r * S) := by
            exact mul_le_mul_of_nonneg_left hreal (by positivity)
      _ = 2000 * S := by field_simp [hr.ne']
  have hβ : beta u Du (x₀, t₀) r ^ 2 ≤ 1000 * S := by
    rw [beta_sq_eq u Du (x₀, t₀) r hr]
    have hright : ENNReal.ofReal (1000 * r * S) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    have hreal := ENNReal.toReal_mono hright hG
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 1000 * r * S)] at hreal
    calc
      r⁻¹ * (∫⁻ z in parabolicCylinder x₀ t₀ r,
          ENNReal.ofReal (spatialGradientSq u Du z)).toReal ≤
          r⁻¹ * (1000 * r * S) := by
            exact mul_le_mul_of_nonneg_left hreal (by positivity)
      _ = 1000 * S := by field_simp [hr.ne']
  have hα₀ : 0 ≤ alpha u (x₀, t₀) r := by unfold alpha; positivity
  have hβ₀ : 0 ≤ beta u Du (x₀, t₀) r := by unfold beta; positivity
  have hleft : 0 ≤ alpha u (x₀, t₀) r + beta u Du (x₀, t₀) r :=
    add_nonneg hα₀ hβ₀
  have hsq : (alpha u (x₀, t₀) r + beta u Du (x₀, t₀) r) ^ 2 ≤
      2 * (alpha u (x₀, t₀) r) ^ 2 +
        2 * (beta u Du (x₀, t₀) r) ^ 2 := by
    nlinarith only [sq_nonneg (alpha u (x₀, t₀) r - beta u Du (x₀, t₀) r)]
  calc
    (alpha u (x₀, t₀) r + beta u Du (x₀, t₀) r) ^ 2 ≤
        2 * (alpha u (x₀, t₀) r) ^ 2 +
          2 * (beta u Du (x₀, t₀) r) ^ 2 := hsq
    _ ≤ 6000 * S := by nlinarith only [hα, hβ, hS]

end CKN
