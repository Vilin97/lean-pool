/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceHarmonicForceTime

/-!
# Measurability of the centered slice terms

Spatial averaging and cutoff multiplication preserve product measurability
of the tensor and divergence source in `eq:pressure-gradient-morrey`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- Spatial component averages are measurable in time. -/
theorem origin_velocity_average_aestronglyMeasurable
    {u : ParabolicPoint → Vec3} {B : Set Vec3} {J : Set ℝ}
    (hu : AEStronglyMeasurable (fun w : Vec3 × ℝ => u w)
      ((volume.restrict B).prod (volume.restrict J))) (j : Fin 3) :
    AEStronglyMeasurable (fun s => average (volume.restrict B) (fun y => u (y, s) j))
      (volume.restrict J) := by
  have hc := (ContinuousLinearMap.proj (R := ℝ) j).continuous.comp_aestronglyMeasurable hu
  simp_rw [average_eq]
  exact hc.prod_swap.integral_prod_right'.const_smul
    (((volume : Measure Vec3).restrict B).real Set.univ)⁻¹

/-- The centered cutoff divergence source is jointly measurable on the full
spatial space and the chosen time window. -/
theorem origin_centered_source_product_aestronglyMeasurable
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {x : Vec3} {ρ : ℝ} {J : Set ℝ} (hρ : 0 < ρ)
    (hu : AEStronglyMeasurable (fun w : Vec3 × ℝ => u w)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)))
    (hDu : AEStronglyMeasurable (fun w : Vec3 × ℝ => Du w)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J))) (i : Fin 3) :
    AEStronglyMeasurable (fun w : Vec3 × ℝ => pressureDivergenceCutoffSourceCentredTensor
      (mollifiedBallCutoff x hρ) (spatialDeriv (mollifiedBallCutoff x hρ))
      (fun y => u (y, w.2)) (fun y => Du (y, w.2))
      (fun j => average (volume.restrict (vec3Ball x ρ)) (fun y => u (y, w.2) j)) w.1 i)
      ((volume : Measure Vec3).prod (volume.restrict J)) := by
  have hum (j : Fin 3) := (ContinuousLinearMap.proj (R := ℝ) j).continuous.comp_aestronglyMeasurable hu
  have hdm (j : Fin 3) := (ContinuousLinearMap.proj (R := ℝ) j).continuous.comp_aestronglyMeasurable
    ((ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable hDu)
  have hmean (j : Fin 3) := origin_velocity_average_aestronglyMeasurable hu j
  have hw (j : Fin 3) := (hum j).sub (hmean j).comp_snd
  have hs := pressure_cutoff_support_subset_ball x hρ
  have hfirst (j : Fin 3) := origin_cutoff_product_aestronglyMeasurable
    (vec3Ball_measurable x ρ) ((hdm j).mul (hw j))
    (mollifiedBallCutoff_smooth x hρ).continuous.aestronglyMeasurable ((subset_tsupport _).trans hs)
  have hsecond (j : Fin 3) := origin_cutoff_product_aestronglyMeasurable
    (vec3Ball_measurable x ρ) ((hum i).mul (hw j))
    (contDiff_spatialDeriv_smooth (mollifiedBallCutoff_smooth x hρ) j).continuous.aestronglyMeasurable
    ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hs))
  simpa only [pressureDivergenceCutoffSourceCentredTensor, Finset.sum_fn, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, ContinuousLinearMap.proj_apply, Prod.mk.eta, mul_assoc] using
    Finset.aestronglyMeasurable_sum Finset.univ (fun j _ => (hfirst j).add (hsecond j))

/-- The real tensor energy appearing in the harmonic bound is measurable in time. -/
theorem origin_tensor_energy_time_aemeasurable
    {u : ParabolicPoint → Vec3} {x : Vec3} {ρ : ℝ} {J : Set ℝ}
    (hu : AEStronglyMeasurable (fun w : Vec3 × ℝ => u w)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J))) :
    AEMeasurable (fun s => (∫ y in vec3Ball x ρ,
      utensorNorm u x ρ s y ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) (volume.restrict J) := by
  have hum (j : Fin 3) := (ContinuousLinearMap.proj (R := ℝ) j).continuous.comp_aestronglyMeasurable hu
  have hmean (j : Fin 3) := origin_velocity_average_aestronglyMeasurable hu j
  have ht (i j : Fin 3) : AEMeasurable (fun w : Vec3 × ℝ => utensor u x ρ w.2 i j w.1)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) :=
    (hum i).neg.aemeasurable.mul ((hum j).sub (hmean j).comp_snd).aemeasurable
  have hnorm : AEMeasurable (fun w : Vec3 × ℝ => utensorNorm u x ρ w.2 w.1)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) := by
    unfold utensorNorm
    apply Real.continuous_sqrt.measurable.comp_aemeasurable
    simp only [Fin.sum_univ_succ]
    fun_prop
  have hpow := hnorm.pow_const (3 / 2 : ℝ)
  exact hpow.aestronglyMeasurable.prod_swap.integral_prod_right'.aemeasurable.pow_const (2 / 3 : ℝ)

end CKN.Core.Step4
