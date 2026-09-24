/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstancePotentialTime

/-!
# Compact-time integrability of the actual harmonic force constant

The harmonic force term in `eq:pressure-gradient-morrey`, including both
potential-growth constants, is measurable and integrable on interior time boxes.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

/-- Multiplication by a spatial cutoff supported in the local ball extends
local product measurability to the full spatial space. -/
theorem origin_cutoff_product_aestronglyMeasurable
    {B : Set Vec3} {J : Set ℝ} {G : Vec3 × ℝ → ℝ} {η : Vec3 → ℝ}
    (hB : MeasurableSet B)
    (hG : AEStronglyMeasurable G ((volume.restrict B).prod (volume.restrict J)))
    (hη : AEStronglyMeasurable η volume) (hs : Function.support η ⊆ B) :
    AEStronglyMeasurable (fun w : Vec3 × ℝ => η w.1 * G w)
      ((volume : Measure Vec3).prod (volume.restrict J)) := by
  have hGi : AEStronglyMeasurable ((B ×ˢ univ).indicator G)
      ((volume : Measure Vec3).prod (volume.restrict J)) := by
    apply (aestronglyMeasurable_indicator_iff (hB.prod MeasurableSet.univ)).mpr
    rw [← Measure.prod_restrict, Measure.restrict_univ]
    exact hG
  have heq : (fun w : Vec3 × ℝ => η w.1 * G w) =
      fun w => η w.1 * (B ×ˢ univ).indicator G w := by
    funext w
    by_cases hw : w.1 ∈ B
    · rw [indicator_of_mem (show w ∈ B ×ˢ univ from ⟨hw, mem_univ _⟩)]
    · have hzero : η w.1 = 0 := by by_contra hn; exact hw (hs hn)
      simp only [hzero, zero_mul]
  rw [heq]
  exact hη.comp_fst.mul hGi

/-- The actual harmonic force constant is time integrable on every local
origin box of a suitable weak solution. -/
theorem origin_harmonic_force_integrable_on_local_box
    {Ω : Set Vec3} {I J : Set ℝ} {q R : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hR : 0 < R)
    (hbox : localBox Ω I (vec3Ball 0 R) J) :
    Integrable (fun s => harmonicRemainderForceBound ((0 : Vec3), 0) hR f s)
      (volume.restrict J) := by
  let η := mollifiedBallCutoff (0 : Vec3) hR
  have hf (j : Fin 3) : AEStronglyMeasurable (fun w : Vec3 × ℝ => f w j)
      ((volume.restrict (vec3Ball 0 R)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact (hsol.2.2.2.2.1 (vec3Ball 0 R) J hbox j).aestronglyMeasurable
  have hs := pressure_cutoff_support_subset_ball (0 : Vec3) hR
  have hη (j : Fin 3) := origin_cutoff_product_aestronglyMeasurable
    (vec3Ball_measurable (0 : Vec3) R) (hf j)
    (mollifiedBallCutoff_smooth (0 : Vec3) hR).continuous.aestronglyMeasurable
    ((subset_tsupport _).trans hs)
  have hd (j : Fin 3) := origin_cutoff_product_aestronglyMeasurable
    (vec3Ball_measurable (0 : Vec3) R) (hf j)
    (contDiff_spatialDeriv_smooth (mollifiedBallCutoff_smooth (0 : Vec3) hR)
      j).continuous.aestronglyMeasurable
    ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hs))
  have h7 (j : Fin 3) := (origin_force_growth_constants_time_aemeasurable (hη j) R).2 j
  have h8 (j : Fin 3) := (origin_force_growth_constants_time_aemeasurable (hd j) R).1
  have h7sum : AEMeasurable (fun s => pressureP7GrowthConstant η f s R) (volume.restrict J) := by
    simpa only [pressureP7GrowthConstant, Finset.sum_fn] using
      Finset.aemeasurable_sum Finset.univ (fun j _ => h7 j)
  have h8sum : AEMeasurable (fun s => pressureP8GrowthConstant η f s R) (volume.restrict J) := by
    simpa only [pressureP8GrowthConstant, Finset.sum_fn] using
      Finset.aemeasurable_sum Finset.univ (fun j _ => h8 j)
  have hm : AEMeasurable (fun s => harmonicRemainderForceBound ((0 : Vec3), 0) hR f s)
      (volume.restrict J) := by
    simpa only [harmonicRemainderForceBound, vec3EuclideanNorm_zero, zero_add, add_zero,
      Pi.add_apply, η] using
      ((h7sum.add h8sum).mul_const (1 + R)).max aemeasurable_const
  have he := origin_force_envelope_obligations_on_local_box hsol hR hbox
  apply he.2.2.mono' hm.aestronglyMeasurable
  filter_upwards [origin_harmonic_force_le_envelope_on_local_box hsol hR hbox, he.2.1] with s hs ht
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  have hnonneg : 0 ≤ harmonicRemainderForceBound ((0 : Vec3), 0) hR f s := le_max_right _ _
  simpa only [ENNReal.toReal_ofReal hnonneg] using
    (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top ht).mpr hs

end CKN.Core.Step4
