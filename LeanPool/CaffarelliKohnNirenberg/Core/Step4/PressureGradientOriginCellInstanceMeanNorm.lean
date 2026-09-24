/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTensorTime
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Slice norms of the mean-free velocity

The mean oscillation estimate behind `eq:Chat` gives a uniform component
`L³` bound for the centered factor of `eq:Uij`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- Each centered component has `L³` norm at most the cube root of eight
times the Euclidean velocity norm. -/
theorem origin_slice_mean_free_component_norm_bound
    {u : ParabolicPoint → Vec3} {x : Vec3} {r s : ℝ}
    (hr : 0 < r)
    (hu : IntegrableOn (fun y : Vec3 => u (y, s)) (vec3Ball x r) volume)
    (hu3 : IntegrableOn (fun y : Vec3 => vec3EuclideanNorm (u (y, s)) ^ (3 : ℕ))
      (vec3Ball x r) volume) (j : Fin 3) :
    eLpNorm (fun y => meanFreeVec u x r s y j) (ENNReal.ofReal (3 : ℝ))
        (volume.restrict (vec3Ball x r)) ≤
      (8 : ℝ≥0∞) ^ (1 / 3 : ℝ) *
        eLpNorm (fun y => vec3EuclideanNorm (u (y, s))) (ENNReal.ofReal (3 : ℝ))
          (volume.restrict (vec3Ball x r)) := by
  have hcont : Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
    unfold vec3EuclideanNorm
    fun_prop
  have huM := hcont.comp_aestronglyMeasurable hu.aestronglyMeasurable
  have hvM : AEStronglyMeasurable (fun y => meanFreeVec u x r s y)
      (volume.restrict (vec3Ball x r)) := by
    rw [meanFreeVec_eq_sub_spatialAverage hu]
    exact hu.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hvN := hcont.comp_aestronglyMeasurable hvM
  have hj := eLpNorm_mono_ae (p := ENNReal.ofReal (3 : ℝ)) ((ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hvM)
    (Eventually.of_forall (fun y => show ‖meanFreeVec u x r s y j‖ ≤
      ‖vec3EuclideanNorm (meanFreeVec u x r s y)‖ from by
      rw [Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _), Real.norm_eq_abs]
      exact abs_apply_le_vec3EuclideanNorm _ j))
  refine hj.trans ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofReal_ne_top hvN,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofReal_ne_top huM]
  simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3),
    Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]
  have h := origin_slice_mean_free_cube_bound hr hu hu3
  have hid := meanFreeVec_eq_sub_spatialAverage hu
  have hmean : (∫⁻ y in vec3Ball x r,
      ENNReal.ofReal (vec3EuclideanNorm (meanFreeVec u x r s y)) ^ (3 : ℝ)) ≤
      8 * ∫⁻ y in vec3Ball x r,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ) := by
    simpa only [congrFun hid] using h
  exact (ENNReal.rpow_le_rpow hmean (by norm_num : (0 : ℝ) ≤ 1 / 3)).trans_eq
    (ENNReal.mul_rpow_of_nonneg _ _ (by norm_num))

end CKN.Core.Step4
