/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.InterpolationBall
public import LeanPool.CaffarelliKohnNirenberg.Setting.InterpolationCylinder
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBridge
public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceIntegrability

/-! Componentwise norm estimates used by Caccioppoli finiteness arguments. -/

public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology
noncomputable section

namespace CKN

theorem caccioppoli_l2_component_bound
    {x₀ : Vec3} {r : ℝ} {u : Vec3 → Vec3} {i : Fin 3}
    (hu : AEMeasurable (fun x => u x i) (volume.restrict (vec3Ball x₀ r)))
    (humeas : AEStronglyMeasurable (fun x => u x)
      (volume.restrict (vec3Ball x₀ r))) :
    lpNormOn 2 (vec3Ball x₀ r) (fun x => u x i) ≤
      (∫⁻ x in vec3Ball x₀ r,
        ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
    unfold vec3EuclideanNorm
    fun_prop
  have hnorm : AEStronglyMeasurable
      (fun x => vec3EuclideanNorm (u x)) (volume.restrict (vec3Ball x₀ r)) := by
    exact (hc.measurable.comp_aemeasurable humeas.aemeasurable).aestronglyMeasurable
  have hmono : eLpNorm (fun x => u x i) 2 (volume.restrict (vec3Ball x₀ r)) ≤
      eLpNorm (fun x => vec3EuclideanNorm (u x)) 2
        (volume.restrict (vec3Ball x₀ r)) := by
    apply eLpNorm_mono_ae_real hu.aestronglyMeasurable
    filter_upwards [] with x
    change |u x i| ≤ vec3EuclideanNorm (u x)
    unfold vec3EuclideanNorm
    apply Real.abs_le_sqrt
    exact Finset.single_le_sum (fun j _ => sq_nonneg (u x j)) (Finset.mem_univ i)
  change eLpNorm (fun x => u x i) 2 (volume.restrict (vec3Ball x₀ r)) ≤ _
  calc
    _ ≤ eLpNorm (fun x => vec3EuclideanNorm (u x)) 2
        (volume.restrict (vec3Ball x₀ r)) := hmono
    _ = (∫⁻ x in vec3Ball x₀ r,
        ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (p := (2 : ℝ≥0∞)) (by norm_num) ENNReal.coe_ne_top hnorm]
      apply congrArg (fun z : ℝ≥0∞ => z ^ (1 / (2 : ℝ) : ℝ))
      apply lintegral_congr
      intro x
      rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _),
        ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _) (by norm_num)]
      norm_num
      rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 2]

theorem caccioppoli_native_norm_le_euclidean (v : Vec3) :
    ‖v‖ ≤ vec3EuclideanNorm v := by
  rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg _)]
  intro i
  change |v i| ≤ vec3EuclideanNorm v
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)

theorem caccioppoli_gradient_component_bound
    {x₀ : Vec3} {r : ℝ} {g : Vec3 → Fin 3 → Vec3} {i : Fin 3}
    (hg : AEStronglyMeasurable g (volume.restrict (vec3Ball x₀ r))) :
    weakGradientLpNormOn 2 (vec3Ball x₀ r) (fun x => g x i) ≤
      (∫⁻ x in vec3Ball x₀ r,
        ENNReal.ofReal (∑ k : Fin 3, ∑ j : Fin 3, (g x k j) ^ (2 : ℕ))) ^
          (1 / 2 : ℝ) := by
  have hrow : ∀ x, ‖g x i‖ ≤
      Real.sqrt (∑ k : Fin 3, ∑ j : Fin 3, (g x k j) ^ (2 : ℕ)) := by
    intro x
    calc
      ‖g x i‖ ≤ vec3EuclideanNorm (g x i) := caccioppoli_native_norm_le_euclidean _
      _ ≤ Real.sqrt (∑ k : Fin 3, ∑ j : Fin 3, (g x k j) ^ (2 : ℕ)) := by
        unfold vec3EuclideanNorm
        apply Real.sqrt_le_sqrt
        exact Finset.single_le_sum (fun k _ =>
          Finset.sum_nonneg (fun j _ => sq_nonneg (g x k j))) (Finset.mem_univ i)
  have hrowmeas : AEStronglyMeasurable (fun x => g x i)
      (volume.restrict (vec3Ball x₀ r)) := by
    simpa only [ContinuousLinearMap.proj_apply] using
      (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable hg
  have hmono : eLpNorm (fun x => g x i) 2
      (volume.restrict (vec3Ball x₀ r)) ≤
      eLpNorm (fun x => Real.sqrt (∑ k : Fin 3, ∑ j : Fin 3,
        (g x k j) ^ (2 : ℕ))) 2
        (volume.restrict (vec3Ball x₀ r)) := by
    apply eLpNorm_mono_ae_real hrowmeas
    exact Filter.Eventually.of_forall hrow
  change eLpNorm (fun x => g x i) 2 (volume.restrict (vec3Ball x₀ r)) ≤ _
  calc
    _ ≤ eLpNorm (fun x => Real.sqrt (∑ k : Fin 3, ∑ j : Fin 3,
        (g x k j) ^ (2 : ℕ))) 2 (volume.restrict (vec3Ball x₀ r)) := hmono
    _ = (∫⁻ x in vec3Ball x₀ r,
        ENNReal.ofReal (∑ k : Fin 3, ∑ j : Fin 3, (g x k j) ^ (2 : ℕ))) ^
          (1 / 2 : ℝ) := by
      have hs : AEMeasurable (fun x : Vec3 => ∑ k : Fin 3, ∑ j : Fin 3,
          (g x k j) ^ (2 : ℕ)) (volume.restrict (vec3Ball x₀ r)) := by
        have hkj : ∀ k j : Fin 3, AEMeasurable (fun x : Vec3 => g x k j)
            (volume.restrict (vec3Ball x₀ r)) := by
          intro k j
          simpa only [ContinuousLinearMap.proj_apply] using
            (ContinuousLinearMap.proj (R := ℝ) j).continuous.comp_aestronglyMeasurable
              ((ContinuousLinearMap.proj (R := ℝ) k).continuous.comp_aestronglyMeasurable hg)
              |>.aemeasurable
        have hsumj : ∀ k : Fin 3, AEMeasurable
            (fun x : Vec3 => ∑ j : Fin 3, (g x k j) ^ (2 : ℕ))
            (volume.restrict (vec3Ball x₀ r)) := by
          intro k
          have hj : ∀ j : Fin 3, AEMeasurable (fun x : Vec3 =>
              (g x k j) ^ (2 : ℕ)) (volume.restrict (vec3Ball x₀ r)) := by
            intro j
            convert (hkj k j).pow_const (2 : ℝ) using 1
            funext x
            exact (Real.rpow_natCast _ _).symm
          have hs' := Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3))
            (fun j _ => hj j)
          convert hs' using 1
          funext x
          simp
        have hs' := Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3))
          (fun k _ => hsumj k)
        convert hs' using 1
        funext x
        simp
      have hroot : AEStronglyMeasurable
          (fun x : Vec3 => Real.sqrt (∑ k : Fin 3, ∑ j : Fin 3,
            (g x k j) ^ (2 : ℕ))) (volume.restrict (vec3Ball x₀ r)) :=
        (Real.continuous_sqrt.measurable.comp_aemeasurable hs).aestronglyMeasurable
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (p := (2 : ℝ≥0∞)) (by norm_num) ENNReal.coe_ne_top hroot]
      apply congrArg (fun z : ℝ≥0∞ => z ^ (1 / (2 : ℝ) : ℝ))
      apply lintegral_congr
      intro x
      rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _),
        ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num)]
      norm_num
      calc
        ENNReal.ofReal (Real.sqrt (∑ k : Fin 3, ∑ j : Fin 3,
            (g x k j) ^ (2 : ℕ))) ^ (2 : ℕ) =
            ENNReal.ofReal ((Real.sqrt (∑ k : Fin 3, ∑ j : Fin 3,
              (g x k j) ^ (2 : ℕ))) ^ (2 : ℕ)) :=
          (ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2).symm
        _ = ENNReal.ofReal (∑ k : Fin 3, ∑ j : Fin 3, (g x k j) ^ (2 : ℕ)) := by
          rw [Real.sq_sqrt]
          exact Finset.sum_nonneg (fun k _ =>
            Finset.sum_nonneg (fun j _ => sq_nonneg (g x k j)))

theorem caccioppoli_eLpNorm_cube_eq_lintegral_abs_cube
    {s : Set Vec3} {f : Vec3 → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict s)) :
    eLpNorm f (3 : ℝ≥0∞) (volume.restrict s) ^ (3 : ℕ) =
      ∫⁻ x in s, ENNReal.ofReal |f x| ^ (3 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (p := (3 : ℝ≥0∞)) (by norm_num) ENNReal.coe_ne_top hf,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs]

end CKN
