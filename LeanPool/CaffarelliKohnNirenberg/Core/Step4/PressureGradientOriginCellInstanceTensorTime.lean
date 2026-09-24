/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34SliceMeanFree
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTimeHolder

/-!
# Tensor energy estimates on spatial slices

The mean oscillation estimate behind `eq:Chat` controls the tensor energy
in `eq:pressure-gradient-morrey` by the velocity cube. The mean oscillation
argument follows the local estimate in `CKN.Pressure.Lin34SliceMeanFree`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- The spatial mean-free velocity cube is at most eight times the raw cube. -/
theorem origin_slice_mean_free_cube_bound
    {u : ParabolicPoint → Vec3} {x : Vec3} {r s : ℝ}
    (hr : 0 < r)
    (hu : IntegrableOn (fun y : Vec3 => u (y,s)) (vec3Ball x r) volume)
    (hu3 : IntegrableOn (fun y : Vec3 => vec3EuclideanNorm (u (y,s)) ^ (3 : ℕ))
      (vec3Ball x r) volume) :
    (∫⁻ y in vec3Ball x r, ENNReal.ofReal
      (vec3EuclideanNorm (u (y,s) - ⨍ z in vec3Ball x r, u (z,s))) ^ (3 : ℝ)) ≤
      8 * (∫⁻ y in vec3Ball x r, ENNReal.ofReal
        (vec3EuclideanNorm (u (y,s))) ^ (3 : ℝ)) := by
  let L := (PiLp.continuousLinearEquiv (2 : ℝ≥0∞) ℝ
    (fun _ : Fin 3 => ℝ)).symm
  have hLint : IntegrableOn (fun y : Vec3 => L (u (y,s)))
      (vec3Ball x r) volume := L.toContinuousLinearMap.integrable_comp hu.integrable
  have hL3 : IntegrableOn (fun y : Vec3 => ‖L (u (y,s))‖ ^ (3 : ℕ))
      (vec3Ball x r) volume := by
    simpa only [vec3EuclideanNorm_eq_l2,
      show (L : Vec3 → L2Vec3) = WithLp.toLp 2 by rfl] using hu3
  have h := CKN.Foundation.Parabolic.Integration.setLaverage_norm_sub_setAverage_rpow_le
    (f := fun y : Vec3 => L (u (y,s))) (p := (3 : ℝ)) (c := (0 : L2Vec3))
    (by norm_num) (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_pos hr)
    (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top (x := x) (r := r))
    hLint (by simpa using hL3)
  have hmap : L (⨍ y in vec3Ball x r, u (y,s)) =
      ⨍ y in vec3Ball x r, L (u (y,s)) := by
    rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
    change L ((volume (vec3Ball x r)).toReal⁻¹ • ∫ y in vec3Ball x r, u (y,s)) =
      (volume (vec3Ball x r)).toReal⁻¹ • ∫ y in vec3Ball x r, L (u (y,s))
    rw [map_smul, L.integral_comp_comm]
  rw [← hmap] at h
  simp only [← map_sub] at h
  rw [MeasureTheory.setLAverage_eq, MeasureTheory.setLAverage_eq] at h
  have h' := h
  norm_num [ENNReal.rpow_natCast] at h'
  have h'' :
      (∫⁻ y in vec3Ball x r, ‖L (u (y,s) - ⨍ z in vec3Ball x r, u (z,s))‖ₑ ^ (3 : ℝ)) /
        volume (vec3Ball x r) ≤
      (8 * (∫⁻ y in vec3Ball x r, ‖L (u (y,s))‖ₑ ^ (3 : ℝ))) /
        volume (vec3Ball x r) := by
    simpa [map_sub, sub_zero, mul_div_assoc, Real.rpow_natCast] using h'
  have hp := CKN.Foundation.Parabolic.Integration.volume_vec3Ball_pos (x := x) (r := r) hr
  have ht := CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top (x := x) (r := r)
  have hraw :
      (∫⁻ y in vec3Ball x r, ‖L (u (y,s) - ⨍ z in vec3Ball x r, u (z,s))‖ₑ ^ (3 : ℝ)) ≤
      8 * (∫⁻ y in vec3Ball x r, ‖L (u (y,s))‖ₑ ^ (3 : ℝ)) := by
    calc
      _ = ((∫⁻ y in vec3Ball x r, ‖L (u (y,s) - ⨍ z in vec3Ball x r, u (z,s))‖ₑ ^ (3 : ℝ)) /
          volume (vec3Ball x r)) * volume (vec3Ball x r) := by rw [ENNReal.div_mul_cancel hp.ne'
            ht.ne]
      _ ≤ ((8 : ℝ≥0∞) * (∫⁻ y in vec3Ball x r, ‖L (u (y,s))‖ₑ ^ (3 : ℝ)) /
          volume (vec3Ball x r)) * volume (vec3Ball x r) := mul_le_mul_of_nonneg_right h'' (by
            positivity)
      _ = 8 * (∫⁻ y in vec3Ball x r, ‖L (u (y,s))‖ₑ ^ (3 : ℝ)) := ENNReal.div_mul_cancel hp.ne'
        ht.ne
  convert hraw using 1 <;> simp [vec3EuclideanNorm_eq_l2,
    show (L : Vec3 → L2Vec3) = WithLp.toLp 2 by rfl, ofReal_norm]

/-- The tensor's three-halves energy is bounded by the velocity cube,
with the square root of eight from subtraction of the spatial average. -/
theorem origin_slice_tensor_energy_bound
    {u : ParabolicPoint → Vec3} {x : Vec3} {r s : ℝ}
    (hr : 0 < r)
    (hu : IntegrableOn (fun y : Vec3 => u (y, s)) (vec3Ball x r) volume)
    (hu3 : IntegrableOn (fun y : Vec3 => vec3EuclideanNorm (u (y, s)) ^ (3 : ℕ))
      (vec3Ball x r) volume) :
    (∫⁻ y in vec3Ball x r, ENNReal.ofReal (utensorNorm u x r s y) ^ (3 / 2 : ℝ)) ≤
      (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        ∫⁻ y in vec3Ball x r, ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ) := by
  have hcont : Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
    unfold vec3EuclideanNorm
    fun_prop
  have huM := hcont.measurable.comp_aemeasurable hu.aemeasurable
  have hvM := hcont.measurable.comp_aemeasurable
    (hu.aemeasurable.sub (aemeasurable_const (b := ⨍ z in vec3Ball x r, u (z, s))))
  have hconj : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (vec3Ball x r))
    hconj (huM.ennreal_ofReal.pow_const (3 / 2 : ℝ))
    (hvM.ennreal_ofReal.pow_const (3 / 2 : ℝ))
  simp only [Pi.mul_apply, ← ENNReal.rpow_mul,
    show (3 / 2 : ℝ) * 2 = 3 by norm_num] at hhold
  have hmean := origin_slice_mean_free_cube_bound hr hu hu3
  have hid := meanFreeVec_eq_sub_spatialAverage hu
  have heq : (∫⁻ y in vec3Ball x r,
      ENNReal.ofReal (utensorNorm u x r s y) ^ (3 / 2 : ℝ)) =
      ∫⁻ y in vec3Ball x r,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 / 2 : ℝ) *
        ENNReal.ofReal (vec3EuclideanNorm
          (u (y, s) - ⨍ z in vec3Ball x r, u (z, s))) ^ (3 / 2 : ℝ) := by
    apply lintegral_congr
    intro y
    rw [utensorNorm_eq, congrFun hid y, ENNReal.ofReal_mul
      (vec3EuclideanNorm_nonneg _), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [heq]
  refine hhold.trans ((mul_le_mul' le_rfl
    (ENNReal.rpow_le_rpow hmean (by norm_num))).trans_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  dsimp only [Function.comp_def]
  rw [mul_left_comm, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

/-- The tensor-energy contribution has the temporal four-fifths estimate
on any time window, with the velocity cube integrated on the same box. -/
theorem origin_tensor_energy_time_bound
    {u : ParabolicPoint → Vec3} {x : Vec3} {r : ℝ} {J : Set ℝ}
    (hr : 0 < r)
    (hu : Integrable u ((volume.restrict (vec3Ball x r)).prod (volume.restrict J)))
    (hu3 : Integrable (fun w : Vec3 × ℝ => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      ((volume.restrict (vec3Ball x r)).prod (volume.restrict J))) :
    (∫⁻ s in J, (∫⁻ y in vec3Ball x r,
      ENNReal.ofReal (utensorNorm u x r s y) ^ (3 / 2 : ℝ)) ^ (4 / 5 : ℝ)) ≤
      (8 : ℝ≥0∞) ^ (2 / 5 : ℝ) *
        (∫⁻ w in vec3Ball x r ×ˢ J,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ^ (4 / 5 : ℝ) *
        volume J ^ (1 / 5 : ℝ) := by
  have hcont : Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
    unfold vec3EuclideanNorm
    fun_prop
  have hA := (hcont.measurable.comp_aemeasurable hu.aemeasurable).ennreal_ofReal.pow_const (3 : ℝ)
  have htime := origin_time_energy_four_fifths_bound hA.lintegral_prod_left'
  have hpoint : ∀ᵐ s ∂volume.restrict J,
      (∫⁻ y in vec3Ball x r, ENNReal.ofReal (utensorNorm u x r s y) ^ (3 / 2 : ℝ)) ^
          (4 / 5 : ℝ) ≤
        (8 : ℝ≥0∞) ^ (2 / 5 : ℝ) *
          (∫⁻ y in vec3Ball x r, ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)) ^
            (4 / 5 : ℝ) := by
    filter_upwards [hu.prod_left_ae, hu3.prod_left_ae] with s hs hs3
    have h := ENNReal.rpow_le_rpow (origin_slice_tensor_energy_bound hr hs hs3)
      (by norm_num : (0 : ℝ) ≤ 4 / 5)
    simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4 / 5),
      ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * (4 / 5) = 2 / 5 by norm_num] using h
  have htonelli : (∫⁻ s in J, ∫⁻ y in vec3Ball x r,
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)) =
      ∫⁻ w in vec3Ball x r ×ˢ J,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) := by
    change _ = ∫⁻ w, ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)
      ∂((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (vec3Ball x r ×ˢ J)
    rw [← Measure.prod_restrict]
    exact (lintegral_prod_symm _ hA).symm
  calc
    _ ≤ ∫⁻ s in J, (8 : ℝ≥0∞) ^ (2 / 5 : ℝ) *
        (∫⁻ y in vec3Ball x r, ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)) ^
          (4 / 5 : ℝ) := lintegral_mono_ae hpoint
    _ = (8 : ℝ≥0∞) ^ (2 / 5 : ℝ) * ∫⁻ s in J,
        (∫⁻ y in vec3Ball x r, ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)) ^
          (4 / 5 : ℝ) := lintegral_const_mul' _ _ (by finiteness)
    _ ≤ _ := by
      have h := mul_le_mul' (le_refl ((8 : ℝ≥0∞) ^ (2 / 5 : ℝ))) htime
      dsimp only [Function.comp_def] at h
      simpa only [Measure.restrict_apply_univ, htonelli, mul_assoc] using h

/-- The real tensor energy used in the harmonic slice bound satisfies the
same time estimate after taking its two-thirds power and then `6/5`. -/
theorem origin_real_tensor_energy_time_bound
    {u : ParabolicPoint → Vec3} {x : Vec3} {r : ℝ} {J : Set ℝ}
    (hr : 0 < r)
    (hu : Integrable u ((volume.restrict (vec3Ball x r)).prod (volume.restrict J)))
    (hu3 : Integrable (fun w : Vec3 × ℝ => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      ((volume.restrict (vec3Ball x r)).prod (volume.restrict J))) :
    (∫⁻ s in J, ENNReal.ofReal
      ((∫ y in vec3Ball x r, utensorNorm u x r s y ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) ^
        (6 / 5 : ℝ)) ≤
      (8 : ℝ≥0∞) ^ (2 / 5 : ℝ) *
        (∫⁻ w in vec3Ball x r ×ˢ J,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ^ (4 / 5 : ℝ) *
        volume J ^ (1 / 5 : ℝ) := by
  refine (lintegral_mono (fun s => ?_)).trans (origin_tensor_energy_time_bound hr hu hu3)
  have hnonneg : ∀ y, 0 ≤ utensorNorm u x r s y := fun _ => Real.sqrt_nonneg _
  have hpow : ∀ y, 0 ≤ utensorNorm u x r s y ^ (3 / 2 : ℝ) :=
    fun y => Real.rpow_nonneg (hnonneg y) _
  have hE : ENNReal.ofReal (∫ y in vec3Ball x r,
      utensorNorm u x r s y ^ (3 / 2 : ℝ)) ≤
      ∫⁻ y in vec3Ball x r, ENNReal.ofReal (utensorNorm u x r s y) ^ (3 / 2 : ℝ) := by
    by_cases hInt : IntegrableOn (fun y => utensorNorm u x r s y ^ (3 / 2 : ℝ))
        (vec3Ball x r) volume
    · rw [ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall hpow)]
      exact le_of_eq (lintegral_congr (fun y =>
        (ENNReal.ofReal_rpow_of_nonneg (hnonneg y) (by norm_num : (0 : ℝ) ≤ 3 / 2)).symm))
    · rw [integral_undef hInt, ENNReal.ofReal_zero]
      exact bot_le
  rw [← ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hpow)
      (by norm_num : (0 : ℝ) ≤ 2 / 3),
    ← ENNReal.rpow_mul, show (2 / 3 : ℝ) * (6 / 5) = 4 / 5 by norm_num]
  exact ENNReal.rpow_le_rpow hE (by norm_num)

end CKN.Core.Step4
