/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyC1
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyBounds

/-!
# L¹ estimates for the two-reflection extension

These estimates are the endpoint companions of the established quadratic Seeley
energy bounds.  They are used to control the value and derivative terms after
the compactly supported cutoff is applied to a mean-subtracted function.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace CKN

noncomputable section

attribute [local instance] Classical.propDecidable

theorem seeleyReflectionOne_lintegral_comp_le_l1 (g : Vec 3 → ℝ≥0∞) :
    ∫⁻ x in seeleyClosedAnnulus, g (seeleyReflectionOne x) ∂volume ≤
      64 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1, g y ∂volume := by
  have hpoint : ∀ x ∈ seeleyClosedAnnulus,
      g (seeleyReflectionOne x) ≤
        (64 : ℝ≥0∞) *
          (ENNReal.ofReal |(fderiv ℝ seeleyReflectionOne x).det| *
            g (seeleyReflectionOne x)) := by
    intro x hx
    have hdet : (1 / 64 : ℝ≥0∞) ≤
        ENNReal.ofReal |(fderiv ℝ seeleyReflectionOne x).det| := by
      calc
        (1 / 64 : ℝ≥0∞) = ENNReal.ofReal (1 / 64 : ℝ) := by
          rw [show (1 / 64 : ℝ) = (64 : ℝ)⁻¹ by norm_num,
            ENNReal.ofReal_inv_of_pos (by norm_num)]
          norm_num
        _ ≤ ENNReal.ofReal |(fderiv ℝ seeleyReflectionOne x).det| :=
          ENNReal.ofReal_le_ofReal (seeleyReflectionOne_fderiv_det_bounds hx).1
    have hmul := mul_le_mul_of_nonneg_right hdet
      (bot_le : (0 : ℝ≥0∞) ≤ g (seeleyReflectionOne x))
    calc
      g (seeleyReflectionOne x) =
          (64 : ℝ≥0∞) * ((1 / 64 : ℝ≥0∞) * g (seeleyReflectionOne x)) := by
            rw [show (1 / 64 : ℝ≥0∞) = (64 : ℝ≥0∞)⁻¹ by
              simp only [div_eq_mul_inv, one_mul]]
            calc
              _ = 1 * g (seeleyReflectionOne x) := (one_mul _).symm
              _ = (64 : ℝ≥0∞) * (64 : ℝ≥0∞)⁻¹ *
                  g (seeleyReflectionOne x) := by
                    rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
              _ = (64 : ℝ≥0∞) *
                  ((64 : ℝ≥0∞)⁻¹ * g (seeleyReflectionOne x)) := by
                    rw [mul_assoc]
      _ ≤ (64 : ℝ≥0∞) *
          (ENNReal.ofReal |(fderiv ℝ seeleyReflectionOne x).det| *
            g (seeleyReflectionOne x)) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
  calc
    ∫⁻ x in seeleyClosedAnnulus, g (seeleyReflectionOne x) ∂volume ≤
        ∫⁻ x in seeleyClosedAnnulus,
          (64 : ℝ≥0∞) *
            (ENNReal.ofReal |(fderiv ℝ seeleyReflectionOne x).det| *
              g (seeleyReflectionOne x)) ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem seeleyClosedAnnulus_measurableSet] with x hx
          exact hpoint x hx
    _ = 64 * ∫⁻ x in seeleyClosedAnnulus,
          ENNReal.ofReal |(fderiv ℝ seeleyReflectionOne x).det| *
            g (seeleyReflectionOne x) ∂volume := by
          rw [lintegral_const_mul' 64 _ (by norm_num)]
    _ = 64 * ∫⁻ y in seeleyReflectionOne '' seeleyClosedAnnulus,
          g y ∂volume := by
          rw [seeley_changeVariables_lintegral_one]
    _ ≤ 64 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1, g y ∂volume := by
          gcongr
          intro y hy
          rcases hy with ⟨x, hx, rfl⟩
          exact seeleyReflectionOne_maps_closedAnnulus hx

theorem seeleyReflectionTwo_lintegral_comp_le_l1 (g : Vec 3 → ℝ≥0∞) :
    ∫⁻ x in seeleyClosedAnnulus, g (seeleyReflectionTwo x) ∂volume ≤
      648 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1, g y ∂volume := by
  have hpoint : ∀ x ∈ seeleyClosedAnnulus,
      g (seeleyReflectionTwo x) ≤
        (648 : ℝ≥0∞) *
          (ENNReal.ofReal |(fderiv ℝ seeleyReflectionTwo x).det| *
            g (seeleyReflectionTwo x)) := by
    intro x hx
    have hdet : (1 / 648 : ℝ≥0∞) ≤
        ENNReal.ofReal |(fderiv ℝ seeleyReflectionTwo x).det| := by
      calc
        (1 / 648 : ℝ≥0∞) = ENNReal.ofReal (1 / 648 : ℝ) := by
          rw [show (1 / 648 : ℝ) = (648 : ℝ)⁻¹ by norm_num,
            ENNReal.ofReal_inv_of_pos (by norm_num)]
          norm_num
        _ ≤ ENNReal.ofReal |(fderiv ℝ seeleyReflectionTwo x).det| :=
          ENNReal.ofReal_le_ofReal (seeleyReflectionTwo_fderiv_det_bounds hx).1
    have hmul := mul_le_mul_of_nonneg_right hdet
      (bot_le : (0 : ℝ≥0∞) ≤ g (seeleyReflectionTwo x))
    calc
      g (seeleyReflectionTwo x) =
          (648 : ℝ≥0∞) * ((1 / 648 : ℝ≥0∞) * g (seeleyReflectionTwo x)) := by
            rw [show (1 / 648 : ℝ≥0∞) = (648 : ℝ≥0∞)⁻¹ by
              simp only [div_eq_mul_inv, one_mul]]
            calc
              _ = 1 * g (seeleyReflectionTwo x) := (one_mul _).symm
              _ = (648 : ℝ≥0∞) * (648 : ℝ≥0∞)⁻¹ *
                  g (seeleyReflectionTwo x) := by
                    rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
              _ = (648 : ℝ≥0∞) *
                  ((648 : ℝ≥0∞)⁻¹ * g (seeleyReflectionTwo x)) := by
                    rw [mul_assoc]
      _ ≤ (648 : ℝ≥0∞) *
          (ENNReal.ofReal |(fderiv ℝ seeleyReflectionTwo x).det| *
            g (seeleyReflectionTwo x)) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
  calc
    ∫⁻ x in seeleyClosedAnnulus, g (seeleyReflectionTwo x) ∂volume ≤
        ∫⁻ x in seeleyClosedAnnulus,
          (648 : ℝ≥0∞) *
            (ENNReal.ofReal |(fderiv ℝ seeleyReflectionTwo x).det| *
              g (seeleyReflectionTwo x)) ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem seeleyClosedAnnulus_measurableSet] with x hx
          exact hpoint x hx
    _ = 648 * ∫⁻ x in seeleyClosedAnnulus,
          ENNReal.ofReal |(fderiv ℝ seeleyReflectionTwo x).det| *
            g (seeleyReflectionTwo x) ∂volume := by
          rw [lintegral_const_mul' 648 _ (by norm_num)]
    _ = 648 * ∫⁻ y in seeleyReflectionTwo '' seeleyClosedAnnulus,
          g y ∂volume := by
          rw [seeley_changeVariables_lintegral_two]
    _ ≤ 648 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1, g y ∂volume := by
          gcongr
          intro y hy
          rcases hy with ⟨x, hx, rfl⟩
          exact seeleyReflectionTwo_maps_closedAnnulus hx

theorem seeleyReflectionOne_value_lintegral_le (v : Vec 3 → ℝ) (c : ℝ) :
    ∫⁻ x in seeleyClosedAnnulus,
        ENNReal.ofReal |v (seeleyReflectionOne x) - c| ∂volume ≤
      64 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
        ENNReal.ofReal |v y - c| ∂volume := by
  exact seeleyReflectionOne_lintegral_comp_le_l1
    (fun y => ENNReal.ofReal |v y - c|)

theorem seeleyReflectionTwo_value_lintegral_le (v : Vec 3 → ℝ) (c : ℝ) :
    ∫⁻ x in seeleyClosedAnnulus,
        ENNReal.ofReal |v (seeleyReflectionTwo x) - c| ∂volume ≤
      648 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
        ENNReal.ofReal |v y - c| ∂volume := by
  exact seeleyReflectionTwo_lintegral_comp_le_l1
    (fun y => ENNReal.ofReal |v y - c|)

theorem seeleyReflectionOne_comp_fderiv_norm_le_l1
    (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    ‖fderiv ℝ (v ∘ seeleyReflectionOne) x‖ ≤
      25 * ‖fderiv ℝ v (seeleyReflectionOne x)‖ := by
  have hAnn : x ∈ seeleyAnnulus := by
    exact ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  have hρ := seeleyReflectionOne_contDiffOn.contDiffAt
    (by
      have hopen : IsOpen seeleyAnnulus := by
        rw [seeleyAnnulus]
        have hnorm : Continuous (vecEuclideanNorm (d := 3)) := by
          change Continuous (fun y : Vec 3 => Real.sqrt (vecNormSq y))
          exact (contDiff_vecNormSq (d := 3)).continuous.sqrt
        exact (isOpen_lt continuous_const hnorm).inter
          (isOpen_lt hnorm continuous_const)
      exact hopen.mem_nhds hAnn)
  have hcomp := fderiv_comp x
    (hv.differentiable_one (seeleyReflectionOne x))
    (hρ.differentiableAt (by simp))
  rw [hcomp]
  calc
    ‖fderiv ℝ v (seeleyReflectionOne x) ∘SL fderiv ℝ seeleyReflectionOne x‖ ≤
        ‖fderiv ℝ v (seeleyReflectionOne x)‖ *
          ‖fderiv ℝ seeleyReflectionOne x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ v (seeleyReflectionOne x)‖ * 25 := by
      exact mul_le_mul_of_nonneg_left
        (seeleyReflectionOne_fderiv_norm_le hx) (norm_nonneg _)
    _ = 25 * ‖fderiv ℝ v (seeleyReflectionOne x)‖ := by ring

theorem seeleyReflectionTwo_comp_fderiv_norm_le_l1
    (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    ‖fderiv ℝ (v ∘ seeleyReflectionTwo) x‖ ≤
      169 * ‖fderiv ℝ v (seeleyReflectionTwo x)‖ := by
  have hAnn : x ∈ seeleyAnnulus := by
    exact ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  have hρ := seeleyReflectionTwo_contDiffOn.contDiffAt
    (by
      have hopen : IsOpen seeleyAnnulus := by
        rw [seeleyAnnulus]
        have hnorm : Continuous (vecEuclideanNorm (d := 3)) := by
          change Continuous (fun y : Vec 3 => Real.sqrt (vecNormSq y))
          exact (contDiff_vecNormSq (d := 3)).continuous.sqrt
        exact (isOpen_lt continuous_const hnorm).inter
          (isOpen_lt hnorm continuous_const)
      exact hopen.mem_nhds hAnn)
  have hcomp := fderiv_comp x
    (hv.differentiable_one (seeleyReflectionTwo x))
    (hρ.differentiableAt (by simp))
  rw [hcomp]
  calc
    ‖fderiv ℝ v (seeleyReflectionTwo x) ∘SL fderiv ℝ seeleyReflectionTwo x‖ ≤
        ‖fderiv ℝ v (seeleyReflectionTwo x)‖ *
          ‖fderiv ℝ seeleyReflectionTwo x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ v (seeleyReflectionTwo x)‖ * 169 := by
      exact mul_le_mul_of_nonneg_left
        (seeleyReflectionTwo_fderiv_norm_le hx) (norm_nonneg _)
    _ = 169 * ‖fderiv ℝ v (seeleyReflectionTwo x)‖ := by ring

end
end CKN
