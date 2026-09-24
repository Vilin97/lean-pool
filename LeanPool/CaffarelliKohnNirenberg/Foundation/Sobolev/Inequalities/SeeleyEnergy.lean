/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleySplit

/-!
# Change-of-variables energy bounds for the two-reflection extension

The closed-annulus Jacobian lower bounds turn the exact change-of-variables
identities into explicit pullback estimates.  The statements are written for
nonnegative extended-valued integrands, so no auxiliary measurability
assumptions are needed at this stage.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace CKN

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The part of the closed annulus lying in the outer unit-ball shell. -/
def seeleyOuterAnnulus : Set (Vec 3) :=
  {x | 1 < vecEuclideanNorm x ∧ vecEuclideanNorm x < 2}

theorem seeleyOuterAnnulus_subset_closedAnnulus :
    seeleyOuterAnnulus ⊆ seeleyClosedAnnulus := by
  intro x hx
  exact ⟨hx.1.le, hx.2.le⟩

theorem seeleyOuterAnnulus_measurableSet :
    MeasurableSet seeleyOuterAnnulus := by
  rw [seeleyOuterAnnulus]
  have hnorm : Continuous (vecEuclideanNorm (d := 3)) := by
    change Continuous (fun x : Vec 3 => Real.sqrt (vecNormSq x))
    exact (contDiff_vecNormSq (d := 3)).continuous.sqrt
  exact (isOpen_lt continuous_const hnorm).inter
    (isOpen_lt hnorm continuous_const) |>.measurableSet

theorem seeleyExtension_value_eq_reflection_combo
    (v : Vec 3 → ℝ) {x : Vec 3} (hx : x ∈ seeleyOuterAnnulus) :
    seeleyExtension v x =
      3 * v (seeleyReflectionOne x) - 2 * v (seeleyReflectionTwo x) := by
  have houtside : x ∉ euclideanClosedBall (0 : Vec 3) 1 := by
    intro hxC
    have hnorm := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (by norm_num)).mp hxC
    have hnorm' : vecEuclideanNorm x ≤ 1 := by
      simpa only [sub_zero] using hnorm
    linarith only [hx.1, hnorm']
  simp [seeleyExtension, seeleyExterior, houtside]

theorem seeleyReflectionOne_lintegral_comp_le (g : Vec 3 → ℝ≥0∞) :
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

theorem seeleyReflectionTwo_lintegral_comp_le (g : Vec 3 → ℝ≥0∞) :
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

private theorem seeleyExtension_value_energy_pointwise
    (v : Vec 3 → ℝ) (c : ℝ) {x : Vec 3} (hx : x ∈ seeleyOuterAnnulus) :
    ENNReal.ofReal |seeleyExtension (fun y => v y - c) x| ^ 2 ≤
      (18 : ℝ≥0∞) * ENNReal.ofReal |v (seeleyReflectionOne x) - c| ^ 2 +
        (8 : ℝ≥0∞) * ENNReal.ofReal |v (seeleyReflectionTwo x) - c| ^ 2 := by
  have hvalue := seeleyExtension_value_eq_reflection_combo
    (v := fun y => v y - c) hx
  have hnorm :
      |seeleyExtension (fun y => v y - c) x| ≤
        3 * |v (seeleyReflectionOne x) - c| +
          2 * |v (seeleyReflectionTwo x) - c| := by
    rw [hvalue]
    calc
      |3 * (v (seeleyReflectionOne x) - c) -
            2 * (v (seeleyReflectionTwo x) - c)| ≤
          |3 * (v (seeleyReflectionOne x) - c)| +
            |2 * (v (seeleyReflectionTwo x) - c)| := abs_sub _ _
      _ = 3 * |v (seeleyReflectionOne x) - c| +
            2 * |v (seeleyReflectionTwo x) - c| := by
        rw [abs_mul, abs_mul]
        norm_num
  have hsq :
      |seeleyExtension (fun y => v y - c) x| ^ 2 ≤
        18 * |v (seeleyReflectionOne x) - c| ^ 2 +
          8 * |v (seeleyReflectionTwo x) - c| ^ 2 := by
    have hnonneg :
        0 ≤ 3 * |v (seeleyReflectionOne x) - c| +
          2 * |v (seeleyReflectionTwo x) - c| := by positivity
    have hsq' := (sq_le_sq₀ (abs_nonneg _) hnonneg).2 hnorm
    nlinarith only [hsq', sq_nonneg
      (3 * |v (seeleyReflectionOne x) - c| -
        2 * |v (seeleyReflectionTwo x) - c|)]
  calc
    _ = ENNReal.ofReal
        |seeleyExtension (fun y => v y - c) x| ^ 2 := rfl
    _ = ENNReal.ofReal
        (|seeleyExtension (fun y => v y - c) x| ^ 2) := by
      rw [ENNReal.ofReal_pow (abs_nonneg _)]
    _ ≤ ENNReal.ofReal
        (18 * |v (seeleyReflectionOne x) - c| ^ 2 +
          8 * |v (seeleyReflectionTwo x) - c| ^ 2) :=
      ENNReal.ofReal_le_ofReal hsq
    _ = (18 : ℝ≥0∞) * ENNReal.ofReal |v (seeleyReflectionOne x) - c| ^ 2 +
        (8 : ℝ≥0∞) * ENNReal.ofReal |v (seeleyReflectionTwo x) - c| ^ 2 := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs, sq_abs]
      norm_num [ENNReal.ofReal_ofNat]

private theorem seeleyExtension_value_energy_outer_le
    (v : Vec 3 → ℝ) (c : ℝ) :
    ∫⁻ x in seeleyOuterAnnulus,
        ENNReal.ofReal |seeleyExtension (fun y => v y - c) x| ^ 2 ∂volume ≤
      ∫⁻ x in seeleyClosedAnnulus,
        (18 : ℝ≥0∞) * ENNReal.ofReal |v (seeleyReflectionOne x) - c| ^ 2 +
          (8 : ℝ≥0∞) * ENNReal.ofReal |v (seeleyReflectionTwo x) - c| ^ 2 ∂volume := by
  calc
    ∫⁻ x in seeleyOuterAnnulus,
        ENNReal.ofReal |seeleyExtension (fun y => v y - c) x| ^ 2 ∂volume ≤
        ∫⁻ x in seeleyOuterAnnulus,
          (18 : ℝ≥0∞) * ENNReal.ofReal |v (seeleyReflectionOne x) - c| ^ 2 +
            (8 : ℝ≥0∞) * ENNReal.ofReal |v (seeleyReflectionTwo x) - c| ^ 2 ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (by
        exact seeleyOuterAnnulus_measurableSet) ] with x hx
      exact seeleyExtension_value_energy_pointwise v c hx
    _ ≤ ∫⁻ x in seeleyClosedAnnulus,
          (18 : ℝ≥0∞) * ENNReal.ofReal |v (seeleyReflectionOne x) - c| ^ 2 +
            (8 : ℝ≥0∞) * ENNReal.ofReal |v (seeleyReflectionTwo x) - c| ^ 2 ∂volume := by
      exact lintegral_mono_set seeleyOuterAnnulus_subset_closedAnnulus

private theorem seeleyExtension_value_energy_outer_le_of_density
    (v : Vec 3 → ℝ) (c : ℝ) (g : Vec 3 → ℝ≥0∞)
    (hρ : ∀ y : Vec 3,
      ENNReal.ofReal |v y - c| ^ 2 = g y) :
    ∫⁻ x in seeleyOuterAnnulus,
        ENNReal.ofReal |seeleyExtension (fun y => v y - c) x| ^ 2 ∂volume ≤
      ∫⁻ x in seeleyClosedAnnulus,
        (18 : ℝ≥0∞) * g (seeleyReflectionOne x) +
          (8 : ℝ≥0∞) * g (seeleyReflectionTwo x) ∂volume := by
  calc
    _ ≤ ∫⁻ x in seeleyClosedAnnulus,
        (18 : ℝ≥0∞) * ENNReal.ofReal |v (seeleyReflectionOne x) - c| ^ 2 +
          (8 : ℝ≥0∞) * ENNReal.ofReal |v (seeleyReflectionTwo x) - c| ^ 2 ∂volume :=
      seeleyExtension_value_energy_outer_le v c
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [] with x
      rw [hρ, hρ]

private theorem seeleyExtension_value_energy_reflection_combo_le
    (g : Vec 3 → ℝ≥0∞) :
    18 * ∫⁻ x in seeleyClosedAnnulus,
          g (seeleyReflectionOne x) ∂volume +
        8 * ∫⁻ x in seeleyClosedAnnulus,
          g (seeleyReflectionTwo x) ∂volume ≤
      18 * (64 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
          g y ∂volume) +
        8 * (648 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
          g y ∂volume) := by
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (seeleyReflectionOne_lintegral_comp_le g) (by positivity))
    (mul_le_mul_of_nonneg_left
      (seeleyReflectionTwo_lintegral_comp_le g) (by positivity))

private theorem seeleyExtension_value_energy_density_measurable
    (v : Vec 3 → ℝ) (c : ℝ) (g : Vec 3 → ℝ≥0∞)
    (hv : Continuous v)
    (hρ : ∀ y : Vec 3,
      ENNReal.ofReal |v y - c| ^ 2 = g y) :
    Measurable g := by
  rw [← funext hρ]
  have hsub : Continuous (fun y => v y - c) := hv.sub continuous_const
  have habs : Continuous (fun y => |v y - c|) := continuous_abs.comp hsub
  exact (ENNReal.measurable_ofReal.comp habs.measurable).pow measurable_const

theorem seeleyExtension_value_energy_le (v : Vec 3 → ℝ) (c : ℝ)
    (hv : Continuous v) :
    ∫⁻ x in seeleyOuterAnnulus,
        ENNReal.ofReal |seeleyExtension (fun y => v y - c) x| ^ 2 ∂volume ≤
      (6336 : ℝ≥0∞) *
        ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
          ENNReal.ofReal |v y - c| ^ 2 ∂volume := by
  generalize hρ : (fun y => ENNReal.ofReal |v y - c| ^ 2) = g
  have hg := seeleyExtension_value_energy_density_measurable v c g hv
    (fun y => congrFun hρ y)
  have hsplit := lintegral_reflection_split seeleyClosedAnnulus_measurableSet g hg
  have houter := seeleyExtension_value_energy_outer_le_of_density v c g
    (fun y => congrFun hρ y)
  calc
    _ ≤ ∫⁻ x in seeleyClosedAnnulus,
        (18 : ℝ≥0∞) * g (seeleyReflectionOne x) +
          (8 : ℝ≥0∞) * g (seeleyReflectionTwo x) ∂volume := houter
    _ = 18 * ∫⁻ x in seeleyClosedAnnulus,
          g (seeleyReflectionOne x) ∂volume +
        8 * ∫⁻ x in seeleyClosedAnnulus,
          g (seeleyReflectionTwo x) ∂volume := hsplit
    _ ≤ 18 * (64 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
          g y ∂volume) +
        8 * (648 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
          g y ∂volume) := seeleyExtension_value_energy_reflection_combo_le g
    _ = 6336 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1, g y ∂volume := by
      ring

end
end CKN
