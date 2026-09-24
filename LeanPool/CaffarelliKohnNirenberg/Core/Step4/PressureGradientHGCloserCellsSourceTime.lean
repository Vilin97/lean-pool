/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsRemainder

/-! # Time integration of spatial source masses

Spatial Hölder converts the `L^1` mass of a source on a ball into its
`L^{6/5}` mass. Enlarging the time window to the ball's parabolic scale
then makes the source's Morrey bound available for exterior kernel terms.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

/-- Spatial Hölder, raised to the source exponent, retains the ball's
volume to the power `1/5`. -/
theorem pressure_source_spatial_mass_power_bound
    {G : Vec3 → ℝ} {B : Set Vec3}
    (hG : AEMeasurable G (volume.restrict B)) :
    (∫⁻ y in B, ‖G y‖ₑ) ^ (6 / 5 : ℝ) ≤
      volume B ^ (1 / 5 : ℝ) * ∫⁻ y in B, ‖G y‖ₑ ^ (6 / 5 : ℝ) := by
  have hpq : (6 / 5 : ℝ).HolderConjugate 6 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict B) hpq
    hG.enorm (aemeasurable_const : AEMeasurable (fun _ : Vec3 => (1 : ℝ≥0∞)) _)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    one_mul, Measure.restrict_apply_univ] at h
  have hr := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 6 / 5)
  refine hr.trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6 / 5),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num
  exact mul_comm _ _

/-- A smaller cell time window is controlled by the full parabolic cylinder
at the source ball's radius. -/
theorem pressure_source_spatial_mass_time_power_bound
    {F : ParabolicPoint → ℝ} (hF : AEMeasurable F volume)
    {x : Vec3} {t r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) :
    (∫⁻ s in Ioc (t - r ^ 2) t,
      (∫⁻ y in vec3Ball x ρ, ‖F (y, s)‖ₑ) ^ (6 / 5 : ℝ)) ≤
      volume (vec3Ball x ρ) ^ (1 / 5 : ℝ) *
        cylinderPowerIntegral (6 / 5 : ℝ) F (x, t) ρ := by
  have hρ : 0 < ρ := hr.trans_le hrρ
  have hFm : AEStronglyMeasurable F
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := by
    change AEStronglyMeasurable F (volume : Measure (Vec3 × ℝ))
    exact hF.aestronglyMeasurable
  have hwin : Ioc (t - r ^ 2) t ⊆ Ioc (t - ρ ^ 2) t := by
    intro s hs
    exact ⟨lt_of_le_of_lt (sub_le_sub_left (pow_le_pow_left₀ hr.le hrρ 2) t) hs.1, hs.2⟩
  have hvol : volume (vec3Ball x ρ) ^ (1 / 5 : ℝ) ≠ ⊤ := by
    rw [volume_vec3Ball_eq]
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)).ne
  calc
    _ ≤ ∫⁻ s in Ioc (t - r ^ 2) t,
        volume (vec3Ball x ρ) ^ (1 / 5 : ℝ) *
          ∫⁻ y in vec3Ball x ρ, ‖F (y, s)‖ₑ ^ (6 / 5 : ℝ) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hFm.prodMk_right] with s hs
      exact pressure_source_spatial_mass_power_bound hs.aemeasurable.restrict
    _ = volume (vec3Ball x ρ) ^ (1 / 5 : ℝ) *
        ∫⁻ s in Ioc (t - r ^ 2) t,
          ∫⁻ y in vec3Ball x ρ, ‖F (y, s)‖ₑ ^ (6 / 5 : ℝ) :=
      lintegral_const_mul' _ _ hvol
    _ ≤ volume (vec3Ball x ρ) ^ (1 / 5 : ℝ) *
        ∫⁻ s in Ioc (t - ρ ^ 2) t,
          ∫⁻ y in vec3Ball x ρ, ‖F (y, s)‖ₑ ^ (6 / 5 : ℝ) :=
      mul_le_mul_right (lintegral_mono' (Measure.restrict_mono_set volume hwin) (fun _ => le_rfl)) _
    _ = _ := by
      rw [cylinderPowerIntegral_eq_lintegral_slices (by norm_num) hF.restrict]
      simp only [Real.enorm_eq_ofReal_abs]

/-- The inverse-cube exterior kernel factor converts the integrated source
mass into the Morrey tail power `ρ^{5/3 - 5/κ}`. -/
theorem pressure_source_exterior_mass_time_bound
    {κ : ℝ} {F : ParabolicPoint → ℝ} (hF : AEMeasurable F volume)
    {x : Vec3} {t r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) :
    ENNReal.ofReal ρ ^ (-3 : ℝ) *
        (∫⁻ s in Ioc (t - r ^ 2) t,
          (∫⁻ y in vec3Ball x ρ, ‖F (y, s)‖ₑ) ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤
      ENNReal.ofReal (Real.pi * 4 / 3) ^ (1 / 6 : ℝ) *
        ENNReal.ofReal ρ ^ (5 / 3 - 5 / κ) * morreyNorm (6 / 5 : ℝ) κ F := by
  have hρ : 0 < ρ := hr.trans_le hrρ
  have h := ENNReal.rpow_le_rpow (pressure_source_spatial_mass_time_power_bound hF (x := x) (t :=
    t) hr hrρ)
    (by norm_num : (0 : ℝ) ≤ 5 / 6)
  have hc : morreyCell (6 / 5 : ℝ) κ F (x, t) ρ ≤ morreyNorm (6 / 5 : ℝ) κ F :=
    le_iSup_of_le ((x, t) : ParabolicPoint) (le_iSup_of_le ⟨ρ, hρ⟩ le_rfl)
  calc
    _ ≤ ENNReal.ofReal ρ ^ (-3 : ℝ) *
        (volume (vec3Ball x ρ) ^ (1 / 5 : ℝ) *
          cylinderPowerIntegral (6 / 5 : ℝ) F (x, t) ρ) ^ (5 / 6 : ℝ) :=
      mul_le_mul_right h _
    _ = ENNReal.ofReal (Real.pi * 4 / 3) ^ (1 / 6 : ℝ) *
        ENNReal.ofReal ρ ^ (5 / 3 - 5 / κ) *
          morreyCell (6 / 5 : ℝ) κ F (x, t) ρ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 5 / 6),
        ← ENNReal.rpow_mul,
        show (1 / 5 : ℝ) * (5 / 6) = 1 / 6 by norm_num,
        volume_vec3Ball_eq,
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 6),
        show (ENNReal.ofReal ρ) ^ (3 : ℕ) = ENNReal.ofReal ρ ^ (3 : ℝ) by norm_cast,
        ← ENNReal.rpow_mul]
      unfold morreyCell
      norm_num only [one_div_div]
      have hexp : (5 / 3 - 5 / κ) + (-(5 * (1 - (6 / 5 : ℝ) / κ) / (6 / 5))) =
          -3 + (3 : ℝ) * (1 / 6) := by ring
      have hp := congrArg (fun a : ℝ => ENNReal.ofReal ρ ^ a) hexp
      rw [ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hρ).ne' ENNReal.ofReal_ne_top,
        ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hρ).ne' ENNReal.ofReal_ne_top] at hp
      calc
        _ = ENNReal.ofReal (Real.pi * 4 / 3) ^ (1 / 6 : ℝ) *
            (ENNReal.ofReal ρ ^ (-3 : ℝ) * ENNReal.ofReal ρ ^ ((3 : ℝ) * (1 / 6))) *
              cylinderPowerIntegral (6 / 5 : ℝ) F (x, t) ρ ^ (5 / 6 : ℝ) := by
                norm_num only [show (3 : ℝ) * (1 / 6) = 1 / 2 by norm_num]
                ac_rfl
        _ = _ := by rw [← hp]; ac_rfl
    _ ≤ _ := mul_le_mul_right hc _

/-- The spatial slice norm agrees almost everywhere with its integral
formula, and is measurable as a function of time. -/
theorem pressure_source_slice_norm_aemeasurable
    {F : ParabolicPoint → ℝ} (hF : AEMeasurable F volume) (B : Set Vec3) :
    AEMeasurable (fun s : ℝ => eLpNorm (fun y : Vec3 => F (y, s))
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B)) volume := by
  have hprod : AEMeasurable F
      ((volume.restrict B).prod (volume : Measure ℝ)) := by
    have h : AEMeasurable F ((volume : Measure Vec3).prod (volume : Measure ℝ)) := by
      change AEMeasurable F (volume : Measure (Vec3 × ℝ))
      exact hF
    exact h.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hm := ((hprod.enorm.pow_const (6 / 5 : ℝ)).lintegral_prod_left').pow_const (5 / 6 : ℝ)
  apply hm.congr
  filter_upwards [hprod.aestronglyMeasurable.prodMk_right] with s hs
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofReal_ne_top hs]
  norm_num

/-- The time integral of a spatial slice norm over a cell window is
controlled by the source power integral on a larger cylinder. -/
theorem pressure_source_slice_norm_time_power_bound
    {F : ParabolicPoint → ℝ} (hF : AEMeasurable F volume)
    {x : Vec3} {t r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) :
    (∫⁻ s in Ioc (t - r ^ 2) t,
      eLpNorm (fun y : Vec3 => F (y, s)) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball x ρ)) ^ (6 / 5 : ℝ)) ≤
      cylinderPowerIntegral (6 / 5 : ℝ) F (x, t) ρ := by
  have hprod : AEMeasurable F
      ((volume.restrict (vec3Ball x ρ)).prod (volume : Measure ℝ)) := by
    have h : AEMeasurable F ((volume : Measure Vec3).prod (volume : Measure ℝ)) := by
      change AEMeasurable F (volume : Measure (Vec3 × ℝ))
      exact hF
    exact h.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hwin : Ioc (t - r ^ 2) t ⊆ Ioc (t - ρ ^ 2) t := by
    intro s hs
    exact ⟨lt_of_le_of_lt (sub_le_sub_left (pow_le_pow_left₀ hr.le hrρ 2) t) hs.1, hs.2⟩
  calc
    _ = ∫⁻ s in Ioc (t - r ^ 2) t,
        ∫⁻ y in vec3Ball x ρ, ‖F (y, s)‖ₑ ^ (6 / 5 : ℝ) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae hprod.aestronglyMeasurable.prodMk_right] with s hs
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofReal_ne_top hs]
      norm_num only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 / 5), one_div_div]
      rw [← ENNReal.rpow_mul]
      norm_num
    _ ≤ ∫⁻ s in Ioc (t - ρ ^ 2) t,
        ∫⁻ y in vec3Ball x ρ, ‖F (y, s)‖ₑ ^ (6 / 5 : ℝ) :=
      lintegral_mono' (Measure.restrict_mono_set volume hwin) (fun _ => le_rfl)
    _ = _ := by
      rw [cylinderPowerIntegral_eq_lintegral_slices (by norm_num) hF.restrict]
      simp only [Real.enorm_eq_ofReal_abs]

/-- Removing the Morrey normalization recovers the source's cell mass
with its exact positive radius power. -/
theorem pressure_source_cylinder_power_root_bound
    {κ : ℝ} (F : ParabolicPoint → ℝ) (z : ParabolicPoint)
    {ρ : ℝ} (hρ : 0 < ρ) :
    cylinderPowerIntegral (6 / 5 : ℝ) F z ρ ^ (5 / 6 : ℝ) ≤
      ENNReal.ofReal ρ ^ (25 / 6 - 5 / κ) * morreyNorm (6 / 5 : ℝ) κ F := by
  have hc : morreyCell (6 / 5 : ℝ) κ F z ρ ≤ morreyNorm (6 / 5 : ℝ) κ F :=
    le_iSup_of_le z (le_iSup_of_le ⟨ρ, hρ⟩ le_rfl)
  have hid : ENNReal.ofReal ρ ^ (25 / 6 - 5 / κ) * morreyCell (6 / 5 : ℝ) κ F z ρ =
      cylinderPowerIntegral (6 / 5 : ℝ) F z ρ ^ (5 / 6 : ℝ) := by
    unfold morreyCell
    norm_num only [one_div_div]
    rw [← mul_assoc, ← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hρ).ne' ENNReal.ofReal_ne_top]
    have he : (25 / 6 - 5 / κ) + -(5 * (1 - (6 / 5 : ℝ) / κ) / (6 / 5)) = 0 := by ring
    rw [he, ENNReal.rpow_zero, one_mul]
  rw [← hid]
  exact mul_le_mul_right hc _

end CKN.Core.Step4
