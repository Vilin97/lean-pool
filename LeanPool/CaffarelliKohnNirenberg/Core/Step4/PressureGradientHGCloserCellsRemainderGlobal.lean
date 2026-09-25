/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsRemainder

/-! # Uniform Morrey bounds for spatially bounded remainders

Finite spatial support controls large cells, while the spatial volume of a
cell controls small cells. Together these estimates give a finite Morrey
seminorm from an `L^{3/2}` temporal bound on the spatial supremum.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

/-- Finite spatial support replaces the cell's spatial volume in the
power-integral estimate. -/
theorem pressure_remainder_supported_cylinder_power_bound
    {F : ParabolicPoint → ℝ} {H : ℝ → ℝ≥0∞} {S : Set Vec3}
    (hF : AEMeasurable F volume) (hH : AEMeasurable H volume)
    (hS : MeasurableSet S)
    (hsupport : ∀ x ∉ S, ∀ t : ℝ, F (x, t) = 0)
    (hbound : ∀ᵐ s ∂volume, ∀ x : Vec3, ‖F (x, s)‖ₑ ≤ H s)
    {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    cylinderPowerIntegral (6 / 5 : ℝ) F (x, t) r ≤
      volume S * (∫⁻ s, H s ^ (3 / 2 : ℝ)) ^ (4 / 5 : ℝ) *
        ENNReal.ofReal r ^ (2 / 5 : ℝ) := by
  rw [cylinderPowerIntegral_eq_lintegral_slices (by norm_num)
    (hF.mono_measure Measure.restrict_le_self)]
  have hstep : (∫⁻ s in Ioc (t - r ^ 2) t,
      ∫⁻ y in vec3Ball x r, ENNReal.ofReal |F (y, s)| ^ (6 / 5 : ℝ)) ≤
      ∫⁻ s in Ioc (t - r ^ 2) t, volume S * H s ^ (6 / 5 : ℝ) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_of_ae hbound] with s hs
    calc
      _ ≤ ∫⁻ y : Vec3, S.indicator (fun _ => H s ^ (6 / 5 : ℝ)) y := by
        apply lintegral_mono' Measure.restrict_le_self
        intro y
        change ENNReal.ofReal |F (y, s)| ^ (6 / 5 : ℝ) ≤ _
        by_cases hy : y ∈ S
        · rw [Set.indicator_of_mem hy, ← Real.enorm_eq_ofReal_abs]
          exact ENNReal.rpow_le_rpow (hs y) (by norm_num)
        · rw [Set.indicator_of_notMem hy, hsupport y hy s]
          simp
      _ = _ := by
        rw [lintegral_indicator hS, lintegral_const,
          Measure.restrict_apply_univ, mul_comm]
  calc
    _ ≤ ∫⁻ s in Ioc (t - r ^ 2) t, volume S * H s ^ (6 / 5 : ℝ) := hstep
    _ = volume S * ∫⁻ s in Ioc (t - r ^ 2) t, H s ^ (6 / 5 : ℝ) :=
      lintegral_const_mul'' _
        ((hH.mono_measure Measure.restrict_le_self).pow_const _)
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_right (pressure_remainder_time_power_bound hH (t := t) hr) _

/-- The supported estimate after normalization, useful for cells of radius
at least one. -/
theorem pressure_remainder_supported_morreyCell_bound
    {κ : ℝ} {F : ParabolicPoint → ℝ} {H : ℝ → ℝ≥0∞} {S : Set Vec3}
    (hF : AEMeasurable F volume) (hH : AEMeasurable H volume)
    (hS : MeasurableSet S)
    (hsupport : ∀ x ∉ S, ∀ t : ℝ, F (x, t) = 0)
    (hbound : ∀ᵐ s ∂volume, ∀ x : Vec3, ‖F (x, s)‖ₑ ≤ H s)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    morreyCell (6 / 5 : ℝ) κ F z r ≤
      volume S ^ (5 / 6 : ℝ) * (∫⁻ s, H s ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
        ENNReal.ofReal r ^ (5 / κ - 23 / 6) := by
  have hm := pressure_remainder_supported_cylinder_power_bound
    hF hH hS hsupport hbound (x := z.1) (t := z.2) hr
  unfold morreyCell
  have hn := ENNReal.rpow_le_rpow hm (by norm_num : (0 : ℝ) ≤ 5 / 6)
  calc
    _ ≤ ENNReal.ofReal r ^ (-(5 * (1 - (6 / 5 : ℝ) / κ) / (6 / 5))) *
        (volume S * (∫⁻ s, H s ^ (3 / 2 : ℝ)) ^ (4 / 5 : ℝ) *
          ENNReal.ofReal r ^ (2 / 5 : ℝ)) ^ (5 / 6 : ℝ) := by
      norm_num only [one_div_div]
      exact mul_le_mul_right hn _
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 5 / 6),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 5 / 6),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      rw [show (4 / 5 : ℝ) * (5 / 6) = 2 / 3 by norm_num]
      rw [show (5 / κ - 23 / 6 : ℝ) =
          -(5 * (1 - (6 / 5 : ℝ) / κ) / (6 / 5)) + (2 / 5) * (5 / 6) by ring,
        ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top]
      ring

/-- All cell radii are controlled by a single explicit constant. -/
theorem pressure_remainder_morreyNorm_bound
    {κ : ℝ} (hκlo : 3 / 2 ≤ κ) (hκhi : κ ≤ 25 / 9)
    {F : ParabolicPoint → ℝ} {H : ℝ → ℝ≥0∞} {S : Set Vec3}
    (hF : AEMeasurable F volume) (hH : AEMeasurable H volume)
    (hS : MeasurableSet S)
    (hsupport : ∀ x ∉ S, ∀ t : ℝ, F (x, t) = 0)
    (hbound : ∀ᵐ s ∂volume, ∀ x : Vec3, ‖F (x, s)‖ₑ ≤ H s) :
    morreyNorm (6 / 5 : ℝ) κ F ≤
      (ENNReal.ofReal (Real.pi * 4 / 3) ^ (5 / 6 : ℝ) + volume S ^ (5 / 6 : ℝ)) *
        (∫⁻ s, H s ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
  have hκ : 0 < κ := lt_of_lt_of_le (by norm_num) hκlo
  have hsmall : 0 ≤ 5 / κ - 4 / 3 := by
    have h := (le_div_iff₀ hκ).mpr (show (9 / 5 : ℝ) * κ ≤ 5 by
      nlinarith only [hκhi])
    linarith only [h]
  have hlarge : 5 / κ - 23 / 6 < 0 := by
    have h := (div_le_iff₀ hκ).mpr (show (5 : ℝ) ≤ (10 / 3) * κ by
      nlinarith only [hκlo])
    linarith only [h]
  unfold morreyNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  obtain ⟨r, hr⟩ := r
  by_cases hr1 : r ≤ 1
  · have hp : ENNReal.ofReal r ^ (5 / κ - 4 / 3) ≤ 1 :=
      ENNReal.rpow_le_one (by simpa using ENNReal.ofReal_le_ofReal hr1) hsmall
    have hb := pressure_remainder_morreyCell_bound (κ := κ) hF hH hbound (z := z) hr
    calc
      _ ≤ _ := hb
      _ ≤ ENNReal.ofReal (Real.pi * 4 / 3) ^ (5 / 6 : ℝ) *
          (∫⁻ s, H s ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
        simpa only [mul_one] using mul_le_mul_right hp
          (ENNReal.ofReal (Real.pi * 4 / 3) ^ (5 / 6 : ℝ) *
            (∫⁻ s, H s ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ))
      _ ≤ _ := mul_le_mul_left le_self_add _
  · have hp : ENNReal.ofReal r ^ (5 / κ - 23 / 6) ≤ 1 :=
      ENNReal.rpow_le_one_of_one_le_of_neg
        (by simpa using ENNReal.ofReal_le_ofReal (le_of_not_ge hr1)) hlarge
    have hb := pressure_remainder_supported_morreyCell_bound
      (κ := κ) hF hH hS hsupport hbound (z := z) hr
    calc
      _ ≤ _ := hb
      _ ≤ volume S ^ (5 / 6 : ℝ) *
          (∫⁻ s, H s ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
        simpa only [mul_one] using mul_le_mul_right hp
          (volume S ^ (5 / 6 : ℝ) * (∫⁻ s, H s ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ))
      _ ≤ _ := mul_le_mul_left le_add_self _

/-- The spatially supported remainder has finite Morrey seminorm whenever
its temporal supremum belongs to `L^{3/2}`. -/
theorem pressure_remainder_morreyNorm_lt_top
    {κ : ℝ} (hκlo : 3 / 2 ≤ κ) (hκhi : κ ≤ 25 / 9)
    {F : ParabolicPoint → ℝ} {H : ℝ → ℝ≥0∞} {S : Set Vec3}
    (hF : AEMeasurable F volume) (hH : AEMeasurable H volume)
    (hS : MeasurableSet S) (hSfinite : volume S < ⊤)
    (hsupport : ∀ x ∉ S, ∀ t : ℝ, F (x, t) = 0)
    (hbound : ∀ᵐ s ∂volume, ∀ x : Vec3, ‖F (x, s)‖ₑ ≤ H s)
    (hHfinite : (∫⁻ s, H s ^ (3 / 2 : ℝ)) < ⊤) :
    morreyNorm (6 / 5 : ℝ) κ F < ⊤ := by
  apply (pressure_remainder_morreyNorm_bound hκlo hκhi hF hH hS hsupport hbound).trans_lt
  apply ENNReal.mul_lt_top
  · apply ENNReal.add_lt_top.mpr
    constructor
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hSfinite.ne
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hHfinite.ne

/-- A measurable restriction to a finite spatial carrier has finite Morrey
seminorm under a temporal bound on its spatial supremum. -/
theorem pressure_remainder_indicator_morreyNorm_lt_top
    {κ : ℝ} (hκlo : 3 / 2 ≤ κ) (hκhi : κ ≤ 25 / 9)
    {F : ParabolicPoint → ℝ} {H : ℝ → ℝ≥0∞}
    {A : Set ParabolicPoint} {S : Set Vec3}
    (hA : MeasurableSet A) (hAS : ∀ z ∈ A, z.1 ∈ S)
    (hF : AEMeasurable F (volume.restrict A)) (hH : AEMeasurable H volume)
    (hS : MeasurableSet S) (hSfinite : volume S < ⊤)
    (hbound : ∀ᵐ s ∂volume, ∀ x : Vec3, (x, s) ∈ A → ‖F (x, s)‖ₑ ≤ H s)
    (hHfinite : (∫⁻ s, H s ^ (3 / 2 : ℝ)) < ⊤) :
    morreyNorm (6 / 5 : ℝ) κ (A.indicator F) < ⊤ := by
  apply pressure_remainder_morreyNorm_lt_top hκlo hκhi
    ((aemeasurable_indicator_iff hA).mpr hF) hH hS hSfinite
  · intro x hx t
    exact Set.indicator_of_notMem (fun hz => hx (hAS (x, t) hz)) F
  · filter_upwards [hbound] with s hs
    intro x
    by_cases hx : (x, s) ∈ A
    · rw [Set.indicator_of_mem (α := ParabolicPoint) hx]
      exact hs x hx
    · rw [Set.indicator_of_notMem (α := ParabolicPoint) hx]
      simp
  · exact hHfinite

end CKN.Core.Step4
