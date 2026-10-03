/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellProducerSlice
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # Cell estimates for spatially bounded pressure remainders

A spatial supremum controlled in `L^{3/2}` in time gives the cell-radius
power needed for the harmonic part of the pressure gradient. The temporal
Hölder factor is retained explicitly before the Morrey normalization.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

/-- Temporal Hölder on a cell window produces the factor `r^{2/5}` for the
`6/5` power integral of a function controlled in `L^{3/2}` in time. -/
theorem pressure_remainder_time_power_bound
    {H : ℝ → ℝ≥0∞} (hH : AEMeasurable H volume)
    {t r : ℝ} (hr : 0 < r) :
    (∫⁻ s in Ioc (t - r ^ 2) t, H s ^ (6 / 5 : ℝ)) ≤
      (∫⁻ s, H s ^ (3 / 2 : ℝ)) ^ (4 / 5 : ℝ) *
        ENNReal.ofReal r ^ (2 / 5 : ℝ) := by
  let μ : Measure ℝ := volume.restrict (Ioc (t - r ^ 2) t)
  have hHolder : (5 / 4 : ℝ).HolderConjugate 5 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hHolder
    ((hH.mono_measure Measure.restrict_le_self).pow_const (6 / 5 : ℝ))
    (aemeasurable_const : AEMeasurable (fun _ : ℝ => (1 : ℝ≥0∞)) μ)
  have hpow : ∀ s, (H s ^ (6 / 5 : ℝ)) ^ (5 / 4 : ℝ) =
      H s ^ (3 / 2 : ℝ) := by
    intro s
    rw [← ENNReal.rpow_mul]
    norm_num
  simp only [Pi.mul_apply, mul_one, hpow, ENNReal.one_rpow,
    lintegral_const, one_mul] at h
  have hμ : μ Set.univ = ENNReal.ofReal r ^ (2 : ℝ) := by
    simp only [μ, Measure.restrict_apply_univ, Real.volume_Ioc]
    rw [sub_sub_cancel, ENNReal.ofReal_pow hr.le]
    norm_num
  have hsmall : (∫⁻ s, H s ^ (3 / 2 : ℝ) ∂μ) ≤
      ∫⁻ s, H s ^ (3 / 2 : ℝ) :=
    lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
  calc
    _ ≤ (∫⁻ s, H s ^ (3 / 2 : ℝ) ∂μ) ^ (1 / (5 / 4 : ℝ)) *
        μ Set.univ ^ (1 / (5 : ℝ)) := h
    _ ≤ (∫⁻ s, H s ^ (3 / 2 : ℝ)) ^ (4 / 5 : ℝ) *
        μ Set.univ ^ (1 / (5 : ℝ)) := by
      norm_num
      exact mul_le_mul_left (ENNReal.rpow_le_rpow hsmall (by norm_num : (0 : ℝ) ≤ 4 / 5)) _
    _ = _ := by
      rw [hμ, ← ENNReal.rpow_mul]
      norm_num

/-- A spatial bound on almost every time slice gives a power-integral
estimate on every cylinder, with its full spatial volume factor. -/
theorem pressure_remainder_cylinder_power_bound
    {F : ParabolicPoint → ℝ} {H : ℝ → ℝ≥0∞}
    (hF : AEMeasurable F volume) (hH : AEMeasurable H volume)
    (hbound : ∀ᵐ s ∂volume, ∀ x : Vec3, ‖F (x, s)‖ₑ ≤ H s)
    {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    cylinderPowerIntegral (6 / 5 : ℝ) F (x, t) r ≤
      volume (vec3Ball x r) *
        (∫⁻ s, H s ^ (3 / 2 : ℝ)) ^ (4 / 5 : ℝ) *
          ENNReal.ofReal r ^ (2 / 5 : ℝ) := by
  rw [cylinderPowerIntegral_eq_lintegral_slices (by norm_num)
    (hF.mono_measure Measure.restrict_le_self)]
  have hstep : (∫⁻ s in Ioc (t - r ^ 2) t,
      ∫⁻ y in vec3Ball x r, ENNReal.ofReal |F (y, s)| ^ (6 / 5 : ℝ)) ≤
      ∫⁻ s in Ioc (t - r ^ 2) t,
        volume (vec3Ball x r) * H s ^ (6 / 5 : ℝ) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_of_ae hbound] with s hs
    calc
      _ ≤ ∫⁻ _y in vec3Ball x r, H s ^ (6 / 5 : ℝ) := by
        apply lintegral_mono
        intro y
        change ENNReal.ofReal |F (y, s)| ^ (6 / 5 : ℝ) ≤ H s ^ (6 / 5 : ℝ)
        rw [← Real.enorm_eq_ofReal_abs]
        exact ENNReal.rpow_le_rpow (hs y) (by norm_num)
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]
  calc
    _ ≤ ∫⁻ s in Ioc (t - r ^ 2) t,
        volume (vec3Ball x r) * H s ^ (6 / 5 : ℝ) := hstep
    _ = volume (vec3Ball x r) *
        ∫⁻ s in Ioc (t - r ^ 2) t, H s ^ (6 / 5 : ℝ) :=
      lintegral_const_mul'' _
        ((hH.mono_measure Measure.restrict_le_self).pow_const _)
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_right (pressure_remainder_time_power_bound hH (t := t) hr) _

/-- The normalized cell estimate for a spatially bounded remainder. Its
radius exponent is positive throughout the pressure-gradient bootstrap range. -/
theorem pressure_remainder_morreyCell_bound
    {κ : ℝ} {F : ParabolicPoint → ℝ} {H : ℝ → ℝ≥0∞}
    (hF : AEMeasurable F volume) (hH : AEMeasurable H volume)
    (hbound : ∀ᵐ s ∂volume, ∀ x : Vec3, ‖F (x, s)‖ₑ ≤ H s)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    morreyCell (6 / 5 : ℝ) κ F z r ≤
      ENNReal.ofReal (Real.pi * 4 / 3) ^ (5 / 6 : ℝ) *
        (∫⁻ s, H s ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
          ENNReal.ofReal r ^ (5 / κ - 4 / 3) := by
  have hmass := pressure_remainder_cylinder_power_bound hF hH hbound
    (x := z.1) (t := z.2) hr
  rw [volume_vec3Ball_eq] at hmass
  have hm : cylinderPowerIntegral (6 / 5 : ℝ) F z r ≤
      ENNReal.ofReal (Real.pi * 4 / 3) *
        (∫⁻ s, H s ^ (3 / 2 : ℝ)) ^ (4 / 5 : ℝ) *
          ENNReal.ofReal r ^ (17 / 5 : ℝ) := by
    refine hmass.trans_eq ?_
    rw [show (ENNReal.ofReal r) ^ (3 : ℕ) =
        ENNReal.ofReal r ^ (3 : ℝ) by norm_cast]
    rw [show (17 / 5 : ℝ) = 3 + 2 / 5 by norm_num,
      ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top]
    ring
  unfold morreyCell
  have hnorm := ENNReal.rpow_le_rpow hm (by norm_num : (0 : ℝ) ≤ 5 / 6)
  calc
    _ ≤ ENNReal.ofReal r ^ (-(5 * (1 - (6 / 5 : ℝ) / κ) / (6 / 5))) *
        (ENNReal.ofReal (Real.pi * 4 / 3) *
          (∫⁻ s, H s ^ (3 / 2 : ℝ)) ^ (4 / 5 : ℝ) *
            ENNReal.ofReal r ^ (17 / 5 : ℝ)) ^ (5 / 6 : ℝ) := by
      norm_num only [one_div_div]
      exact mul_le_mul_right hnorm _
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 5 / 6),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 5 / 6),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      have hpow : (4 / 5 : ℝ) * (5 / 6) = 2 / 3 := by norm_num
      rw [hpow]
      rw [show (5 / κ - 4 / 3 : ℝ) =
          -(5 * (1 - (6 / 5 : ℝ) / κ) / (6 / 5)) + (17 / 5) * (5 / 6) by ring,
        ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top]
      ring

end CKN.Core.Step4
