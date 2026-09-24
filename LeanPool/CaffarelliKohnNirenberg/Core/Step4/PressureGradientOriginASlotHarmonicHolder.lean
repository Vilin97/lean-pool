/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average

/-!
# Hölder below exponent one and its slice-then-time form

This module records two measure-theoretic inequalities in `ℝ≥0∞` that feed the
`A`-slot pressure-gradient estimate.

* `originASlot_lintegral_rpow_le` is Hölder's inequality for a single exponent `t`
  with `0 < t < 1`: it compares the `t`-power integral with the full integral times
  a power of the total mass.
* `originASlot_slice_time_rpow_bound` combines a spatial Hölder step with a temporal
  one: it controls the `6/5`-power of the space integral, integrated in time, by the
  product-measure integral of the `c`-power of the integrand, with the exponents
  dictated by the two applications of the first inequality.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- Hölder's inequality for an exponent `t` strictly between zero and one: the integral of
`g ^ t` is bounded by a power of the total mass times the `t`-power of the integral of `g`. -/
theorem originASlot_lintegral_rpow_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (∫⁻ y, g y ^ t ∂μ) ≤ μ Set.univ ^ (1 - t) * (∫⁻ y, g y ∂μ) ^ t := by
  have ht0' : t ≠ 0 := ne_of_gt ht0
  have hpq : Real.HolderConjugate (1 / t) (1 / (1 - t)) := by
    constructor
    · rw [one_div, inv_inv, one_div, inv_inv, inv_one]
      ring
    · exact one_div_pos.mpr ht0
    · exact one_div_pos.mpr (sub_pos.mpr ht1)
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
      (hg.pow_const t) (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one] at h
  have hR1 : (∫⁻ a, (g a ^ t) ^ (1 / t) ∂μ) = ∫⁻ a, g a ∂μ := by
    apply lintegral_congr
    intro a
    rw [← ENNReal.rpow_mul, mul_one_div_cancel ht0', ENNReal.rpow_one]
  have hR2 : (1 : ℝ) / (1 / t) = t := by rw [one_div_one_div]
  have hR3 : (∫⁻ a, (1 : ℝ≥0∞) ^ (1 / (1 - t)) ∂μ) = μ Set.univ := by simp
  have hR4 : (1 : ℝ) / (1 / (1 - t)) = 1 - t := by rw [one_div_one_div]
  rw [hR1, hR2, hR3, hR4] at h
  exact h.trans (le_of_eq (mul_comm _ _))

/-- The slice-then-time Hölder bound: the `6/5`-power of the spatial integral of `G ^ a`,
integrated over the time window, is bounded by powers of the spatial and temporal volumes
times the `6a/(5c)`-power of the product-measure integral of `G ^ c`. -/
theorem originASlot_slice_time_rpow_bound
    {B : Set Vec3} {W : Set ℝ} {G : Vec3 × ℝ → ℝ≥0∞}
    (hG : AEMeasurable G ((volume.restrict B).prod (volume.restrict W)))
    {a c : ℝ} (ha : 0 < a) (hac : 6 * a < 5 * c) :
    (∫⁻ s in W, (∫⁻ y in B, G (y, s) ^ a) ^ (6 / 5 : ℝ)) ≤
      volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) * volume W ^ (1 - 6 * a / (5 * c)) *
        (∫⁻ w in B ×ˢ W, G w ^ c) ^ (6 * a / (5 * c)) := by
  have hc0 : 0 < c := by nlinarith only [ha, hac]
  have hlt : a < c := by nlinarith only [ha, hac]
  have ht_pos : 0 < a / c := div_pos ha hc0
  have ht_lt_one : a / c < 1 := (div_lt_one hc0).mpr hlt
  set t : ℝ := 6 * a / (5 * c) with ht_def
  have ht0 : 0 < t := by
    rw [ht_def]; exact div_pos (by linarith only [ha]) (by linarith only [hc0])
  have ht1 : t < 1 := by
    rw [ht_def]
    exact (div_lt_one (by linarith only [hc0] : (0 : ℝ) < 5 * c)).mpr hac
  have hspat_ae : ∀ᵐ s ∂(volume.restrict W),
      (∫⁻ y in B, G (y, s) ^ a) ≤
        volume B ^ (1 - a / c) * (∫⁻ y in B, G (y, s) ^ c) ^ (a / c) := by
    filter_upwards [hG.aestronglyMeasurable.prodMk_right] with s hs
    have hle := originASlot_lintegral_rpow_le (volume.restrict B)
      (hs.aemeasurable.pow_const c) ht_pos ht_lt_one
    rw [Measure.restrict_apply_univ] at hle
    have heq : (∫⁻ y, (G (y, s) ^ c) ^ (a / c) ∂(volume.restrict B))
        = ∫⁻ y in B, G (y, s) ^ a := by
      apply lintegral_congr
      intro y
      rw [← ENNReal.rpow_mul, mul_div_cancel₀ a (ne_of_gt hc0)]
    rw [heq] at hle
    exact hle
  have hH_meas : AEMeasurable (fun s => ∫⁻ y in B, G (y, s) ^ c) (volume.restrict W) :=
    (hG.pow_const c).lintegral_prod_left'
  have hstep_ae : ∀ᵐ s ∂(volume.restrict W),
      (∫⁻ y in B, G (y, s) ^ a) ^ (6 / 5 : ℝ) ≤
        volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) *
          (∫⁻ y in B, G (y, s) ^ c) ^ t := by
    filter_upwards [hspat_ae] with s hs
    have h1 := ENNReal.rpow_le_rpow hs (by norm_num : (0 : ℝ) ≤ 6 / 5)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6 / 5)] at h1
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h1
    have e1 : (1 - a / c) * (6 / 5 : ℝ) = (6 / 5 : ℝ) * (1 - a / c) := by ring
    have e2 : (a / c) * (6 / 5 : ℝ) = t := by rw [ht_def]; field_simp
    rw [e1, e2] at h1
    exact h1
  have hmono : (∫⁻ s in W, (∫⁻ y in B, G (y, s) ^ a) ^ (6 / 5 : ℝ)) ≤
      ∫⁻ s in W, volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) *
        (∫⁻ y in B, G (y, s) ^ c) ^ t :=
    lintegral_mono_ae hstep_ae
  have hpull : (∫⁻ s in W, volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) *
        (∫⁻ y in B, G (y, s) ^ c) ^ t)
      = volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) *
        (∫⁻ s in W, (∫⁻ y in B, G (y, s) ^ c) ^ t) := by
    rw [lintegral_const_mul'' _ (hH_meas.pow_const t)]
  have htime : (∫⁻ s in W, (∫⁻ y in B, G (y, s) ^ c) ^ t) ≤
      volume W ^ (1 - t) * (∫⁻ s in W, ∫⁻ y in B, G (y, s) ^ c) ^ t := by
    have h := originASlot_lintegral_rpow_le (volume.restrict W) hH_meas ht0 ht1
    rwa [Measure.restrict_apply_univ] at h
  have hTonelli : (∫⁻ s in W, ∫⁻ y in B, G (y, s) ^ c) = ∫⁻ w in B ×ˢ W, G w ^ c := by
    rw [← lintegral_prod_symm _ (hG.pow_const c), Measure.prod_restrict]
    rfl
  calc
    (∫⁻ s in W, (∫⁻ y in B, G (y, s) ^ a) ^ (6 / 5 : ℝ))
        ≤ ∫⁻ s in W, volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) *
            (∫⁻ y in B, G (y, s) ^ c) ^ t := hmono
    _ = volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) *
          (∫⁻ s in W, (∫⁻ y in B, G (y, s) ^ c) ^ t) := hpull
    _ ≤ volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) *
          (volume W ^ (1 - t) * (∫⁻ s in W, ∫⁻ y in B, G (y, s) ^ c) ^ t) :=
        mul_le_mul' le_rfl htime
    _ = volume B ^ ((6 / 5 : ℝ) * (1 - a / c)) *
          (volume W ^ (1 - t) * (∫⁻ w in B ×ˢ W, G w ^ c) ^ t) := by rw [hTonelli]
    _ = _ := by rw [mul_assoc]

end CKN.Core.Step4
