/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedTimeBounds
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsSourceMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsRieszMorrey
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.AdamsBridge

/-! # Time bounds for localized pressure sources

The spatial `6/5` norm on a cell has a finite `6/5` time moment from
Morrey control. Intersecting the time window and spatial ball with carriers
preserves the estimate, with the explicit radius power `5 * (1 - (6/5)/κ)`.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean

namespace CKN.Core.Step4

/-- The clipped spatial slice norm obeys the exact Morrey radius growth. -/
theorem glued_clipped_slice_time_bound
    {F : ParabolicPoint → ℝ} {κ : ℝ} (hF : AEMeasurable F volume)
    (B : Set Vec3) (J : Set ℝ) (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    let W := Ioc (z.2 - r ^ 2) z.2 ∩ J
    let K := fun t => eLpNorm (fun x => F (x,t)) (ENNReal.ofReal (6/5 : ℝ))
      (volume.restrict (vec3Ball z.1 r ∩ B))
    AEMeasurable K (volume.restrict W) ∧
    (∫⁻ t in W, K t ^ (6/5 : ℝ)) ≤
      ENNReal.ofReal r ^ (5 * (1 - (6/5 : ℝ) / κ)) *
        morreyNorm (6/5 : ℝ) κ F ^ (6/5 : ℝ) := by
  dsimp only
  have hm : AEStronglyMeasurable F
      ((volume.restrict (vec3Ball z.1 r ∩ B)).prod
        (volume.restrict (Ioc (z.2 - r ^ 2) z.2 ∩ J))) := by
    rw [← originClauseRestrict_prod_eq]
    exact hF.restrict.aestronglyMeasurable
  obtain ⟨hmeas, heq⟩ := glued_slice_norm_power_integral (by norm_num : (0 : ℝ) < 6/5) hm
  refine ⟨hmeas, heq.le.trans ?_⟩
  have hsub : (vec3Ball z.1 r ∩ B) ×ˢ (Ioc (z.2 - r ^ 2) z.2 ∩ J) ⊆
      parabolicCylinder z.1 z.2 r := fun _ h => ⟨h.1.1, h.2.1⟩
  have hi := lintegral_mono_set (μ := volume) (f := fun w : ParabolicPoint => ‖F w‖ₑ ^ (6/5 : ℝ))
    hsub
  apply hi.trans
  simpa only [cylinderPowerIntegral, Real.enorm_eq_ofReal_abs] using
    (cylinderPowerIntegral_le_morreyNorm_pow (q := κ) (by norm_num) hF hr)

/-- A bounded cylindrical source with finite Morrey norm has full-space
`6/5` slices at almost every time. -/
theorem glued_supported_source_slice_memLp
    {F : ParabolicPoint → ℝ} {κ : ℝ} (hF : AEMeasurable F volume)
    (hN : morreyNorm (6 / 5 : ℝ) κ F < ⊤)
    {z₀ : ParabolicPoint} {R : ℝ} (hR : 0 < R)
    (hs : ∀ w ∉ parabolicCylinder z₀.1 z₀.2 R, F w = 0) :
    ∀ᵐ t ∂volume, MemLp (fun x : Vec3 => F (x,t))
      (ENNReal.ofReal (6/5 : ℝ)) volume := by
  have hm : AEStronglyMeasurable F ((volume : Measure Vec3).prod volume) :=
    hF.aestronglyMeasurable
  have hslice := glued_slice_norm_power_integral
    (B := Set.univ) (J := Set.univ) (by norm_num : (0 : ℝ) < 6/5)
    (by simpa only [Measure.restrict_univ] using hm)
  simp only [Measure.restrict_univ, univ_prod_univ] at hslice
  have heq : (parabolicCylinder z₀.1 z₀.2 R).indicator
      (fun w => ‖F w‖ₑ ^ (6/5 : ℝ)) = fun w => ‖F w‖ₑ ^ (6/5 : ℝ) := by
    funext w
    by_cases hw : w ∈ parabolicCylinder z₀.1 z₀.2 R
    · exact indicator_of_mem hw _
    · simp [indicator_of_notMem hw, hs w hw]
  have hmass : (∫⁻ w, ‖F w‖ₑ ^ (6/5 : ℝ)) < ⊤ := by
    rw [← heq, lintegral_indicator (measurableSet_parabolicCylinder _ _ _)]
    have hb := cylinderPowerIntegral_le_morreyNorm_pow (p := (6/5 : ℝ)) (q := κ) (z := z₀) (by
      norm_num) hF hR
    apply (show (∫⁻ w in parabolicCylinder z₀.1 z₀.2 R, ‖F w‖ₑ ^ (6/5 : ℝ)) ≤ _ from
      by simpa only [cylinderPowerIntegral, Real.enorm_eq_ofReal_abs] using hb).trans_lt
    exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
        (ENNReal.ofReal_pos.mpr hR).ne' ENNReal.ofReal_ne_top))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hN.ne)
  have hfin := ae_lt_top' (hslice.1.pow_const (6/5 : ℝ)) (hslice.2.trans_lt hmass).ne
  filter_upwards [hfin] with t ht
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 6/5)).mp ht

end CKN.Core.Step4
