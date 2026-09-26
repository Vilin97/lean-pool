/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.BootstrapPotential
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.PotentialMeasurability
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.AdamsAEMeasurable
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientMorrey

/-! # Morrey improvement from actual localized sources

The potential comparison uses almost-everywhere finiteness. Measurability
of the potential and finiteness of the explicit Adams constants are derived,
rather than supplied as extra inputs.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4

noncomputable section

namespace CKN.Core.Endgame

private theorem potential_majorant_morrey_of_aemeasurable
    {g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    (hgn : AEMeasurable (fun w => vec3EuclideanNorm (g w)) volume)
    (hhn : ∀ j, AEMeasurable (fun w => vec3EuclideanNorm (h j w)) volume)
    (hgN : morreyNorm (6 / 5) (25 / 11) (fun w => vec3EuclideanNorm (g w)) < ∞)
    (hhN : ∀ j, morreyNorm 3 (25 / 6) (fun w => vec3EuclideanNorm (h j w)) < ∞) :
    morreyNorm 3 25 (pointwisePotentialMajorant g h) < ∞ := by
  let P₂ : ParabolicPoint → ℝ := fun z =>
    (parabolicRieszPotential 2 (fun w => vec3EuclideanNorm (g w)) z).toReal
  let P₁ : Fin 3 → ParabolicPoint → ℝ := fun j z =>
    (parabolicRieszPotential 1 (fun w => vec3EuclideanNorm (h j w)) z).toReal
  have hP₂ : morreyNorm 3 25 P₂ < ∞ :=
    order_two_adams_lower_three_of_aemeasurable hgn hgN
  have hP₁ : ∀ j, morreyNorm 3 25 (P₁ j) < ∞ := fun j =>
    order_one_adams_lower_three_of_aemeasurable (hhn j) (hhN j)
  have hM₂ : AEMeasurable P₂ volume :=
    (measurable_riesz_potential_of_aemeasurable 2 hgn).ennreal_toReal.aemeasurable
  have hM₁ : ∀ j, AEMeasurable (P₁ j) volume := fun j =>
    (measurable_riesz_potential_of_aemeasurable 1 (hhn j)).ennreal_toReal.aemeasurable
  have hsum12 := (routeA_morreyNorm_add_le (hM₁ 1) (hM₁ 2)).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hP₁ 1, hP₁ 2⟩)
  have hsum : morreyNorm 3 25 (fun z => P₁ 0 z + (P₁ 1 z + P₁ 2 z)) < ∞ :=
    (routeA_morreyNorm_add_le (hM₁ 0) ((hM₁ 1).add (hM₁ 2))).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hP₁ 0, hsum12⟩)
  have hscaled₂ := routeA_morreyNorm_const_mul_finite (c := 3000) (by norm_num) hP₂
  have hscaled₁ := routeA_morreyNorm_const_mul_finite (c := 900000) (by norm_num) hsum
  have htotal := (routeA_morreyNorm_add_le (hM₂.const_mul (3000 : ℝ))
    (((hM₁ 0).add ((hM₁ 1).add (hM₁ 2))).const_mul (900000 : ℝ))).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hscaled₂, hscaled₁⟩)
  change morreyNorm 3 25 (fun z => 3000 * P₂ z + 900000 * ∑ j, P₁ j z) < ∞
  simpa [Fin.sum_univ_succ] using htotal

/-- The first velocity-exponent improvement follows from the real localized
source norms and representation, without all-point integrability assumptions. -/
theorem bootstrap_morrey_of_sources
    {v g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    {z₀ : ParabolicPoint} {R : ℝ} (hR : 0 < R)
    (hg : ∀ i, AEMeasurable (fun w => g w i) volume)
    (hh : ∀ j i, AEMeasurable (fun w => h j w i) volume)
    (hgN : morreyNorm (6 / 5) (25 / 11) (fun w => vec3EuclideanNorm (g w)) < ∞)
    (hhN : ∀ j, morreyNorm 3 (25 / 6) (fun w => vec3EuclideanNorm (h j w)) < ∞)
    (hgsupp : ∀ w ∉ parabolicCylinder z₀.1 z₀.2 R, g w = 0)
    (hhsupp : ∀ j w, w ∉ parabolicCylinder z₀.1 z₀.2 R → h j w = 0)
    (hrep : v =ᵐ[volume] duhamelPotential g h) :
    morreyNorm 3 25 (fun z => vec3EuclideanNorm (v z)) < ∞ := by
  have hgn := aemeasurable_euclidean_norm_of_components hg
  have hhn := fun j => aemeasurable_euclidean_norm_of_components (hh j)
  have hpoint := pointwisePotentialBound_ae_of_bootstrap_sources hR hg hh hgn hhn
    hgN hhN hgsupp hhsupp hrep
  have hmajorant := potential_majorant_morrey_of_aemeasurable hgn hhn hgN hhN
  apply lt_of_le_of_lt _ hmajorant
  apply routeA_morreyNorm_mono_ae (by norm_num)
  filter_upwards [hpoint] with z hz
  have hn : 0 ≤ pointwisePotentialMajorant g h z := by
    unfold pointwisePotentialMajorant
    positivity
  simpa only [abs_of_nonneg (vec3EuclideanNorm_nonneg _), abs_of_nonneg hn] using hz

end CKN.Core.Endgame
