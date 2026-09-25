/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSWSSource

/-!
# Quantitative majorant for the centred source on a slice ball

This module controls the absolute spatial mean of one slice component by the
slice `L³` norm, and splits the centred source majorant of
`eq:pressure-gradient-decomposition` into a mixed velocity-gradient term, a quadratic
velocity term, and a localized force term, with explicit numerical constants.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- The absolute spatial mean of one component is controlled by the slice `L³` norm. -/
theorem ofReal_ball_average_abs_mul_rpow_le_eLpNorm
    {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {g : Vec3 → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (vec3Ball x ρ))) :
    ENNReal.ofReal (⨍ y in vec3Ball x ρ, |g y|) *
        volume (vec3Ball x ρ) ^ (1 / 3 : ℝ) ≤
      eLpNorm g 3 (volume.restrict (vec3Ball x ρ)) := by
  have htop : volume (vec3Ball x ρ) ≠ ⊤ :=
    (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top (x := x) (r := ρ)).ne
  have hne : volume (vec3Ball x ρ) ≠ 0 :=
    ne_of_gt (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_pos hρ)
  set W : ℝ≥0∞ := volume (vec3Ball x ρ) with hW
  have hWtop : W ≠ ⊤ := by rw [hW]; exact htop
  have hWne : W ≠ 0 := by rw [hW]; exact hne
  set a' : ℝ≥0∞ := eLpNorm g 3 (volume.restrict (vec3Ball x ρ)) with ha'
  have havg : ⨍ y in vec3Ball x ρ, |g y| =
      (W.toReal)⁻¹ * ∫ y in vec3Ball x ρ, |g y| := by
    rw [setAverage_eq, Measure.real_def, ← hW, smul_eq_mul]
  have hofReal : ENNReal.ofReal (⨍ y in vec3Ball x ρ, |g y|) =
      W⁻¹ * ENNReal.ofReal (∫ y in vec3Ball x ρ, |g y|) := by
    rw [havg, ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg),
      ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hWne hWtop),
      ENNReal.ofReal_toReal hWtop]
  have h1 : ENNReal.ofReal (∫ y in vec3Ball x ρ, |g y|) ≤
      ∫⁻ y in vec3Ball x ρ, ‖g y‖ₑ := by
    have h := enorm_integral_le_lintegral_enorm
      (μ := volume.restrict (vec3Ball x ρ)) (fun y : Vec3 => |g y|)
    simp only [Real.enorm_eq_ofReal_abs, abs_abs] at h
    refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
    simpa only [← Real.enorm_eq_ofReal_abs] using h
  have h2 : ∫⁻ y in vec3Ball x ρ, ‖g y‖ₑ =
      eLpNorm g 1 (volume.restrict (vec3Ball x ρ)) := by
    rw [eLpNorm_one_eq_lintegral_enorm hg]
  have h3 : eLpNorm g 1 (volume.restrict (vec3Ball x ρ)) ≤ a' * W ^ (2 / 3 : ℝ) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := volume.restrict (vec3Ball x ρ)) (p := (1 : ℝ≥0∞)) (q := (3 : ℝ≥0∞))
      (by norm_num) hg
    rw [show ((1 : ℝ≥0∞).toReal) = 1 by simp, show ((3 : ℝ≥0∞).toReal) = 3 by simp,
      show (1 : ℝ) / 1 - 1 / 3 = 2 / 3 by norm_num] at h
    simpa only [← hW, ← ha', Measure.restrict_apply_univ] using h
  have hA : ENNReal.ofReal (∫ y in vec3Ball x ρ, |g y|) ≤ a' * W ^ (2 / 3 : ℝ) :=
    h1.trans (h2.trans_le h3)
  have hsplit : W ^ (2 / 3 : ℝ) * W ^ (1 / 3 : ℝ) = W := by
    rw [← ENNReal.rpow_add (2 / 3 : ℝ) (1 / 3 : ℝ) hWne hWtop,
      show (2 / 3 : ℝ) + 1 / 3 = 1 by norm_num, ENNReal.rpow_one]
  have key : W⁻¹ * (a' * W ^ (2 / 3 : ℝ)) * W ^ (1 / 3 : ℝ) = a' := by
    calc W⁻¹ * (a' * W ^ (2 / 3 : ℝ)) * W ^ (1 / 3 : ℝ)
        = W⁻¹ * ((a' * W ^ (2 / 3 : ℝ)) * W ^ (1 / 3 : ℝ)) := mul_assoc _ _ _
      _ = W⁻¹ * (a' * (W ^ (2 / 3 : ℝ) * W ^ (1 / 3 : ℝ))) := by rw [mul_assoc]
      _ = W⁻¹ * (a' * W) := by rw [hsplit]
      _ = a' * (W⁻¹ * W) := mul_left_comm _ _ _
      _ = a' * 1 := by rw [ENNReal.inv_mul_cancel hWne hWtop]
      _ = a' := mul_one _
  rw [hofReal]
  exact (mul_le_mul_left (mul_le_mul_right hA W⁻¹) (W ^ (1 / 3 : ℝ))).trans_eq key

/-- The centred source majorant splits into a mixed term, a quadratic velocity
term and a force term, with explicit numerical coefficients. -/
theorem centredSWSCentredMajorant_le_three_terms
    {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ) (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (f : ParabolicPoint → Vec3) (s : ℝ)
    (hu : AEStronglyMeasurable (fun y => u (y, s)) (volume.restrict (vec3Ball x ρ))) :
    centredSWSCentredMajorant x ρ q u Du f s ≤
      18 * (eLpNorm (fun y => u (y, s)) 3 (volume.restrict (vec3Ball x ρ)) *
            eLpNorm (fun y => Du (y, s)) 2 (volume.restrict (vec3Ball x ρ))) +
      (18 * ENNReal.ofReal (cutoffGradientConstant / ρ) *
            volume (vec3Ball x ρ) ^ (1 / 6 : ℝ)) *
        eLpNorm (fun y => u (y, s)) 3 (volume.restrict (vec3Ball x ρ)) ^ (2 : ℝ) +
      (4 * volume (vec3Ball x ρ) ^ (5 / 6 - 1 / q : ℝ)) *
        eLpNorm (fun y => f (y, s)) (ENNReal.ofReal q) (volume.restrict (vec3Ball x ρ)) := by
  have hWtop : volume (vec3Ball x ρ) ≠ ⊤ :=
    (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top (x := x) (r := ρ)).ne
  have hWne : volume (vec3Ball x ρ) ≠ 0 :=
    ne_of_gt (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_pos hρ)
  rw [centredSWSCentredMajorant, centredSWSUncentredMajorant]
  simp only [Measure.restrict_apply_univ]
  set W : ℝ≥0∞ := volume (vec3Ball x ρ) with hW
  set a : ℝ≥0∞ := eLpNorm (fun y => u (y, s)) 3 (volume.restrict (vec3Ball x ρ)) with ha
  set d : ℝ≥0∞ := eLpNorm (fun y => Du (y, s)) 2 (volume.restrict (vec3Ball x ρ)) with hd
  set F : ℝ≥0∞ := eLpNorm (fun y => f (y, s)) (ENNReal.ofReal q) (volume.restrict (vec3Ball x ρ))
    with hF
  set c : ℝ≥0∞ := ENNReal.ofReal (cutoffGradientConstant / ρ) with hc
  set S : ℝ≥0∞ := ENNReal.ofReal (∑ j : Fin 3, ⨍ y in vec3Ball x ρ, |u (y, s) j|) with hSdef
  have hWtop' : W ≠ ⊤ := by rw [hW]; exact hWtop
  have hWne' : W ≠ 0 := by rw [hW]; exact hWne
  have hcomp (j : Fin 3) :
      eLpNorm (fun y => u (y, s) j) 3 (volume.restrict (vec3Ball x ρ)) ≤ a := by
    rw [ha]
    exact eLpNorm_mono_ae ((continuous_apply j).comp_aestronglyMeasurable hu)
      (Filter.Eventually.of_forall fun y => norm_le_pi_norm (u (y, s)) j)
  have hsum_eq : S = ∑ j : Fin 3, ENNReal.ofReal (⨍ y in vec3Ball x ρ, |u (y, s) j|) := by
    rw [hSdef]
    exact ENNReal.ofReal_sum_of_nonneg (fun j _ =>
      CKN.Foundation.Parabolic.Integration.setAverage_nonneg_of_ae
        (Filter.Eventually.of_forall fun y => abs_nonneg _))
  have hS : S * W ^ (1 / 3 : ℝ) ≤ 3 * a := by
    rw [hsum_eq, Finset.sum_mul]
    calc ∑ j : Fin 3, ENNReal.ofReal (⨍ y in vec3Ball x ρ, |u (y, s) j|) * W ^ (1 / 3 : ℝ)
        ≤ ∑ j : Fin 3,
            eLpNorm (fun y => u (y, s) j) 3 (volume.restrict (vec3Ball x ρ)) := by
          apply Finset.sum_le_sum
          intro j _
          exact ofReal_ball_average_abs_mul_rpow_le_eLpNorm hρ
            ((continuous_apply j).comp_aestronglyMeasurable hu)
      _ ≤ ∑ _j : Fin 3, a := by
          apply Finset.sum_le_sum
          intro j _
          exact hcomp j
      _ = 3 * a := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  have hsplit12 : W ^ (1 / 2 : ℝ) = W ^ (1 / 6 : ℝ) * W ^ (1 / 3 : ℝ) := by
    rw [← ENNReal.rpow_add (1 / 6 : ℝ) (1 / 3 : ℝ) hWne' hWtop',
      show (1 / 6 : ℝ) + 1 / 3 = 1 / 2 by norm_num]
  have hSmid : S * W ^ (1 / 2 : ℝ) ≤ 3 * a * W ^ (1 / 6 : ℝ) := by
    calc S * W ^ (1 / 2 : ℝ) = (S * W ^ (1 / 3 : ℝ)) * W ^ (1 / 6 : ℝ) := by
          rw [hsplit12]; ring
      _ ≤ (3 * a) * W ^ (1 / 6 : ℝ) := by gcongr
  have hsum3 : (∑ _j : Fin 3, (d * W ^ (1 / 3 : ℝ) + c * (a * W ^ (1 / 2 : ℝ))))
      = 3 * (d * W ^ (1 / 3 : ℝ) + c * (a * W ^ (1 / 2 : ℝ))) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hX : S * (d * W ^ (1 / 3 : ℝ)) ≤ 3 * (d * a) := by
    calc S * (d * W ^ (1 / 3 : ℝ)) = d * (S * W ^ (1 / 3 : ℝ)) := by ring
      _ ≤ d * (3 * a) := by gcongr
      _ = 3 * (d * a) := by ring
  have hY : S * (c * (a * W ^ (1 / 2 : ℝ))) ≤ 3 * (c * (a * a * W ^ (1 / 6 : ℝ))) := by
    calc S * (c * (a * W ^ (1 / 2 : ℝ))) = c * a * (S * W ^ (1 / 2 : ℝ)) := by ring
      _ ≤ c * a * (3 * a * W ^ (1 / 6 : ℝ)) := by gcongr
      _ = 3 * (c * (a * a * W ^ (1 / 6 : ℝ))) := by ring
  have hM : S * (∑ _j : Fin 3, (d * W ^ (1 / 3 : ℝ) + c * (a * W ^ (1 / 2 : ℝ)))) ≤
      9 * (d * a) + 9 * (c * (a * a * W ^ (1 / 6 : ℝ))) := by
    rw [hsum3]
    calc S * (3 * (d * W ^ (1 / 3 : ℝ) + c * (a * W ^ (1 / 2 : ℝ))))
        = 3 * (S * (d * W ^ (1 / 3 : ℝ))) + 3 * (S * (c * (a * W ^ (1 / 2 : ℝ)))) := by ring
      _ ≤ 3 * (3 * (d * a)) + 3 * (3 * (c * (a * a * W ^ (1 / 6 : ℝ)))) :=
            add_le_add (mul_le_mul_right hX 3) (mul_le_mul_right hY 3)
      _ = 9 * (d * a) + 9 * (c * (a * a * W ^ (1 / 6 : ℝ))) := by ring
  have hU : 3 * (3 * (d * a + c * (a * a * W ^ (1 / 6 : ℝ))) + F * W ^ (5 / 6 - 1 / q : ℝ)) ≤
      9 * (d * a) + 9 * (c * (a * a * W ^ (1 / 6 : ℝ))) + 3 * (F * W ^ (5 / 6 - 1 / q : ℝ)) :=
    le_of_eq (by ring)
  have hfinal : (9 * (d * a) + 9 * (c * (a * a * W ^ (1 / 6 : ℝ))) +
          3 * (F * W ^ (5 / 6 - 1 / q : ℝ))) +
        (9 * (d * a) + 9 * (c * (a * a * W ^ (1 / 6 : ℝ)))) + F * W ^ (5 / 6 - 1 / q : ℝ) ≤
      18 * (a * d) + (18 * c * W ^ (1 / 6 : ℝ)) * a ^ (2 : ℝ) +
        (4 * W ^ (5 / 6 - 1 / q : ℝ)) * F :=
    le_of_eq (by
      rw [show a * a = a ^ (2 : ℝ) by rw [ENNReal.rpow_two, sq]]
      ring)
  exact (add_le_add (add_le_add hU hM) le_rfl).trans hfinal

end CKN.Core.Step4
