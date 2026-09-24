/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsNormalization

/-! # Parabolic Morrey bounds for the spatial pressure Riesz operator

For a spatially supported source, finitely many annuli suffice at every
cell. The normalized bound is uniform in their number. It therefore bounds
the Morrey seminorm of any measurable representative of the slice operator.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

/-- The explicit constant in the parabolic Morrey bound for one spatial
Riesz component. -/
def pressureRieszMorreyConstant (κ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (czGradientComponentConstant rieszSecondWeakTypeConstant 1) *
      (2 : ℝ≥0∞) ^ (25 / 6 - 5 / κ) +
    ENNReal.ofReal (6912 * (4 * Real.pi)⁻¹) * ENNReal.ofReal (Real.pi * 4 / 3) *
      (4 : ℝ≥0∞) ^ (5 / 3 - 5 / κ) * (1 - (2 : ℝ≥0∞) ^ (-2 / 15 : ℝ))⁻¹

/-- The explicit component constant is finite. -/
theorem pressureRieszMorreyConstant_lt_top (κ : ℝ) : pressureRieszMorreyConstant κ < ⊤ := by
  unfold pressureRieszMorreyConstant
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)))
  · exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))))
      pressure_source_dyadic_constant_lt_top

private theorem exists_source_covering_radius
    {F : ParabolicPoint → ℝ} {L : ℝ}
    (hsupport : ∀ (y : Vec3) (s : ℝ), L < ‖y‖ → F (y, s) = 0)
    (x : Vec3) {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ s : ℝ,
      (vec3Ball x ((2 : ℝ) ^ N * (2 * r))).indicator (fun y => F (y, s)) =
        fun y => F (y, s) := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (3 * (L + ‖x‖) / (2 * r))
    (by norm_num : (1 : ℝ) < 2)
  have hrad : 3 * (L + ‖x‖) < (2 : ℝ) ^ N * (2 * r) :=
    (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * r)).mp hN
  refine ⟨N, fun s => ?_⟩
  funext y
  by_cases hy : y ∈ vec3Ball x ((2 : ℝ) ^ N * (2 * r))
  · exact Set.indicator_of_mem hy _
  · rw [Set.indicator_of_notMem hy]
    symm
    apply hsupport y s
    by_contra hnot
    have hyL : ‖y‖ ≤ L := le_of_not_gt hnot
    have hnorm : vec3EuclideanNorm (y - x) ≤ 3 * (L + ‖x‖) := by
      have h := euclideanNorm_le_three_mul_space_norm (y - x)
      change vec3EuclideanNorm (y - x) ≤ 3 * ‖y - x‖ at h
      exact h.trans (mul_le_mul_of_nonneg_left
        ((norm_sub_le y x).trans (add_le_add_left hyL _)) (by norm_num))
    exact hy (hnorm.trans_lt hrad)

/-- The canonical slice operator has the normalized time bound itself;
no choice of a jointly measurable representative is needed for this form. -/
theorem pressure_riesz_normalized_slice_time_bound
    (i j : Fin 3) {κ : ℝ} (hκ : 0 < κ) (hκhi : κ ≤ 25 / 9)
    {F : ParabolicPoint → ℝ} (hF : AEMeasurable F volume)
    (hFs : ∀ᵐ s ∂volume, MemLp (fun y : Vec3 => F (y, s))
      (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    {L : ℝ} (hsupport : ∀ (y : Vec3) (s : ℝ), L < ‖y‖ → F (y, s) = 0)
    (x : Vec3) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal r ^ (-(5 * (1 - (6 / 5 : ℝ) / κ) / (6 / 5))) *
      (∫⁻ s in Ioc (t - r ^ 2) t,
        eLpNorm (rieszSecondGradientExtensionOperator
          (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) (fun y => F (y, s)))
          (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball x r)) ^ (6 / 5 : ℝ)) ^
            (5 / 6 : ℝ) ≤
      pressureRieszMorreyConstant κ * morreyNorm (6 / 5 : ℝ) κ F := by
  obtain ⟨N, hN⟩ := exists_source_covering_radius hsupport x hr
  have h := pressure_riesz_finite_annuli_normalized_time_bound i j hκ hκhi hF hFs x t hr N
  simpa only [hN, pressureRieszMorreyConstant] using h

/-- The concrete spatial Riesz operator preserves the parabolic Morrey
seminorm in the pressure-gradient range, for a measurable representative
of its slice action and a spatially supported source. -/
theorem pressure_riesz_morreyNorm_bound
    (i j : Fin 3) {κ : ℝ} (hκ : 0 < κ) (hκhi : κ ≤ 25 / 9)
    {F T : ParabolicPoint → ℝ} (hF : AEMeasurable F volume)
    (hFs : ∀ᵐ s ∂volume, MemLp (fun y : Vec3 => F (y, s))
      (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    {L : ℝ} (hsupport : ∀ (y : Vec3) (s : ℝ), L < ‖y‖ → F (y, s) = 0)
    (hT : AEMeasurable T volume)
    (hident : ∀ᵐ s ∂volume, (fun y : Vec3 => T (y, s)) =ᵐ[volume]
      rieszSecondGradientExtensionOperator
        (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) (fun y => F (y, s))) :
    morreyNorm (6 / 5 : ℝ) κ T ≤
      pressureRieszMorreyConstant κ * morreyNorm (6 / 5 : ℝ) κ F := by
  refine iSup_le fun z => iSup_le fun r => ?_
  obtain ⟨N, hN⟩ := exists_source_covering_radius hsupport z.1 r.2
  have hmass : cylinderPowerIntegral (6 / 5 : ℝ) T z r.1 ≤
      ∫⁻ s in Ioc (z.2 - r.1 ^ 2) z.2,
        eLpNorm (rieszSecondGradientExtensionOperator
          (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j)
          ((vec3Ball z.1 ((2 : ℝ) ^ N * (2 * r.1))).indicator (fun y => F (y, s))))
          (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball z.1 r.1)) ^ (6 / 5 : ℝ) := by
    apply cylinderPowerIntegral_le_of_slice_eLpNorm (by norm_num) hT.restrict
    filter_upwards [ae_restrict_of_ae hident] with s hs
    rw [hN s]
    exact (eLpNorm_congr_ae (ae_restrict_of_ae hs)).le
  have hn := ENNReal.rpow_le_rpow hmass (by norm_num : (0 : ℝ) ≤ 5 / 6)
  have hfinal := pressure_riesz_finite_annuli_normalized_time_bound i j hκ hκhi
    hF hFs z.1 z.2 r.2 N
  unfold morreyCell
  norm_num only [one_div_div]
  exact (mul_le_mul_right hn _).trans hfinal

/-- Finite source Morrey seminorm gives finite Morrey seminorm of its
measurable concrete Riesz representative. -/
theorem pressure_riesz_morreyNorm_lt_top
    (i j : Fin 3) {κ : ℝ} (hκ : 0 < κ) (hκhi : κ ≤ 25 / 9)
    {F T : ParabolicPoint → ℝ} (hF : AEMeasurable F volume)
    (hFs : ∀ᵐ s ∂volume, MemLp (fun y : Vec3 => F (y, s))
      (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    {L : ℝ} (hsupport : ∀ (y : Vec3) (s : ℝ), L < ‖y‖ → F (y, s) = 0)
    (hT : AEMeasurable T volume)
    (hident : ∀ᵐ s ∂volume, (fun y : Vec3 => T (y, s)) =ᵐ[volume]
      rieszSecondGradientExtensionOperator
        (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) (fun y => F (y, s)))
    (hFnorm : morreyNorm (6 / 5 : ℝ) κ F < ⊤) :
    morreyNorm (6 / 5 : ℝ) κ T < ⊤ :=
  (pressure_riesz_morreyNorm_bound i j hκ hκhi hF hFs hsupport hT hident).trans_lt
    (ENNReal.mul_lt_top (pressureRieszMorreyConstant_lt_top κ) hFnorm)

/-- Restriction to a measurable spatial carrier preserves the concrete
Riesz bound when the selected representative agrees with the operator only
on that carrier and is zero outside it. -/
theorem pressure_riesz_restricted_morreyNorm_bound
    (i j : Fin 3) {κ : ℝ} (hκ : 0 < κ) (hκhi : κ ≤ 25 / 9)
    {F T : ParabolicPoint → ℝ} (hF : AEMeasurable F volume)
    (hFs : ∀ᵐ s ∂volume, MemLp (fun y : Vec3 => F (y, s))
      (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    {L : ℝ} (hsupport : ∀ (y : Vec3) (s : ℝ), L < ‖y‖ → F (y, s) = 0)
    {B : Set Vec3} (hB : MeasurableSet B)
    (hT : AEMeasurable T volume)
    (hTzero : ∀ (y : Vec3) (s : ℝ), y ∉ B → T (y, s) = 0)
    (hident : ∀ᵐ s ∂volume, (fun y : Vec3 => T (y, s)) =ᵐ[volume.restrict B]
      rieszSecondGradientExtensionOperator
        (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) (fun y => F (y, s))) :
    morreyNorm (6 / 5 : ℝ) κ T ≤
      pressureRieszMorreyConstant κ * morreyNorm (6 / 5 : ℝ) κ F := by
  refine iSup_le fun z => iSup_le fun r => ?_
  have hmass : cylinderPowerIntegral (6 / 5 : ℝ) T z r.1 ≤
      ∫⁻ s in Ioc (z.2 - r.1 ^ 2) z.2,
        eLpNorm (rieszSecondGradientExtensionOperator
          (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) (fun y => F (y, s)))
          (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball z.1 r.1)) ^ (6 / 5 : ℝ) := by
    apply cylinderPowerIntegral_le_of_slice_eLpNorm (by norm_num) hT.restrict
    filter_upwards [ae_restrict_of_ae hident] with s hs
    have hfull := (ae_eq_restrict_iff_indicator_ae_eq hB).mp hs
    have hzero : B.indicator (fun y : Vec3 => T (y, s)) = fun y => T (y, s) := by
      funext y
      by_cases hy : y ∈ B
      · exact Set.indicator_of_mem hy _
      · rw [Set.indicator_of_notMem hy, hTzero y s hy]
    rw [hzero] at hfull
    rw [eLpNorm_congr_ae (ae_restrict_of_ae hfull), eLpNorm_indicator_eq_eLpNorm_restrict hB]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hn := ENNReal.rpow_le_rpow hmass (by norm_num : (0 : ℝ) ≤ 5 / 6)
  have hfinal := pressure_riesz_normalized_slice_time_bound i j hκ hκhi hF hFs hsupport z.1 z.2 r.2
  unfold morreyCell
  norm_num only [one_div_div]
  exact (mul_le_mul_right hn _).trans hfinal

end CKN.Core.Step4
