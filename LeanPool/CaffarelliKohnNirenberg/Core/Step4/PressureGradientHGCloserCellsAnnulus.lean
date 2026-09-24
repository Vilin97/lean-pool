/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsRiesz
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-! # Exterior Riesz estimates for spatial annuli

An annulus outside twice the observation radius is separated from the
observation ball. The exterior formula for the concrete pressure operator
then supplies its inverse-cube source estimate.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

/-- A source restricted to a bounded spatial annulus has compact support. -/
theorem pressure_source_annulus_hasCompactSupport
    (G : Vec3 → ℝ) (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ) :
    HasCompactSupport ((vec3Ball x (2 * ρ) \ vec3Ball x ρ).indicator G) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closure_vec3Ball (x := x) (mul_pos (by norm_num : (0 : ℝ) < 2) hρ))
  intro y hy
  apply subset_closure
  by_contra hyB
  exact hy (Set.indicator_of_notMem (fun h => hyB h.1) G)

/-- The annular component of the concrete Riesz operator has a pointwise
bound on a smaller ball, with an explicit inverse-cube scale factor. -/
theorem pressure_riesz_annulus_enorm_bound
    (i j : Fin 3) {G : Vec3 → ℝ}
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (x : Vec3) {r ρ : ℝ} (hr : 0 < r) (hrρ : 2 * r ≤ ρ) :
    ∀ᵐ y ∂(volume.restrict (vec3Ball x r)),
      ‖rieszSecondGradientExtensionOperator
        (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j)
        ((vec3Ball x (2 * ρ) \ vec3Ball x ρ).indicator G) y‖ₑ ≤
      ENNReal.ofReal (6912 * (4 * Real.pi)⁻¹) * ENNReal.ofReal (2 * ρ) ^ (-3 : ℝ) *
        ∫⁻ z in vec3Ball x (2 * ρ), ‖G z‖ₑ := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by linarith only [hr]) hrρ
  let A : Set Vec3 := vec3Ball x (2 * ρ) \ vec3Ball x ρ
  have hA : MeasurableSet A := (vec3Ball_measurable _ _).diff (vec3Ball_measurable _ _)
  have hGA := hG.indicator hA
  have hGc := pressure_source_annulus_hasCompactSupport G x hρ
  have hsep : ∀ y ∈ vec3Ball x r, ∀ z ∈ A, ρ / 6 ≤ ‖y - z‖ := by
    intro y hy z hz
    have hyx : vec3EuclideanNorm (y - x) < r := hy
    have hzx : ρ ≤ vec3EuclideanNorm (z - x) := le_of_not_gt hz.2
    have htri : vec3EuclideanNorm (z - x) ≤
        vec3EuclideanNorm (z - y) + vec3EuclideanNorm (y - x) := by
      have heq : z - x = (z - y) + (y - x) := by abel
      rw [heq]
      exact vec3EuclideanNorm_add_le _ _
    have hnorm : vec3EuclideanNorm (z - y) ≤ 3 * ‖y - z‖ := by
      simpa only [spaceEuclideanNorm, vec3EuclideanNorm, norm_sub_rev] using euclideanNorm_le_three_mul_space_norm (z - y)
    linarith only [hyx, hzx, htri, hnorm, hrρ]
  have hAb : Bornology.IsBounded A :=
    (isCompact_closure_vec3Ball (x := x) (mul_pos (by norm_num : (0 : ℝ) < 2) hρ)).isBounded.subset
      (fun _ hy => subset_closure hy.1)
  have h := pressure_riesz_component_exterior_bound i j (by positivity : 0 < ρ / 6)
    hGA hGc (isOpen_vec3Ball x r) (fun y hy => Set.indicator_of_notMem hy G) hAb hsep
  have hmass : (∫⁻ z, ‖A.indicator G z‖ₑ) ≤ ∫⁻ z in vec3Ball x (2 * ρ), ‖G z‖ₑ := by
    rw [show (fun z => ‖A.indicator G z‖ₑ) = A.indicator (fun z => ‖G z‖ₑ) by
      funext z
      by_cases hz : z ∈ A <;> simp [hz]]
    rw [lintegral_indicator hA]
    exact lintegral_mono' (Measure.restrict_mono_set volume (fun _ hz => hz.1))
      (fun _ => le_rfl)
  have hc : ENNReal.ofReal (4 * (4 * Real.pi)⁻¹ * ((ρ / 6) ^ 3)⁻¹) =
      ENNReal.ofReal (6912 * (4 * Real.pi)⁻¹) * ENNReal.ofReal (2 * ρ) ^ (-3 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hρ), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.rpow_neg (by positivity), Real.rpow_ofNat]
    field_simp
    ring
  filter_upwards [h] with y hy
  rw [hc] at hy
  exact hy.trans (mul_le_mul_right hmass _)

/-- The pointwise annular estimate gives its local `L^{6/5}` bound, retaining
the observation ball's volume factor. -/
theorem pressure_riesz_annulus_eLpNorm_bound
    (i j : Fin 3) {G : Vec3 → ℝ}
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (x : Vec3) {r ρ : ℝ} (hr : 0 < r) (hrρ : 2 * r ≤ ρ) :
    eLpNorm (rieszSecondGradientExtensionOperator
      (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j)
      ((vec3Ball x (2 * ρ) \ vec3Ball x ρ).indicator G))
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball x r)) ≤
      (ENNReal.ofReal (6912 * (4 * Real.pi)⁻¹) * ENNReal.ofReal (2 * ρ) ^ (-3 : ℝ) *
        ∫⁻ z in vec3Ball x (2 * ρ), ‖G z‖ₑ) * volume (vec3Ball x r) ^ (5 / 6 : ℝ) := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by linarith only [hr]) hrρ
  have hmem := rieszSecondGradientExtension_memLp
    (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j)
    (hG.indicator ((vec3Ball_measurable _ _).diff (vec3Ball_measurable _ _)))
    (pressure_source_annulus_hasCompactSupport G x hρ)
  have h := eLpNorm_le_of_ae_enorm_bound (p := ENNReal.ofReal (6 / 5 : ℝ)) hmem.aestronglyMeasurable.restrict
    (pressure_riesz_annulus_enorm_bound i j hG x hr hrρ)
  simpa only [Measure.restrict_apply_univ, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 / 5),
    inv_div, smul_eq_mul] using h

end CKN.Core.Step4
