/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.RepresentativeBound
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.HolderGluing
public import LeanPool.CaffarelliKohnNirenberg.Setting.ExcessComparisonCore

/-! # The velocity average supplied by the small-data hypothesis

The original nonnegative sum in the unit-cylinder hypothesis controls the
cubic velocity average on the half-cylinder. This supplies the absolute-value
part of the reanchored heat representative without any additional assumption
on that average.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential

noncomputable section
namespace CKN.Core.Endgame

/-- The full small-data hypothesis bounds the half-cylinder velocity average
and supplies both integrability conditions used in reanchoring. -/
theorem halfCylinder_velocity_average_of_small_data
    {Ω : Set Vec3} {I : Set ℝ} {q ε₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hε₀ : 0 ≤ ε₀) (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ z in parabolicCylinder 0 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀) :
    IntegrableOn (fun x => vec3EuclideanNorm (u x)) (parabolicCylinder 0 0 (1 / 2)) ∧
    IntegrableOn (fun x => vec3EuclideanNorm (u x) ^ (3 : ℝ))
      (parabolicCylinder 0 0 (1 / 2)) ∧
    (⨍ x in parabolicCylinder 0 0 (1 / 2), vec3EuclideanNorm (u x) ^ (3 : ℝ)) ^
      (1 / 3 : ℝ) ≤
        ((volume (parabolicCylinder 0 0 (1 / 2))).toReal⁻¹ * ε₀) ^ (1 / 3 : ℝ) := by
  have hhalf : closure (parabolicCylinder 0 0 (1 / 2)) ⊆ spaceTimeSet Ω I :=
    (closure_parabolicCylinder_mono (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans hdom
  have huvec := tsai_integrable_velocity_on_cylinder (z := ((0, 0) : ParabolicPoint))
    hsol (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  let L := (PiLp.continuousLinearEquiv (2 : ℝ≥0∞) ℝ (fun _ : Fin 3 => ℝ)).symm
  have hu : IntegrableOn (fun x => vec3EuclideanNorm (u x))
      (parabolicCylinder 0 0 (1 / 2)) := by
    have hL := ((L : Vec3 →L[ℝ] L2Vec3).integrable_comp huvec).norm
    simpa only [IntegrableOn, L, ContinuousLinearEquiv.coe_coe,
      PiLp.coe_symm_continuousLinearEquiv, vec3EuclideanNorm_eq_l2] using hL
  have hu3 : IntegrableOn (fun x => vec3EuclideanNorm (u x) ^ (3 : ℝ))
      (parabolicCylinder 0 0 (1 / 2)) := by
    simpa only [Real.rpow_ofNat] using
      (tsai_integrable_velocity_cube_on_cylinder (z := ((0, 0) : ParabolicPoint))
        hsol (by norm_num : (0 : ℝ) < 1 / 2) hhalf)
  refine ⟨hu, hu3, ?_⟩
  have hvel : (∫⁻ x in parabolicCylinder 0 0 (1 / 2),
      ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ (3 : ℝ)) ≤ ENNReal.ofReal ε₀ := by
    calc
      _ ≤ ∫⁻ x in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ (3 : ℝ) :=
        lintegral_mono_set (parabolicCylinder_mono (by norm_num) (by norm_num))
      _ ≤ ∫⁻ x in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ (3 : ℝ) +
            ENNReal.ofReal |p x| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f x)) ^ q :=
        lintegral_mono fun x => (le_add_right le_rfl).trans (le_add_right le_rfl)
      _ ≤ _ := hsmall
  have hint : (∫ x in parabolicCylinder 0 0 (1 / 2),
      vec3EuclideanNorm (u x) ^ (3 : ℝ)) ≤ ε₀ := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (vec3EuclideanNorm_nonneg _) _)
      hu3.aestronglyMeasurable]
    simp_rw [← ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _) (by norm_num : (0 : ℝ) ≤
      3)]
    exact (ENNReal.toReal_le_toReal (ne_of_lt (lt_of_le_of_lt hvel ENNReal.ofReal_lt_top))
      ENNReal.ofReal_ne_top).mpr hvel |>.trans_eq (ENNReal.toReal_ofReal hε₀)
  apply Real.rpow_le_rpow
    (Integration.setAverage_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (vec3EuclideanNorm_nonneg _) _)) _ (by norm_num)
  rw [Integration.setAverage_eq_toReal_inv_smul]
  exact mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- The original small-data hypothesis and genuine heat sources give a
closed-half-cylinder representative whose explicit norm uses only the source
coefficient and the small-data threshold, together with interior regularity. -/
theorem halfCylinder_representative_of_heat_sources_of_small_data
    {Ω : Set Vec3} {I : Set ℝ} {q ε₀ γ θ₀ θ₁ P : ℝ}
    {u F : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {G : Fin 3 → ParabolicPoint → Vec3}
    (hε₀ : 0 ≤ ε₀) (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ z in parabolicCylinder 0 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀)
    (hγ : 0 < γ) (hγ1 : γ < 1)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5) (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : ∀ i, AEMeasurable (fun x => F x i) volume)
    (hG : ∀ j i, AEMeasurable (fun x => G j x i) volume)
    (hNF : ∀ i, morreyNorm P θ₀ (fun x => F x i) < ∞)
    (hNG : ∀ j i, morreyNorm P θ₁ (fun x => G j x i) < ∞)
    (hSupportF : ∀ i, HasCompactSupport (fun x => F x i))
    (hSupportG : ∀ j i, HasCompactSupport (fun x => G j x i))
    (hrep : u =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))]
      (fun x i => heatPotential (fun y => F y i) (fun j y => G j y i) x)) :
    ∃ w : ParabolicPoint → Vec3,
      w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
      ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2))) w γ
        (2 * vectorHeatHolderCoefficient F G γ θ₀ θ₁ P +
          ((volume (parabolicCylinder 0 0 (1 / 2))).toReal⁻¹ * ε₀) ^ (1 / 3 : ℝ)) ∧
      ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
        IsRegularPoint Ω I u z := by
  obtain ⟨hu, hu3, havg⟩ := halfCylinder_velocity_average_of_small_data hε₀ hsol hdom hsmall
  obtain ⟨w, hwu, hw⟩ := halfCylinder_reanchored_heat_representative
    hγ hγ1 hθ₀ hθ₁ hP hPθ₀ hPθ₁ hF hG hNF hNG hSupportF hSupportG hrep hu hu3
  have hw' : ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2))) w γ
      (2 * vectorHeatHolderCoefficient F G γ θ₀ θ₁ P +
        ((volume (parabolicCylinder 0 0 (1 / 2))).toReal⁻¹ * ε₀) ^ (1 / 3 : ℝ)) := by
    obtain ⟨B, K, hB, hK, hC, hb, hk⟩ := hw
    exact ⟨B, K, hB, hK, hC.trans (add_le_add_right havg _), hb, hk⟩
  refine ⟨w, hwu, hw', ?_⟩
  have hinterior : interior (parabolicCylinder 0 0 (1 / 2)) =
      vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0 := by
    rw [interior_parabolicCylinder]
    norm_num
    rfl
  intro z hz
  have hz' : z ∈ interior (parabolicCylinder 0 0 (1 / 2)) := hinterior.symm ▸ hz
  have hsub : parabolicCylinder 0 0 (1 / 2) ⊆ spaceTimeSet Ω I :=
    subset_closure.trans ((closure_parabolicCylinder_mono
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans hdom)
  exact regular_point_of_holder_norm isOpen_interior hz' interior_subset
    (interior_subset.trans hsub) hγ hγ1.le hwu
    (holder_norm_mono hw' subset_closure)

end CKN.Core.Endgame
