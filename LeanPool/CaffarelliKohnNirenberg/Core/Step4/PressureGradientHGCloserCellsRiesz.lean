/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ConcreteRieszConsumption
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionExterior

/-! # Local pieces of the concrete pressure Riesz operator

The concrete operator has its global `L^{6/5}` bound and respects a spatial
near/far decomposition. Away from the support its exterior formula gives a
pointwise bound by the source's spatial `L^1` norm.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

/-- The concrete component operator has a fixed global `L^{6/5}` bound. -/
theorem pressure_riesz_component_eLpNorm_bound
    (i j : Fin 3) {G : Vec3 → ℝ}
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hGc : HasCompactSupport G) :
    eLpNorm (rieszSecondGradientExtensionOperator
      (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) G)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
        ENNReal.ofReal (czGradientComponentConstant rieszSecondWeakTypeConstant 1) *
          eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  exact CKN.Core.Endgame.eLpNorm_le_of_toLp_norm_le hG
    (rieszSecondGradientExtension_memLp _ _ hG hGc)
    (by unfold czGradientComponentConstant; positivity)
    (rieszSecondGradientExtension_toLp_bound _ _ hG hGc)

/-- Splitting the source into two measurable spatial regions commutes with
its concrete Riesz operator up to almost-everywhere equality. -/
theorem pressure_riesz_component_indicator_add_ae
    (i j : Fin 3) {G : Vec3 → ℝ}
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    {A : Set Vec3} (hA : MeasurableSet A) :
    rieszSecondGradientExtensionOperator
      (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) G =ᵐ[volume]
      rieszSecondGradientExtensionOperator
        (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) (A.indicator G) +
      rieszSecondGradientExtensionOperator
        (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) (Aᶜ.indicator G) := by
  let : Fact (1 ≤ ENNReal.ofReal (6 / 5 : ℝ)) := ⟨by norm_num⟩
  have heq : G = A.indicator G + Aᶜ.indicator G := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  have h := lpExtensionRepresentative_add_ae (by norm_num)
    (rieszSecondGradientExtensionInput (rieszSecondL2Input i j)
      (rieszSecondL2_weak_type i j)) (hG.indicator hA) (hG.indicator hA.compl)
  rw [← heq] at h
  exact h

/-- On a region separated from the source, the concrete operator is bounded
by the spatial `L^1` mass times the inverse cube of the separation. -/
theorem pressure_riesz_component_exterior_bound
    (i j : Fin 3) {δ : ℝ} (hδ : 0 < δ)
    {G : Vec3 → ℝ} (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hGc : HasCompactSupport G) {A U : Set Vec3} (hU : IsOpen U)
    (hGA : ∀ y ∉ A, G y = 0) (hAb : Bornology.IsBounded A)
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ ‖x - y‖) :
    ∀ᵐ x ∂(volume.restrict U),
      ‖rieszSecondGradientExtensionOperator
        (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) G x‖ₑ ≤
      ENNReal.ofReal (4 * (4 * Real.pi)⁻¹ * (δ ^ 3)⁻¹) * ∫⁻ y, ‖G y‖ₑ := by
  have hsepE : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y) := by
    intro x hx y hy
    exact (hsep x hx y hy).trans (space_norm_le_euclideanNorm (x - y))
  have hid := rieszSecondGradientExtensionOperator_agrees_exterior
    (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j)
    hG hGc hU hGA hAb hδ hsepE
  filter_upwards [hid, ae_restrict_mem hU.measurableSet] with x hx hxU
  rw [hx]
  calc
    _ ≤ ∫⁻ y, ‖(-spatialDeriv (spatialDeriv newtonianKernel i) j) (x - y) * G y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, ENNReal.ofReal (4 * (4 * Real.pi)⁻¹ * (δ ^ 3)⁻¹) * ‖G y‖ₑ := by
      apply lintegral_mono
      intro y
      dsimp only
      by_cases hy : y ∈ A
      · have hnorm : δ ≤ ‖x - y‖ := hsep x hxU y hy
        have hxy : x - y ≠ 0 := norm_pos_iff.mp (hδ.trans_le hnorm)
        have hinv : (‖x - y‖ ^ 3)⁻¹ ≤ (δ ^ 3)⁻¹ :=
          inv_anti₀ (pow_pos hδ _) (pow_le_pow_left₀ hδ.le hnorm _)
        have hk : |(-spatialDeriv (spatialDeriv newtonianKernel i) j) (x - y)| ≤
            4 * (4 * Real.pi)⁻¹ * (δ ^ 3)⁻¹ := by
          simp only [Pi.neg_apply, abs_neg]
          exact (newtonianKernel_spatialDeriv_second_size_bound hxy i j).trans
            (mul_le_mul_of_nonneg_left hinv (by positivity))
        rw [enorm_mul, Real.enorm_eq_ofReal_abs]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hk) _
      · rw [hGA y hy]
        simp
    _ = _ := lintegral_const_mul'' _ hG.aestronglyMeasurable.aemeasurable.enorm

end CKN.Core.Step4
