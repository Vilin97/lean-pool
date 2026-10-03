/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorEstimates

/-!
# Interior Gradient

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Heat

theorem smooth_harmonic_interior_gradient_norm_bound
    {H : Vec3 → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hHarm : ∀ y ∈ euclideanBall x₀ ρ,
      CKN.spatialLaplacian H y = 0)
    (hHmem : MemLp H (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ))) :
    ∀ x ∈ euclideanBall x₀ (ρ / 2),
      vec3EuclideanNorm (classicalGradient H x) ≤
        3 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
          lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ)) := by
  intro x hx
  let C : ℝ := harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
    lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ))
  have hC : 0 ≤ C := by
    dsimp [C]
    have hG := harmonicInteriorGradientSupConstant_nonneg
    exact mul_nonneg (mul_nonneg hG (by positivity)) lpNorm_nonneg
  have hcoord : ∀ j : Fin 3, |classicalGradient H x j| ≤ C := by
    intro j
    have hj := smooth_harmonic_interior_gradient_bound hH hρ hHarm hHmem x hx j
    simpa [C, spatialDeriv, classicalGradient, classicalGradient_apply,
      CKN.basisVec_apply] using hj
  have hspace : ‖classicalGradient H x‖ ≤ C := by
    rw [Pi.norm_def]
    change (↑(Finset.univ.sup (fun b => ‖classicalGradient H x b‖₊) : NNReal) : ℝ) ≤ C
    have hs : Finset.univ.sup (fun b => ‖classicalGradient H x b‖₊) ≤
        ⟨C, hC⟩ := by
      apply Finset.sup_le
      intro j hj
      have hj' := hcoord j
      exact_mod_cast hj'
    exact_mod_cast hs
  have heuc := CKN.euclideanNorm_le_three_mul_space_norm
    (classicalGradient H x)
  calc
    vec3EuclideanNorm (classicalGradient H x) ≤ 3 * C := by
      simpa [vec3EuclideanNorm, CKN.spaceEuclideanNorm] using
        (heuc.trans
          (mul_le_mul_of_nonneg_left hspace (by norm_num : 0 ≤ (3 : ℝ))))
    _ = 3 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
        lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
      dsimp [C]
      ring

end CKN.Foundation.Heat
