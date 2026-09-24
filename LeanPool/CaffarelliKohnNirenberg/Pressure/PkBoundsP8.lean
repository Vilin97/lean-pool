/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsBasic

/-!
# Pk Bounds P8

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-! Fixed-time annular estimate for the force term. -/

theorem pressureP8_component_annular_bound
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {x₀ : Vec3}
    {ρ r s : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (x : Vec3) (hx : x ∈ vec3Ball x₀ r) (j : Fin 3)
    (hInt : Integrable (fun y => spatialDeriv η j y * f (y, s) j) volume)
    (hProd : Integrable (fun y => (-CKN.Foundation.Heat.newtonianKernel (x - y)) *
      (spatialDeriv η j y * f (y, s) j)) volume)
    (hAnn : ∀ y, spatialDeriv η j y * f (y, s) j ≠ 0 →
      y ∈ pressureAnnulus x₀ ρ) :
    |pressureNewtonianPotential
        (fun y => spatialDeriv η j y * f (y, s) j) x| ≤
      (2 / ρ) * ∫ y, |spatialDeriv η j y * f (y, s) j| := by
  apply pressure_newtonian_potential_bound (by positivity) hInt hProd
  intro y hne
  exact pressure_kernel_bound_on_annulus hρ hr hhalf hx (hAnn y hne)


theorem pressureP8_pointwise_annular_bound_on_ball
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {x₀ : Vec3}
    {ρ r s C₁ : ℝ} (hρ : 0 < ρ) (hC₁ : 0 ≤ C₁)
    (hf : Integrable (fun y => vec3EuclideanNorm (f (y, s)))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hD₁ : ∀ j y, |spatialDeriv η j y| ≤ C₁ / ρ)
    (hI₈ : ∀ j, Integrable
      (fun y => spatialDeriv η j y * f (y, s) j) volume)
    (hP₈ : ∀ j, ∀ {x}, x ∈ vec3Ball x₀ r → Integrable
      (fun y => (-CKN.Foundation.Heat.newtonianKernel (x - y)) *
      (spatialDeriv η j y * f (y, s) j)) volume)
    (hA₈ : ∀ j y, spatialDeriv η j y * f (y, s) j ≠ 0 →
      y ∈ pressureAnnulus x₀ ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2) {x : Vec3} (hx : x ∈ vec3Ball x₀ r) :
    |pressureP8 η f s x| ≤
      (6 * C₁) / ρ ^ 2 *
        ∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s)) := by
  let I : ℝ := ∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s))
  have hfi : Integrable
      ((vec3Ball x₀ ρ).indicator (fun y => vec3EuclideanNorm (f (y, s)))) volume :=
    (show IntegrableOn (fun y => vec3EuclideanNorm (f (y, s)))
      (vec3Ball x₀ ρ) volume from hf).integrable_indicator
      (vec3Ball_measurable x₀ ρ)
  have hsrc (j : Fin 3) :
      ∫ y, |spatialDeriv η j y * f (y, s) j| ≤ (C₁ / ρ) * I := by
    have hmono := integral_mono (hI₈ j).norm (hfi.const_mul (C₁ / ρ)) (fun y => by
      have hle : |spatialDeriv η j y * f (y, s) j| ≤
          (C₁ / ρ) * (vec3Ball x₀ ρ).indicator
            (fun y => vec3EuclideanNorm (f (y, s))) y := by
        by_cases hzero : spatialDeriv η j y * f (y, s) j = 0
        · rw [hzero]
          by_cases hy : y ∈ vec3Ball x₀ ρ
          · simp only [Set.indicator_of_mem hy, abs_zero]
            exact mul_nonneg (div_nonneg hC₁ (by positivity))
              (vec3EuclideanNorm_nonneg _)
          · simp only [Set.indicator_of_notMem hy, mul_zero, abs_zero]
            norm_num
        · have hyann := hA₈ j y hzero
          have hyball : y ∈ vec3Ball x₀ ρ :=
            vec3Ball_mono (x := x₀) (r₁ := 3 * ρ / 4) (r₂ := ρ)
              (by nlinarith only [hρ]) (pressure_annulus_subset_ball hyann)
          rw [Set.indicator_of_mem hyball, abs_mul]
          calc
            |spatialDeriv η j y| * |f (y, s) j| ≤
                (C₁ / ρ) * |f (y, s) j| :=
              mul_le_mul_of_nonneg_right (hD₁ j y) (abs_nonneg _)
            _ ≤ (C₁ / ρ) * vec3EuclideanNorm (f (y, s)) := by
              gcongr
              simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
                abs_apply_le_vecEuclideanNorm (f (y, s)) j
      simpa only [Real.norm_eq_abs] using hle)
    calc
      ∫ y, |spatialDeriv η j y * f (y, s) j| ≤
          ∫ y, (C₁ / ρ) * (vec3Ball x₀ ρ).indicator
            (fun y => vec3EuclideanNorm (f (y, s))) y := hmono
      _ = (C₁ / ρ) * I := by
        rw [integral_const_mul, integral_indicator (vec3Ball_measurable x₀ ρ)]
  have hp (j : Fin 3) :
      |pressureNewtonianPotential
          (fun y => spatialDeriv η j y * f (y, s) j) x| ≤
        (2 / ρ) * (C₁ / ρ) * I := by
    calc
      _ ≤ (2 / ρ) * ∫ y, |spatialDeriv η j y * f (y, s) j| :=
        pressureP8_component_annular_bound hρ hr hhalf x hx j
          (hI₈ j) (hP₈ j hx) (hA₈ j)
      _ ≤ (2 / ρ) * ((C₁ / ρ) * I) :=
        mul_le_mul_of_nonneg_left (hsrc j) (by positivity)
      _ = (2 / ρ) * (C₁ / ρ) * I := by ring
  calc
    |pressureP8 η f s x| =
        |∑ j, pressureNewtonianPotential
          (fun y => spatialDeriv η j y * f (y, s) j) x| := by
      rw [pressureP8, abs_neg]
    _ ≤ ∑ j, |pressureNewtonianPotential
          (fun y => spatialDeriv η j y * f (y, s) j) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ((2 / ρ) * (C₁ / ρ) * I) := by
      gcongr with j hj
      exact hp j
    _ = (6 * C₁) / ρ ^ 2 *
        ∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s)) := by
      simp only [Fin.sum_univ_three]
      dsimp [I]
      ring

end CKN
