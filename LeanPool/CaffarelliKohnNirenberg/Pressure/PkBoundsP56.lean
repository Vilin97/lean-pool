/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsBasic

/-!
# Pk Bounds P56

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-! Fixed-time annular estimates for the pressure and cutoff terms. -/

theorem pressureP5_annular_bound
    {η : Vec3 → ℝ} {p : ParabolicPoint → ℝ} {x₀ : Vec3}
    {ρ r s : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (x : Vec3) (hx : x ∈ vec3Ball x₀ r)
    (hInt : Integrable (fun y => p (y, s) * spatialLaplacian η y) volume)
    (hProd : Integrable (fun y => (-CKN.Foundation.Heat.newtonianKernel (x - y)) *
      (p (y, s) * spatialLaplacian η y)) volume)
    (hAnn : ∀ y, p (y, s) * spatialLaplacian η y ≠ 0 →
      y ∈ pressureAnnulus x₀ ρ) :
    |pressureNewtonianPotential (fun y => p (y, s) * spatialLaplacian η y) x| ≤
      (2 / ρ) * ∫ y, |p (y, s) * spatialLaplacian η y| := by
  apply pressure_newtonian_potential_bound (by positivity) hInt hProd
  intro y hne
  exact pressure_kernel_bound_on_annulus hρ hr hhalf hx (hAnn y hne)

theorem pressureP6_component_annular_bound
    {η : Vec3 → ℝ} {p : ParabolicPoint → ℝ} {x₀ : Vec3}
    {ρ r s : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (x : Vec3) (hx : x ∈ vec3Ball x₀ r) (j : Fin 3)
    (hInt : Integrable (fun y => spatialDeriv η j y * p (y, s)) volume)
    (hProd : Integrable (fun y => CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel j
      (x - y) * (spatialDeriv η j y * p (y, s))) volume)
    (hAnn : ∀ y, spatialDeriv η j y * p (y, s) ≠ 0 →
      y ∈ pressureAnnulus x₀ ρ) :
    |pressureNewtonianDerivativePotential j
        (fun y => spatialDeriv η j y * p (y, s)) x| ≤
      (40 / ρ ^ 2) * ∫ y, |spatialDeriv η j y * p (y, s)| := by
  apply pressure_newtonian_derivative_potential_bound (by positivity) j hInt hProd
  intro y hne
  exact pressure_kernel_deriv_bound_on_annulus hρ hr hhalf hx (hAnn y hne) j

theorem pressureP56_pointwise_annular_bound
    {η : Vec3 → ℝ} {p : ParabolicPoint → ℝ} {x₀ : Vec3}
    {ρ r s C₁ C₂ : ℝ} (hρ : 0 < ρ) (_ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hp : Integrable (fun y => |p (y, s)|)
      (volume.restrict (vec3Ball x₀ ρ)))
    (hLap : ∀ y, |spatialLaplacian η y| ≤ C₂ / ρ ^ 2)
    (hD₁ : ∀ j y, |spatialDeriv η j y| ≤ C₁ / ρ)
    (hI₅ : Integrable (fun y => p (y, s) * spatialLaplacian η y) volume)
    (hP₅ : ∀ {x}, x ∈ vec3Ball x₀ r → Integrable
      (fun y => (-CKN.Foundation.Heat.newtonianKernel (x - y)) *
      (p (y, s) * spatialLaplacian η y)) volume)
    (hA₅ : ∀ y, p (y, s) * spatialLaplacian η y ≠ 0 →
      y ∈ pressureAnnulus x₀ ρ)
    (hI₆ : ∀ j, Integrable (fun y => spatialDeriv η j y * p (y, s)) volume)
    (hP₆ : ∀ j, ∀ {x}, x ∈ vec3Ball x₀ r → Integrable (fun y => CKN.spatialDeriv
      CKN.Foundation.Heat.newtonianKernel j (x - y) *
      (spatialDeriv η j y * p (y, s))) volume)
    (hA₆ : ∀ j y, spatialDeriv η j y * p (y, s) ≠ 0 →
      y ∈ pressureAnnulus x₀ ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2) {x : Vec3} (hx : x ∈ vec3Ball x₀ r) :
    |pressureP5 η p s x| + |pressureP6 η p s x| ≤
      (6 * C₂ + 240 * C₁) / ρ ^ 3 *
        ∫ y in vec3Ball x₀ ρ, |p (y, s)| := by
  let I : ℝ := ∫ y in vec3Ball x₀ ρ, |p (y, s)|
  have hpi : Integrable ((vec3Ball x₀ ρ).indicator (fun y => |p (y, s)|)) volume :=
    (show IntegrableOn (fun y => |p (y, s)|) (vec3Ball x₀ ρ) volume from hp).integrable_indicator
      (vec3Ball_measurable x₀ ρ)
  have hsrc₅ : ∫ y, |p (y, s) * spatialLaplacian η y| ≤
      (C₂ / ρ ^ 2) * I := by
    have hmono := integral_mono hI₅.norm (hpi.const_mul (C₂ / ρ ^ 2)) (fun y => by
      have hle : |p (y, s) * spatialLaplacian η y| ≤
          (C₂ / ρ ^ 2) * (vec3Ball x₀ ρ).indicator (fun y => |p (y, s)|) y := by
        by_cases hzero : p (y, s) * spatialLaplacian η y = 0
        · rw [hzero]
          by_cases hy : y ∈ vec3Ball x₀ ρ
          · simp only [Set.indicator_of_mem hy, abs_zero]
            positivity
          · simp only [Set.indicator_of_notMem hy, mul_zero, abs_zero]
            norm_num
        · have hyann := hA₅ y hzero
          have hyball : y ∈ vec3Ball x₀ ρ :=
            vec3Ball_mono (x := x₀) (r₁ := 3 * ρ / 4) (r₂ := ρ)
              (by nlinarith only [hρ]) (pressure_annulus_subset_ball hyann)
          rw [Set.indicator_of_mem hyball, abs_mul]
          calc
            |p (y, s)| * |spatialLaplacian η y| =
                |spatialLaplacian η y| * |p (y, s)| := mul_comm _ _
            _ ≤ (C₂ / ρ ^ 2) * |p (y, s)| :=
              mul_le_mul_of_nonneg_right (hLap y) (abs_nonneg _)
      simpa only [Real.norm_eq_abs] using hle)
    calc
      ∫ y, |p (y, s) * spatialLaplacian η y| ≤
          ∫ y, (C₂ / ρ ^ 2) *
            (vec3Ball x₀ ρ).indicator (fun y => |p (y, s)|) y := hmono
      _ = (C₂ / ρ ^ 2) * I := by
        rw [integral_const_mul, integral_indicator (vec3Ball_measurable x₀ ρ)]
  have hsrc₆ (j : Fin 3) : ∫ y, |spatialDeriv η j y * p (y, s)| ≤
      (C₁ / ρ) * I := by
    have hmono := integral_mono (hI₆ j).norm (hpi.const_mul (C₁ / ρ)) (fun y => by
      have hle : |spatialDeriv η j y * p (y, s)| ≤
          (C₁ / ρ) * (vec3Ball x₀ ρ).indicator (fun y => |p (y, s)|) y := by
        by_cases hzero : spatialDeriv η j y * p (y, s) = 0
        · rw [hzero]
          by_cases hy : y ∈ vec3Ball x₀ ρ
          · simp only [Set.indicator_of_mem hy, abs_zero]
            positivity
          · simp only [Set.indicator_of_notMem hy, mul_zero, abs_zero]
            norm_num
        · have hyann := hA₆ j y hzero
          have hyball : y ∈ vec3Ball x₀ ρ :=
            vec3Ball_mono (x := x₀) (r₁ := 3 * ρ / 4) (r₂ := ρ)
              (by nlinarith only [hρ]) (pressure_annulus_subset_ball hyann)
          rw [Set.indicator_of_mem hyball, abs_mul]
          exact mul_le_mul_of_nonneg_right (hD₁ j y) (abs_nonneg _)
      simpa only [Real.norm_eq_abs] using hle)
    calc
      ∫ y, |spatialDeriv η j y * p (y, s)| ≤
          ∫ y, (C₁ / ρ) * (vec3Ball x₀ ρ).indicator (fun y => |p (y, s)|) y := hmono
      _ = (C₁ / ρ) * I := by
        rw [integral_const_mul, integral_indicator (vec3Ball_measurable x₀ ρ)]
  have hp₅ : |pressureNewtonianPotential
      (fun y => p (y, s) * spatialLaplacian η y) x| ≤
      (2 / ρ) * (C₂ / ρ ^ 2) * I := by
    calc
      _ ≤ (2 / ρ) * ∫ y, |p (y, s) * spatialLaplacian η y| :=
        pressureP5_annular_bound hρ hr hhalf x hx hI₅ (hP₅ hx) hA₅
      _ ≤ (2 / ρ) * ((C₂ / ρ ^ 2) * I) :=
        mul_le_mul_of_nonneg_left hsrc₅ (by positivity)
      _ = (2 / ρ) * (C₂ / ρ ^ 2) * I := by ring
  have hp₆ (j : Fin 3) : |pressureNewtonianDerivativePotential j
      (fun y => spatialDeriv η j y * p (y, s)) x| ≤
      (40 / ρ ^ 2) * (C₁ / ρ) * I := by
    calc
      _ ≤ (40 / ρ ^ 2) * ∫ y, |spatialDeriv η j y * p (y, s)| :=
        pressureP6_component_annular_bound hρ hr hhalf x hx j
          (hI₆ j) (hP₆ j hx) (hA₆ j)
      _ ≤ (40 / ρ ^ 2) * ((C₁ / ρ) * I) :=
        mul_le_mul_of_nonneg_left (hsrc₆ j) (by positivity)
      _ = (40 / ρ ^ 2) * (C₁ / ρ) * I := by ring
  have hsum₆ : |∑ j, pressureNewtonianDerivativePotential j
      (fun y => spatialDeriv η j y * p (y, s)) x| ≤ 120 * C₁ / ρ ^ 3 * I := by
    calc
      |∑ j, pressureNewtonianDerivativePotential j
          (fun y => spatialDeriv η j y * p (y, s)) x| ≤
          ∑ j, |pressureNewtonianDerivativePotential j
            (fun y => spatialDeriv η j y * p (y, s)) x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ((40 / ρ ^ 2) * (C₁ / ρ) * I) := by
        gcongr with j hj
        exact hp₆ j
      _ = 120 * C₁ / ρ ^ 3 * I := by
        simp only [Fin.sum_univ_three]
        ring
  calc
    |pressureP5 η p s x| + |pressureP6 η p s x| ≤
        (6 * C₂ / ρ ^ 3) * I + 2 *
          (120 * C₁ / ρ ^ 3 * I) := by
      rw [pressureP5, pressureP6]
      rw [abs_neg, abs_mul]
      norm_num
      apply add_le_add
      · calc
          |pressureNewtonianPotential
              (fun y => p (y, s) * spatialLaplacian η y) x| ≤
              (2 / ρ) * (C₂ / ρ ^ 2) * I := hp₅
          _ ≤ 6 * C₂ / ρ ^ 3 * I := by
            gcongr
            field_simp [hρ.ne']
            nlinarith only [hC₂]
      · exact mul_le_mul_of_nonneg_left hsum₆ (by norm_num)
    _ = (6 * C₂ + 240 * C₁) / ρ ^ 3 *
        ∫ y in vec3Ball x₀ ρ, |p (y, s)| := by
      dsimp [I]
      ring

end CKN
