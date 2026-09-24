/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsBasic

/-!
# Pk Bounds P234

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-! Fixed-time annular estimates for the three terms containing `U`. -/

theorem pressureP2_component_annular_bound
    {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {x₀ : Vec3} {ρ r s : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2) (x : Vec3) (hx : x ∈ vec3Ball x₀ r) (i j : Fin 3)
    (hInt : Integrable
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) volume)
    (hProd : Integrable
      (fun y => (-CKN.Foundation.Heat.newtonianKernel (x - y)) *
        (mixedSecond η i j y * pressureUTensor u c (y, s) i j)) volume)
    (hAnn : ∀ y, mixedSecond η i j y * pressureUTensor u c (y, s) i j ≠ 0 →
      y ∈ pressureAnnulus x₀ ρ) :
    |pressureNewtonianPotential
        (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x| ≤
      (2 / ρ) * ∫ y, |mixedSecond η i j y * pressureUTensor u c (y, s) i j| := by
  apply pressure_newtonian_potential_bound (by positivity) hInt hProd
  intro y hne
  exact pressure_kernel_bound_on_annulus hρ hr hhalf hx (hAnn y hne)

theorem pressureP3_component_annular_bound
    {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {x₀ : Vec3} {ρ r s : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2) (x : Vec3) (hx : x ∈ vec3Ball x₀ r) (i j : Fin 3)
    (hInt : Integrable
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) volume)
    (hProd : Integrable
      (fun y => CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel j
        (x - y) * (pressureUTensor u c (y, s) i j * spatialDeriv η i y)) volume)
    (hAnn : ∀ y, pressureUTensor u c (y, s) i j * spatialDeriv η i y ≠ 0 →
      y ∈ pressureAnnulus x₀ ρ) :
    |pressureNewtonianDerivativePotential j
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x| ≤
      (40 / ρ ^ 2) * ∫ y,
        |pressureUTensor u c (y, s) i j * spatialDeriv η i y| := by
  apply pressure_newtonian_derivative_potential_bound (by positivity) j hInt hProd
  intro y hne
  exact pressure_kernel_deriv_bound_on_annulus hρ hr hhalf hx (hAnn y hne) j

theorem pressureP4_component_annular_bound
    {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {x₀ : Vec3} {ρ r s : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2) (x : Vec3) (hx : x ∈ vec3Ball x₀ r) (i j : Fin 3)
    (hInt : Integrable
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) volume)
    (hProd : Integrable
      (fun y => CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
        (x - y) * (pressureUTensor u c (y, s) i j * spatialDeriv η j y)) volume)
    (hAnn : ∀ y, pressureUTensor u c (y, s) i j * spatialDeriv η j y ≠ 0 →
      y ∈ pressureAnnulus x₀ ρ) :
    |pressureNewtonianDerivativePotential i
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x| ≤
      (40 / ρ ^ 2) * ∫ y,
        |pressureUTensor u c (y, s) i j * spatialDeriv η j y| := by
  apply pressure_newtonian_derivative_potential_bound (by positivity) i hInt hProd
  intro y hne
  exact pressure_kernel_deriv_bound_on_annulus hρ hr hhalf hx (hAnn y hne) i

theorem pressureP234_pointwise_annular_bound
    {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {x₀ : Vec3} {ρ r s C₁ C₂ : ℝ} (hρ : 0 < ρ) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hU : Integrable (pressureUTensorNorm u c s)
      (volume.restrict (vec3Ball x₀ ρ)))
    (hD₂ : ∀ i j y, |mixedSecond η i j y| ≤ C₂ / ρ ^ 2)
    (hD₁ : ∀ i y, |spatialDeriv η i y| ≤ C₁ / ρ)
    (hI₂ : ∀ i j, Integrable
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) volume)
    (hP₂ : ∀ i j, ∀ {x}, x ∈ vec3Ball x₀ r → Integrable
      (fun y => (-CKN.Foundation.Heat.newtonianKernel (x - y)) *
        (mixedSecond η i j y * pressureUTensor u c (y, s) i j)) volume)
    (hA₂ : ∀ i j y, mixedSecond η i j y * pressureUTensor u c (y, s) i j ≠ 0 →
      y ∈ pressureAnnulus x₀ ρ)
    (hI₃ : ∀ i j, Integrable
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) volume)
    (hP₃ : ∀ i j, ∀ {x}, x ∈ vec3Ball x₀ r → Integrable
      (fun y => CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel j
        (x - y) * (pressureUTensor u c (y, s) i j * spatialDeriv η i y)) volume)
    (hA₃ : ∀ i j y, pressureUTensor u c (y, s) i j * spatialDeriv η i y ≠ 0 →
      y ∈ pressureAnnulus x₀ ρ)
    (hI₄ : ∀ i j, Integrable
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) volume)
    (hP₄ : ∀ i j, ∀ {x}, x ∈ vec3Ball x₀ r → Integrable
      (fun y => CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i
        (x - y) * (pressureUTensor u c (y, s) i j * spatialDeriv η j y)) volume)
    (hA₄ : ∀ i j y, pressureUTensor u c (y, s) i j * spatialDeriv η j y ≠ 0 →
      y ∈ pressureAnnulus x₀ ρ) {x : Vec3} (hr : 0 < r)
    (hhalf : r ≤ ρ / 2) (hx : x ∈ vec3Ball x₀ r) :
    |pressureP2 η u c s x| + |pressureP3 η u c s x| +
        |pressureP4 η u c s x| ≤
      (18 * C₂ + 720 * C₁) / ρ ^ 3 *
        ∫ y in vec3Ball x₀ ρ, pressureUTensorNorm u c s y := by
  let I : ℝ := ∫ y in vec3Ball x₀ ρ, pressureUTensorNorm u c s y
  have hUi : Integrable
      ((vec3Ball x₀ ρ).indicator (pressureUTensorNorm u c s)) volume :=
    (show IntegrableOn (pressureUTensorNorm u c s) (vec3Ball x₀ ρ) volume from hU).integrable_indicator
      (vec3Ball_measurable x₀ ρ)
  have hsrc₂ (i j : Fin 3) :
      ∫ y, |mixedSecond η i j y * pressureUTensor u c (y, s) i j| ≤
        (C₂ / ρ ^ 2) * I := by
    have hmono := integral_mono (hI₂ i j).norm
      (hUi.const_mul (C₂ / ρ ^ 2)) (fun y => by
        have hle : |mixedSecond η i j y * pressureUTensor u c (y, s) i j| ≤
            (C₂ / ρ ^ 2) * (vec3Ball x₀ ρ).indicator
              (pressureUTensorNorm u c s) y := by
          by_cases hzero : mixedSecond η i j y * pressureUTensor u c (y, s) i j = 0
          · rw [hzero]
            by_cases hy : y ∈ vec3Ball x₀ ρ
            · simp only [Set.indicator_of_mem hy]
              simp only [abs_zero]
              have hnorm : 0 ≤ pressureUTensorNorm u c s y := by
                unfold pressureUTensorNorm
                exact Real.sqrt_nonneg _
              exact mul_nonneg (div_nonneg hC₂ (sq_nonneg _)) hnorm
            · simp only [Set.indicator_of_notMem hy, mul_zero]
              norm_num
          · have hyann := hA₂ i j y hzero
            have hyball : y ∈ vec3Ball x₀ ρ :=
              vec3Ball_mono (x := x₀) (r₁ := 3 * ρ / 4) (r₂ := ρ)
                (by nlinarith only [hρ]) (pressure_annulus_subset_ball hyann)
            rw [Set.indicator_of_mem hyball]
            rw [abs_mul]
            exact mul_le_mul (hD₂ i j y)
              (pressure_component_abs_le_utensorNorm u c s y i j)
              (abs_nonneg _) (by positivity)
        simpa only [Real.norm_eq_abs] using hle)
    calc
      ∫ y, |mixedSecond η i j y * pressureUTensor u c (y, s) i j| ≤
          ∫ y, (C₂ / ρ ^ 2) *
            (vec3Ball x₀ ρ).indicator (pressureUTensorNorm u c s) y := hmono
      _ = (C₂ / ρ ^ 2) * I := by
        rw [integral_const_mul, integral_indicator (vec3Ball_measurable x₀ ρ)]
  have hsrc₃ (i j : Fin 3) :
      ∫ y, |pressureUTensor u c (y, s) i j * spatialDeriv η i y| ≤
        (C₁ / ρ) * I := by
    have hmono := integral_mono (hI₃ i j).norm
      (hUi.const_mul (C₁ / ρ)) (fun y => by
        have hle : |pressureUTensor u c (y, s) i j * spatialDeriv η i y| ≤
            (C₁ / ρ) * (vec3Ball x₀ ρ).indicator
              (pressureUTensorNorm u c s) y := by
          by_cases hzero : pressureUTensor u c (y, s) i j * spatialDeriv η i y = 0
          · rw [hzero]
            by_cases hy : y ∈ vec3Ball x₀ ρ
            · simp only [Set.indicator_of_mem hy]
              simp only [abs_zero]
              have hnorm : 0 ≤ pressureUTensorNorm u c s y := by
                unfold pressureUTensorNorm
                exact Real.sqrt_nonneg _
              exact mul_nonneg (div_nonneg hC₁ (by positivity)) hnorm
            · simp only [Set.indicator_of_notMem hy, mul_zero]
              norm_num
          · have hyann := hA₃ i j y hzero
            have hyball : y ∈ vec3Ball x₀ ρ :=
              vec3Ball_mono (x := x₀) (r₁ := 3 * ρ / 4) (r₂ := ρ)
                (by nlinarith only [hρ]) (pressure_annulus_subset_ball hyann)
            rw [Set.indicator_of_mem hyball]
            rw [abs_mul]
            calc
              |pressureUTensor u c (y, s) i j| * |spatialDeriv η i y| =
                  |spatialDeriv η i y| *
                    |pressureUTensor u c (y, s) i j| := mul_comm _ _
              _ ≤ (C₁ / ρ) * pressureUTensorNorm u c s y := by
                exact mul_le_mul (hD₁ i y)
                  (pressure_component_abs_le_utensorNorm u c s y i j)
                  (abs_nonneg _) (by positivity)
        simpa only [Real.norm_eq_abs] using hle)
    calc
      ∫ y, |pressureUTensor u c (y, s) i j * spatialDeriv η i y| ≤
          ∫ y, (C₁ / ρ) * (vec3Ball x₀ ρ).indicator
            (pressureUTensorNorm u c s) y := hmono
      _ = (C₁ / ρ) * I := by
        rw [integral_const_mul, integral_indicator (vec3Ball_measurable x₀ ρ)]
  have hsrc₄ (i j : Fin 3) :
      ∫ y, |pressureUTensor u c (y, s) i j * spatialDeriv η j y| ≤
        (C₁ / ρ) * I := by
    have hmono := integral_mono (hI₄ i j).norm
      (hUi.const_mul (C₁ / ρ)) (fun y => by
        have hle : |pressureUTensor u c (y, s) i j * spatialDeriv η j y| ≤
            (C₁ / ρ) * (vec3Ball x₀ ρ).indicator
              (pressureUTensorNorm u c s) y := by
          by_cases hzero : pressureUTensor u c (y, s) i j * spatialDeriv η j y = 0
          · rw [hzero]
            by_cases hy : y ∈ vec3Ball x₀ ρ
            · simp only [Set.indicator_of_mem hy]
              simp only [abs_zero]
              have hnorm : 0 ≤ pressureUTensorNorm u c s y := by
                unfold pressureUTensorNorm
                exact Real.sqrt_nonneg _
              exact mul_nonneg (div_nonneg hC₁ (by positivity)) hnorm
            · simp only [Set.indicator_of_notMem hy, mul_zero]
              norm_num
          · have hyann := hA₄ i j y hzero
            have hyball : y ∈ vec3Ball x₀ ρ :=
              vec3Ball_mono (x := x₀) (r₁ := 3 * ρ / 4) (r₂ := ρ)
                (by nlinarith only [hρ]) (pressure_annulus_subset_ball hyann)
            rw [Set.indicator_of_mem hyball]
            rw [abs_mul]
            calc
              |pressureUTensor u c (y, s) i j| * |spatialDeriv η j y| =
                  |spatialDeriv η j y| *
                    |pressureUTensor u c (y, s) i j| := mul_comm _ _
              _ ≤ (C₁ / ρ) * pressureUTensorNorm u c s y := by
                exact mul_le_mul (hD₁ j y)
                  (pressure_component_abs_le_utensorNorm u c s y i j)
                  (abs_nonneg _) (by positivity)
        simpa only [Real.norm_eq_abs] using hle)
    calc
      ∫ y, |pressureUTensor u c (y, s) i j * spatialDeriv η j y| ≤
          ∫ y, (C₁ / ρ) * (vec3Ball x₀ ρ).indicator
            (pressureUTensorNorm u c s) y := hmono
      _ = (C₁ / ρ) * I := by
        rw [integral_const_mul, integral_indicator (vec3Ball_measurable x₀ ρ)]
  have hp₂ (i j : Fin 3) :
      |pressureNewtonianPotential
          (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x| ≤
        (2 / ρ) * (C₂ / ρ ^ 2) * I := by
    calc
      _ ≤ (2 / ρ) * ∫ y,
          |mixedSecond η i j y * pressureUTensor u c (y, s) i j| :=
        pressureP2_component_annular_bound hρ hr hhalf x hx i j
          (hI₂ i j) (hP₂ i j hx) (hA₂ i j)
      _ ≤ (2 / ρ) * ((C₂ / ρ ^ 2) * I) := by
        exact mul_le_mul_of_nonneg_left (hsrc₂ i j) (by positivity)
      _ = (2 / ρ) * (C₂ / ρ ^ 2) * I := by ring
  have hp₃ (i j : Fin 3) :
      |pressureNewtonianDerivativePotential j
          (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x| ≤
        (40 / ρ ^ 2) * (C₁ / ρ) * I := by
    calc
      _ ≤ (40 / ρ ^ 2) * ∫ y,
          |pressureUTensor u c (y, s) i j * spatialDeriv η i y| :=
        pressureP3_component_annular_bound hρ hr hhalf x hx i j
          (hI₃ i j) (hP₃ i j hx) (hA₃ i j)
      _ ≤ (40 / ρ ^ 2) * ((C₁ / ρ) * I) := by
        exact mul_le_mul_of_nonneg_left (hsrc₃ i j) (by positivity)
      _ = (40 / ρ ^ 2) * (C₁ / ρ) * I := by ring
  have hp₄ (i j : Fin 3) :
      |pressureNewtonianDerivativePotential i
          (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x| ≤
        (40 / ρ ^ 2) * (C₁ / ρ) * I := by
    calc
      _ ≤ (40 / ρ ^ 2) * ∫ y,
          |pressureUTensor u c (y, s) i j * spatialDeriv η j y| :=
        pressureP4_component_annular_bound hρ hr hhalf x hx i j
          (hI₄ i j) (hP₄ i j hx) (hA₄ i j)
      _ ≤ (40 / ρ ^ 2) * ((C₁ / ρ) * I) := by
        exact mul_le_mul_of_nonneg_left (hsrc₄ i j) (by positivity)
      _ = (40 / ρ ^ 2) * (C₁ / ρ) * I := by ring
  have hsum₂ : |pressureP2 η u c s x| ≤ 18 * C₂ / ρ ^ 3 * I := by
    rw [pressureP2]
    calc
      |∑ i, ∑ j, pressureNewtonianPotential
          (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x| ≤
          ∑ i, |∑ j, pressureNewtonianPotential
            (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |pressureNewtonianPotential
            (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x| := by
        gcongr with i hi
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, ((2 / ρ) * (C₂ / ρ ^ 2) * I) := by
        gcongr with i hi j hj
        exact hp₂ i j
      _ = 18 * C₂ / ρ ^ 3 * I := by
        simp only [Fin.sum_univ_three]
        ring
  have hsum₃ : |pressureP3 η u c s x| ≤ 360 * C₁ / ρ ^ 3 * I := by
    rw [pressureP3]
    calc
      |∑ i, ∑ j, pressureNewtonianDerivativePotential j
          (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x| ≤
          ∑ i, |∑ j, pressureNewtonianDerivativePotential j
            (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |pressureNewtonianDerivativePotential j
            (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x| := by
        gcongr with i hi
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, ((40 / ρ ^ 2) * (C₁ / ρ) * I) := by
        gcongr with i hi j hj
        exact hp₃ i j
      _ = 360 * C₁ / ρ ^ 3 * I := by
        simp only [Fin.sum_univ_three]
        ring
  have hsum₄ : |pressureP4 η u c s x| ≤ 360 * C₁ / ρ ^ 3 * I := by
    rw [pressureP4]
    calc
      |∑ i, ∑ j, pressureNewtonianDerivativePotential i
          (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x| ≤
          ∑ i, |∑ j, pressureNewtonianDerivativePotential i
            (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |pressureNewtonianDerivativePotential i
            (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x| := by
        gcongr with i hi
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, ((40 / ρ ^ 2) * (C₁ / ρ) * I) := by
        gcongr with i hi j hj
        exact hp₄ i j
      _ = 360 * C₁ / ρ ^ 3 * I := by
        simp only [Fin.sum_univ_three]
        ring
  calc
    |pressureP2 η u c s x| + |pressureP3 η u c s x| +
        |pressureP4 η u c s x| ≤
        18 * C₂ / ρ ^ 3 * I + 360 * C₁ / ρ ^ 3 * I +
          360 * C₁ / ρ ^ 3 * I := by gcongr
    _ = (18 * C₂ + 720 * C₁) / ρ ^ 3 *
        ∫ y in vec3Ball x₀ ρ, pressureUTensorNorm u c s y := by
      dsimp [I]
      ring

end CKN
