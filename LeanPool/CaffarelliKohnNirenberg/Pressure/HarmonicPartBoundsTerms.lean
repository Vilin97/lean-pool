/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicPartBoundsHelpers

/-!
# Harmonic Part Bounds Terms

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

private theorem norm_iteratedFDeriv_fin3_double_sum_le
    {P : Fin 3 → Fin 3 → Vec3 → ℝ} {U : Set Vec3} {k : ℕ} {C : ℝ}
    (hU : IsOpen U) (hP : ∀ i j, ContDiffOn ℝ (k : ℕ) (P i j) U)
    {x : Vec3} (hx : x ∈ U)
    (hbound : ∀ i j, ‖iteratedFDeriv ℝ k (P i j) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (fun z => ∑ i : Fin 3, ∑ j : Fin 3, P i j z) x‖ ≤
      9 * C := by
  have hinner (i : Fin 3) : ContDiffOn ℝ (k : ℕ)
      (fun z => ∑ j : Fin 3, P i j z) U :=
    ContDiffOn.sum (fun j _ => hP i j)
  calc
    _ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ k (fun z => ∑ j : Fin 3, P i j z) x‖ :=
      norm_iteratedFDeriv_fin3_sum_le hU hinner hx
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖iteratedFDeriv ℝ k (P i j) x‖ :=
      Finset.sum_le_sum (fun i _ => norm_iteratedFDeriv_fin3_sum_le hU (hP i) hx)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, C :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hbound i j))
    _ = 9 * C := by
      simp only [Fin.sum_univ_three]
      ring

private lemma harmonicPressurePart_term_bounds_hLap_1 :
    ∀ {η : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ),
      η = mollifiedBallCutoff x₀ hρ →
        ∀ (y : Vec3),
          |spatialLaplacian η y| ≤ (3 : ℝ) * cutoffSecondDerivativeConstant / ρ ^ (2 : ℕ)
    := by
  intro η x₀ ρ hρ hηeq y
  rw [spatialLaplacian]
  calc
    |∑ i : Fin 3, mixedSecond η i i y| ≤
        ∑ i : Fin 3, |mixedSecond η i i y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, cutoffSecondDerivativeConstant / ρ ^ 2 := by
      gcongr with i hi
      simpa [hηeq] using pressure_cutoff_mixedSecond_bound x₀ hρ y i i
    _ = 3 * cutoffSecondDerivativeConstant / ρ ^ 2 := by
      simp only [Fin.sum_univ_three]
      ring

private lemma harmonicPressurePart_term_bounds_h2term_2 :
    ∀ (k : ℕ) (cN : ℝ),
      (0 : ℝ) ≤ cN →
        (∀ (x₀ : Vec3) (ρ : ℝ),
            (0 : ℝ) < ρ →
              ∀ (g : Vec3 → ℝ),
                @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                  (∀ y ∉ pressureAnnulus x₀ ρ, g y = (0 : ℝ)) →
                    ∀ x ∈ vec3Ball x₀ (ρ / (2 : ℝ)),
                      norm (E := Vec3 [×k]→L[ℝ] ℝ)
                          (iteratedFDeriv ℝ k (pressureNewtonianPotential g) x) ≤
                        cN * (((3 : ℝ) * ρ / (20 : ℝ)) ^ ((1 : ℕ) + k))⁻¹ *
                          @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                            ‖g y‖) →
          ∀ {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ}
            {s : ℝ} {x₀ : Vec3} {ρ : ℝ},
            (0 : ℝ) < ρ →
              PressureHarmonicPotentialData (vec3Ball x₀ ((13 : ℝ) * ρ / (20 : ℝ))) η u c p s →
                ∀ (A : ℝ),
                  ∀ x ∈ vec3Ball x₀ (ρ / (2 : ℝ)),
                    let W : Set Vec3 := vec3Ball x₀ ρ;
                    let Ann : Set Vec3 := pressureAnnulus x₀ ρ;
                    (0 : ℝ) ≤ cutoffSecondDerivativeConstant / ρ ^ (2 : ℕ) →
                      (∀ (i j : Fin (3 : ℕ)) (y : Vec3),
                          mixedSecond η i j y * pressureUTensor u c (y, s) i j ≠ (0 : ℝ) →
                            y ∈ Ann) →
                        (∀ (i j : Fin (3 : ℕ)),
                            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                                fun (y : Vec3) =>
                                |mixedSecond η i j y * pressureUTensor u c (y, s) i j|) ≤
                              cutoffSecondDerivativeConstant / ρ ^ (2 : ℕ) *
                                @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                  (Measure.restrict volume W) fun (y : Vec3) =>
                                  pressureUTensorNorm u c s y) →
                          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                (Measure.restrict volume W) fun (y : Vec3) =>
                                pressureUTensorNorm u c s y) ≤
                              (2 : ℝ) * ρ * A →
                            ∀ (i j : Fin (3 : ℕ)),
                              norm (E := Vec3 [×k]→L[ℝ] ℝ)
                                  (iteratedFDeriv ℝ k
                                    (pressureNewtonianPotential fun (y : Vec3) =>
                                      mixedSecond η i j y * pressureUTensor u c (y, s) i j)
                                    x) ≤
                                (2 : ℝ) * cN * cutoffSecondDerivativeConstant *
                                      (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) *
                                    ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                                  A
    := by
  intro k cN hcN hN η u c p s x₀ ρ hρ hdata A x hx W Ann hC₂ρ hsource2 hU2 hUboundW i j
  have hpot := hN x₀ ρ hρ
    (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j)
    (hdata.p2_integrable i j)
    (fun y hy => by
      by_contra hne
      exact hy (hsource2 i j y hne)) x hx
  have hfac : 0 ≤ cN * ((3 * ρ / 20) ^ (1 + k))⁻¹ := by
    exact mul_nonneg hcN (inv_nonneg.mpr (by positivity))
  calc
    _ ≤ cN * ((3 * ρ / 20) ^ (1 + k))⁻¹ *
        ∫ y, |mixedSecond η i j y * pressureUTensor u c (y, s) i j| := by
      simpa only [Real.norm_eq_abs] using hpot
    _ ≤ cN * ((3 * ρ / 20) ^ (1 + k))⁻¹ *
        ((cutoffSecondDerivativeConstant / ρ ^ 2) *
          ∫ y in W, pressureUTensorNorm u c s y) := by
      exact mul_le_mul_of_nonneg_left (hU2 i j) hfac
    _ ≤ cN * ((3 * ρ / 20) ^ (1 + k))⁻¹ *
        ((cutoffSecondDerivativeConstant / ρ ^ 2) * (2 * ρ * A)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hUboundW hC₂ρ) hfac
    _ = _ := by
      rw [div_eq_mul_inv]
      calc
        cN * ((3 * ρ / 20) ^ (1 + k))⁻¹ *
            (cutoffSecondDerivativeConstant * (ρ ^ 2)⁻¹ * (2 * ρ * A)) =
            2 * cN * cutoffSecondDerivativeConstant *
              (((3 * ρ / 20) ^ (1 + k))⁻¹ * (ρ ^ 2)⁻¹ * ρ) * A := by ring
        _ = _ := by rw [annulus_power_normalize_potential hρ k]; ring_nf

private lemma harmonicPressurePart_term_bounds_hDall_3 :
    ∀ (k : ℕ) (cD0 : ℝ),
      (∀ (x₀ : Vec3) (ρ : ℝ),
          (0 : ℝ) < ρ →
            ∀ (g : Vec3 → ℝ),
              @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                (∀ y ∉ pressureAnnulus x₀ ρ, g y = (0 : ℝ)) →
                  ∀ x ∈ vec3Ball x₀ (ρ / (2 : ℝ)),
                    norm (E := Vec3 [×k]→L[ℝ] ℝ)
                        (iteratedFDeriv ℝ k
                          (pressureNewtonianDerivativePotential (0 : Fin (3 : ℕ)) g) x) ≤
                      cD0 * (((3 : ℝ) * ρ / (20 : ℝ)) ^ ((2 : ℕ) + k))⁻¹ *
                        @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                          ‖g y‖) →
        ∀ (cD1 : ℝ),
          (∀ (x₀ : Vec3) (ρ : ℝ),
              (0 : ℝ) < ρ →
                ∀ (g : Vec3 → ℝ),
                  @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                    (∀ y ∉ pressureAnnulus x₀ ρ, g y = (0 : ℝ)) →
                      ∀ x ∈ vec3Ball x₀ (ρ / (2 : ℝ)),
                        norm (E := Vec3 [×k]→L[ℝ] ℝ)
                            (iteratedFDeriv ℝ k
                              (pressureNewtonianDerivativePotential (1 : Fin (3 : ℕ)) g) x) ≤
                          cD1 * (((3 : ℝ) * ρ / (20 : ℝ)) ^ ((2 : ℕ) + k))⁻¹ *
                            @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                              fun (y : Vec3) => ‖g y‖) →
            ∀ (cD2 : ℝ),
              (∀ (x₀ : Vec3) (ρ : ℝ),
                  (0 : ℝ) < ρ →
                    ∀ (g : Vec3 → ℝ),
                      @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                        (∀ y ∉ pressureAnnulus x₀ ρ, g y = (0 : ℝ)) →
                          ∀ x ∈ vec3Ball x₀ (ρ / (2 : ℝ)),
                            norm (E := Vec3 [×k]→L[ℝ] ℝ)
                                (iteratedFDeriv ℝ k
                                  (pressureNewtonianDerivativePotential (2 : Fin (3 : ℕ)) g) x) ≤
                              cD2 * (((3 : ℝ) * ρ / (20 : ℝ)) ^ ((2 : ℕ) + k))⁻¹ *
                                @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                                  fun (y : Vec3) => ‖g y‖) →
                let cD : ℝ := cD0 + cD1 + cD2;
                ∀ {x₀ : Vec3} {ρ : ℝ},
                  (0 : ℝ) < ρ →
                    ∀ x ∈ vec3Ball x₀ (ρ / (2 : ℝ)),
                      let Ann : Set Vec3 := pressureAnnulus x₀ ρ;
                      cD0 ≤ cD →
                        cD1 ≤ cD →
                          cD2 ≤ cD →
                            ∀ {j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                              @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                                (∀ y ∉ Ann, g y = (0 : ℝ)) →
                                  norm (E := Vec3 [×k]→L[ℝ] ℝ)
                                      (iteratedFDeriv ℝ k (pressureNewtonianDerivativePotential j g)
                                        x) ≤
                                    cD * (((3 : ℝ) * ρ / (20 : ℝ)) ^ ((2 : ℕ) + k))⁻¹ *
                                      @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                                        fun (y : Vec3) => ‖g y‖
    := by
  intro k cD0 hD0 cD1 hD1 cD2 hD2 cD x₀ ρ hρ x hx Ann hcD0le hcD1le hcD2le j g hg hg0
  fin_cases j
  · have h := hD0 x₀ ρ hρ g hg hg0 x hx
    calc
      _ ≤ cD0 * ((3 * ρ / 20) ^ (2 + k))⁻¹ * ∫ y, ‖g y‖ := h
      _ ≤ cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ * ∫ y, ‖g y‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcD0le (by positivity)) (by positivity)
  · have h := hD1 x₀ ρ hρ g hg hg0 x hx
    calc
      _ ≤ cD1 * ((3 * ρ / 20) ^ (2 + k))⁻¹ * ∫ y, ‖g y‖ := h
      _ ≤ cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ * ∫ y, ‖g y‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcD1le (by positivity)) (by positivity)
  · have h := hD2 x₀ ρ hρ g hg hg0 x hx
    calc
      _ ≤ cD2 * ((3 * ρ / 20) ^ (2 + k))⁻¹ * ∫ y, ‖g y‖ := h
      _ ≤ cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ * ∫ y, ‖g y‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcD2le (by positivity)) (by positivity)

private lemma harmonicPressurePart_term_bounds_h3term_4 :
    ∀ (k : ℕ) (cD0 cD1 cD2 : ℝ),
      let cD : ℝ := cD0 + cD1 + cD2;
      (0 : ℝ) ≤ cD →
        ∀ {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ} {s : ℝ}
          {x₀ : Vec3} {ρ : ℝ},
          (0 : ℝ) < ρ →
            PressureHarmonicPotentialData (vec3Ball x₀ ((13 : ℝ) * ρ / (20 : ℝ))) η u c p s →
              ∀ (A : ℝ) (x : Vec3),
                let W : Set Vec3 := vec3Ball x₀ ρ;
                let Ann : Set Vec3 := pressureAnnulus x₀ ρ;
                (0 : ℝ) ≤ cutoffGradientConstant / ρ →
                  (∀ (i j : Fin (3 : ℕ)) (y : Vec3),
                      spatialDeriv η i y * pressureUTensor u c (y, s) i j ≠ (0 : ℝ) → y ∈ Ann) →
                    (∀ (i j : Fin (3 : ℕ)),
                        (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                            |spatialDeriv η i y * pressureUTensor u c (y, s) i j|) ≤
                          cutoffGradientConstant / ρ *
                            @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                              (Measure.restrict volume W) fun (y : Vec3) =>
                              pressureUTensorNorm u c s y) →
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume W)
                            fun (y : Vec3) => pressureUTensorNorm u c s y) ≤
                          (2 : ℝ) * ρ * A →
                        (∀ {j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                            @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                              (∀ y ∉ Ann, g y = (0 : ℝ)) →
                                norm (E := Vec3 [×k]→L[ℝ] ℝ)
                                    (iteratedFDeriv ℝ k (pressureNewtonianDerivativePotential j g)
                                      x) ≤
                                  cD * (((3 : ℝ) * ρ / (20 : ℝ)) ^ ((2 : ℕ) + k))⁻¹ *
                                    @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                                      fun (y : Vec3) => ‖g y‖) →
                          ∀ (i j : Fin (3 : ℕ)),
                            norm (E := Vec3 [×k]→L[ℝ] ℝ)
                                (iteratedFDeriv ℝ k
                                  (pressureNewtonianDerivativePotential j fun (y : Vec3) =>
                                    pressureUTensor u c (y, s) i j * spatialDeriv η i y)
                                  x) ≤
                              (2 : ℝ) * cD * cutoffGradientConstant *
                                    (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                                  ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                                A
    := by
  intro k cD0 cD1 cD2 cD hcD η u c p s x₀ ρ hρ hdata A x W Ann hC₁ρ hsource3 hU3 hUboundW hDall i j
  have hpot := hDall (j := j)
    (hdata.p3_integrable i j) (fun y hy => by
      by_contra hne
      exact hy (hsource3 i j y (by simpa [mul_comm] using hne)))
  have hfac : 0 ≤ cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ := by
    exact mul_nonneg hcD (inv_nonneg.mpr (by positivity))
  calc
    _ ≤ cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ *
        ∫ y, |pressureUTensor u c (y, s) i j * spatialDeriv η i y| := by
      simpa only [Real.norm_eq_abs] using hpot
    _ ≤ cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ *
        ((cutoffGradientConstant / ρ) *
          ∫ y in W, pressureUTensorNorm u c s y) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [mul_comm] using hU3 i j) hfac
    _ ≤ cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ *
        ((cutoffGradientConstant / ρ) * (2 * ρ * A)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hUboundW hC₁ρ) hfac
    _ = _ := by
      rw [div_eq_mul_inv]
      calc
        cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ *
            (cutoffGradientConstant * ρ⁻¹ * (2 * ρ * A)) =
            2 * cD * cutoffGradientConstant *
              (((3 * ρ / 20) ^ (2 + k))⁻¹ * (ρ ^ (1 : ℕ))⁻¹ * ρ) * A := by ring
        _ = _ := by rw [annulus_power_normalize_derivative hρ k]; ring_nf

private lemma harmonicPressurePart_term_bounds_h4term_5 :
    ∀ (k : ℕ) (cD0 cD1 cD2 : ℝ),
      let cD : ℝ := cD0 + cD1 + cD2;
      (0 : ℝ) ≤ cD →
        ∀ {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ} {s : ℝ}
          {x₀ : Vec3} {ρ : ℝ},
          (0 : ℝ) < ρ →
            PressureHarmonicPotentialData (vec3Ball x₀ ((13 : ℝ) * ρ / (20 : ℝ))) η u c p s →
              ∀ (A : ℝ) (x : Vec3),
                let W : Set Vec3 := vec3Ball x₀ ρ;
                let Ann : Set Vec3 := pressureAnnulus x₀ ρ;
                (0 : ℝ) ≤ cutoffGradientConstant / ρ →
                  (∀ (i j : Fin (3 : ℕ)) (y : Vec3),
                      spatialDeriv η j y * pressureUTensor u c (y, s) i j ≠ (0 : ℝ) → y ∈ Ann) →
                    (∀ (i j : Fin (3 : ℕ)),
                        (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                            |spatialDeriv η j y * pressureUTensor u c (y, s) i j|) ≤
                          cutoffGradientConstant / ρ *
                            @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                              (Measure.restrict volume W) fun (y : Vec3) =>
                              pressureUTensorNorm u c s y) →
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume W)
                            fun (y : Vec3) => pressureUTensorNorm u c s y) ≤
                          (2 : ℝ) * ρ * A →
                        (∀ {j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                            @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                              (∀ y ∉ Ann, g y = (0 : ℝ)) →
                                norm (E := Vec3 [×k]→L[ℝ] ℝ)
                                    (iteratedFDeriv ℝ k (pressureNewtonianDerivativePotential j g)
                                      x) ≤
                                  cD * (((3 : ℝ) * ρ / (20 : ℝ)) ^ ((2 : ℕ) + k))⁻¹ *
                                    @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                                      fun (y : Vec3) => ‖g y‖) →
                          ∀ (i j : Fin (3 : ℕ)),
                            norm (E := Vec3 [×k]→L[ℝ] ℝ)
                                (iteratedFDeriv ℝ k
                                  (pressureNewtonianDerivativePotential i fun (y : Vec3) =>
                                    pressureUTensor u c (y, s) i j * spatialDeriv η j y)
                                  x) ≤
                              (2 : ℝ) * cD * cutoffGradientConstant *
                                    (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                                  ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                                A
    := by
  intro k cD0 cD1 cD2 cD hcD η u c p s x₀ ρ hρ hdata A x W Ann hC₁ρ hsource4 hU4 hUboundW hDall i j
  have hpot := hDall (j := i)
    (hdata.p4_integrable i j) (fun y hy => by
      by_contra hne
      exact hy (hsource4 i j y (by simpa [mul_comm] using hne)))
  have hfac : 0 ≤ cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ := by
    exact mul_nonneg hcD (inv_nonneg.mpr (by positivity))
  calc
    _ ≤ cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ *
        ∫ y, |pressureUTensor u c (y, s) i j * spatialDeriv η j y| := by
      simpa only [Real.norm_eq_abs] using hpot
    _ ≤ cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ *
        ((cutoffGradientConstant / ρ) *
          ∫ y in W, pressureUTensorNorm u c s y) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [mul_comm] using hU4 i j) hfac
    _ ≤ cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ *
        ((cutoffGradientConstant / ρ) * (2 * ρ * A)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hUboundW hC₁ρ) hfac
    _ = _ := by
      rw [div_eq_mul_inv]
      calc
        cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ *
            (cutoffGradientConstant * ρ⁻¹ * (2 * ρ * A)) =
            2 * cD * cutoffGradientConstant *
              (((3 * ρ / 20) ^ (2 + k))⁻¹ * (ρ ^ (1 : ℕ))⁻¹ * ρ) * A := by ring
        _ = _ := by rw [annulus_power_normalize_derivative hρ k]; ring_nf

private lemma harmonicPressurePart_term_bounds_h5term_6 :
    ∀ (k : ℕ) (cN : ℝ),
      (0 : ℝ) ≤ cN →
        (∀ (x₀ : Vec3) (ρ : ℝ),
            (0 : ℝ) < ρ →
              ∀ (g : Vec3 → ℝ),
                @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                  (∀ y ∉ pressureAnnulus x₀ ρ, g y = (0 : ℝ)) →
                    ∀ x ∈ vec3Ball x₀ (ρ / (2 : ℝ)),
                      norm (E := Vec3 [×k]→L[ℝ] ℝ)
                          (iteratedFDeriv ℝ k (pressureNewtonianPotential g) x) ≤
                        cN * (((3 : ℝ) * ρ / (20 : ℝ)) ^ ((1 : ℕ) + k))⁻¹ *
                          @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                            ‖g y‖) →
          let κ : ℝ := (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ);
          ∀ {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ}
            {s : ℝ} {x₀ : Vec3} {ρ : ℝ},
            (0 : ℝ) < ρ →
              PressureHarmonicPotentialData (vec3Ball x₀ ((13 : ℝ) * ρ / (20 : ℝ))) η u c p s →
                ∀ (B : ℝ),
                  ∀ x ∈ vec3Ball x₀ (ρ / (2 : ℝ)),
                    let W : Set Vec3 := vec3Ball x₀ ρ;
                    let Ann : Set Vec3 := pressureAnnulus x₀ ρ;
                    (0 : ℝ) ≤ (3 : ℝ) * cutoffSecondDerivativeConstant / ρ ^ (2 : ℕ) →
                      (∀ (y : Vec3), spatialLaplacian η y * p (y, s) ≠ (0 : ℝ) → y ∈ Ann) →
                        ((@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                              |spatialLaplacian η y * p (y, s)|) ≤
                            (3 : ℝ) * cutoffSecondDerivativeConstant / ρ ^ (2 : ℕ) *
                              @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                (Measure.restrict volume W) fun (y : Vec3) => |p (y, s)|) →
                          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                (Measure.restrict volume W) fun (y : Vec3) => |p (y, s)|) ≤
                              κ * ρ * B →
                            norm (E := Vec3 [×k]→L[ℝ] ℝ) (iteratedFDeriv ℝ k (pressureP5 η p s) x) ≤
                              (3 : ℝ) * κ * cN * cutoffSecondDerivativeConstant *
                                    (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) *
                                  ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                                B
    := by
  intro k cN hcN hN κ η u c p s x₀ ρ hρ hdata B x hx W Ann hC₂ρ3 hsource5 hP5 hPboundW
  have hpot := hN x₀ ρ hρ
    (fun y => p (y, s) * spatialLaplacian η y)
    (hdata.p5_integrable)
    (fun y hy => by
      by_contra hne
      exact hy (hsource5 y (by simpa [mul_comm] using hne))) x hx
  have hfac : 0 ≤ cN * ((3 * ρ / 20) ^ (1 + k))⁻¹ := by
    exact mul_nonneg hcN (inv_nonneg.mpr (by positivity))
  calc
    _ = ‖iteratedFDeriv ℝ k
        (pressureNewtonianPotential
          (fun y => p (y, s) * spatialLaplacian η y)) x‖ := by
      change ‖iteratedFDeriv ℝ k
        (fun z => -pressureNewtonianPotential
          (fun y => p (y, s) * spatialLaplacian η y) z) x‖ = _
      rw [show (fun z => -pressureNewtonianPotential
            (fun y => p (y, s) * spatialLaplacian η y) z) =
          -(pressureNewtonianPotential
            (fun y => p (y, s) * spatialLaplacian η y)) by rfl]
      rw [iteratedFDeriv_neg, Pi.neg_apply, norm_neg]
    _ ≤ cN * ((3 * ρ / 20) ^ (1 + k))⁻¹ *
        ∫ y, |p (y, s) * spatialLaplacian η y| := by
      simpa only [Real.norm_eq_abs] using hpot
    _ ≤ cN * ((3 * ρ / 20) ^ (1 + k))⁻¹ *
        ((3 * cutoffSecondDerivativeConstant / ρ ^ 2) *
          ∫ y in W, |p (y, s)|) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [mul_comm] using hP5) hfac
    _ ≤ cN * ((3 * ρ / 20) ^ (1 + k))⁻¹ *
        ((3 * cutoffSecondDerivativeConstant / ρ ^ 2) * (κ * ρ * B)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hPboundW hC₂ρ3) hfac
    _ = _ := by
      rw [div_eq_mul_inv]
      calc
        cN * ((3 * ρ / 20) ^ (1 + k))⁻¹ *
            (3 * cutoffSecondDerivativeConstant * (ρ ^ 2)⁻¹ * (κ * ρ * B)) =
            3 * κ * cN * cutoffSecondDerivativeConstant *
              (((3 * ρ / 20) ^ (1 + k))⁻¹ * (ρ ^ 2)⁻¹ * ρ) * B := by ring
        _ = _ := by rw [annulus_power_normalize_potential hρ k]; ring_nf

private lemma harmonicPressurePart_term_bounds_h6term_7 :
    ∀ (k : ℕ) (cD0 cD1 cD2 : ℝ),
      let cD : ℝ := cD0 + cD1 + cD2;
      let κ : ℝ := (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ);
      (0 : ℝ) ≤ cD →
        ∀ {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ} {s : ℝ}
          {x₀ : Vec3} {ρ : ℝ},
          (0 : ℝ) < ρ →
            PressureHarmonicPotentialData (vec3Ball x₀ ((13 : ℝ) * ρ / (20 : ℝ))) η u c p s →
              ∀ (B : ℝ) (x : Vec3),
                let W : Set Vec3 := vec3Ball x₀ ρ;
                let Ann : Set Vec3 := pressureAnnulus x₀ ρ;
                (0 : ℝ) ≤ cutoffGradientConstant / ρ →
                  (∀ (j : Fin (3 : ℕ)) (y : Vec3),
                      spatialDeriv η j y * p (y, s) ≠ (0 : ℝ) → y ∈ Ann) →
                    (∀ (j : Fin (3 : ℕ)),
                        (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                            |spatialDeriv η j y * p (y, s)|) ≤
                          cutoffGradientConstant / ρ *
                            @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                              (Measure.restrict volume W) fun (y : Vec3) => |p (y, s)|) →
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume W)
                            fun (y : Vec3) => |p (y, s)|) ≤
                          κ * ρ * B →
                        (∀ {j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                            @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                              (∀ y ∉ Ann, g y = (0 : ℝ)) →
                                norm (E := Vec3 [×k]→L[ℝ] ℝ)
                                    (iteratedFDeriv ℝ k (pressureNewtonianDerivativePotential j g)
                                      x) ≤
                                  cD * (((3 : ℝ) * ρ / (20 : ℝ)) ^ ((2 : ℕ) + k))⁻¹ *
                                    @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                                      fun (y : Vec3) => ‖g y‖) →
                          ∀ (j : Fin (3 : ℕ)),
                            norm (E := Vec3 [×k]→L[ℝ] ℝ)
                                (iteratedFDeriv ℝ k
                                  (pressureNewtonianDerivativePotential j fun (y : Vec3) =>
                                    spatialDeriv η j y * p (y, s))
                                  x) ≤
                              κ * cD * cutoffGradientConstant *
                                    (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                                  ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                                B
    := by
  intro k cD0 cD1 cD2 cD κ hcD η u c p s x₀ ρ hρ hdata B x W Ann hC₁ρ hsource6 hP6 hPboundW hDall j
  have hpot := hDall (j := j)
    (hdata.p6_integrable j) (fun y hy => by
      by_contra hne
      exact hy (hsource6 j y hne))
  have hfac : 0 ≤ cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ := by
    exact mul_nonneg hcD (inv_nonneg.mpr (by positivity))
  calc
    _ ≤ cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ *
        ∫ y, |spatialDeriv η j y * p (y, s)| := by
      simpa only [Real.norm_eq_abs] using hpot
    _ ≤ cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ *
        ((cutoffGradientConstant / ρ) * ∫ y in W, |p (y, s)|) := by
      exact mul_le_mul_of_nonneg_left (hP6 j) hfac
    _ ≤ cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ *
        ((cutoffGradientConstant / ρ) * (κ * ρ * B)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hPboundW hC₁ρ) hfac
    _ = _ := by
      rw [div_eq_mul_inv]
      calc
        cD * ((3 * ρ / 20) ^ (2 + k))⁻¹ *
            (cutoffGradientConstant * ρ⁻¹ * (κ * ρ * B)) =
            κ * cD * cutoffGradientConstant *
              (((3 * ρ / 20) ^ (2 + k))⁻¹ * (ρ ^ (1 : ℕ))⁻¹ * ρ) * B := by ring
        _ = _ := by rw [annulus_power_normalize_derivative hρ k]; ring_nf

private lemma harmonicPressurePart_term_bounds_hcont6_8 :
    ∀ (k : ℕ) {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ}
      {s : ℝ} {x₀ : Vec3} {ρ : ℝ},
      PressureHarmonicPotentialData (vec3Ball x₀ ((13 : ℝ) * ρ / (20 : ℝ))) η u c p s →
        ∀ (_ : Vec3),
          let V : Set Vec3 := vec3Ball x₀ (ρ / (2 : ℝ));
          let Ann : Set Vec3 := pressureAnnulus x₀ ρ;
          (∀ (j : Fin (3 : ℕ)) (y : Vec3), spatialDeriv η j y * p (y, s) ≠ (0 : ℝ) → y ∈ Ann) →
            (∀ {j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                  (∀ y ∉ Ann, g y = (0 : ℝ)) →
                    ContDiffOn ℝ (↑k : WithTop ℕ∞) (pressureNewtonianDerivativePotential j g) V) →
              ContDiffOn ℝ (↑k : WithTop ℕ∞) (pressureP6 η p s) V
    := by
  intro k η u c p s x₀ ρ hdata x V Ann hsource6 hcontD
  have hsum : ContDiffOn ℝ (k : ℕ)
      (fun x => ∑ j, pressureNewtonianDerivativePotential j
        (fun y => spatialDeriv η j y * p (y, s)) x) V := by
    apply ContDiffOn.sum
    intro j hj
    exact hcontD (hdata.p6_integrable j) (fun y hy => by
      by_contra hne
      exact hy (hsource6 j y hne))
  change ContDiffOn ℝ (k : ℕ)
    (fun x => -2 * ∑ j, pressureNewtonianDerivativePotential j
      (fun y => spatialDeriv η j y * p (y, s)) x) V
  simpa only [smul_eq_mul] using hsum.const_smul (-2 : ℝ)

private lemma harmonicPressurePart_term_bounds_h2deriv_9 :
    ∀ (k : ℕ) (cN : ℝ) {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
      {p : ParabolicPoint → ℝ} {s : ℝ} {x₀ : Vec3} {ρ : ℝ},
      PressureHarmonicPotentialData (vec3Ball x₀ ((13 : ℝ) * ρ / (20 : ℝ))) η u c p s →
        ∀ (A : ℝ) (x : Vec3),
          let V : Set Vec3 := vec3Ball x₀ (ρ / (2 : ℝ));
          let Ann : Set Vec3 := pressureAnnulus x₀ ρ;
          (∀ (i j : Fin (3 : ℕ)) (y : Vec3),
              mixedSecond η i j y * pressureUTensor u c (y, s) i j ≠ (0 : ℝ) → y ∈ Ann) →
            (∀ (i j : Fin (3 : ℕ)),
                norm (E := Vec3 [×k]→L[ℝ] ℝ)
                    (iteratedFDeriv ℝ k
                      (pressureNewtonianPotential fun (y : Vec3) =>
                        mixedSecond η i j y * pressureUTensor u c (y, s) i j)
                      x) ≤
                  (2 : ℝ) * cN * cutoffSecondDerivativeConstant *
                        (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) *
                      ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                    A) →
              (∀ {g : Vec3 → ℝ},
                  @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                    (∀ y ∉ Ann, g y = (0 : ℝ)) →
                      ContDiffOn ℝ (↑k : WithTop ℕ∞) (pressureNewtonianPotential g) V) →
                IsOpen V →
                  x ∈ V →
                    norm (E := Vec3 [×k]→L[ℝ] ℝ) (iteratedFDeriv ℝ k (pressureP2 η u c s) x) ≤
                      (18 : ℝ) * cN * cutoffSecondDerivativeConstant *
                            (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) *
                          ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                        A
    := by
  intro k cN η u c p s x₀ ρ hdata A x V Ann hsource2 h2term hcontN hVopen hxV
  have hsum := norm_iteratedFDeriv_fin3_double_sum_le
    (P := fun i j => pressureNewtonianPotential
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j))
    hVopen (fun i j => hcontN (hdata.p2_integrable i j) (fun y hy => by
      by_contra hne
      exact hy (hsource2 i j y hne))) hxV h2term
  calc
    _ ≤ 9 * (2 * cN * cutoffSecondDerivativeConstant *
        (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) *
          ρ ^ (-(2 + k : ℝ)) * A) := hsum
    _ = _ := by ring

private lemma harmonicPressurePart_term_bounds_h3deriv_10 :
    ∀ (k : ℕ) (cD0 cD1 cD2 : ℝ),
      let cD : ℝ := cD0 + cD1 + cD2;
      ∀ {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ} {s : ℝ}
        {x₀ : Vec3} {ρ : ℝ},
        PressureHarmonicPotentialData (vec3Ball x₀ ((13 : ℝ) * ρ / (20 : ℝ))) η u c p s →
          ∀ (A : ℝ) (x : Vec3),
            let V : Set Vec3 := vec3Ball x₀ (ρ / (2 : ℝ));
            let Ann : Set Vec3 := pressureAnnulus x₀ ρ;
            (∀ (i j : Fin (3 : ℕ)) (y : Vec3),
                spatialDeriv η i y * pressureUTensor u c (y, s) i j ≠ (0 : ℝ) → y ∈ Ann) →
              (∀ (i j : Fin (3 : ℕ)),
                  norm (E := Vec3 [×k]→L[ℝ] ℝ)
                      (iteratedFDeriv ℝ k
                        (pressureNewtonianDerivativePotential j fun (y : Vec3) =>
                          pressureUTensor u c (y, s) i j * spatialDeriv η i y)
                        x) ≤
                    (2 : ℝ) * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                        ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                      A) →
                (∀ {j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                    @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                      (∀ y ∉ Ann, g y = (0 : ℝ)) →
                        ContDiffOn ℝ (↑k : WithTop ℕ∞) (pressureNewtonianDerivativePotential j g)
                          V) →
                  IsOpen V →
                    x ∈ V →
                      norm (E := Vec3 [×k]→L[ℝ] ℝ) (iteratedFDeriv ℝ k (pressureP3 η u c s) x) ≤
                        (18 : ℝ) * cD * cutoffGradientConstant *
                              (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                            ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                          A
    := by
  intro k cD0 cD1 cD2 cD η u c p s x₀ ρ hdata A x V Ann hsource3 h3term hcontD hVopen hxV
  have hsum := norm_iteratedFDeriv_fin3_double_sum_le
    (P := fun i j => pressureNewtonianDerivativePotential j
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y))
    hVopen (fun i j => hcontD (hdata.p3_integrable i j) (fun y hy => by
      by_contra hne
      exact hy (hsource3 i j y (by simpa [mul_comm] using hne)))) hxV h3term
  calc
    _ ≤ 9 * (2 * cD * cutoffGradientConstant *
        (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) *
          ρ ^ (-(2 + k : ℝ)) * A) := hsum
    _ = _ := by ring

private lemma harmonicPressurePart_term_bounds_h4deriv_11 :
    ∀ (k : ℕ) (cD0 cD1 cD2 : ℝ),
      let cD : ℝ := cD0 + cD1 + cD2;
      ∀ {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ} {s : ℝ}
        {x₀ : Vec3} {ρ : ℝ},
        PressureHarmonicPotentialData (vec3Ball x₀ ((13 : ℝ) * ρ / (20 : ℝ))) η u c p s →
          ∀ (A : ℝ) (x : Vec3),
            let V : Set Vec3 := vec3Ball x₀ (ρ / (2 : ℝ));
            let Ann : Set Vec3 := pressureAnnulus x₀ ρ;
            (∀ (i j : Fin (3 : ℕ)) (y : Vec3),
                spatialDeriv η j y * pressureUTensor u c (y, s) i j ≠ (0 : ℝ) → y ∈ Ann) →
              (∀ (i j : Fin (3 : ℕ)),
                  norm (E := Vec3 [×k]→L[ℝ] ℝ)
                      (iteratedFDeriv ℝ k
                        (pressureNewtonianDerivativePotential i fun (y : Vec3) =>
                          pressureUTensor u c (y, s) i j * spatialDeriv η j y)
                        x) ≤
                    (2 : ℝ) * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                        ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                      A) →
                (∀ {j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                    @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                      (∀ y ∉ Ann, g y = (0 : ℝ)) →
                        ContDiffOn ℝ (↑k : WithTop ℕ∞) (pressureNewtonianDerivativePotential j g)
                          V) →
                  IsOpen V →
                    x ∈ V →
                      norm (E := Vec3 [×k]→L[ℝ] ℝ) (iteratedFDeriv ℝ k (pressureP4 η u c s) x) ≤
                        (18 : ℝ) * cD * cutoffGradientConstant *
                              (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                            ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                          A
    := by
  intro k cD0 cD1 cD2 cD η u c p s x₀ ρ hdata A x V Ann hsource4 h4term hcontD hVopen hxV
  have hsum := norm_iteratedFDeriv_fin3_double_sum_le
    (P := fun i j => pressureNewtonianDerivativePotential i
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y))
    hVopen (fun i j => hcontD (hdata.p4_integrable i j) (fun y hy => by
      by_contra hne
      exact hy (hsource4 i j y (by simpa [mul_comm] using hne)))) hxV h4term
  calc
    _ ≤ 9 * (2 * cD * cutoffGradientConstant *
        (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) *
          ρ ^ (-(2 + k : ℝ)) * A) := hsum
    _ = _ := by ring

private lemma harmonicPressurePart_term_bounds_h6atomDeriv_12 :
    ∀ (k : ℕ) (cD0 cD1 cD2 : ℝ),
      let cD : ℝ := cD0 + cD1 + cD2;
      let κ : ℝ := (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ);
      ∀ {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ} {s : ℝ}
        {x₀ : Vec3} {ρ : ℝ},
        PressureHarmonicPotentialData (vec3Ball x₀ ((13 : ℝ) * ρ / (20 : ℝ))) η u c p s →
          ∀ (B : ℝ) (x : Vec3),
            let V : Set Vec3 := vec3Ball x₀ (ρ / (2 : ℝ));
            let Ann : Set Vec3 := pressureAnnulus x₀ ρ;
            (∀ (j : Fin (3 : ℕ)) (y : Vec3), spatialDeriv η j y * p (y, s) ≠ (0 : ℝ) → y ∈ Ann) →
              (∀ (j : Fin (3 : ℕ)),
                  norm (E := Vec3 [×k]→L[ℝ] ℝ)
                      (iteratedFDeriv ℝ k
                        (pressureNewtonianDerivativePotential j fun (y : Vec3) =>
                          spatialDeriv η j y * p (y, s))
                        x) ≤
                    κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                        ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                      B) →
                (∀ {j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                    @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                      (∀ y ∉ Ann, g y = (0 : ℝ)) →
                        ContDiffOn ℝ (↑k : WithTop ℕ∞) (pressureNewtonianDerivativePotential j g)
                          V) →
                  IsOpen V →
                    x ∈ V →
                      let Q6 : Fin (3 : ℕ) → Vec3 → ℝ := fun (j : Fin (3 : ℕ)) (z : Vec3) =>
                        (-2 : ℝ) *
                          pressureNewtonianDerivativePotential j
                            (fun (y : Vec3) => spatialDeriv η j y * p (y, s)) z;
                      ∀ (j : Fin (3 : ℕ)),
                        norm (E := Vec3 [×k]→L[ℝ] ℝ) (iteratedFDeriv ℝ k (Q6 j) x) ≤
                          (2 : ℝ) *
                            (κ * cD * cutoffGradientConstant *
                                  (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                                ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                              B)
    := by
  intro k cD0 cD1 cD2 cD κ η u c p s x₀ ρ hdata B x V Ann hsource6 h6term hcontD hVopen hxV Q6 j
  have h := h6term j
  have heq : Q6 j = (-2 : ℝ) •
      (pressureNewtonianDerivativePotential j
        (fun y => spatialDeriv η j y * p (y, s))) := by
    funext z
    simp [Q6, smul_eq_mul]
  have hQ : ContDiffAt ℝ (k : ℕ)
      (pressureNewtonianDerivativePotential j
        (fun y => spatialDeriv η j y * p (y, s))) x :=
    ((hcontD (hdata.p6_integrable j) (fun y hy => by
      by_contra hne
      exact hy (hsource6 j y hne))) x hxV).contDiffAt
        (hVopen.mem_nhds hxV)
  rw [heq, iteratedFDeriv_const_smul_apply hQ]
  calc
    ‖(-2 : ℝ) • iteratedFDeriv ℝ k
        (pressureNewtonianDerivativePotential j
          (fun y => spatialDeriv η j y * p (y, s))) x‖ =
        2 * ‖iteratedFDeriv ℝ k
          (pressureNewtonianDerivativePotential j
            (fun y => spatialDeriv η j y * p (y, s))) x‖ := by
      rw [norm_smul]
      norm_num [Real.norm_eq_abs]
    _ ≤ 2 * (κ * cD * cutoffGradientConstant *
        (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) *
          ρ ^ (-(2 + k : ℝ)) * B) :=
      mul_le_mul_of_nonneg_left h (by norm_num)

private lemma harmonicPressurePart_term_bounds_h6deriv_13 :
    ∀ (k : ℕ) (cD0 cD1 cD2 : ℝ),
      let cD : ℝ := cD0 + cD1 + cD2;
      let κ : ℝ := (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ);
      ∀ {η : Vec3 → ℝ} {p : ParabolicPoint → ℝ} {s : ℝ} {x₀ : Vec3} {ρ : ℝ} (B : ℝ) (x : Vec3),
        let V : Set Vec3 := vec3Ball x₀ (ρ / (2 : ℝ));
        IsOpen V →
          x ∈ V →
            let Q6 : Fin (3 : ℕ) → Vec3 → ℝ := fun (j : Fin (3 : ℕ)) (z : Vec3) =>
              (-2 : ℝ) *
                pressureNewtonianDerivativePotential j
                  (fun (y : Vec3) => spatialDeriv η j y * p (y, s)) z;
            (∀ (j : Fin (3 : ℕ)), ContDiffOn ℝ (↑k : WithTop ℕ∞) (Q6 j) V) →
              (∀ (j : Fin (3 : ℕ)),
                  norm (E := Vec3 [×k]→L[ℝ] ℝ) (iteratedFDeriv ℝ k (Q6 j) x) ≤
                    (2 : ℝ) *
                      (κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                          ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                        B)) →
                norm (E := Vec3 [×k]→L[ℝ] ℝ) (iteratedFDeriv ℝ k (pressureP6 η p s) x) ≤
                  (6 : ℝ) * κ * cD * cutoffGradientConstant *
                        (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                      ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                    B
    := by
  intro k cD0 cD1 cD2 cD κ η p s x₀ ρ B x V hVopen hxV Q6 h6atomCont h6atomDeriv
  have heq : pressureP6 η p s = ∑ j : Fin 3, Q6 j := by
    funext z
    simp only [pressureP6, neg_mul, Finset.sum_apply, Finset.sum_neg_distrib, neg_inj, Q6]
    rw [Finset.mul_sum]
  rw [heq]
  calc
    _ ≤ ∑ j : Fin 3, ‖iteratedFDeriv ℝ k (Q6 j) x‖ := by
      exact norm_iteratedFDeriv_fin3_sum_le hVopen h6atomCont hxV
    _ ≤ ∑ j : Fin 3,
        (2 * κ * cD * cutoffGradientConstant *
          (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) *
            ρ ^ (-(2 + k : ℝ)) * B) := by
      exact Finset.sum_le_sum (fun j hj => by
        simpa only [mul_assoc] using h6atomDeriv j)
    _ = _ := by
      simp only [Fin.sum_univ_three]
      ring

private lemma harmonicPressurePart_term_bounds_hcont2_1 :
    ∀ (k : ℕ) {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ}
      {s : ℝ} {x₀ : Vec3} {ρ : ℝ},
      PressureHarmonicPotentialData (vec3Ball x₀ ((13 : ℝ) * ρ / (20 : ℝ))) η u c p s →
        let V : Set Vec3 := vec3Ball x₀ (ρ / (2 : ℝ));
        let Ann : Set Vec3 := pressureAnnulus x₀ ρ;
        (∀ (i j : Fin (3 : ℕ)) (y : Vec3),
            mixedSecond η i j y * pressureUTensor u c (y, s) i j ≠ (0 : ℝ) → y ∈ Ann) →
          (∀ {g : Vec3 → ℝ},
              @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                (∀ y ∉ Ann, g y = (0 : ℝ)) →
                  ContDiffOn ℝ (↑k : WithTop ℕ∞) (pressureNewtonianPotential g) V) →
            ContDiffOn ℝ (↑k : WithTop ℕ∞) (pressureP2 η u c s) V
    := by
  intro k η u c p s x₀ ρ hdata V Ann hsource2 hcontN
  unfold pressureP2
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro j hj
  exact hcontN (hdata.p2_integrable i j) (fun y hy => by
    by_contra hne
    exact hy (hsource2 i j y hne))

private lemma harmonicPressurePart_term_bounds_hcont3_2 :
    ∀ (k : ℕ) {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ}
      {s : ℝ} {x₀ : Vec3} {ρ : ℝ},
      PressureHarmonicPotentialData (vec3Ball x₀ ((13 : ℝ) * ρ / (20 : ℝ))) η u c p s →
        let V : Set Vec3 := vec3Ball x₀ (ρ / (2 : ℝ));
        let Ann : Set Vec3 := pressureAnnulus x₀ ρ;
        (∀ (i j : Fin (3 : ℕ)) (y : Vec3),
            spatialDeriv η i y * pressureUTensor u c (y, s) i j ≠ (0 : ℝ) → y ∈ Ann) →
          (∀ {j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
              @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                (∀ y ∉ Ann, g y = (0 : ℝ)) →
                  ContDiffOn ℝ (↑k : WithTop ℕ∞) (pressureNewtonianDerivativePotential j g) V) →
            ContDiffOn ℝ (↑k : WithTop ℕ∞) (pressureP3 η u c s) V
    := by
  intro k η u c p s x₀ ρ hdata V Ann hsource3 hcontD
  unfold pressureP3
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro j hj
  exact hcontD (hdata.p3_integrable i j) (fun y hy => by
    by_contra hne
    exact hy (hsource3 i j y (by simpa [mul_comm] using hne)))

private lemma harmonicPressurePart_term_bounds_hcont4_3 :
    ∀ (k : ℕ) {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ}
      {s : ℝ} {x₀ : Vec3} {ρ : ℝ},
      PressureHarmonicPotentialData (vec3Ball x₀ ((13 : ℝ) * ρ / (20 : ℝ))) η u c p s →
        let V : Set Vec3 := vec3Ball x₀ (ρ / (2 : ℝ));
        let Ann : Set Vec3 := pressureAnnulus x₀ ρ;
        (∀ (i j : Fin (3 : ℕ)) (y : Vec3),
            spatialDeriv η j y * pressureUTensor u c (y, s) i j ≠ (0 : ℝ) → y ∈ Ann) →
          (∀ {j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
              @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume →
                (∀ y ∉ Ann, g y = (0 : ℝ)) →
                  ContDiffOn ℝ (↑k : WithTop ℕ∞) (pressureNewtonianDerivativePotential j g) V) →
            ContDiffOn ℝ (↑k : WithTop ℕ∞) (pressureP4 η u c s) V
    := by
  intro k η u c p s x₀ ρ hdata V Ann hsource4 hcontD
  unfold pressureP4
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro j hj
  exact hcontD (hdata.p4_integrable i j) (fun y hy => by
    by_contra hne
    exact hy (hsource4 i j y (by simpa [mul_comm] using hne)))

theorem harmonicPressurePart_term_bounds (k : ℕ) :
    ∃ cN cD κ : ℝ, 0 ≤ cN ∧ 0 ≤ cD ∧ 0 ≤ κ ∧
      ∀ {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
        {p : ParabolicPoint → ℝ} {s : ℝ} {x₀ : Vec3} {ρ : ℝ},
        (hρ : 0 < ρ) →
        PressureHarmonicPotentialData (vec3Ball x₀ (13 * ρ / 20)) η u c p s →
        η = mollifiedBallCutoff x₀ hρ →
        (∀ y, y ∉ pressureAnnulus x₀ ρ →
          (∀ i, spatialDeriv η i y = 0) ∧
          (∀ i j, mixedSecond η i j y = 0) ∧
          spatialLaplacian η y = 0) →
        Integrable (pressureUTensorNorm u c s)
          (volume.restrict (vec3Ball x₀ ρ)) →
        Integrable (fun y => |p (y, s)|)
          (volume.restrict (vec3Ball x₀ ρ)) →
        ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
          (∫ y in vec3Ball x₀ ρ, pressureUTensorNorm u c s y) ≤ 2 * ρ * A →
          (∫ y in vec3Ball x₀ ρ, |p (y, s)|) ≤
            (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ * B →
        ∀ x ∈ vec3Ball x₀ (ρ / 2),
          ContDiffOn ℝ (k : ℕ) (pressureP2 η u c s)
            (vec3Ball x₀ (ρ / 2)) ∧
          ContDiffOn ℝ (k : ℕ) (pressureP3 η u c s)
            (vec3Ball x₀ (ρ / 2)) ∧
          ContDiffOn ℝ (k : ℕ) (pressureP4 η u c s)
            (vec3Ball x₀ (ρ / 2)) ∧
          ContDiffOn ℝ (k : ℕ) (pressureP5 η p s)
            (vec3Ball x₀ (ρ / 2)) ∧
          ContDiffOn ℝ (k : ℕ) (pressureP6 η p s)
            (vec3Ball x₀ (ρ / 2)) ∧
          ‖iteratedFDeriv ℝ k (pressureP2 η u c s) x‖ ≤
            18 * cN * cutoffSecondDerivativeConstant *
              (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) *
              ρ ^ (-(2 + k : ℝ)) * A ∧
          ‖iteratedFDeriv ℝ k (pressureP3 η u c s) x‖ ≤
            18 * cD * cutoffGradientConstant *
              (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) *
              ρ ^ (-(2 + k : ℝ)) * A ∧
          ‖iteratedFDeriv ℝ k (pressureP4 η u c s) x‖ ≤
            18 * cD * cutoffGradientConstant *
              (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) *
              ρ ^ (-(2 + k : ℝ)) * A ∧
          ‖iteratedFDeriv ℝ k (pressureP5 η p s) x‖ ≤
            3 * κ * cN * cutoffSecondDerivativeConstant *
              (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) *
              ρ ^ (-(2 + k : ℝ)) * B ∧
          ‖iteratedFDeriv ℝ k (pressureP6 η p s) x‖ ≤
            6 * κ * cD * cutoffGradientConstant *
              (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) *
              ρ ^ (-(2 + k : ℝ)) * B := by
  obtain ⟨cN, hcN, hN⟩ :=
    exists_norm_iteratedFDeriv_pressureNewtonianPotential_annulus_le k
  obtain ⟨cD0, hcD0, hD0⟩ :=
    exists_norm_iteratedFDeriv_pressureNewtonianDerivativePotential_annulus_le
      (0 : Fin 3) k
  obtain ⟨cD1, hcD1, hD1⟩ :=
    exists_norm_iteratedFDeriv_pressureNewtonianDerivativePotential_annulus_le
      (1 : Fin 3) k
  obtain ⟨cD2, hcD2, hD2⟩ :=
    exists_norm_iteratedFDeriv_pressureNewtonianDerivativePotential_annulus_le
      (2 : Fin 3) k
  let cD : ℝ := cD0 + cD1 + cD2
  let κ : ℝ := (Real.pi * 4 / 3) ^ (1 / 3 : ℝ)
  have hcD : 0 ≤ cD := by dsimp [cD]; positivity
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  refine ⟨cN, cD, κ, hcN, hcD, hκ, ?_⟩
  intro η u c p s x₀ ρ hρ hdata hηeq hzero hUint hpInt A B hA hB hUbound hPbound x hx
  let V : Set Vec3 := vec3Ball x₀ (ρ / 2)
  let W : Set Vec3 := vec3Ball x₀ ρ
  let Ann : Set Vec3 := pressureAnnulus x₀ ρ
  have hW : MeasurableSet W := by
    dsimp [W]
    exact vec3Ball_measurable x₀ ρ
  have hAnnSub : Ann ⊆ W := by
    intro y hy
    exact vec3Ball_mono (x := x₀) (r₁ := 3 * ρ / 4) (r₂ := ρ)
      (by nlinarith only [hρ]) (pressure_annulus_subset_ball hy)
  have hC := pressure_cutoff_constants_nonneg (x₀ := x₀) hρ
  rcases hC with ⟨hC₁, hC₂⟩
  have hC₁ρ : 0 ≤ cutoffGradientConstant / ρ := by positivity
  have hC₂ρ : 0 ≤ cutoffSecondDerivativeConstant / ρ ^ 2 := by positivity
  have hC₂ρ3 : 0 ≤ 3 * cutoffSecondDerivativeConstant / ρ ^ 2 := by positivity
  have hsource2 (i j : Fin 3) :
      ∀ y, (mixedSecond η i j y * pressureUTensor u c (y, s) i j) ≠ 0 →
        y ∈ Ann := by
    intro y hy
    by_contra hnot
    have hz := hzero y hnot
    exact hy (by rw [hz.2.1 i j, zero_mul])
  have hsource3 (i j : Fin 3) :
      ∀ y, (spatialDeriv η i y * pressureUTensor u c (y, s) i j) ≠ 0 →
        y ∈ Ann := by
    intro y hy
    by_contra hnot
    have hz := hzero y hnot
    exact hy (by rw [hz.1 i, zero_mul])
  have hsource4 (i j : Fin 3) :
      ∀ y, (spatialDeriv η j y * pressureUTensor u c (y, s) i j) ≠ 0 →
        y ∈ Ann := by
    intro y hy
    by_contra hnot
    have hz := hzero y hnot
    exact hy (by rw [hz.1 j, zero_mul])
  have hsource5 :
      ∀ y, (spatialLaplacian η y * p (y, s)) ≠ 0 → y ∈ Ann := by
    intro y hy
    by_contra hnot
    have hz := hzero y hnot
    exact hy (by rw [hz.2.2, zero_mul])
  have hsource6 (j : Fin 3) :
      ∀ y, (spatialDeriv η j y * p (y, s)) ≠ 0 → y ∈ Ann := by
    intro y hy
    by_contra hnot
    have hz := hzero y hnot
    exact hy (by rw [hz.1 j, zero_mul])
  have hU2 (i j : Fin 3) :
      ∫ y, |mixedSecond η i j y * pressureUTensor u c (y, s) i j| ≤
        (cutoffSecondDerivativeConstant / ρ ^ 2) *
          ∫ y in W, pressureUTensorNorm u c s y :=
    integral_abs_mul_le_ball_indicator (hdata.p2_integrable i j) hUint
      (fun y => by unfold pressureUTensorNorm; positivity) hC₂ρ hW hAnnSub
      (hsource2 i j)
      (fun y => by simpa [hηeq] using
        pressure_cutoff_mixedSecond_bound x₀ hρ y i j)
      (fun y => pressure_component_abs_le_utensorNorm u c s y i j)
  have hU3 (i j : Fin 3) :
      ∫ y, |spatialDeriv η i y * pressureUTensor u c (y, s) i j| ≤
        (cutoffGradientConstant / ρ) *
          ∫ y in W, pressureUTensorNorm u c s y :=
    integral_abs_mul_le_ball_indicator
      (by simpa [mul_comm] using hdata.p3_integrable i j) hUint
      (fun y => by unfold pressureUTensorNorm; positivity) hC₁ρ hW hAnnSub
      (hsource3 i j)
      (fun y => by simpa [hηeq] using
        pressure_cutoff_spatialDeriv_bound x₀ hρ y i)
      (fun y => pressure_component_abs_le_utensorNorm u c s y i j)
  have hU4 (i j : Fin 3) :
      ∫ y, |spatialDeriv η j y * pressureUTensor u c (y, s) i j| ≤
        (cutoffGradientConstant / ρ) *
          ∫ y in W, pressureUTensorNorm u c s y :=
    integral_abs_mul_le_ball_indicator
      (by simpa [mul_comm] using hdata.p4_integrable i j) hUint
      (fun y => by unfold pressureUTensorNorm; positivity) hC₁ρ hW hAnnSub
      (hsource4 i j)
      (fun y => by simpa [hηeq] using
        pressure_cutoff_spatialDeriv_bound x₀ hρ y j)
      (fun y => pressure_component_abs_le_utensorNorm u c s y i j)
  have hP5 :
      ∫ y, |spatialLaplacian η y * p (y, s)| ≤
        (3 * cutoffSecondDerivativeConstant / ρ ^ 2) *
          ∫ y in W, |p (y, s)| :=
    integral_abs_mul_le_ball_indicator
      (by simpa [mul_comm] using hdata.p5_integrable) hpInt
      (fun y => abs_nonneg _) hC₂ρ3 hW hAnnSub hsource5
      (fun y => by
        have hLap := @harmonicPressurePart_term_bounds_hLap_1 η x₀ ρ hρ hηeq y
        exact hLap)
      (fun y => by simp)
  have hP6 (j : Fin 3) :
      ∫ y, |spatialDeriv η j y * p (y, s)| ≤
        (cutoffGradientConstant / ρ) * ∫ y in W, |p (y, s)| :=
    integral_abs_mul_le_ball_indicator (hdata.p6_integrable j) hpInt
      (fun y => abs_nonneg _) hC₁ρ hW hAnnSub (hsource6 j)
      (fun y => by simpa [hηeq] using
        pressure_cutoff_spatialDeriv_bound x₀ hρ y j)
      (fun y => by simp)
  have hUboundW :
      (∫ y in W, pressureUTensorNorm u c s y) ≤ 2 * ρ * A := by
    simpa [W] using hUbound
  have hPboundW :
      (∫ y in W, |p (y, s)|) ≤ κ * ρ * B := by
    simpa [W, κ] using hPbound
  have h2term (i j : Fin 3) := @harmonicPressurePart_term_bounds_h2term_2 k cN hcN hN η u c p s x₀
    ρ hρ hdata A x hx hC₂ρ hsource2 hU2 hUboundW i j
  have hcD0le : cD0 ≤ cD := by
    dsimp [cD]
    linarith only [hcD1, hcD2]
  have hcD1le : cD1 ≤ cD := by
    dsimp [cD]
    linarith only [hcD0, hcD2]
  have hcD2le : cD2 ≤ cD := by
    dsimp [cD]
    linarith only [hcD0, hcD1]
  have hDall {j : Fin 3} {g : Vec3 → ℝ}
      (hg : Integrable g volume) (hg0 : ∀ y ∉ Ann, g y = 0) :=
        @harmonicPressurePart_term_bounds_hDall_3 k cD0 hD0 cD1 hD1 cD2 hD2 x₀ ρ hρ x hx hcD0le
        hcD1le hcD2le j g hg hg0
  have h3term (i j : Fin 3) := @harmonicPressurePart_term_bounds_h3term_4 k cD0 cD1 cD2 hcD η u c
    p s x₀ ρ hρ hdata A x hC₁ρ hsource3 hU3 hUboundW hDall i j
  have h4term (i j : Fin 3) := @harmonicPressurePart_term_bounds_h4term_5 k cD0 cD1 cD2 hcD η u c
    p s x₀ ρ hρ hdata A x hC₁ρ hsource4 hU4 hUboundW hDall i j
  have h5term := @harmonicPressurePart_term_bounds_h5term_6 k cN hcN hN η u c p s x₀ ρ hρ hdata B
    x hx hC₂ρ3 hsource5 hP5 hPboundW
  have h6term (j : Fin 3) := @harmonicPressurePart_term_bounds_h6term_7 k cD0 cD1 cD2 hcD η u c p
    s x₀ ρ hρ hdata B x hC₁ρ hsource6 hP6 hPboundW hDall j
  have hcontN {g : Vec3 → ℝ} (hg : Integrable g volume)
      (hg0 : ∀ y ∉ Ann, g y = 0) :
      ContDiffOn ℝ (k : ℕ) (pressureNewtonianPotential g) V := by
    exact contDiffOn_pressureNewtonianPotential_annulus hρ hg hg0 k
  have hcontD {j : Fin 3} {g : Vec3 → ℝ} (hg : Integrable g volume)
      (hg0 : ∀ y ∉ Ann, g y = 0) :
      ContDiffOn ℝ (k : ℕ) (pressureNewtonianDerivativePotential j g) V := by
    exact contDiffOn_pressureNewtonianDerivativePotential_annulus j hρ hg hg0 k
  have hcont2 := @harmonicPressurePart_term_bounds_hcont2_1 k η u c p s x₀ ρ hdata hsource2 hcontN
  have hcont3 := @harmonicPressurePart_term_bounds_hcont3_2 k η u c p s x₀ ρ hdata hsource3 hcontD
  have hcont4 := @harmonicPressurePart_term_bounds_hcont4_3 k η u c p s x₀ ρ hdata hsource4 hcontD
  have hcont5 : ContDiffOn ℝ (k : ℕ) (pressureP5 η p s) V := by
    unfold pressureP5
    exact (hcontN hdata.p5_integrable (fun y hy => by
      by_contra hne
      exact hy (hsource5 y (by simpa [mul_comm] using hne)))).neg
  have hcont6 := @harmonicPressurePart_term_bounds_hcont6_8 k η u c p s x₀ ρ hdata x hsource6 hcontD
  have hVopen : IsOpen V := by
    dsimp [V]
    exact isOpen_vec3Ball x₀ (ρ / 2)
  have hxV : x ∈ V := by simpa [V] using hx
  have h2deriv := @harmonicPressurePart_term_bounds_h2deriv_9 k cN η u c p s x₀ ρ hdata A x
    hsource2 h2term hcontN hVopen hxV
  have h3deriv := @harmonicPressurePart_term_bounds_h3deriv_10 k cD0 cD1 cD2 η u c p s x₀ ρ hdata
    A x hsource3 h3term hcontD hVopen hxV
  have h4deriv := @harmonicPressurePart_term_bounds_h4deriv_11 k cD0 cD1 cD2 η u c p s x₀ ρ hdata
    A x hsource4 h4term hcontD hVopen hxV
  let Q6 : Fin 3 → Vec3 → ℝ := fun j z => -2 *
    pressureNewtonianDerivativePotential j
      (fun y => spatialDeriv η j y * p (y, s)) z
  have h6atomCont (j : Fin 3) : ContDiffOn ℝ (k : ℕ) (Q6 j) V := by
    dsimp [Q6]
    exact (hcontD (hdata.p6_integrable j) (fun y hy => by
      by_contra hne
      exact hy (hsource6 j y hne))).const_smul (-2 : ℝ)
  have h6atomDeriv (j : Fin 3) := @harmonicPressurePart_term_bounds_h6atomDeriv_12 k cD0 cD1 cD2 η
    u c p s x₀ ρ hdata B x hsource6 h6term hcontD hVopen hxV j
  have h6deriv := @harmonicPressurePart_term_bounds_h6deriv_13 k cD0 cD1 cD2 η p s x₀ ρ B x hVopen
    hxV h6atomCont h6atomDeriv
  exact ⟨by simpa [V] using hcont2, by simpa [V] using hcont3,
    by simpa [V] using hcont4, by simpa [V] using hcont5,
    by simpa [V] using hcont6, h2deriv, h3deriv, h4deriv, h5term, h6deriv⟩

end CKN
