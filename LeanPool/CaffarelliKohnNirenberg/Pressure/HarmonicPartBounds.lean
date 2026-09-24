/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicPartBoundsTerms

/-!
# Harmonic Part Bounds

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

private lemma exists_harmonicPressurePart_Ck_constant_htotal_1 :
    ∀ (k : ℕ) (cN cD κ : ℝ) {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
      {p : ParabolicPoint → ℝ} {s ρ : ℝ} (A B : ℝ) (x : Vec3),
      norm (E := Vec3 [×k]→L[ℝ] ℝ) (iteratedFDeriv ℝ k (pressureP2 η u c s) x) ≤
          (18 : ℝ) * cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) *
              ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
            A →
        norm (E := Vec3 [×k]→L[ℝ] ℝ) (iteratedFDeriv ℝ k (pressureP3 η u c s) x) ≤
            (18 : ℝ) * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
              A →
          norm (E := Vec3 [×k]→L[ℝ] ℝ) (iteratedFDeriv ℝ k (pressureP4 η u c s) x) ≤
              (18 : ℝ) * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                  ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                A →
            norm (E := Vec3 [×k]→L[ℝ] ℝ) (iteratedFDeriv ℝ k (pressureP5 η p s) x) ≤
                (3 : ℝ) * κ * cN * cutoffSecondDerivativeConstant *
                      (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) *
                    ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                  B →
              norm (E := Vec3 [×k]→L[ℝ] ℝ) (iteratedFDeriv ℝ k (pressureP6 η p s) x) ≤
                  (6 : ℝ) * κ * cD * cutoffGradientConstant *
                        (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                      ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                    B →
                ContDiffAt ℝ (↑k : WithTop ℕ∞)
                    (pressureP2 η u c s + pressureP3 η u c s + pressureP4 η u c s +
                      pressureP5 η p s)
                    x →
                  ContDiffAt ℝ (↑k : WithTop ℕ∞) (pressureP6 η p s) x →
                    norm (E := Vec3 [×k]→L[ℝ] ℝ)
                          (iteratedFDeriv ℝ k
                            (pressureP2 η u c s + pressureP3 η u c s + pressureP4 η u c s +
                              pressureP5 η p s)
                            x) ≤
                        norm (E := Vec3 [×k]→L[ℝ] ℝ) (iteratedFDeriv ℝ k (pressureP2 η u c s) x) +
                              norm (E := Vec3 [×k]→L[ℝ] ℝ)
                                (iteratedFDeriv ℝ k (pressureP3 η u c s) x) +
                            norm (E := Vec3 [×k]→L[ℝ] ℝ)
                              (iteratedFDeriv ℝ k (pressureP4 η u c s) x) +
                          norm (E := Vec3 [×k]→L[ℝ] ℝ) (iteratedFDeriv ℝ k (pressureP5 η p s) x) →
                      norm (E := Vec3 [×k]→L[ℝ] ℝ)
                          (iteratedFDeriv ℝ k (harmonicPressurePart η u c p s) x) ≤
                        (18 : ℝ) * cN * cutoffSecondDerivativeConstant *
                                      (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) *
                                    ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                                  A +
                                (18 : ℝ) * cD * cutoffGradientConstant *
                                      (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                                    ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                                  A +
                              (18 : ℝ) * cD * cutoffGradientConstant *
                                    (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                                  ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                                A +
                            (3 : ℝ) * κ * cN * cutoffSecondDerivativeConstant *
                                  (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) *
                                ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                              B +
                          (6 : ℝ) * κ * cD * cutoffGradientConstant *
                                (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                              ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                            B
    := by
  intro k cN cD κ η u c p s ρ A B x h2deriv h3deriv h4deriv h5term h6deriv hP2345 hP6at h2345bound
  unfold harmonicPressurePart
  calc
    _ ≤ ‖iteratedFDeriv ℝ k
        (pressureP2 η u c s + pressureP3 η u c s + pressureP4 η u c s +
          pressureP5 η p s) x‖ +
        ‖iteratedFDeriv ℝ k (pressureP6 η p s) x‖ :=
      norm_iteratedFDeriv_add_le hP2345 hP6at
    _ ≤ ((‖iteratedFDeriv ℝ k (pressureP2 η u c s) x‖ +
        ‖iteratedFDeriv ℝ k (pressureP3 η u c s) x‖) +
        ‖iteratedFDeriv ℝ k (pressureP4 η u c s) x‖) +
        ‖iteratedFDeriv ℝ k (pressureP5 η p s) x‖ +
        ‖iteratedFDeriv ℝ k (pressureP6 η p s) x‖ := by
      exact add_le_add_left h2345bound _
    _ ≤ ((18 * cN * cutoffSecondDerivativeConstant *
          (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) *
            ρ ^ (-(2 + k : ℝ)) * A) +
        (18 * cD * cutoffGradientConstant *
          (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) *
            ρ ^ (-(2 + k : ℝ)) * A)) +
        (18 * cD * cutoffGradientConstant *
          (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) *
            ρ ^ (-(2 + k : ℝ)) * A) +
        (3 * κ * cN * cutoffSecondDerivativeConstant *
          (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) *
            ρ ^ (-(2 + k : ℝ)) * B) +
        (6 * κ * cD * cutoffGradientConstant *
          (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) *
            ρ ^ (-(2 + k : ℝ)) * B) := by
      exact add_le_add
        (add_le_add
          (add_le_add
            (add_le_add h2deriv h3deriv) h4deriv) h5term) h6deriv

private lemma exists_harmonicPressurePart_Ck_constant_hT₁_2 :
    ∀ (k : ℕ) (cN cD κ : ℝ),
      (0 : ℝ) ≤ cN →
        (0 : ℝ) ≤ cD →
          (0 : ℝ) ≤ κ →
            (0 : ℝ) ≤ cutoffGradientConstant →
              (0 : ℝ) ≤ cutoffSecondDerivativeConstant →
                let T : ℝ :=
                  (1 : ℝ) +
                          cN * cutoffSecondDerivativeConstant *
                            (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                        cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) +
                      κ * cN * cutoffSecondDerivativeConstant *
                        (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                    κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ)));
                cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) ≤ T
    := by
  intro k cN cD κ hcN hcD hκ hC₁ hC₂ T
  calc
    _ ≤ cN * cutoffSecondDerivativeConstant *
        (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
        (1 + cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) +
          κ * cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
          κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-(2 + k : ℝ))) := by
      exact le_add_of_nonneg_right
        (show 0 ≤ 1 + cD * cutoffGradientConstant *
            (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) +
          κ * cN * cutoffSecondDerivativeConstant *
            (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
          κ * cD * cutoffGradientConstant *
            (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) by positivity)
    _ = T := by dsimp [T]; ring

private lemma exists_harmonicPressurePart_Ck_constant_hT₂_3 :
    ∀ (k : ℕ) (cN cD κ : ℝ),
      (0 : ℝ) ≤ cN →
        (0 : ℝ) ≤ cD →
          (0 : ℝ) ≤ κ →
            (0 : ℝ) ≤ cutoffGradientConstant →
              (0 : ℝ) ≤ cutoffSecondDerivativeConstant →
                let T : ℝ :=
                  (1 : ℝ) +
                          cN * cutoffSecondDerivativeConstant *
                            (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                        cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) +
                      κ * cN * cutoffSecondDerivativeConstant *
                        (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                    κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ)));
                cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) ≤ T
    := by
  intro k cN cD κ hcN hcD hκ hC₁ hC₂ T
  calc
    _ ≤ cD * cutoffGradientConstant *
        (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) +
        (1 + cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
          κ * cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
          κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-(2 + k : ℝ))) := by
      exact le_add_of_nonneg_right
        (show 0 ≤ 1 + cN * cutoffSecondDerivativeConstant *
            (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
          κ * cN * cutoffSecondDerivativeConstant *
            (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
          κ * cD * cutoffGradientConstant *
            (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) by positivity)
    _ = T := by dsimp [T]; ring

private lemma exists_harmonicPressurePart_Ck_constant_hT₃_4 :
    ∀ (k : ℕ) (cN cD κ : ℝ),
      (0 : ℝ) ≤ cN →
        (0 : ℝ) ≤ cD →
          (0 : ℝ) ≤ κ →
            (0 : ℝ) ≤ cutoffGradientConstant →
              (0 : ℝ) ≤ cutoffSecondDerivativeConstant →
                let T : ℝ :=
                  (1 : ℝ) +
                          cN * cutoffSecondDerivativeConstant *
                            (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                        cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) +
                      κ * cN * cutoffSecondDerivativeConstant *
                        (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                    κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ)));
                κ * cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) ≤ T
    := by
  intro k cN cD κ hcN hcD hκ hC₁ hC₂ T
  calc
    _ ≤ κ * cN * cutoffSecondDerivativeConstant *
        (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
        (1 + cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
          cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) +
          κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-(2 + k : ℝ))) := by
      exact le_add_of_nonneg_right
        (show 0 ≤ 1 + cN * cutoffSecondDerivativeConstant *
            (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
          cD * cutoffGradientConstant *
            (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) +
          κ * cD * cutoffGradientConstant *
            (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) by positivity)
    _ = T := by dsimp [T]; ring

private lemma exists_harmonicPressurePart_Ck_constant_hT₄_5 :
    ∀ (k : ℕ) (cN cD κ : ℝ),
      (0 : ℝ) ≤ cN →
        (0 : ℝ) ≤ cD →
          (0 : ℝ) ≤ κ →
            (0 : ℝ) ≤ cutoffGradientConstant →
              (0 : ℝ) ≤ cutoffSecondDerivativeConstant →
                let T : ℝ :=
                  (1 : ℝ) +
                          cN * cutoffSecondDerivativeConstant *
                            (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                        cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) +
                      κ * cN * cutoffSecondDerivativeConstant *
                        (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                    κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ)));
                κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) ≤ T
    := by
  intro k cN cD κ hcN hcD hκ hC₁ hC₂ T
  calc
    _ ≤ κ * cD * cutoffGradientConstant *
        (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) +
        (1 + cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
          cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) +
          κ * cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-(1 + k : ℝ))) := by
      exact le_add_of_nonneg_right
        (show 0 ≤ 1 + cN * cutoffSecondDerivativeConstant *
            (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
          cD * cutoffGradientConstant *
            (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) +
          κ * cN * cutoffSecondDerivativeConstant *
            (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) by positivity)
    _ = T := by dsimp [T]; ring

private lemma exists_harmonicPressurePart_Ck_constant_hcoeffA_6 :
    ∀ (k : ℕ) (cN cD κ : ℝ),
      (0 : ℝ) ≤ cN →
        (0 : ℝ) ≤ cD →
          (0 : ℝ) ≤ κ →
            let C₁₆ : ℝ :=
              (100 : ℝ) *
                ((1 : ℝ) +
                        cN * cutoffSecondDerivativeConstant *
                          (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                      cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) +
                    κ * cN * cutoffSecondDerivativeConstant *
                      (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                  κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))));
            (0 : ℝ) ≤ cutoffGradientConstant →
              (0 : ℝ) ≤ cutoffSecondDerivativeConstant →
                let T : ℝ :=
                  (1 : ℝ) +
                          cN * cutoffSecondDerivativeConstant *
                            (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                        cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) +
                      κ * cN * cutoffSecondDerivativeConstant *
                        (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                    κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ)));
                cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) ≤ T →
                  cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) ≤ T →
                    (18 : ℝ) * cN * cutoffSecondDerivativeConstant *
                          (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                        (36 : ℝ) * cD * cutoffGradientConstant *
                          (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) ≤
                      C₁₆
    := by
  intro k cN cD κ hcN hcD hκ C₁₆ hC₁ hC₂ T hT₁ hT₂
  calc
    _ ≤ 18 * T + 36 * T := by
      have h₁ := mul_le_mul_of_nonneg_left hT₁
        (by norm_num : (0 : ℝ) ≤ 18)
      have h₂ := mul_le_mul_of_nonneg_left hT₂
        (by norm_num : (0 : ℝ) ≤ 36)
      exact add_le_add
        (by simpa only [mul_assoc] using h₁)
        (by simpa only [mul_assoc] using h₂)
    _ = 54 * T := by ring
    _ ≤ 100 * T := by
      exact mul_le_mul_of_nonneg_right (by norm_num)
        (by dsimp [T]; positivity)
    _ = C₁₆ := by rfl

private lemma exists_harmonicPressurePart_Ck_constant_hcoeffB_7 :
    ∀ (k : ℕ) (cN cD κ : ℝ),
      (0 : ℝ) ≤ cN →
        (0 : ℝ) ≤ cD →
          (0 : ℝ) ≤ κ →
            let C₁₆ : ℝ :=
              (100 : ℝ) *
                ((1 : ℝ) +
                        cN * cutoffSecondDerivativeConstant *
                          (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                      cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) +
                    κ * cN * cutoffSecondDerivativeConstant *
                      (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                  κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))));
            (0 : ℝ) ≤ cutoffGradientConstant →
              (0 : ℝ) ≤ cutoffSecondDerivativeConstant →
                let T : ℝ :=
                  (1 : ℝ) +
                          cN * cutoffSecondDerivativeConstant *
                            (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                        cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) +
                      κ * cN * cutoffSecondDerivativeConstant *
                        (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                    κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ)));
                κ * cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) ≤
                    T →
                  κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) ≤ T →
                    (3 : ℝ) * κ * cN * cutoffSecondDerivativeConstant *
                          (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                        (6 : ℝ) * κ * cD * cutoffGradientConstant *
                          (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) ≤
                      C₁₆
    := by
  intro k cN cD κ hcN hcD hκ C₁₆ hC₁ hC₂ T hT₃ hT₄
  calc
    _ ≤ 3 * T + 6 * T := by
      have h₃ := mul_le_mul_of_nonneg_left hT₃
        (by norm_num : (0 : ℝ) ≤ 3)
      have h₄ := mul_le_mul_of_nonneg_left hT₄
        (by norm_num : (0 : ℝ) ≤ 6)
      exact add_le_add
        (by simpa only [mul_assoc] using h₃)
        (by simpa only [mul_assoc] using h₄)
    _ = 9 * T := by ring
    _ ≤ 100 * T := by
      exact mul_le_mul_of_nonneg_right (by norm_num)
        (by dsimp [T]; positivity)
    _ = C₁₆ := by rfl

private lemma exists_harmonicPressurePart_Ck_constant_hAglobal_8 :
    ∀ (k : ℕ) (cN cD κ : ℝ),
      let C₁₆ : ℝ :=
        (100 : ℝ) *
          ((1 : ℝ) + cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) +
              κ * cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
            κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))));
      ∀ {ρ : ℝ} (A : ℝ),
        (0 : ℝ) ≤ A →
          (0 : ℝ) ≤ ρ ^ (-((2 : ℝ) + (↑k : ℝ))) →
            (18 : ℝ) * cN * cutoffSecondDerivativeConstant *
                    (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                  (36 : ℝ) * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) ≤
                C₁₆ →
              (18 : ℝ) * cN * cutoffSecondDerivativeConstant *
                          (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) *
                        ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                      A +
                    (18 : ℝ) * cD * cutoffGradientConstant *
                          (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                        ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                      A +
                  (18 : ℝ) * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                      ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                    A ≤
                C₁₆ * ρ ^ (-((2 : ℝ) + (↑k : ℝ))) * A
    := by
  intro k cN cD κ C₁₆ ρ A hA hR hcoeffA
  calc
    _ = (18 * cN * cutoffSecondDerivativeConstant *
        (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
      36 * cD * cutoffGradientConstant *
        (3 / 20 : ℝ) ^ (-(2 + k : ℝ))) *
          (ρ ^ (-(2 + k : ℝ)) * A) := by ring
    _ ≤ C₁₆ * (ρ ^ (-(2 + k : ℝ)) * A) := by
      exact mul_le_mul_of_nonneg_right hcoeffA
        (mul_nonneg hR hA)
    _ = _ := by ring

private lemma exists_harmonicPressurePart_Ck_constant_hBglobal_9 :
    ∀ (k : ℕ) (cN cD κ : ℝ),
      let C₁₆ : ℝ :=
        (100 : ℝ) *
          ((1 : ℝ) + cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) +
              κ * cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
            κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))));
      ∀ {ρ : ℝ} (B : ℝ),
        (0 : ℝ) ≤ B →
          (0 : ℝ) ≤ ρ ^ (-((2 : ℝ) + (↑k : ℝ))) →
            (3 : ℝ) * κ * cN * cutoffSecondDerivativeConstant *
                    (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) +
                  (6 : ℝ) * κ * cD * cutoffGradientConstant *
                    (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) ≤
                C₁₆ →
              (3 : ℝ) * κ * cN * cutoffSecondDerivativeConstant *
                        (3 / 20 : ℝ) ^ (-((1 : ℝ) + (↑k : ℝ))) *
                      ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                    B +
                  (6 : ℝ) * κ * cD * cutoffGradientConstant *
                        (3 / 20 : ℝ) ^ (-((2 : ℝ) + (↑k : ℝ))) *
                      ρ ^ (-((2 : ℝ) + (↑k : ℝ))) *
                    B ≤
                C₁₆ * ρ ^ (-((2 : ℝ) + (↑k : ℝ))) * B
    := by
  intro k cN cD κ C₁₆ ρ B hB hR hcoeffB
  calc
    _ = (3 * κ * cN * cutoffSecondDerivativeConstant *
        (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
      6 * κ * cD * cutoffGradientConstant *
        (3 / 20 : ℝ) ^ (-(2 + k : ℝ))) *
          (ρ ^ (-(2 + k : ℝ)) * B) := by ring
    _ ≤ C₁₆ * (ρ ^ (-(2 + k : ℝ)) * B) := by
      exact mul_le_mul_of_nonneg_right hcoeffB
        (mul_nonneg hR hB)
    _ = _ := by ring

theorem exists_harmonicPressurePart_Ck_constant (k : ℕ) :
    ∃ C₁₆ : ℝ, 0 ≤ C₁₆ ∧
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
          ‖iteratedFDeriv ℝ k (harmonicPressurePart η u c p s) x‖ ≤
            C₁₆ * ρ ^ (-(2 + k : ℝ)) * (A + B) := by
  obtain ⟨cN, cD, κ, hcN, hcD, hκ, hterm⟩ :=
    harmonicPressurePart_term_bounds k
  let C₁₆ : ℝ := 100 * (1 +
    cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
    cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) +
    κ * cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
    κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-(2 + k : ℝ)))
  have hcutoff := pressure_cutoff_constants_nonneg (x₀ := (0 : Vec3))
    (ρ := 1) (by positivity)
  rcases hcutoff with ⟨hC₁, hC₂⟩
  have hC₁₆ : 0 ≤ C₁₆ := by
    dsimp [C₁₆]
    positivity
  refine ⟨C₁₆, hC₁₆, ?_⟩
  intro η u c p s x₀ ρ hρ hdata hηeq hzero hUint hpInt A B hA hB hUbound hPbound x hx
  let V : Set Vec3 := vec3Ball x₀ (ρ / 2)
  have hVopen : IsOpen V := by
    dsimp [V]
    exact isOpen_vec3Ball x₀ (ρ / 2)
  have hxV : x ∈ V := by simpa [V] using hx
  rcases hterm hρ hdata hηeq hzero hUint hpInt A B hA hB hUbound hPbound x hx with
    ⟨hcont2ball, hcont3ball, hcont4ball, hcont5ball, hcont6ball,
      h2deriv, h3deriv, h4deriv, h5term, h6deriv⟩
  have hcont2 : ContDiffOn ℝ (k : ℕ) (pressureP2 η u c s) V := by
    simpa [V] using hcont2ball
  have hcont3 : ContDiffOn ℝ (k : ℕ) (pressureP3 η u c s) V := by
    simpa [V] using hcont3ball
  have hcont4 : ContDiffOn ℝ (k : ℕ) (pressureP4 η u c s) V := by
    simpa [V] using hcont4ball
  have hcont5 : ContDiffOn ℝ (k : ℕ) (pressureP5 η p s) V := by
    simpa [V] using hcont5ball
  have hcont6 : ContDiffOn ℝ (k : ℕ) (pressureP6 η p s) V := by
    simpa [V] using hcont6ball
  have hP23 : ContDiffAt ℝ (k : ℕ)
      (pressureP2 η u c s + pressureP3 η u c s) x :=
    (hcont2 x hxV).add (hcont3 x hxV) |>.contDiffAt (hVopen.mem_nhds hxV)
  have hP234 : ContDiffAt ℝ (k : ℕ)
      (pressureP2 η u c s + pressureP3 η u c s + pressureP4 η u c s) x :=
    hP23.add ((hcont4 x hxV).contDiffAt (hVopen.mem_nhds hxV))
  have hP2345 : ContDiffAt ℝ (k : ℕ)
      (pressureP2 η u c s + pressureP3 η u c s + pressureP4 η u c s +
        pressureP5 η p s) x :=
    hP234.add ((hcont5 x hxV).contDiffAt (hVopen.mem_nhds hxV))
  have hP2at : ContDiffAt ℝ (k : ℕ) (pressureP2 η u c s) x :=
    (hcont2 x hxV).contDiffAt (hVopen.mem_nhds hxV)
  have hP3at : ContDiffAt ℝ (k : ℕ) (pressureP3 η u c s) x :=
    (hcont3 x hxV).contDiffAt (hVopen.mem_nhds hxV)
  have hP4at : ContDiffAt ℝ (k : ℕ) (pressureP4 η u c s) x :=
    (hcont4 x hxV).contDiffAt (hVopen.mem_nhds hxV)
  have hP5at : ContDiffAt ℝ (k : ℕ) (pressureP5 η p s) x :=
    (hcont5 x hxV).contDiffAt (hVopen.mem_nhds hxV)
  have hP6at : ContDiffAt ℝ (k : ℕ) (pressureP6 η p s) x :=
    (hcont6 x hxV).contDiffAt (hVopen.mem_nhds hxV)
  have h234bound :
      ‖iteratedFDeriv ℝ k
          (pressureP2 η u c s + pressureP3 η u c s + pressureP4 η u c s) x‖ ≤
        (‖iteratedFDeriv ℝ k (pressureP2 η u c s) x‖ +
          ‖iteratedFDeriv ℝ k (pressureP3 η u c s) x‖) +
          ‖iteratedFDeriv ℝ k (pressureP4 η u c s) x‖ := by
    calc
      _ ≤ ‖iteratedFDeriv ℝ k
          (pressureP2 η u c s + pressureP3 η u c s) x‖ +
          ‖iteratedFDeriv ℝ k (pressureP4 η u c s) x‖ :=
        norm_iteratedFDeriv_add_le hP23 hP4at
      _ ≤ _ := by
        exact add_le_add_left
          (norm_iteratedFDeriv_add_le hP2at hP3at) _
  have h2345bound :
      ‖iteratedFDeriv ℝ k
          (pressureP2 η u c s + pressureP3 η u c s + pressureP4 η u c s +
            pressureP5 η p s) x‖ ≤
        ((‖iteratedFDeriv ℝ k (pressureP2 η u c s) x‖ +
          ‖iteratedFDeriv ℝ k (pressureP3 η u c s) x‖) +
          ‖iteratedFDeriv ℝ k (pressureP4 η u c s) x‖) +
          ‖iteratedFDeriv ℝ k (pressureP5 η p s) x‖ := by
    calc
      _ ≤ ‖iteratedFDeriv ℝ k
          (pressureP2 η u c s + pressureP3 η u c s + pressureP4 η u c s) x‖ +
          ‖iteratedFDeriv ℝ k (pressureP5 η p s) x‖ :=
        norm_iteratedFDeriv_add_le hP234 hP5at
      _ ≤ _ := by exact add_le_add_left h234bound _
  have htotal := @exists_harmonicPressurePart_Ck_constant_htotal_1 k cN cD κ η u c p s ρ A B x
    h2deriv h3deriv h4deriv h5term h6deriv hP2345 hP6at h2345bound
  have hq₁ : 0 ≤ (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) := by positivity
  have hq₂ : 0 ≤ (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) := by positivity
  have hR : 0 ≤ ρ ^ (-(2 + k : ℝ)) := by positivity
  let T : ℝ := 1 +
    cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
    cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) +
    κ * cN * cutoffSecondDerivativeConstant * (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) +
    κ * cD * cutoffGradientConstant * (3 / 20 : ℝ) ^ (-(2 + k : ℝ))
  have hT₁ := @exists_harmonicPressurePart_Ck_constant_hT₁_2 k cN cD κ hcN hcD hκ hC₁ hC₂
  have hT₂ := @exists_harmonicPressurePart_Ck_constant_hT₂_3 k cN cD κ hcN hcD hκ hC₁ hC₂
  have hT₃ := @exists_harmonicPressurePart_Ck_constant_hT₃_4 k cN cD κ hcN hcD hκ hC₁ hC₂
  have hT₄ := @exists_harmonicPressurePart_Ck_constant_hT₄_5 k cN cD κ hcN hcD hκ hC₁ hC₂
  have hcoeffA := @exists_harmonicPressurePart_Ck_constant_hcoeffA_6 k cN cD κ hcN hcD hκ hC₁ hC₂
    hT₁ hT₂
  have hcoeffB := @exists_harmonicPressurePart_Ck_constant_hcoeffB_7 k cN cD κ hcN hcD hκ hC₁ hC₂
    hT₃ hT₄
  have hAglobal := @exists_harmonicPressurePart_Ck_constant_hAglobal_8 k cN cD κ ρ A hA hR hcoeffA
  have hBglobal := @exists_harmonicPressurePart_Ck_constant_hBglobal_9 k cN cD κ ρ B hB hR hcoeffB
  calc
    _ ≤ (18 * cN * cutoffSecondDerivativeConstant *
          (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) *
            ρ ^ (-(2 + k : ℝ)) * A) +
        (18 * cD * cutoffGradientConstant *
          (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) *
            ρ ^ (-(2 + k : ℝ)) * A) +
        (18 * cD * cutoffGradientConstant *
          (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) *
            ρ ^ (-(2 + k : ℝ)) * A) +
        ((3 * κ * cN * cutoffSecondDerivativeConstant *
          (3 / 20 : ℝ) ^ (-(1 + k : ℝ)) *
            ρ ^ (-(2 + k : ℝ)) * B) +
          (6 * κ * cD * cutoffGradientConstant *
            (3 / 20 : ℝ) ^ (-(2 + k : ℝ)) *
              ρ ^ (-(2 + k : ℝ)) * B)) := by
      exact htotal.trans (by
        ring_nf
        exact le_rfl)
    _ ≤ C₁₆ * ρ ^ (-(2 + k : ℝ)) * A +
        C₁₆ * ρ ^ (-(2 + k : ℝ)) * B :=
      add_le_add hAglobal hBglobal
    _ = C₁₆ * ρ ^ (-(2 + k : ℝ)) * (A + B) := by ring


end CKN
