/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.HeatRepresentative

/-!
# Uniform bounds for heat Hölder coefficients

The scalar coefficient is linear in the source Morrey norms. Factoring
its numerical weights and taking absolute values gives a uniform vector
bound from finite bounds on the scalar source norms.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential


noncomputable section

namespace CKN.Core.Endgame

/-- Numerical weight of the scalar heat source in its Hölder coefficient. -/
def heatHolderForceWeight (γ θ₀ P : ℝ) : ℝ :=
  parabolicCampanatoHolderConstant γ P *
    (2 * 1000 * (2 : ℝ) ^ (8 - 5 / θ₀) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ +
      (1800000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 16) +
        40000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₀)) - 20)) *
          (1 - (2 : ℝ) ^ (γ - 1))⁻¹) *
    (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P)

/-- Numerical weight of each differentiated heat source. -/
def heatHolderDivergenceWeight (γ θ₁ P : ℝ) : ℝ :=
  parabolicCampanatoHolderConstant γ P *
    (2 * 300000 * (2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ +
      (120000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 20) +
        120000000000 * (2 : ℝ) ^ (8 * (5 * (1 - 1 / θ₁)) - 24)) *
          (1 - (2 : ℝ) ^ (γ - 1))⁻¹) *
    (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P)

/-- The scalar heat Hölder coefficient is linear in the source norm values. -/
theorem heatHolderCoefficient_eq_linear
    (F : ParabolicPoint → ℝ) (G : Fin 3 → ParabolicPoint → ℝ)
    (γ θ₀ θ₁ P : ℝ) :
    heatHolderCoefficient F G γ θ₀ θ₁ P =
      heatHolderForceWeight γ θ₀ P * (morreyNorm P θ₀ F).toReal +
        heatHolderDivergenceWeight γ θ₁ P * ∑ j, (morreyNorm P θ₁ (G j)).toReal := by
  unfold heatHolderCoefficient heatHolderForceWeight heatHolderDivergenceWeight
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  ring

/-- Uniform finite source bounds control the absolute scalar coefficient;
absolute weights avoid any additional sign assumptions on the exponents. -/
theorem abs_heatHolderCoefficient_le_of_source_bounds
    (γ θ₀ θ₁ P : ℝ) (KF KG : ℝ≥0∞) (hKF : KF < ⊤) (hKG : KG < ⊤)
    {F : ParabolicPoint → ℝ} {G : Fin 3 → ParabolicPoint → ℝ}
    (hF : morreyNorm P θ₀ F ≤ KF) (hG : ∀ j, morreyNorm P θ₁ (G j) ≤ KG) :
    |heatHolderCoefficient F G γ θ₀ θ₁ P| ≤
      |heatHolderForceWeight γ θ₀ P| * KF.toReal +
        |heatHolderDivergenceWeight γ θ₁ P| * 3 * KG.toReal := by
  have hFreal := ENNReal.toReal_mono hKF.ne hF
  have hGreal : (∑ j : Fin 3, (morreyNorm P θ₁ (G j)).toReal) ≤ 3 * KG.toReal := by
    calc
      _ ≤ ∑ _j : Fin 3, KG.toReal :=
        Finset.sum_le_sum (fun j _ => ENNReal.toReal_mono hKG.ne (hG j))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat]
  have hGnonneg : 0 ≤ ∑ j : Fin 3, (morreyNorm P θ₁ (G j)).toReal :=
    Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  rw [heatHolderCoefficient_eq_linear]
  calc
    _ ≤ |heatHolderForceWeight γ θ₀ P * (morreyNorm P θ₀ F).toReal| +
        |heatHolderDivergenceWeight γ θ₁ P * ∑ j, (morreyNorm P θ₁ (G j)).toReal| :=
      abs_add_le _ _
    _ = |heatHolderForceWeight γ θ₀ P| * (morreyNorm P θ₀ F).toReal +
        |heatHolderDivergenceWeight γ θ₁ P| * ∑ j, (morreyNorm P θ₁ (G j)).toReal := by
      rw [abs_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg hGnonneg]
    _ ≤ |heatHolderForceWeight γ θ₀ P| * KF.toReal +
        |heatHolderDivergenceWeight γ θ₁ P| * (3 * KG.toReal) :=
      add_le_add (mul_le_mul_of_nonneg_left hFreal (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hGreal (abs_nonneg _))
    _ = _ := by rw [mul_assoc]

/-- A uniform vector Hölder coefficient, expressed only in numerical weights
and the bounds on the scalar source norms. -/
def uniformVectorHeatHolderCoefficient (γ θ₀ θ₁ P : ℝ) (KF KG : ℝ≥0∞) : ℝ :=
  3 * (|heatHolderForceWeight γ θ₀ P| * KF.toReal +
    |heatHolderDivergenceWeight γ θ₁ P| * 3 * KG.toReal)

/-- The uniform coefficient is nonnegative. -/
theorem uniformVectorHeatHolderCoefficient_nonneg
    (γ θ₀ θ₁ P : ℝ) (KF KG : ℝ≥0∞) :
    0 ≤ uniformVectorHeatHolderCoefficient γ θ₀ θ₁ P KF KG := by
  unfold uniformVectorHeatHolderCoefficient
  positivity

/-- Componentwise finite Morrey bounds give a solution-independent upper
bound for the vector heat Hölder coefficient. -/
theorem vectorHeatHolderCoefficient_le_of_source_bounds
    (γ θ₀ θ₁ P : ℝ) (KF KG : ℝ≥0∞) (hKF : KF < ⊤) (hKG : KG < ⊤)
    {F : ParabolicPoint → Vec3} {G : Fin 3 → ParabolicPoint → Vec3}
    (hF : ∀ i, morreyNorm P θ₀ (fun x => F x i) ≤ KF)
    (hG : ∀ j i, morreyNorm P θ₁ (fun x => G j x i) ≤ KG) :
    vectorHeatHolderCoefficient F G γ θ₀ θ₁ P ≤
      uniformVectorHeatHolderCoefficient γ θ₀ θ₁ P KF KG := by
  unfold vectorHeatHolderCoefficient uniformVectorHeatHolderCoefficient
  calc
    _ ≤ ∑ _i : Fin 3, (|heatHolderForceWeight γ θ₀ P| * KF.toReal +
        |heatHolderDivergenceWeight γ θ₁ P| * 3 * KG.toReal) :=
      Finset.sum_le_sum (fun i _ => abs_heatHolderCoefficient_le_of_source_bounds
        γ θ₀ θ₁ P KF KG hKF hKG (hF i) (fun j => hG j i))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat]

end CKN.Core.Endgame
