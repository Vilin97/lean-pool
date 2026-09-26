/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponents

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology


noncomputable section

namespace CKN.Core.HeatPotential

lemma heat_morrey_theta_zero_identity {γ θ₀ : ℝ}
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5) :
    2 - 5 / θ₀ = γ := by
  rw [div_eq_mul_inv] at hθ₀ ⊢
  nlinarith only [hθ₀]

lemma heat_morrey_theta_one_identity {γ θ₁ : ℝ}
    (hθ₁ : 1 / θ₁ = (1 - γ) / 5) :
    1 - 5 / θ₁ = γ := by
  rw [div_eq_mul_inv] at hθ₁ ⊢
  nlinarith only [hθ₁]


lemma heat_morrey_geometric_ratio_lt_one {γ : ℝ}
    (hγ : γ < 1) :
    (2 : ℝ) ^ (γ - 1) < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hγ])

lemma heat_morrey_geometric_ratio_nonneg {γ : ℝ} :
    0 ≤ (2 : ℝ) ^ (γ - 1) := by
  positivity

lemma heat_morrey_geometric_series {γ : ℝ} (hγ : γ < 1) :
    ∑' j : ℕ, (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) =
      (1 - (2 : ℝ) ^ (γ - 1))⁻¹ := by
  let q : ℝ := (2 : ℝ) ^ (γ - 1)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact heat_morrey_geometric_ratio_lt_one hγ
  have hsum := hasSum_geometric_of_lt_one hq0 hq1
  have hterm : (fun j : ℕ => (2 : ℝ) ^ ((j : ℝ) * (γ - 1))) =
      (fun j : ℕ => q ^ j) := by
    funext j
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hterm]
  simpa [q] using hsum.tsum_eq

end CKN.Core.HeatPotential
