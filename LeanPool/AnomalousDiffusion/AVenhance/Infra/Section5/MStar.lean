/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.MTheta0IsLeast

/-! Index and power bookkeeping for §5.4. Constants at the first scale explicitly
retain their dependence on Λ; fixing Λ(β) makes them depend only on β. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance AVenhance.Infra.Ingredients

/-- Membership in the set defining the minimum. -/
theorem mTheta0_spec {β R : ℝ} {Λ : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3)
    (hΛ : 2 ^ 7 ≤ Λ) (hR : 0 < R) :
    2 ≤ mTheta0 β Λ R ∧ epsilon β Λ (mTheta0 β Λ R - 1) ^
      (1 + gamma β / 2) ≤ R :=
  (mTheta0_isLeast hβ hβ' hΛ hR).1

theorem MStar.epsilon_le_inv_128 {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hm : 1 ≤ m) :
    epsilon β Λ m ≤ (128 : ℝ)⁻¹ := by
  have hbase : 1 ≤ (Λ : ℝ) := by exact_mod_cast (show 1 ≤ Λ by omega)
  have h128 : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hexp : -(m : ℝ) ≤ -1 := by linarith only [hmreal]
  calc
    epsilon β Λ m ≤ (Λ : ℝ) ^ (-(m : ℝ)) := epsilon_le_lambda_pow hβ hβ' hΛ
    _ ≤ (Λ : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hbase hexp
    _ = (Λ : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ (128 : ℝ)⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).2 h128

theorem MStar.exponent_product (g t v : ℝ) (hg : 0 < 1 + g / 2) :
    v / (1 + g / 2) * t = 2 * v * t / (2 + g) := by
  have h1 : 1 + g / 2 ≠ 0 := ne_of_gt hg
  have h2 : 2 + g ≠ 0 := by linarith only [hg]
  field_simp [h1, h2]

end AVenhance.Infra.Section5
