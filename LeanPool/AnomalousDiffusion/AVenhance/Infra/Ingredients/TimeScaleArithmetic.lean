/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScaleBounds

/-! Integer-ratio consequences for the time scales. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Ingredients

/-- Natural ceiling entering the first time-scale definition. -/
def TimeScaleArithmetic.tauCeil (β : ℝ) (Λ m : ℕ) : ℕ :=
  ⌈AVenhance.epsilon β Λ (m - 1) ^ (-AVenhance.delta β)⌉₊

/-- Natural ceiling entering the finer time-scale definition. -/
def TimeScaleArithmetic.tauPPceil (β : ℝ) (Λ m : ℕ) : ℕ :=
  ⌈AVenhance.a β Λ (m - 1) /
    AVenhance.epsilon β Λ (m - 1) ^ (2 * AVenhance.delta β)⌉₊

theorem TimeScaleArithmetic.tauPP_reciprocal_exact {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    1 / AVenhance.tauPP β Λ m =
      (2 : ℝ) ^ (25 : ℕ) * (TimeScaleArithmetic.tauPPceil β Λ m : ℝ) := by
  let A := TimeScaleArithmetic.tauPPceil β Λ m
  have hApos : 0 < A := by
    dsimp [A, TimeScaleArithmetic.tauPPceil]
    apply Nat.ceil_pos.mpr
    exact div_pos
      (AVenhance.Infra.Cutoff.a_pos hβ hβ' hΛ)
      (Real.rpow_pos_of_pos
        (AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ) _)
  have hAne : (A : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hApos)
  have hpow : (2 : ℝ) ^ (-25 : ℤ) = ((2 : ℝ) ^ (25 : ℕ))⁻¹ := by
    norm_num
  unfold AVenhance.tauPP
  rw [hpow]
  dsimp [A, TimeScaleArithmetic.tauPPceil]
  field_simp [hAne]

theorem TimeScaleArithmetic.tauFactor_cast {β : ℝ} {Λ m : ℕ} :
    tauCellFactor β Λ m = (4 * TimeScaleArithmetic.tauCeil β Λ m + 1 : ℕ) := by
  simp [tauCellFactor, TimeScaleArithmetic.tauCeil]

/-- `e.ratios.taum` (1140-1147): `1/τ''_m` is an integer multiple of four. -/
theorem tauPP_reciprocal_multiple_four {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (_hm : 1 ≤ m) :
    ∃ n : ℕ, 1 / AVenhance.tauPP β Λ m = (4 * n : ℕ) := by
  refine ⟨2 ^ 23 * TimeScaleArithmetic.tauPPceil β Λ m, ?_⟩
  rw [TimeScaleArithmetic.tauPP_reciprocal_exact (m := m) hβ hβ' hΛ]
  norm_num
  ring

/-- `e.ratios.taum` (1140-1147): `τ''_m/τ_m` is an integer congruent to one
modulo four, and `1/τ_m` is an integer multiple of four. -/
theorem tauPP_ratio_and_tau_reciprocal {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hm : 1 ≤ m) :
    AVenhance.tauPP β Λ m / AVenhance.tau β Λ m =
        (tauCellCount β Λ m : ℕ) ∧
      ∃ n : ℕ, 1 / AVenhance.tau β Λ m = (4 * n : ℕ) := by
  let A := TimeScaleArithmetic.tauPPceil β Λ m
  let C := TimeScaleArithmetic.tauCeil β Λ m
  have hτ : 0 < AVenhance.tau β Λ m := tau_pos hβ hβ' hΛ
  have hPP : 0 < AVenhance.tauPP β Λ m :=
    AVenhance.Infra.Cutoff.tauPP_pos hβ hβ' hΛ
  have hFpos : 0 < tauCellFactor β Λ m := by
    unfold tauCellFactor
    positivity
  have hfactor : AVenhance.tau β Λ m =
      (tauCellFactor β Λ m)⁻¹ ^ 2 * AVenhance.tauPP β Λ m := by
    have hm0 : m ≠ 0 := by omega
    simp [AVenhance.tau, tauCellFactor, hm0]
  have hratio : AVenhance.tauPP β Λ m / AVenhance.tau β Λ m =
      (tauCellFactor β Λ m) ^ 2 := by
    rw [tauPP_eq_cellFactor_sq_mul_tau hm]
    field_simp [ne_of_gt hτ]
  have hrecip : 1 / AVenhance.tau β Λ m =
      (tauCellFactor β Λ m) ^ 2 * (1 / AVenhance.tauPP β Λ m) := by
    rw [hfactor]
    field_simp [ne_of_gt hPP, ne_of_gt hFpos]
  have hpprec := TimeScaleArithmetic.tauPP_reciprocal_exact (m := m) hβ hβ' hΛ
  have hcount : tauCellCount β Λ m =
      (4 * C + 1) ^ 2 := by
    simp [tauCellCount, C, TimeScaleArithmetic.tauCeil]
  have hF : tauCellFactor β Λ m = (4 * C + 1 : ℕ) := by
    simpa [C] using TimeScaleArithmetic.tauFactor_cast (β := β) (Λ := Λ) (m := m)
  constructor
  · rw [hratio, hF, hcount]
    push_cast
    ring
  · refine ⟨((4 * C + 1) ^ 2) * (2 ^ 23 * A), ?_⟩
    rw [hrecip, hpprec, hF]
    dsimp [A, TimeScaleArithmetic.tauPPceil]
    norm_num
    ring

end AVenhance.Infra.Ingredients
