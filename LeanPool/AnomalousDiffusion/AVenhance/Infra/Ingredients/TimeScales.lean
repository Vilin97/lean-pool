/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.TimeScaleFacts
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Parameters

/-! Exact scale ratios and elementary bounds for the time scales. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Ingredients

/-- The integer factor relating the three §2.1 time scales. -/
def tauCellFactor (β : ℝ) (Λ m : ℕ) : ℝ :=
  4 * (⌈AVenhance.epsilon β Λ (m - 1) ^ (-AVenhance.delta β)⌉₊ : ℝ) + 1

/-- Integer number of small time cells in a large time cell. -/
def tauCellCount (β : ℝ) (Λ m : ℕ) : ℕ :=
  (4 * ⌈AVenhance.epsilon β Λ (m - 1) ^ (-AVenhance.delta β)⌉₊ + 1) ^ 2

theorem tauCellFactor_sq_eq_count (β : ℝ) (Λ m : ℕ) :
    tauCellFactor β Λ m ^ 2 = (tauCellCount β Λ m : ℝ) := by
  unfold tauCellFactor tauCellCount
  push_cast
  ring

/-- `e.ratios.taum` (1140-1147): `τ'_m = (4⌈ε_{m-1}^{-δ}⌉+1) τ_m`. -/
theorem tauP_eq_cellFactor_mul_tau {β : ℝ} {Λ m : ℕ}
    (hm : 1 ≤ m) :
    AVenhance.tauP β Λ m = tauCellFactor β Λ m * AVenhance.tau β Λ m := by
  have hm0 : m ≠ 0 := by omega
  have hF : tauCellFactor β Λ m ≠ 0 := by
    unfold tauCellFactor
    positivity
  simp [AVenhance.tauP, AVenhance.tau, tauCellFactor, hm0]
  field_simp [hF]

/-- `e.ratios.taum` (1140-1147): `τ''_m = (4⌈ε_{m-1}^{-δ}⌉+1)^2 τ_m`. -/
theorem tauPP_eq_cellFactor_sq_mul_tau {β : ℝ} {Λ m : ℕ}
    (hm : 1 ≤ m) :
    AVenhance.tauPP β Λ m = tauCellFactor β Λ m ^ 2 * AVenhance.tau β Λ m := by
  have hm0 : m ≠ 0 := by omega
  have hF : tauCellFactor β Λ m ≠ 0 := by
    unfold tauCellFactor
    positivity
  simp [AVenhance.tau, tauCellFactor, hm0]
  field_simp [hF]

/-- `e.ratios.taum` (1140-1147): `τ''_m = (4⌈ε_{m-1}^{-δ}⌉+1) τ'_m`. -/
theorem tauPP_eq_cellFactor_mul_tauP {β : ℝ} {Λ m : ℕ}
    (hm : 1 ≤ m) :
    AVenhance.tauPP β Λ m = tauCellFactor β Λ m * AVenhance.tauP β Λ m := by
  have hτp := tauP_eq_cellFactor_mul_tau (β := β) (Λ := Λ) hm
  have hτpp := tauPP_eq_cellFactor_sq_mul_tau (β := β) (Λ := Λ) hm
  rw [hτp, hτpp]
  ring

/-- `e.ratios.taum` (1140-1147): the ratio `τ''_m/τ_m` is the odd integer
`(4⌈ε_{m-1}^{-δ}⌉+1)^2`. -/
theorem tauPP_eq_cellCount_mul_tau {β : ℝ} {Λ m : ℕ}
    (hm : 1 ≤ m) :
    AVenhance.tauPP β Λ m = (tauCellCount β Λ m : ℝ) * AVenhance.tau β Λ m := by
  rw [tauPP_eq_cellFactor_sq_mul_tau hm, tauCellFactor_sq_eq_count]

end AVenhance.Infra.Ingredients
