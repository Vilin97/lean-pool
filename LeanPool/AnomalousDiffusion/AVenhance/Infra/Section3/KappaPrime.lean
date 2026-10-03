/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.TimeScaleFacts
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KappaAt

/-! A positive auxiliary diffusivity sequence for the §3.3 recurrence. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section3

open AVenhance

/-- The auxiliary sequence `κ'` from `e.kappa.prime.sequence`, indexed by its
current scale and the distance from its terminal value. -/
def kappaPrimeAt (β : ℝ) (Λ : ℕ) (κ : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => κ
  | m, d + 1 =>
      let κnext := kappaPrimeAt β Λ κ (m + 1) d
      κnext + 9 * a β Λ (m + 1) ^ 2 * epsilon β Λ (m + 1) ^ 4 /
        (80 * κnext)

theorem kappaPrimeAt_pos {β : ℝ} {Λ : ℕ} (hβ : 1 < β)
    (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) {κ : ℝ} (hκ : 0 < κ)
    (m d : ℕ) : 0 < kappaPrimeAt β Λ κ m d := by
  induction d generalizing m with
  | zero => simp [kappaPrimeAt, hκ]
  | succ d ih =>
      rw [kappaPrimeAt]
      let κnext := kappaPrimeAt β Λ κ (m + 1) d
      have hnext : 0 < κnext := ih (m + 1)
      have ha : 0 < a β Λ (m + 1) :=
        Infra.Cutoff.a_pos hβ hβ' hΛ
      have he : 0 < epsilon β Λ (m + 1) :=
        Infra.Cutoff.epsilon_pos hβ hβ' hΛ
      have hterm : 0 ≤ 9 * a β Λ (m + 1) ^ 2 *
          epsilon β Λ (m + 1) ^ 4 / (80 * κnext) := by
        apply div_nonneg
        · positivity
        · positivity
      exact lt_of_lt_of_le hnext (le_add_of_nonneg_right hterm)

end AVenhance.Infra.Section3
