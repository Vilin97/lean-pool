/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTwistie1Bound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTinyContract

/-! # The word energies of `T` in the `twistie1` bound

From the three gradient contracts (`‖∇ ∂^w T‖`, `|w| ≤ 2`, at the rate `L`) to the bound of the sum
`U = ∑_w 14336 D² L^{2(2-|w|)} ‖∇ ∂^w T‖²_{L²((0,1)×𝕋²)}` of `se_time_bound`. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

theorem se_U_le {κp L A Bm CB1 : ℝ} (hκp : 0 < κp) (hCB1 : 0 ≤ CB1) (hAB : 0 ≤ A * Bm)
    (S : List (Fin 2) → ℝ) (hS0 : ∀ w ∈ scWords2, 0 ≤ S w)
    (hS : ∀ w ∈ scWords2, Real.sqrt κp * Real.sqrt (S w) ≤ A * Bm * L ^ w.length) :
    Real.sqrt (∑ w ∈ scWords2, (14336 * (κp * CB1) ^ 2 * (L ^ (2 - w.length)) ^ 2) * S w) ≤
      Real.sqrt 100352 * (CB1 * A * Bm * L ^ 2) * Real.sqrt κp := by
  have hterm : ∀ w ∈ scWords2, (14336 * (κp * CB1) ^ 2 * (L ^ (2 - w.length)) ^ 2) * S w ≤
      14336 * κp * CB1 ^ 2 * (A * Bm) ^ 2 * L ^ 4 := by
    intro w hw
    have hn := sc_length_le_two_of_mem hw
    have h1 : κp * S w ≤ (A * Bm * L ^ w.length) ^ 2 := by
      have h := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (hS w hw) 2
      rwa [mul_pow, Real.sq_sqrt hκp.le, Real.sq_sqrt (hS0 w hw)] at h
    have h2 : (L ^ (2 - w.length)) ^ 2 * (L ^ w.length) ^ 2 = L ^ 4 := by
      rw [← mul_pow, ← pow_add, show 2 - w.length + w.length = 2 by omega]
      ring
    calc (14336 * (κp * CB1) ^ 2 * (L ^ (2 - w.length)) ^ 2) * S w
        = 14336 * κp * CB1 ^ 2 * (L ^ (2 - w.length)) ^ 2 * (κp * S w) := by ring
      _ ≤ 14336 * κp * CB1 ^ 2 * (L ^ (2 - w.length)) ^ 2 * (A * Bm * L ^ w.length) ^ 2 := by
          apply mul_le_mul_of_nonneg_left h1; positivity
      _ = 14336 * κp * CB1 ^ 2 * (A * Bm) ^ 2 * ((L ^ (2 - w.length)) ^ 2 * (L ^ w.length) ^ 2) :=
          by
          ring
      _ = _ := by rw [h2]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, sc_card_scWords2] at hsum
  have hY : 0 ≤ Real.sqrt 100352 * (CB1 * A * Bm * L ^ 2) * Real.sqrt κp := by
    have : 0 ≤ CB1 * A * Bm * L ^ 2 := by
      rw [show CB1 * A * Bm * L ^ 2 = CB1 * (A * Bm) * L ^ 2 by ring]
      exact mul_nonneg (mul_nonneg hCB1 hAB) (by positivity)
    positivity
  apply Real.sqrt_le_iff.2
  refine ⟨hY, ?_⟩
  have hsq : (Real.sqrt 100352 * (CB1 * A * Bm * L ^ 2) * Real.sqrt κp) ^ 2 =
      100352 * κp * CB1 ^ 2 * (A * Bm) ^ 2 * L ^ 4 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hκp.le]
    ring
  rw [hsq]
  calc _ ≤ (7 : ℕ) • (14336 * κp * CB1 ^ 2 * (A * Bm) ^ 2 * L ^ 4) := hsum
    _ = _ := by rw [nsmul_eq_mul]; push_cast; ring

end AVenhance.Infra.Section5.Contracts
end
