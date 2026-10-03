/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.WordOrdering

/-! Finite constants for quantitative ordering of material/spatial words. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Constants are indexed by the weighted total budget. Each commutator
product involves two strictly smaller budgets. -/
def amnrNormalOrderConstant (N : ℕ) (Cb : ℝ) : ℕ → ℝ
  | 0 => 1
  | q + 1 => (amnrNormalOrderConstant N Cb q + 1 +
      (2 : ℝ) ^ (N + 1) * Cb * amnrNormalOrderConstant N Cb q ^ 2) ^ (N ^ 2 + 1)

/-- The per-swap factor at a positive weighted budget. -/
def amnrNormalOrderSwapFactor (N : ℕ) (Cb : ℝ) (q : ℕ) : ℝ :=
  amnrNormalOrderConstant N Cb q + 1 +
    (2 : ℝ) ^ (N + 1) * Cb * amnrNormalOrderConstant N Cb q ^ 2

theorem amnrNormalOrderConstant_one_le {N : ℕ} {Cb : ℝ} (hCb : 0 ≤ Cb) (q : ℕ) :
    1 ≤ amnrNormalOrderConstant N Cb q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    have hR : 1 ≤ amnrNormalOrderSwapFactor N Cb q := by
      have hc : 0 ≤ (2 : ℝ) ^ (N + 1) * Cb * amnrNormalOrderConstant N Cb q ^ 2 := by positivity
      unfold amnrNormalOrderSwapFactor
      linarith only [ih, hc]
    exact one_le_pow₀ hR

theorem amnrNormalOrderSwapFactor_one_le {N : ℕ} {Cb : ℝ} (hCb : 0 ≤ Cb) (q : ℕ) :
    1 ≤ amnrNormalOrderSwapFactor N Cb q := by
  have hK := amnrNormalOrderConstant_one_le (N := N) hCb q
  have hc : 0 ≤ (2 : ℝ) ^ (N + 1) * Cb * amnrNormalOrderConstant N Cb q ^ 2 := by positivity
  unfold amnrNormalOrderSwapFactor
  linarith only [hK, hc]

/-- The finite inversion count is absorbed at its current weighted level. -/
theorem amnrNormalOrderSwapFactor_pow_le {N q : ℕ} {Cb : ℝ} (hCb : 0 ≤ Cb)
    (w : List (Option (Fin 2))) (hw : w.length ≤ N) :
    amnrNormalOrderSwapFactor N Cb q ^ amnrWordInversions w ≤
      amnrNormalOrderConstant N Cb (q + 1) := by
  have hinv := amnrWordInversions_le_length_sq w
  have hNs : w.length ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hw 2
  exact pow_le_pow_right₀ (amnrNormalOrderSwapFactor_one_le hCb q) (by omega)

/-- One swapped word and its commutator correction fit the next inversion power. -/
theorem amnrNormalOrderSwapFactor_absorb {N q : ℕ} {Cb : ℝ} (hCb : 0 ≤ Cb) (r : ℕ) :
    amnrNormalOrderSwapFactor N Cb q ^ r +
      (2 : ℝ) ^ (N + 1) * Cb * amnrNormalOrderConstant N Cb q ^ 2 ≤
        amnrNormalOrderSwapFactor N Cb q ^ (r + 1) := by
  let R := amnrNormalOrderSwapFactor N Cb q
  let D := (2 : ℝ) ^ (N + 1) * Cb * amnrNormalOrderConstant N Cb q ^ 2
  have hK := amnrNormalOrderConstant_one_le (N := N) hCb q
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hR := amnrNormalOrderSwapFactor_one_le (N := N) hCb q
  have hr : 1 ≤ R ^ r := one_le_pow₀ hR
  have hd := mul_le_mul_of_nonneg_right hr hD
  simp only [one_mul] at hd
  change R ^ r + D ≤ R ^ (r + 1)
  rw [pow_succ]
  have hdef : R = amnrNormalOrderConstant N Cb q + 1 + D := rfl
  have hz : 0 ≤ R ^ r * amnrNormalOrderConstant N Cb q :=
    mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans hr) ((by norm_num : (0 : ℝ) ≤ 1).trans hK)
  calc
    _ ≤ R ^ r + R ^ r * D := add_le_add le_rfl hd
    _ ≤ R ^ r * amnrNormalOrderConstant N Cb q + (R ^ r + R ^ r * D) := le_add_of_nonneg_left hz
    _ = R ^ r * R := by rw [hdef]; ring

end AVenhance.Infra.Section4
