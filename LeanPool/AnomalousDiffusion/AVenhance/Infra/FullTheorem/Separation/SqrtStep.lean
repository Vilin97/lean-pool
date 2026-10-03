/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith

/-! # From an energy gap to a norm gap

If `0 ≤ E₂ ≤ E₁ ≤ E₀`, `K ≥ 0` and `E₁ - E₂ ≥ 3.2 K E₀`, then `K √E₀ ≤ 2 (√E₁ - √E₂)`. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.FullTheorem.Separation

theorem sqrt_gap {E₀ E₁ E₂ K : ℝ} (h1 : E₁ ≤ E₀) (h2 : 0 ≤ E₂) (h12 : E₂ ≤ E₁) (hK : 0 ≤ K)
    (hgap : (16 / 5) * K * E₀ ≤ E₁ - E₂) :
    K * Real.sqrt E₀ ≤ 2 * (Real.sqrt E₁ - Real.sqrt E₂) := by
  have hE1 : 0 ≤ E₁ := h2.trans h12
  have hE0 : 0 ≤ E₀ := hE1.trans h1
  set r := Real.sqrt E₀ with hr
  set a := Real.sqrt E₁ with ha
  set b := Real.sqrt E₂ with hb
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have har : a ≤ r := Real.sqrt_le_sqrt h1
  have hab : b ≤ a := Real.sqrt_le_sqrt h12
  have hr2 : r ^ 2 = E₀ := Real.sq_sqrt hE0
  have ha2 : a ^ 2 = E₁ := Real.sq_sqrt hE1
  have hb2 : b ^ 2 = E₂ := Real.sq_sqrt h2
  rcases eq_or_lt_of_le hr0 with hr00 | hrpos
  · have hr' : r = 0 := hr00.symm
    have ha' : a = 0 := le_antisymm (by linarith) ha0
    have hb' : b = 0 := le_antisymm (by linarith) hb0
    rw [hr', ha', hb']
    simp
  · -- (a - b)(a + b) ≥ 3.2 K r², and a + b ≤ 2 r
    have hgap' : (16 / 5) * K * r ^ 2 ≤ (a - b) * (a + b) := by nlinarith
    have hab' : (a - b) * (a + b) ≤ (a - b) * (2 * r) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have : (16 / 5) * K * r * r ≤ (a - b) * (2 * r) := by nlinarith
    have hKr : 0 ≤ K * r := mul_nonneg hK hr0
    have : (16 / 5) * (K * r) ≤ 2 * (a - b) := by
      have h3 : ((16 / 5) * (K * r)) * r ≤ (2 * (a - b)) * r := by nlinarith
      exact le_of_mul_le_mul_right h3 hrpos
    linarith

end AVenhance.Infra.FullTheorem.Separation
