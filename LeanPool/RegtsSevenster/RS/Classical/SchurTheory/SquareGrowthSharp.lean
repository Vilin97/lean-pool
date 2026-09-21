/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SquareGrowth

/-!
# Sharp square dimension growth via the exponential bound

The sharp form of the square-dimension growth: it runs on the
analytic `n ^ n ≤ e ^ n · n !` (one term of the Taylor series of
`exp`) where `square_growth` runs on the cruder combinatorial
`n ^ n ≤ 3 ^ n · n !`, and it is the sharp constant that yields the
displayed `2e` of the paper.
-/

namespace RS

open Finset

/-- The key analytic fact: `n ^ n ≤ exp n · n!`, obtained from
`pow_div_factorial_le_exp`. -/
private theorem pow_le_exp_mul_factorial (n : ℕ) :
    ((n : ℝ)) ^ n ≤ Real.exp ((n : ℝ)) * ((n.factorial : ℕ) : ℝ) := by
  have hfact_pos : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hpdf := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
  calc ((n : ℝ)) ^ n
      = ((n : ℝ)) ^ n / ((n.factorial : ℕ) : ℝ) * ((n.factorial : ℕ) : ℝ) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hfact_pos)]
    _ ≤ Real.exp ((n : ℝ)) * ((n.factorial : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hpdf hfact_pos.le

open scoped Classical in
/-- **Sharp square dimension growth.**  For a real `R ≥ 0` and any
`s > 2eR`, every submodule of the regular module whose character
equals the JT character of the `s × s` square diagram has dimension
exceeding `R ^ (s²)`.

This recovers the paper's displayed `2e`: the proof runs on
`n ^ n ≤ e ^ n · n !`, and it is that `e` which appears in the
threshold.  The paper makes no claim that `2e` cannot be
improved. -/
theorem square_growth_sharp (R : ℝ) (hR : 0 ≤ R) (s : ℕ)
    (hs : 2 * Real.exp 1 * R < s) :
    ∀ S₀ : Submodule
      (MonoidAlgebra ℂ (Equiv.Perm (Fin (squareDiagram s).card)))
      (MonoidAlgebra ℂ (Equiv.Perm (Fin (squareDiagram s).card))),
      (∀ π, jtChar (squareDiagram s) π = nChar S₀ π) →
      R ^ (s ^ 2) < (nDim S₀ : ℝ) := by
  intro S₀ hchar
  -- ═══════ PRELIMINARY: 1 ≤ s ═══════
  -- `2eR` is nonnegative, so a strictly larger natural number is
  -- positive.
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · exact absurd hs (by
        simpa using not_lt.2 (mul_nonneg
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos 1).le) hR))
    · exact hpos
  -- ═══════ STAGE 1: THE ℕ-IDENTITY GIVES (s²)! ≤ dim · (2s)^(s²) ═══════
  have hid := dim_mul_eq (squareDiagram s) S₀ hchar
  rw [square_V_eq] at hid
  have hn : (squareDiagram s).card = s ^ 2 := squareDiagram_card s
  set V := ∏ i : Fin (squareDiagram s).rowLens.length,
    (((squareDiagram s).rowLens.length - 1) - (i : ℕ)).factorial
    with hV_def
  have hVpos : 0 < V := Finset.prod_pos fun i _ => Nat.factorial_pos _
  have hD := square_D_le s hs1
  have h_fact_le : (s ^ 2).factorial ≤ nDim S₀ * (2 * s) ^ (s ^ 2) := by
    have h3 : (squareDiagram s).card.factorial * V ≤
        (nDim S₀ * (2 * s) ^ (s ^ 2)) * V := by
      calc (squareDiagram s).card.factorial * V
          ≤ nDim S₀ * ((2 * s) ^ (s ^ 2) * V) := by
            rw [← hid]; exact Nat.mul_le_mul_left _ hD
        _ = (nDim S₀ * (2 * s) ^ (s ^ 2)) * V := by ring
    have h4 := Nat.le_of_mul_le_mul_right h3 hVpos
    exact hn ▸ h4
  -- ═══════ STAGE 2: THE ANALYTIC BOUND, IN ℝ ═══════
  have hs_pos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr (by omega)
  have h_analytic : ((s ^ 2 : ℕ) : ℝ) ^ (s ^ 2) ≤
      Real.exp ((s ^ 2 : ℕ) : ℝ) * (((s ^ 2).factorial : ℕ) : ℝ) :=
    pow_le_exp_mul_factorial (s ^ 2)
  have h_fact_le_R : (((s ^ 2).factorial : ℕ) : ℝ) ≤
      ((nDim S₀ : ℕ) : ℝ) * (((2 * s) ^ (s ^ 2) : ℕ) : ℝ) := by
    exact_mod_cast h_fact_le
  have hexp_eq : Real.exp ((s ^ 2 : ℕ) : ℝ) = Real.exp 1 ^ (s ^ 2) :=
    (Real.exp_one_pow (s ^ 2)).symm
  have hcast_sq : ((s ^ 2 : ℕ) : ℝ) = (s : ℝ) ^ 2 := by push_cast; ring
  have hcast_2s : (((2 * s) ^ (s ^ 2) : ℕ) : ℝ) = (2 * (s : ℝ)) ^ (s ^ 2) := by
    push_cast; ring
  set C := Real.exp 1 ^ (s ^ 2) * (2 * (s : ℝ)) ^ (s ^ 2) with hC_def
  have hC_pos : (0 : ℝ) < C :=
    mul_pos (pow_pos (Real.exp_pos 1) _) (pow_pos (by linarith) _)
  have h_combined : ((s : ℝ) ^ 2) ^ (s ^ 2) ≤ (nDim S₀ : ℝ) * C := by
    calc ((s : ℝ) ^ 2) ^ (s ^ 2)
        = ((s ^ 2 : ℕ) : ℝ) ^ (s ^ 2) := by rw [hcast_sq]
      _ ≤ Real.exp ((s ^ 2 : ℕ) : ℝ) * ((((s ^ 2).factorial : ℕ) : ℝ)) :=
          h_analytic
      _ ≤ Real.exp ((s ^ 2 : ℕ) : ℝ) *
          (((nDim S₀ : ℕ) : ℝ) * (((2 * s) ^ (s ^ 2) : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h_fact_le_R (Real.exp_nonneg _)
      _ = (nDim S₀ : ℝ) * C := by
          rw [hexp_eq, hcast_2s, hC_def]; ring
  -- ═══════ STAGE 3: THE BASE COMPARISON, AND CANCELLING C ═══════
  -- `R ^ (s²) · C` is exactly `(2eRs) ^ (s²)`, which the hypothesis
  -- puts below `(s²) ^ (s²)`.
  have hbase : 2 * Real.exp 1 * R * (s : ℝ) < (s : ℝ) ^ 2 := by
    calc 2 * Real.exp 1 * R * (s : ℝ)
        = (2 * Real.exp 1 * R) * (s : ℝ) := by ring
      _ < (s : ℝ) * (s : ℝ) := mul_lt_mul_of_pos_right hs hs_pos
      _ = (s : ℝ) ^ 2 := by ring
  have h_pow_lt : (2 * Real.exp 1 * R * (s : ℝ)) ^ (s ^ 2) <
      ((s : ℝ) ^ 2) ^ (s ^ 2) :=
    pow_lt_pow_left₀ hbase (by positivity) (pow_ne_zero 2 (by omega))
  have h_lhs_eq : R ^ (s ^ 2) * C =
      (2 * Real.exp 1 * R * (s : ℝ)) ^ (s ^ 2) := by
    rw [hC_def, ← mul_assoc, ← mul_pow, ← mul_pow]
    congr 1; ring
  have h_main : R ^ (s ^ 2) * C < (nDim S₀ : ℝ) * C :=
    calc R ^ (s ^ 2) * C
        = (2 * Real.exp 1 * R * (s : ℝ)) ^ (s ^ 2) := h_lhs_eq
      _ < ((s : ℝ) ^ 2) ^ (s ^ 2) := h_pow_lt
      _ ≤ (nDim S₀ : ℝ) * C := h_combined
  exact lt_of_mul_lt_mul_right h_main hC_pos.le

end RS
