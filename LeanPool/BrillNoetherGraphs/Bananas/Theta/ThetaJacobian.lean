/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaResidue

/-! # Theta Jacobian -/

@[expose] public section

namespace Bananas

open Utilities

/-! Pure telescoping input for the theta Jacobian calculation.  The index
`k` is the unit-step number, so the coefficient `k+1` matches the path
coordinate of the interior vertex represented by that step. -/
/- TeX label: `prop-JacBanana` (weighted Jacobian telescoping identity). -/
theorem weighted_step_difference_telescope
    (A : ℕ) (s : ℕ → ℤ) :
    (Finset.sum (Finset.range (A - 1))
      (fun k => ((k + 1 : ℕ) : ℤ) * (s (k + 1) - s k))) -
        (A : ℤ) * s (A - 1) =
      - Finset.sum (Finset.range A) (fun k => s k) := by
  induction A with
  | zero => simp
  | succ A ih =>
    cases A with
    | zero => simp
    | succ A =>
      simp only [Nat.succ_sub_one, Finset.sum_range_succ, Nat.cast_add,
        Nat.cast_one]
      simp only [Nat.add_sub_cancel] at ih
      simp only [Nat.cast_add, Nat.cast_one] at ih ⊢
      rw [Finset.sum_range_succ] at ih
      linear_combination ih

end Bananas
