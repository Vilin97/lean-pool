/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-! # `ζ(5)` as a real number
-/

public section

namespace Zeta5Irrational

/-- `ζ(5)` as a real number. -/
@[expose] noncomputable def zeta5 : ℝ :=
  ∑' n : ℕ, 1 / (n : ℝ) ^ 5

/-- Mathlib's `riemannZeta 5` is the real number `zeta5`. -/
theorem riemannZeta_five : riemannZeta 5 = (zeta5 : ℂ) := by
  have h := zeta_nat_eq_tsum_of_gt_one (k := 5) (by norm_num)
  rw [Nat.cast_ofNat] at h
  rw [h, zeta5, Complex.ofReal_tsum]
  push_cast
  rfl

end Zeta5Irrational
