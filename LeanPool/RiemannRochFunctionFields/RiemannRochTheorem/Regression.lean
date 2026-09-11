/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.RiemannRochTheorem.Corollaries

/-!
# Regression theorems via Riemann–Roch
Sanity checks on `k(t)` and spot checks for the specialty index table.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

namespace FunctionField.Chart

variable (k : Type*) [Field k]

/-- `genus (RatFunc k) = 0` revisited through the corollary package. -/
theorem genus_ratFunc_via_corollaries : genus k (RatFunc k) = 0 :=
  genus_ratFunc k

/-- When `g = 0`, a canonical divisor has degree `−2`. -/
theorem deg_canonical_ratFunc {W : DivisorA k (RatFunc k)} (hW : IsCanonical k (RatFunc k) W) :
    deg k (RatFunc k) W = -2 := by
  rw [deg_canonical k (RatFunc k) hW, genus_ratFunc]
  norm_num

/-- Spot check: negative degree forces `ℓ(D) = 0` on `RatFunc k`. -/
theorem ell_neg_deg_ratFunc (D : DivisorA k (RatFunc k)) (h : deg k (RatFunc k) D < 0) :
    ell k (RatFunc k) D = 0 := by
  exact RRspace_neg_deg_ell k (RatFunc k) h

/-- Spot check: large degree forces `ℓ(D) = deg D + 1` when `g = 0`. -/
theorem ell_large_deg_ratFunc {W : DivisorA k (RatFunc k)} (hW : IsCanonical k (RatFunc k) W)
    (D : DivisorA k (RatFunc k)) (h : deg k (RatFunc k) D ≥ -1) :
    (ell k (RatFunc k) D : ℤ) = deg k (RatFunc k) D + 1 := by
  have h' : deg k (RatFunc k) D ≥ 2 * (genus k (RatFunc k) : ℤ) - 1 := by
    rw [genus_ratFunc]
    norm_num
    exact h
  simpa [genus_ratFunc] using ell_eq_of_deg_ge k (RatFunc k) hW D h'

end FunctionField.Chart

end
