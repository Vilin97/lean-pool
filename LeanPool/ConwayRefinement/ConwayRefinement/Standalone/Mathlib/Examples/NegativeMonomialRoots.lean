/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.HahnSeriesGCD

/-!
# Arbitrarily long factorisations of a Hahn monomial

In the ring `ℚ((ℝ^{≤0}))`, the nonunit monomial `t⁻¹` is the `n`-th power of the nonunit
monomial `t⁻¹⁄ⁿ` for every positive integer `n`. This is a useful boundary example: the GCD and
primality theorems impose no bound on factorisation length. This example by itself makes no
atomicity claim.
-/

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.Hahn.NegativeMonomialExample

/-- The Hahn-series ring `ℚ((ℝ^{≤0}))`. -/
abbrev Ring := Hahn.nonpos ℚ

/-- The elements of `ℚ((ℝ^{≤0}))` are exactly the Hahn series supported in `(-∞, 0]`. -/
theorem mem_ring_iff (x : HahnSeries ℝ ℚ) :
    x ∈ Ring ↔ x.support ⊆ Set.Iic 0 := (Iff.rfl)

/-- The monomial `tˣ`, for `x ≤ 0`, as an element of `ℚ((ℝ^{≤0}))`. -/
def monomial (x : ℝ) (hx : x ≤ 0) : Ring :=
  ⟨HahnSeries.single x 1, fun y hy ↦ by
    rw [HahnSeries.eq_of_mem_support_single hy]
    exact hx⟩

/-- The monomial `t⁻¹⁄ⁿ`. -/
def nthRoot (n : ℕ) : Ring :=
  monomial (-(n : ℝ)⁻¹) (neg_nonpos.mpr (inv_nonneg.mpr (Nat.cast_nonneg n)))

/-- The monomial `t⁻¹`. -/
def negativeOne : Ring := monomial (-1) (by norm_num)

/-- For every `n > 0`, `t⁻¹⁄ⁿ` is a nonunit and `(t⁻¹⁄ⁿ)ⁿ = t⁻¹`. -/
def NegativeMonomialHasAllRoots : Prop :=
  ∀ (n : ℕ), 0 < n → ¬ IsUnit (nthRoot n) ∧ nthRoot n ^ n = negativeOne

end ConwayRefinement.Standalone.Hahn.NegativeMonomialExample

/-!
## Formal proof

Proof module: `NegativeMonomialRootsProof`.

* `NegativeMonomialHasAllRoots` → `NegativeMonomialHasAllRoots.proof`
-/
