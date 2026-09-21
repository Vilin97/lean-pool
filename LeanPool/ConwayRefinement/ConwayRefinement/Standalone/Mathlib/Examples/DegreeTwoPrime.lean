/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Prime.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# An explicit degree-two prime Hahn series

The coefficient-one series on the displayed two-dimensional support is prime in
`K((ℝ^{≤ 0}))` over every field of characteristic zero. Its rows converge to
`-1 / (m + 1)`, and those row limits converge to zero.
-/

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.Hahn.DegreeTwoExample

universe u

/-- Hahn series over `K` supported in the nonpositive real exponents. -/
def NonpositiveSeries (K : Type u) [Field K] : Subring (HahnSeries ℝ K) where
  carrier := {x | x.support ⊆ Set.Iic 0}
  zero_mem' := by simp
  one_mem' := fun _ hg ↦ (HahnSeries.support_single_subset hg).le
  add_mem' := fun hx hy ↦
    (HahnSeries.support_add_subset _ _).trans (Set.union_subset hx hy)
  neg_mem' := fun hx ↦ (HahnSeries.support_neg_subset _).trans hx
  mul_mem' := fun hx hy ↦ HahnSeries.support_mul_subset.trans fun _ ⟨i, hi, j, hj, h⟩ ↦
    h ▸ show i + j ≤ 0 from add_nonpos (hx hi) (hy hj)

/-- The exponent in row `m` and column `n` of the displayed support. -/
def exponent (m n : ℕ) : ℝ :=
  -(1 / (m + 1 : ℝ)) -
    1 / ((m + 1 : ℝ) * (m + 2 : ℝ) * (n + 1 : ℝ))

/-- The support consists exactly of zero and the displayed row-column exponents. -/
def IsDisplayedExponent (r : ℝ) : Prop :=
  r = 0 ∨ ∃ m n : ℕ, r = exponent m n

/-- Over every characteristic-zero field there is a prime series whose coefficient is one at
exactly the displayed exponents and zero elsewhere. -/
def ExistsPrime (K : Type u) [Field K] : Prop :=
  CharZero K → ∃ x : NonpositiveSeries K,
    (∀ r : ℝ, IsDisplayedExponent r → (x : HahnSeries ℝ K).coeff r = 1) ∧
      (∀ r : ℝ, ¬ IsDisplayedExponent r → (x : HahnSeries ℝ K).coeff r = 0) ∧
        Prime x

end ConwayRefinement.Standalone.Hahn.DegreeTwoExample

/-!
## Formal proof

Proof module: `DegreeTwoPrimeProof`.

* `ExistsPrime` → `ExistsPrime.proof`
-/
