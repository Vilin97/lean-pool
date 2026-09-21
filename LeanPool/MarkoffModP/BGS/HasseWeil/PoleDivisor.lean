/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionRiemannSpace

/-!
# Pole divisors in the exhaustive finite-extension place model

The existing Corvaja--Zannier infrastructure records principal divisors and
their total pole height.  The Stepanov argument also needs the actual
effective pole divisor.  This file defines it by retaining the negative
coefficients of the principal divisor and changing their signs, proves that
it makes the original function a section, and identifies its divisor degree
with the existing height.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped nonZeroDivisors Polynomial

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance poleDivisorConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance poleDivisorConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The effective negative part of the principal divisor of `x`. -/
def finiteExtensionPoleDivisor (x : L) : FiniteExtensionDivisor K L :=
  by
    classical
    let D := finiteExtensionPrincipalDivisor K L x
    exact -(D.filter (fun v => D v < 0))

@[simp]
theorem finiteExtensionPoleDivisor_apply (x : L)
    (v : FiniteExtensionPlace K L) :
    finiteExtensionPoleDivisor K L x v =
      if finiteExtensionPrincipalDivisor K L x v < 0 then
        -finiteExtensionPrincipalDivisor K L x v else 0 := by
  simp only [finiteExtensionPoleDivisor, Finsupp.neg_apply,
    Finsupp.filter_apply]
  split <;> simp_all

/-- A pole divisor is effective. -/
theorem finiteExtensionPoleDivisor_effective (x : L) :
    ∀ v, 0 ≤ finiteExtensionPoleDivisor K L x v := by
  intro v
  rw [finiteExtensionPoleDivisor_apply]
  split <;> omega

/-- Adding the pole divisor to the principal divisor is effective. -/
theorem finiteExtensionPrincipal_add_poleDivisor_effective (x : L) :
    ∀ v, 0 ≤ finiteExtensionPrincipalDivisor K L x v +
      finiteExtensionPoleDivisor K L x v := by
  intro v
  rw [finiteExtensionPoleDivisor_apply]
  split <;> omega

/-- Every nonzero function is a section of its pole divisor. -/
theorem mem_finiteExtensionRiemannSpace_poleDivisor
    (x : L) (hx : x ≠ 0) :
    x ∈ finiteExtensionRiemannSpace K L
      (finiteExtensionPoleDivisor K L x) := by
  rw [mem_finiteExtensionRiemannSpace]
  exact Or.inr ⟨hx,
    finiteExtensionPrincipal_add_poleDivisor_effective K L x⟩

/-- The degree of the pole divisor is the previously defined pole height. -/
theorem finiteExtensionDivisorDegree_poleDivisor
    (x : L) :
    finiteExtensionDivisorDegree K L
      (finiteExtensionPoleDivisor K L x) =
        (finiteExtensionHeight K L x : ℤ) := by
  classical
  let D := finiteExtensionPrincipalDivisor K L x
  have hnegative := finiteExtensionHeight_negativeSum K L x
  change -((finiteExtensionHeight K L x : ℕ) : ℤ) =
      ∑ v ∈ D.support.filter (fun v => D v < 0),
        D v * (finiteExtensionPlaceDegree K L v : ℤ) at hnegative
  rw [finiteExtensionDivisorDegree, Finsupp.sum,
    finiteExtensionPoleDivisor]
  simp only [Finsupp.support_neg, Finsupp.support_filter,
    Finsupp.neg_apply, Finsupp.filter_apply]
  calc
    ∑ a ∈ D.support.filter (fun v => D v < 0),
        -(if D a < 0 then D a else 0) *
          (finiteExtensionPlaceDegree K L a : ℤ) =
        -∑ a ∈ D.support.filter (fun v => D v < 0),
          D a * (finiteExtensionPlaceDegree K L a : ℤ) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro a ha
            rw [if_pos (Finset.mem_filter.mp ha).2]
            ring
    _ = (finiteExtensionHeight K L x : ℤ) := by omega

/-- Divisor degree commutes with natural scaling. -/
theorem finiteExtensionDivisorDegree_nsmul
    (n : ℕ) (D : FiniteExtensionDivisor K L) :
    finiteExtensionDivisorDegree K L (n • D) =
      (n : ℤ) * finiteExtensionDivisorDegree K L D := by
  induction n with
  | zero => simp [finiteExtensionDivisorDegree]
  | succ n ih =>
      rw [succ_nsmul, finiteExtensionDivisorDegree_add, ih]
      push_cast
      ring

/-- A coordinate monomial is a section of the sum of the correspondingly
scaled pole divisors. -/
theorem pow_mul_pow_mem_poleDivisor_budget
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) (i j : ℕ) :
    x ^ i * y ^ j ∈ finiteExtensionRiemannSpace K L
      (i • finiteExtensionPoleDivisor K L x +
        j • finiteExtensionPoleDivisor K L y) := by
  exact finiteExtensionRiemannSpace_mul_mem K L
    (finiteExtensionRiemannSpace_pow_mem K L
      (mem_finiteExtensionRiemannSpace_poleDivisor K L x hx) i)
    (finiteExtensionRiemannSpace_pow_mem K L
      (mem_finiteExtensionRiemannSpace_poleDivisor K L y hy) j)

/-- The degree of the monomial pole budget is the corresponding linear
combination of the two coordinate heights. -/
theorem finiteExtensionDivisorDegree_pow_mul_pow_budget
    (x y : L) (i j : ℕ) :
    finiteExtensionDivisorDegree K L
      (i • finiteExtensionPoleDivisor K L x +
        j • finiteExtensionPoleDivisor K L y) =
      (i : ℤ) * finiteExtensionHeight K L x +
        (j : ℤ) * finiteExtensionHeight K L y := by
  rw [finiteExtensionDivisorDegree_add,
    finiteExtensionDivisorDegree_nsmul,
    finiteExtensionDivisorDegree_nsmul,
    finiteExtensionDivisorDegree_poleDivisor,
    finiteExtensionDivisorDegree_poleDivisor]

end

end BGS.HasseWeil
