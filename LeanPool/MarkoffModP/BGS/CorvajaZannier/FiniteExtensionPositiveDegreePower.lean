/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionExceptionalSupport
import Mathlib.Tactic

/-! # Positive divisor degree of a power -/

namespace BGS.CorvajaZannier

noncomputable section

open scoped BigOperators

variable (K : Type*) [Field K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- The positive degree of a principal divisor scales by the exponent. -/
theorem finiteExtensionPositiveDegree_pow
    (x : L) (hx : x ≠ 0) (m : ℕ) :
    finiteExtensionPositiveDegree K L (x ^ m) =
      m * finiteExtensionPositiveDegree K L x := by
  classical
  by_cases hm : m = 0
  · subst m
    simp [finiteExtensionPositiveDegree,
      finiteExtensionPrincipalDivisor_one K L]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  rw [finiteExtensionPositiveDegree,
    finiteExtensionPrincipalDivisor_pow K L x hx m]
  have hsupp :
      (m • finiteExtensionPrincipalDivisor K L x).support =
        (finiteExtensionPrincipalDivisor K L x).support := by
    ext w
    simp only [Finsupp.mem_support_iff, Finsupp.smul_apply, nsmul_eq_mul]
    constructor
    · exact fun h hzero ↦ h (by rw [hzero, mul_zero])
    · exact fun h hzero ↦ h (mul_eq_zero.mp hzero |>.resolve_left
        (by exact_mod_cast hm))
  rw [hsupp]
  have hfilter :
      (finiteExtensionPrincipalDivisor K L x).support.filter
          (fun w ↦ 0 < (m • finiteExtensionPrincipalDivisor K L x) w) =
        (finiteExtensionPrincipalDivisor K L x).support.filter
          (fun w ↦ 0 < finiteExtensionPrincipalDivisor K L x w) := by
    apply Finset.filter_congr
    intro w hw
    simp only [Finsupp.smul_apply, nsmul_eq_mul]
    have hmposInt : (0 : ℤ) < m := by exact_mod_cast hmpos
    constructor
    · intro h
      nlinarith
    · intro h
      exact mul_pos hmposInt h
  rw [hfilter, finiteExtensionPositiveDegree, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hwpos : 0 < finiteExtensionPrincipalDivisor K L x w :=
    (Finset.mem_filter.mp hw).2
  simp only [Finsupp.smul_apply, nsmul_eq_mul]
  rw [Int.toNat_mul (by positivity) hwpos.le]
  simp [Nat.mul_assoc]

end

end BGS.CorvajaZannier
