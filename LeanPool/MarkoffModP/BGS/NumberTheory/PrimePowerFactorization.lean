/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

/-!
# Prime-power factorization data

This module contains the certificate-independent data and executable
recurrences used to describe a finite prime-power factorization and the ranks
of its divisor lattice.
-/

namespace BGS.NumberTheory

/-- One claimed prime power `prime ^ exponent`. -/
structure PrimePowerFactor where
  prime : ℕ
  exponent : ℕ
  deriving DecidableEq, Repr

namespace PrimePowerFactor

/-- A factor is meaningful when its base is prime and its exponent is
positive. -/
def Valid (factor : PrimePowerFactor) : Prop :=
  factor.prime.Prime ∧ 0 < factor.exponent

/-- Executable checker for one prime-power factor. -/
def check (factor : PrimePowerFactor) : Bool :=
  decide factor.prime.Prime && decide (0 < factor.exponent)

@[simp]
theorem check_eq_true_iff (factor : PrimePowerFactor) :
    factor.check = true ↔ factor.Valid := by
  simp [check, Valid]

end PrimePowerFactor

/-- Every supplied prime-power entry is individually valid. -/
def allPrimePowerFactorsValid : List PrimePowerFactor → Prop
  | [] => True
  | factor :: factors =>
      factor.Valid ∧ allPrimePowerFactorsValid factors

/-- Executable counterpart of `allPrimePowerFactorsValid`. -/
def allPrimePowerFactorsCheck : List PrimePowerFactor → Bool
  | [] => true
  | factor :: factors =>
      factor.check && allPrimePowerFactorsCheck factors

@[simp]
theorem allPrimePowerFactorsCheck_eq_true_iff
    (factors : List PrimePowerFactor) :
    allPrimePowerFactorsCheck factors = true ↔
      allPrimePowerFactorsValid factors := by
  induction factors with
  | nil => simp [allPrimePowerFactorsCheck, allPrimePowerFactorsValid]
  | cons factor factors ih =>
      simp [allPrimePowerFactorsCheck, allPrimePowerFactorsValid, ih]

/-- The prime bases occur in strict increasing order. `List.Pairwise` rejects
duplicates and checks all later bases, not only adjacent entries. -/
def primePowerBasesStrictlyIncreasing
    (factors : List PrimePowerFactor) : Prop :=
  factors.Pairwise fun left right => left.prime < right.prime

/-- Executable strict-order checker. -/
def primePowerBasesStrictlyIncreasingCheck
    (factors : List PrimePowerFactor) : Bool :=
  decide (factors.Pairwise fun left right => left.prime < right.prime)

@[simp]
theorem primePowerBasesStrictlyIncreasingCheck_eq_true_iff
    (factors : List PrimePowerFactor) :
    primePowerBasesStrictlyIncreasingCheck factors = true ↔
      primePowerBasesStrictlyIncreasing factors := by
  simp [primePowerBasesStrictlyIncreasingCheck,
    primePowerBasesStrictlyIncreasing]

/-- Canonical prime-power input: valid entries with distinct, increasing
prime bases. -/
def canonicalPrimePowerFactors (factors : List PrimePowerFactor) : Prop :=
  allPrimePowerFactorsValid factors ∧
    primePowerBasesStrictlyIncreasing factors

/-- Executable counterpart of `canonicalPrimePowerFactors`. -/
def canonicalPrimePowerFactorsCheck
    (factors : List PrimePowerFactor) : Bool :=
  allPrimePowerFactorsCheck factors &&
    primePowerBasesStrictlyIncreasingCheck factors

@[simp]
theorem canonicalPrimePowerFactorsCheck_eq_true_iff
    (factors : List PrimePowerFactor) :
    canonicalPrimePowerFactorsCheck factors = true ↔
      canonicalPrimePowerFactors factors := by
  simp [canonicalPrimePowerFactorsCheck, canonicalPrimePowerFactors]

/-- The integer represented by a supplied prime-power list. -/
def primePowerFactorizationValue : List PrimePowerFactor → ℕ
  | [] => 1
  | factor :: factors =>
      factor.prime ^ factor.exponent *
        primePowerFactorizationValue factors

/-- The total exponent, i.e. the top rank of the divisor lattice. -/
def primePowerTotalExponent : List PrimePowerFactor → ℕ
  | [] => 0
  | factor :: factors =>
      factor.exponent + primePowerTotalExponent factors

/-- Coefficient recurrence for `∏ (1 + X + ... + X^e)`. -/
def divisorRankCoefficient :
    List PrimePowerFactor → ℕ → ℕ
  | [], 0 => 1
  | [], _ + 1 => 0
  | factor :: factors, rank =>
      ∑ exponent ∈ Finset.range (min factor.exponent rank + 1),
        divisorRankCoefficient factors (rank - exponent)

/-- The central rank coefficient recomputed from the supplied exponents. -/
def centralDivisorRankCoefficient
    (factors : List PrimePowerFactor) : ℕ :=
  divisorRankCoefficient factors (primePowerTotalExponent factors / 2)

end BGS.NumberTheory
