/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionRiemannSpace
public import Mathlib.Tactic

/-!
# Splitting an effective divisor at one place

The one-point Stepanov argument starts with a many-pole divisor supplied by
plane monomials, then removes every allowed pole except the distinguished
one.  This file records the elementary divisor identities needed for that
comparison.  The actual codimension estimate is kept separate.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- Delete the coefficient of `D` at `P`, retaining all other coefficients. -/
def finiteExtensionDivisorAway
    (D : FiniteExtensionDivisor K L) (P : FiniteExtensionPlace K L) :
    FiniteExtensionDivisor K L :=
  D - Finsupp.single P (D P)

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem finiteExtensionDivisorAway_apply_self
    (D : FiniteExtensionDivisor K L) (P : FiniteExtensionPlace K L) :
    finiteExtensionDivisorAway K L D P P = 0 := by
  simp [finiteExtensionDivisorAway]

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem finiteExtensionDivisorAway_apply_of_ne
    (D : FiniteExtensionDivisor K L) (P v : FiniteExtensionPlace K L)
    (hv : v ≠ P) :
    finiteExtensionDivisorAway K L D P v = D v := by
  simp [finiteExtensionDivisorAway, hv]

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- Splitting off the `P` coefficient recovers the original divisor. -/
theorem single_add_finiteExtensionDivisorAway
    (D : FiniteExtensionDivisor K L) (P : FiniteExtensionPlace K L) :
    Finsupp.single P (D P) + finiteExtensionDivisorAway K L D P = D := by
  ext v
  by_cases hv : v = P
  · subst v
    simp
  · simp [finiteExtensionDivisorAway]

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- Removing one coefficient preserves effectiveness. -/
theorem finiteExtensionDivisorAway_effective
    (D : FiniteExtensionDivisor K L) (P : FiniteExtensionPlace K L)
    (hD : ∀ v, 0 ≤ D v) :
    ∀ v, 0 ≤ finiteExtensionDivisorAway K L D P v := by
  intro v
  by_cases hv : v = P
  · subst v
    simp
  · simpa [finiteExtensionDivisorAway, hv] using hD v

omit [Fintype K] [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
/-- The degree of a divisor supported at one place. -/
@[simp]
theorem finiteExtensionDivisorDegree_single
    (P : FiniteExtensionPlace K L) (z : ℤ) :
    finiteExtensionDivisorDegree K L (Finsupp.single P z) =
      z * (finiteExtensionPlaceDegree K L P : ℤ) := by
  classical
  simp [finiteExtensionDivisorDegree]

omit [Fintype K] [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
/-- Divisor degree changes sign under negation. -/
theorem finiteExtensionDivisorDegree_neg
    (D : FiniteExtensionDivisor K L) :
    finiteExtensionDivisorDegree K L (-D) =
      -finiteExtensionDivisorDegree K L D := by
  have h := finiteExtensionDivisorDegree_add K L D (-D)
  rw [add_neg_cancel] at h
  have hzero : finiteExtensionDivisorDegree K L (0 : FiniteExtensionDivisor K L) = 0 := by
    simp [finiteExtensionDivisorDegree]
  rw [hzero] at h
  omega

/-- Divisor degree respects subtraction. -/
theorem finiteExtensionDivisorDegree_sub
    (D E : FiniteExtensionDivisor K L) :
    finiteExtensionDivisorDegree K L (D - E) =
      finiteExtensionDivisorDegree K L D -
        finiteExtensionDivisorDegree K L E := by
  rw [sub_eq_add_neg, finiteExtensionDivisorDegree_add,
    finiteExtensionDivisorDegree_neg]
  rfl

/-- Degree bookkeeping for the divisor away from the selected place. -/
theorem finiteExtensionDivisorDegree_away
    (D : FiniteExtensionDivisor K L) (P : FiniteExtensionPlace K L) :
    finiteExtensionDivisorDegree K L (finiteExtensionDivisorAway K L D P) =
      finiteExtensionDivisorDegree K L D -
        D P * (finiteExtensionPlaceDegree K L P : ℤ) := by
  rw [finiteExtensionDivisorAway, finiteExtensionDivisorDegree_sub,
    finiteExtensionDivisorDegree_single]

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- For an effective divisor, its one-place part is coefficientwise below it. -/
theorem single_coeff_le_of_effective
    (D : FiniteExtensionDivisor K L) (P : FiniteExtensionPlace K L)
    (hD : ∀ v, 0 ≤ D v) :
    Finsupp.single P (D P) ≤ D := by
  intro v
  by_cases hv : v = P
  · subst v
    simp
  · simpa [Finsupp.single_eq_of_ne hv] using hD v

/-- The one-point space using the selected coefficient embeds in the full
Riemann space of an effective divisor. -/
theorem onePointRiemannSpace_le_of_effective
    (D : FiniteExtensionDivisor K L) (P : FiniteExtensionPlace K L)
    (hD : ∀ v, 0 ≤ D v) :
    finiteExtensionOnePointRiemannSpace K L P (D P).toNat ≤
      finiteExtensionRiemannSpace K L D := by
  have hcoeff : ((D P).toNat : ℤ) = D P :=
    Int.toNat_of_nonneg (hD P)
  change finiteExtensionRiemannSpace K L
      (Finsupp.single P ((D P).toNat : ℤ)) ≤
    finiteExtensionRiemannSpace K L D
  rw [hcoeff]
  exact finiteExtensionRiemannSpace_mono K L
    (single_coeff_le_of_effective K L D P hD)

end

end BGS.HasseWeil
