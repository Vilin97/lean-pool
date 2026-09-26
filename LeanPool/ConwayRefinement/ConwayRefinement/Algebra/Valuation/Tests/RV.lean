/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.RV
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.OfValuation
public import Mathlib.Algebra.Order.Ring.Rat

import Mathlib.Algebra.Ring.Prod

/-!
# API checks for RV classes, initial forms, and the residue ring

The fixtures are Mathlib valuations read as multiplicative max-additive degrees through
`MaxAddDegree.ofValuation`. The first-projection valuation on `ℚ × ℚ` is nonseparated. Its
nonzero kernel element `(0, 1)` therefore separates LM24's RV quotient from a quotient that
collapses only literal zero. The representatives `(1, 1)` and `(1, 0)` further verify that adding
a kernel element preserves both the RV class and the leading homogeneous class.

The separated trivial valuation on `ℚ` checks the grade-zero residue-ring multiplication on
nontrivial representatives. These tests use only the public RV and associated-graded interfaces.
-/
public noncomputable section

namespace Tests

open scoped DirectSum

/-- The trivial valuation pulled back along the first projection, used to test the RV quotient. -/
def rvFirstProjectionValuation : MaxAddDegree (ℚ × ℚ) ℕ :=
  MaxAddDegree.ofValuation
    ((1 : Valuation ℚ (WithZero (Multiplicative ℕ))).comap (RingHom.fst ℚ ℚ))

instance : rvFirstProjectionValuation.IsMultiplicative :=
  inferInstanceAs (MaxAddDegree.ofValuation _).IsMultiplicative

/-- The nonzero element `(0, 1)` in the support of the first-projection valuation. -/
def rvSupportElement : ℚ × ℚ :=
  (0, 1)

theorem rvSupportElement_ne_zero : rvSupportElement ≠ 0 := by
  norm_num [rvSupportElement]

theorem rvFirstProjectionValuation_value_support :
    rvFirstProjectionValuation rvSupportElement = ⊥ := by
  simp [MaxAddDegree.ofValuation_apply, rvSupportElement, rvFirstProjectionValuation,
    Valuation.one_apply_def]

/-- The RV zero class contains the nonzero support element `(0, 1)`. -/
theorem rvSupportElement_rv_eq_zero :
    rvFirstProjectionValuation.rv rvSupportElement = 0 := by
  rw [MaxAddDegree.rv_eq_zero_iff]
  exact rvFirstProjectionValuation_value_support

/-- The standard-order encoding of the RV relation is reflexive at a nonzero support element. -/
theorem rvSupportElement_self_related :
    rvFirstProjectionValuation.RVRel rvSupportElement rvSupportElement :=
  rvFirstProjectionValuation.rvRel_refl rvSupportElement

/-- Representatives differing by a nonzero support element have the same RV class. -/
theorem rvFirstProjectionValuation_same_rv :
    rvFirstProjectionValuation.rv (1, 1) = rvFirstProjectionValuation.rv (1, 0) := by
  rw [MaxAddDegree.rv_eq_iff]
  rw [MaxAddDegree.rvRel_iff]
  right
  constructor
  · simp [MaxAddDegree.ofValuation_apply, rvFirstProjectionValuation,
      Valuation.one_apply_def]
  · simp [MaxAddDegree.ofValuation_apply, rvFirstProjectionValuation,
      Valuation.one_apply_def]

/-- RV-equivalent representatives have the same initial form. -/
theorem rvFirstProjectionValuation_same_initialForm :
    rvFirstProjectionValuation.initialForm (1, 1) =
      rvFirstProjectionValuation.initialForm (1, 0) := by
  exact rvFirstProjectionValuation.initialForm_eq_of_rvRel
    ((MaxAddDegree.rv_eq_iff rvFirstProjectionValuation).mp
      rvFirstProjectionValuation_same_rv)

/-- The RV-to-homogeneous map retains multiplication and the support zero. -/
theorem rvHomogeneous_support_mul_one :
    rvFirstProjectionValuation.rvHomogeneous
        (rvFirstProjectionValuation.rv rvSupportElement *
          rvFirstProjectionValuation.rv (1, 0)) = 0 := by
  rw [rvSupportElement_rv_eq_zero, zero_mul, map_zero]

/-- The trivial valuation on the rationals in max-additive notation for RV computations. -/
def rvTrivialValuation : MaxAddDegree ℚ ℕ :=
  MaxAddDegree.ofValuation 1

instance : rvTrivialValuation.IsMultiplicative :=
  inferInstanceAs (MaxAddDegree.ofValuation _).IsMultiplicative

/-- The rational number two in filtration degree zero for the RV multiplication fixture. -/
def rvTwoRepresentative : rvTrivialValuation.filtrationLE 0 :=
  ⟨2, by simp [MaxAddDegree.ofValuation_apply, rvTrivialValuation, Valuation.one_apply_def]⟩

/-- The rational number three in filtration degree zero for the RV multiplication fixture. -/
def rvThreeRepresentative : rvTrivialValuation.filtrationLE 0 :=
  ⟨3, by simp [MaxAddDegree.ofValuation_apply, rvTrivialValuation, Valuation.one_apply_def]⟩

/-- The rational number six in filtration degree zero for the RV multiplication fixture. -/
def rvSixRepresentative : rvTrivialValuation.filtrationLE 0 :=
  ⟨6, by simp [MaxAddDegree.ofValuation_apply, rvTrivialValuation, Valuation.one_apply_def]⟩

/-- Multiplication in the residue ring computes the product of the classes of two and three. -/
theorem residueRing_two_mul_three :
    rvTrivialValuation.componentMk 0 rvTwoRepresentative *
        rvTrivialValuation.componentMk 0 rvThreeRepresentative =
      rvTrivialValuation.componentMk 0 rvSixRepresentative := by
  apply rvTrivialValuation.residueRingHom_injective
  rw [map_mul]
  rw [MaxAddDegree.residueRingHom_apply,
    MaxAddDegree.residueRingHom_apply, MaxAddDegree.residueRingHom_apply,
    ← MaxAddDegree.homogeneousMk_apply, ← MaxAddDegree.homogeneousMk_apply,
    ← MaxAddDegree.homogeneousMk_apply]
  rw [MaxAddDegree.homogeneousMk_mul]
  apply congrArg (rvTrivialValuation.homogeneousMk 0)
  apply Subtype.ext
  norm_num [rvTwoRepresentative, rvThreeRepresentative, rvSixRepresentative]

end Tests
