/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeAssociatedGraded
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.OfValuation
public import Mathlib.Algebra.Order.Ring.Rat

import Mathlib.Algebra.Ring.Prod

/-!
# API checks for max-additive degrees and associated graded rings

The raw constant-value fixture satisfies the two multiplicative semi-valuation axioms printed at
the start of LM24, Section 4, but the relation in Definition 4.1.1 is not reflexive. This verifies
that the additional zero-to-bottom condition used by the formalization is not a consequence of the
printed axioms.

The remaining fixtures are Mathlib valuations read as multiplicative max-additive degrees through
`MaxAddDegree.ofValuation`. The first is a nonseparated counterexample to representative-sensitive
quotient rules. It pulls the trivial valuation on `ℚ` back along the first projection
`ℚ × ℚ → ℚ`. Thus `(0, 1)` is a nonzero element of the kernel. The certificates verify that its
homogeneous class is zero and that `(1, 1)` and `(1, 0)` have the same nonzero class. These
statements would fail for a construction that collapsed only the literal zero representative.

The second fixture uses the separated trivial valuation on `ℚ`. It proves that the asymmetric
zero-plus-one test printed in LM24, Definition 4.2.4 selects the zero branch even though the class
of one is nonzero. Its grade-zero multiplication certificate also computes the product of the
homogeneous classes of two and three as the class of six. Together the fixtures exercise support,
separation, the strict quotient, and multiplication.
-/

public noncomputable section

namespace Tests

/-- The constant finite value map used to test the two semi-valuation axioms printed in LM24.
Ignoring its argument is the point of the fixture, hence the `nolint`. -/
def printedConstantValue (_ : ℚ) : WithBot ℕ :=
  0

theorem printedConstantValue_add_le_max (x y : ℚ) :
    printedConstantValue (x + y) ≤ max (printedConstantValue x) (printedConstantValue y) := by
  simp [printedConstantValue]

theorem printedConstantValue_mul (x y : ℚ) :
    printedConstantValue (x * y) = printedConstantValue x + printedConstantValue y := by
  simp [printedConstantValue]

/-- The two semi-valuation axioms printed in LM24 do not make Definition 4.1.1 reflexive. -/
theorem printedSemivaluationRelation_not_reflexive :
    ¬ Std.Refl (fun x y : ℚ ↦ printedConstantValue (x - y) < printedConstantValue x) := by
  intro h
  simpa [printedConstantValue] using h.refl 0

/-- The trivial valuation on the first coordinate of `ℚ × ℚ`. -/
def firstProjectionValuation : MaxAddDegree (ℚ × ℚ) ℕ :=
  MaxAddDegree.ofValuation
    ((1 : Valuation ℚ (WithZero (Multiplicative ℕ))).comap (RingHom.fst ℚ ℚ))

instance : firstProjectionValuation.IsMultiplicative :=
  inferInstanceAs (MaxAddDegree.ofValuation _).IsMultiplicative

theorem firstProjectionValuation_value_zero_one :
    firstProjectionValuation (0, 1) = ⊥ := by
  simp [MaxAddDegree.ofValuation_apply, firstProjectionValuation, Valuation.one_apply_def]

theorem firstProjectionValuation_value_one_one :
    firstProjectionValuation (1, 1) = 0 := by
  simp [MaxAddDegree.ofValuation_apply, firstProjectionValuation, Valuation.one_apply_def]

/-- The first-projection valuation is genuinely nonseparated. -/
theorem firstProjectionValuation_not_isSeparated :
    ¬ firstProjectionValuation.IsSeparated := by
  rw [MaxAddDegree.isSeparated_iff]
  push Not
  exact ⟨(0, 1), by simp [MaxAddDegree.ofValuation_apply, firstProjectionValuation,
    Valuation.one_apply_def]⟩

def supportRepresentative : firstProjectionValuation.filtrationLE 0 :=
  ⟨(0, 1), by simp [MaxAddDegree.ofValuation_apply, firstProjectionValuation,
    Valuation.one_apply_def]⟩

def nonzeroRepresentative : firstProjectionValuation.filtrationLE 0 :=
  ⟨(1, 1), by simp [MaxAddDegree.ofValuation_apply, firstProjectionValuation,
    Valuation.one_apply_def]⟩

def sameLeadingRepresentative : firstProjectionValuation.filtrationLE 0 :=
  ⟨(1, 0), by simp [MaxAddDegree.ofValuation_apply, firstProjectionValuation,
    Valuation.one_apply_def]⟩

/-- A nonzero element of the support ideal represents homogeneous zero. -/
theorem supportRepresentative_componentMk_eq_zero :
    firstProjectionValuation.componentMk 0 supportRepresentative = 0 := by
  rw [MaxAddDegree.componentMk_eq_zero_iff]
  simp [MaxAddDegree.ofValuation_apply, supportRepresentative, firstProjectionValuation,
    Valuation.one_apply_def]

/-- The class represented by `(1, 1)` is nonzero. -/
theorem nonzeroRepresentative_componentMk_ne_zero :
    firstProjectionValuation.componentMk 0 nonzeroRepresentative ≠ 0 := by
  rw [ne_eq, MaxAddDegree.componentMk_eq_zero_iff]
  simp [MaxAddDegree.ofValuation_apply, nonzeroRepresentative, firstProjectionValuation,
    Valuation.one_apply_def]

/-- Representatives differing by the nonzero support element `(0, 1)` have the same class. -/
theorem firstProjectionValuation_same_leading_class :
    firstProjectionValuation.componentMk 0 nonzeroRepresentative =
      firstProjectionValuation.componentMk 0 sameLeadingRepresentative := by
  rw [← sub_eq_zero, ← map_sub, MaxAddDegree.componentMk_eq_zero_iff]
  change firstProjectionValuation ((1, 1) - (1, 0)) < (0 : ℕ)
  simp [MaxAddDegree.ofValuation_apply, firstProjectionValuation, Valuation.one_apply_def]

/-- Adding a nonzero support representative does not change a homogeneous class. -/
theorem firstProjectionValuation_add_support_class :
    firstProjectionValuation.componentMk 0 nonzeroRepresentative +
        firstProjectionValuation.componentMk 0 supportRepresentative =
      firstProjectionValuation.componentMk 0 nonzeroRepresentative := by
  rw [supportRepresentative_componentMk_eq_zero, add_zero]

/-- The separated trivial valuation on `ℚ`. -/
def trivialValuation : MaxAddDegree ℚ ℕ :=
  MaxAddDegree.ofValuation 1

instance : trivialValuation.IsMultiplicative :=
  inferInstanceAs (MaxAddDegree.ofValuation _).IsMultiplicative

def oneRepresentative : trivialValuation.filtrationLE 0 :=
  ⟨1, by simp [MaxAddDegree.ofValuation_apply, trivialValuation, Valuation.one_apply_def]⟩

theorem oneRepresentative_componentMk_ne_zero :
    trivialValuation.componentMk 0 oneRepresentative ≠ 0 := by
  rw [ne_eq, MaxAddDegree.componentMk_eq_zero_iff]
  simp [MaxAddDegree.ofValuation_apply, oneRepresentative, trivialValuation,
    Valuation.one_apply_def]

/-- The representative-level addition formula printed in LM24, Definition 4.2.4 at grade zero. -/
def printedRepresentativeAdd
    (x y : trivialValuation.filtrationLE 0) : trivialValuation.Component 0 :=
  if trivialValuation ((x : ℚ) + (y : ℚ)) = trivialValuation x then
    trivialValuation.componentMk 0 (x + y)
  else
    0

/-- The addition formula printed in LM24, Definition 4.2.4 is not commutative. -/
theorem printedRepresentativeAdd_not_commutative :
    printedRepresentativeAdd 0 oneRepresentative ≠
      printedRepresentativeAdd oneRepresentative 0 := by
  have hzeroOne :
      trivialValuation
          (((0 : trivialValuation.filtrationLE 0) : ℚ) + (oneRepresentative : ℚ)) ≠
        trivialValuation ((0 : trivialValuation.filtrationLE 0) : ℚ) := by
    simp [MaxAddDegree.ofValuation_apply, oneRepresentative, trivialValuation,
      Valuation.one_apply_def]
  have honeZero :
      trivialValuation
          ((oneRepresentative : ℚ) + ((0 : trivialValuation.filtrationLE 0) : ℚ)) =
        trivialValuation oneRepresentative := by
    simp
  rw [printedRepresentativeAdd, ite_eq_right hzeroOne, printedRepresentativeAdd, ite_eq_left honeZero]
  simp only [add_zero]
  exact oneRepresentative_componentMk_ne_zero.symm

theorem trivialValuation_isSeparated : trivialValuation.IsSeparated := by
  rw [MaxAddDegree.isSeparated_iff]
  intro x
  by_cases hx : x = 0
  · simp [MaxAddDegree.ofValuation_apply, trivialValuation, Valuation.one_apply_def, hx]
  · simp [MaxAddDegree.ofValuation_apply, trivialValuation, Valuation.one_apply_def, hx]

def twoRepresentative : trivialValuation.filtrationLE 0 :=
  ⟨2, by simp [MaxAddDegree.ofValuation_apply, trivialValuation, Valuation.one_apply_def]⟩

def threeRepresentative : trivialValuation.filtrationLE 0 :=
  ⟨3, by simp [MaxAddDegree.ofValuation_apply, trivialValuation, Valuation.one_apply_def]⟩

def sixRepresentative : trivialValuation.filtrationLE 0 :=
  ⟨6, by simp [MaxAddDegree.ofValuation_apply, trivialValuation, Valuation.one_apply_def]⟩

/-- Homogeneous multiplication computes `2 * 3 = 6` in the grade-zero component. -/
theorem trivialValuation_two_mul_three :
    trivialValuation.homogeneousMk 0 twoRepresentative *
        trivialValuation.homogeneousMk 0 threeRepresentative =
      trivialValuation.homogeneousMk 0 sixRepresentative := by
  rw [MaxAddDegree.homogeneousMk_mul]
  apply congrArg (trivialValuation.homogeneousMk 0)
  apply Subtype.ext
  norm_num [twoRepresentative, threeRepresentative, sixRepresentative]

end Tests
