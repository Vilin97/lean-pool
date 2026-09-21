/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.TrailingGrade
public import Mathlib.Algebra.MonoidAlgebra.ToDirectSum

import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# Factors of a constant in an additive monoid algebra

Suppose the grading monoid is linearly ordered, cancellative, and has zero as its largest element.
If a nonzero additive-monoid-algebra element has trailing grade zero, it is supported only at
zero. Consequently, over a coefficient semiring without zero divisors, both nonzero factors of a
monomial supported at zero are themselves supported at zero.
-/

open scoped DirectSum

universe u v

namespace AddMonoidAlgebra

public noncomputable section

variable {R : Type u} {M : Type v}
  [Semiring R] [LinearOrder M] [AddCommMonoid M] [OrderTop M]

private abbrev component (_ : M) := R

/-- An element with trailing grade zero is supported only at zero when zero is the largest
grade. -/
theorem exists_eq_single_zero_of_trailingGrade_eq_zero
    (hzeroTop : (⊤ : M) = 0) {f : AddMonoidAlgebra R M}
    (htrail : DirectSum.trailingGrade (fun _ : M ↦ R) f.toDirectSum =
      (0 : WithTop M)) :
    ∃ r : R, f = AddMonoidAlgebra.single 0 r := by
  classical
  refine ⟨f.toDirectSum 0, ?_⟩
  have hdirect : f.toDirectSum = DirectSum.of component 0 (f.toDirectSum 0) := by
    apply DirectSum.ext
    intro i
    by_cases hi : i = 0
    · subst i
      simp
    · have hfi : f.toDirectSum i = 0 := by
        by_contra hfi
        have hzeroLe : (0 : M) ≤ i :=
          (DirectSum.trailingGrade_eq_coe_iff component f.toDirectSum 0).mp htrail |>.2 i hfi
        have hiZero : i ≤ 0 := by
          rw [← hzeroTop]
          exact le_top
        exact hi (le_antisymm hiZero hzeroLe)
      rw [hfi, DirectSum.of_eq_of_ne 0 i _ hi]
  have h := congrArg DirectSum.toAddMonoidAlgebra hdirect
  simpa using h

variable [NoZeroDivisors R] [IsOrderedCancelAddMonoid M]

/-- If a product is supported only at zero, each nonzero factor is supported only at zero. -/
theorem exists_eq_single_zero_of_mul_eq_single_zero
    (hzeroTop : (⊤ : M) = 0) {f g : AddMonoidAlgebra R M} {r : R}
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f * g = AddMonoidAlgebra.single 0 r) :
    ∃ a b : R,
      f = AddMonoidAlgebra.single 0 a ∧
        g = AddMonoidAlgebra.single 0 b := by
  classical
  have hr : r ≠ 0 := by
    intro hr
    subst r
    have hzero : f * g = 0 := hfg.trans (AddMonoidAlgebra.single_zero 0)
    exact (mul_eq_zero.mp hzero).elim hf hg
  have hfDirect : f.toDirectSum ≠ 0 := by
    intro hzero
    apply hf
    have := congrArg DirectSum.toAddMonoidAlgebra hzero
    simpa using this
  have hgDirect : g.toDirectSum ≠ 0 := by
    intro hzero
    apply hg
    have := congrArg DirectSum.toAddMonoidAlgebra hzero
    simpa using this
  obtain ⟨m, hm, _⟩ :=
    DirectSum.exists_grade_eq_trailingGrade component hfDirect
  obtain ⟨n, hn, _⟩ :=
    DirectSum.exists_grade_eq_trailingGrade component hgDirect
  have hfgDirect : f.toDirectSum * g.toDirectSum =
      DirectSum.of component 0 r := by
    simpa using congrArg AddMonoidAlgebra.toDirectSum hfg
  have hsumTop : ((m + n : M) : WithTop M) = (0 : M) := by
    calc
      ((m + n : M) : WithTop M) =
          DirectSum.trailingGrade component f.toDirectSum +
            DirectSum.trailingGrade component g.toDirectSum := by
        rw [hm, hn, WithTop.coe_add]
      _ = DirectSum.trailingGrade component
            (f.toDirectSum * g.toDirectSum) :=
        (DirectSum.trailingGrade_mul component
          (fun a b ha hb ↦ mul_ne_zero ha hb) f.toDirectSum g.toDirectSum).symm
      _ = DirectSum.trailingGrade component (DirectSum.of component 0 r) := by
        rw [hfgDirect]
      _ = (0 : M) := DirectSum.trailingGrade_of component hr
  have hsum : m + n = 0 := WithTop.coe_injective hsumTop
  have hmLe : m ≤ 0 := by
    rw [← hzeroTop]
    exact le_top
  have hnLe : n ≤ 0 := by
    rw [← hzeroTop]
    exact le_top
  have hzeroLeM : 0 ≤ m := by
    calc
      0 = m + n := hsum.symm
      _ ≤ m + 0 := add_le_add_right hnLe m
      _ = m := add_zero m
  have hzeroLeN : 0 ≤ n := by
    calc
      0 = m + n := hsum.symm
      _ ≤ 0 + n := add_le_add_left hmLe n
      _ = n := zero_add n
  have hmZero : m = 0 := le_antisymm hmLe hzeroLeM
  have hnZero : n = 0 := le_antisymm hnLe hzeroLeN
  obtain ⟨a, ha⟩ := exists_eq_single_zero_of_trailingGrade_eq_zero
    hzeroTop (hm.trans (congrArg WithTop.some hmZero))
  obtain ⟨b, hb⟩ := exists_eq_single_zero_of_trailingGrade_eq_zero
    hzeroTop (hn.trans (congrArg WithTop.some hnZero))
  exact ⟨a, b, ha, hb⟩

end

end AddMonoidAlgebra
