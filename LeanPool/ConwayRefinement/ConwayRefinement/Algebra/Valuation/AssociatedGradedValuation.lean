/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.LeadingGrade
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.RV
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeAssociatedGradedDomain

/-!
# The valuation on an associated graded ring

The largest nonzero grade of an associated-graded element is a max-additive degree on
`ν.AssociatedGraded` for every max-additive degree `ν`: products of homogeneous components land
in the sum grade, so the leading grade is submultiplicative. It is separated because direct-sum
support is finite, independently of whether `ν` is separated. For a multiplicative `ν`,
multiplication of nonzero homogeneous classes is nonzero, and the leading grade is multiplicative.

This is the valuation constructed in LM24, Definition 4.3.4 and Proposition 4.3.5. The degree of
an initial form is the degree of its representative, so iteration retains the original
homogeneous data.
-/

universe u v

public noncomputable section

open scoped DirectSum

namespace MaxAddDegree

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
  [LinearOrder M] [IsOrderedCancelAddMonoid M]

variable (ν : MaxAddDegree R M)

/-- The largest nonzero grade of an associated-graded element. -/
def associatedGradedValue (x : ν.AssociatedGraded) : WithBot M :=
  DirectSum.leadingGrade ν.Component x

@[simp]
theorem associatedGradedValue_zero : ν.associatedGradedValue 0 = ⊥ :=
  DirectSum.leadingGrade_zero ν.Component

@[simp]
theorem associatedGradedValue_eq_bot_iff (x : ν.AssociatedGraded) :
    ν.associatedGradedValue x = ⊥ ↔ x = 0 :=
  DirectSum.leadingGrade_eq_bot_iff ν.Component x

omit [IsOrderedCancelAddMonoid M] in
theorem associatedGradedValue_eq_coe_iff (x : ν.AssociatedGraded) (m : M) :
    ν.associatedGradedValue x = (m : WithBot M) ↔
      x m ≠ 0 ∧ ∀ i, x i ≠ 0 → i ≤ m :=
  DirectSum.leadingGrade_eq_coe_iff ν.Component x m

theorem associatedGradedValue_add_le_max (x y : ν.AssociatedGraded) :
    ν.associatedGradedValue (x + y) ≤
      max (ν.associatedGradedValue x) (ν.associatedGradedValue y) :=
  DirectSum.leadingGrade_add_le_max ν.Component x y

omit [IsOrderedCancelAddMonoid M] in
@[simp]
theorem associatedGradedValue_neg (x : ν.AssociatedGraded) :
    ν.associatedGradedValue (-x) = ν.associatedGradedValue x :=
  DirectSum.leadingGrade_neg ν.Component x

/-- The leading grade of an initial form is the degree of its representative. -/
@[simp]
theorem associatedGradedValue_initialForm (x : R) :
    ν.associatedGradedValue (ν.initialForm x) = ν x := by
  by_cases hx : ν x = ⊥
  · rw [ν.initialForm_eq_zero_of_eq_bot hx, ν.associatedGradedValue_zero, hx]
  · have hc : ν.componentMk ((ν x).unbot hx) (ν.initialRepresentative x hx) ≠ 0 := by
      intro hzero
      apply ν.initialForm_ne_zero_of_ne_bot hx
      rw [ν.initialForm_eq_homogeneousMk_of_ne_bot hx, ν.homogeneousMk_apply, hzero,
        (DirectSum.of ν.Component _).map_zero]
    rw [ν.initialForm_eq_homogeneousMk_of_ne_bot hx, ν.homogeneousMk_apply,
      associatedGradedValue]
    rw [DirectSum.leadingGrade_of ν.Component hc, WithBot.coe_unbot]

/-- The leading grade of the unit is the degree of the unit: zero, unless the degree is the
degenerate one that is bottom everywhere, in which case the graded ring is trivial. -/
@[simp]
theorem associatedGradedValue_one :
    ν.associatedGradedValue 1 = ν 1 := by
  rw [← ν.initialForm_one, ν.associatedGradedValue_initialForm]

/-- The leading grade of a product is at most the sum of the leading grades: products of
homogeneous components land in the sum grade. -/
theorem associatedGradedValue_mul_le (x y : ν.AssociatedGraded) :
    ν.associatedGradedValue (x * y) ≤
      ν.associatedGradedValue x + ν.associatedGradedValue y :=
  DirectSum.leadingGrade_mul_le ν.Component x y

/-- The leading-grade degree on the associated graded ring, for LM24, Proposition 4.3.5. It is
a max-additive degree for every `ν`, and multiplicative when `ν` is. -/
def associatedGradedValuation : MaxAddDegree ν.AssociatedGraded M where
  toFun := ν.associatedGradedValue
  map_zero' := ν.associatedGradedValue_zero
  map_one_le_zero' := by
    rw [ν.associatedGradedValue_one]
    exact ν.map_one_le_zero
  map_neg' := ν.associatedGradedValue_neg
  map_add_le_max' := ν.associatedGradedValue_add_le_max
  map_mul_le_add' := ν.associatedGradedValue_mul_le

@[simp]
theorem associatedGradedValuation_apply (x : ν.AssociatedGraded) :
    ν.associatedGradedValuation x = ν.associatedGradedValue x :=
  (rfl)

@[simp]
theorem associatedGradedValue_mul [ν.IsMultiplicative] (x y : ν.AssociatedGraded) :
    ν.associatedGradedValue (x * y) =
      ν.associatedGradedValue x + ν.associatedGradedValue y :=
  DirectSum.leadingGrade_mul ν.Component (fun a b ha hb ↦ ν.componentMul_ne_zero a b ha hb) x y

/-- The leading-grade valuation of LM24, Proposition 4.3.5, is multiplicative for a multiplicative
degree. -/
instance [ν.IsMultiplicative] : ν.associatedGradedValuation.IsMultiplicative :=
  ⟨ν.associatedGradedValue_mul⟩

/-- The leading-grade valuation is separated, regardless of whether `ν` is separated. -/
theorem associatedGradedValuation_isSeparated : ν.associatedGradedValuation.IsSeparated := by
  rw [isSeparated_iff]
  intro x
  rw [ν.associatedGradedValuation_apply, ν.associatedGradedValue_eq_bot_iff]

theorem associatedGradedValuation_initialForm (x : R) :
    ν.associatedGradedValuation (ν.initialForm x) = ν x := by
  rw [ν.associatedGradedValuation_apply, ν.associatedGradedValue_initialForm]

end MaxAddDegree
