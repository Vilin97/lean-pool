/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure

/-!
# Relative algebraic closure

This module packages the assertion that a field is relatively algebraically closed in a field
extension. The elementwise definition is convenient in theorem statements, while the
characteristic theorem identifies it with Mathlib's relative algebraic closure.
-/

universe u v

namespace Algebra

public noncomputable section

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

/-- The field `F` is relatively algebraically closed in `E` when every element of `E` algebraic
over `F` belongs to the range of the scalar embedding. -/
def IsRelativelyAlgebraicallyClosed : Prop :=
  ∀ x : E, IsAlgebraic F x → x ∈ (algebraMap F E).range

theorem isRelativelyAlgebraicallyClosed_iff :
    IsRelativelyAlgebraicallyClosed F E ↔
      ∀ x : E, IsAlgebraic F x →
        ∃ k : F, algebraMap F E k = x :=
  Iff.rfl

theorem isRelativelyAlgebraicallyClosed_iff_algebraicClosure_eq_bot :
    IsRelativelyAlgebraicallyClosed F E ↔
      algebraicClosure F E = ⊥ := by
  constructor
  · intro h
    ext x
    rw [mem_algebraicClosure_iff, IntermediateField.mem_bot]
    constructor
    · exact h x
    · rintro ⟨k, rfl⟩
      exact isAlgebraic_algebraMap k
  · intro h x hx
    have hx' : x ∈ algebraicClosure F E :=
      mem_algebraicClosure_iff.mpr hx
    rw [h, IntermediateField.mem_bot] at hx'
    exact hx'

/-- A field is relatively algebraically closed in an extension if every algebraic element has
minimal polynomial of degree at most one. -/
theorem isRelativelyAlgebraicallyClosed_of_minpoly_natDegree_le_one
    (hlinear : ∀ x : E, IsAlgebraic F x →
      (minpoly F x).natDegree ≤ 1) :
    IsRelativelyAlgebraicallyClosed F E := by
  rw [isRelativelyAlgebraicallyClosed_iff]
  intro x hx
  apply minpoly.natDegree_eq_one_iff.mp
  apply le_antisymm (hlinear x hx)
  exact minpoly.natDegree_pos (isAlgebraic_iff_isIntegral.mp hx)

end

end Algebra
