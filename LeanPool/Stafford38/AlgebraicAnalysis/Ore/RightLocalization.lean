/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Algebra.Group.Units.Opposite

/-!
# Right Ore localization

The opposite-ring presentation of a right Ore localization and its
right-denominator clearing API. Extracted from Stafford38 commit
c8a513d553b24c7c08da82f496c44dbbaeb1f2fc.
-/

namespace AlgebraicAnalysis.OreRightLocalization

/-- The copy of `S` in the opposite ring. -/
def oppositeSubmonoid {R : Type u} [Monoid R] (S : Submonoid R) :
    Submonoid Rᵐᵒᵖ where
  carrier := {x | x.unop ∈ S}
  one_mem' := S.one_mem
  mul_mem' := by
    intro a b ha hb
    exact S.mul_mem hb ha

/-- The right Ore localization of `R`, implemented as the opposite of
Mathlib's left Ore localization of `Rᵐᵒᵖ`. -/
abbrev RightOreLocalization (R : Type u) [Ring R] (S : Submonoid R)
    [OreLocalization.OreSet (oppositeSubmonoid S)] :=
  (OreLocalization (oppositeSubmonoid S) (Rᵐᵒᵖ))ᵐᵒᵖ

/-- The numerator map into the right Ore localization. -/
def rightNumeratorRingHom
    {R : Type u} [Ring R] {S : Submonoid R}
    [OreLocalization.OreSet (oppositeSubmonoid S)] :
    R →+* RightOreLocalization R S where
  toFun r := MulOpposite.op
    (OreLocalization.numeratorRingHom (S := oppositeSubmonoid S) (MulOpposite.op r))
  map_one' := by
    apply MulOpposite.unop_injective
    exact RingHom.map_one _
  map_zero' := by
    apply MulOpposite.unop_injective
    exact RingHom.map_zero _
  map_add' a b := by
    apply MulOpposite.unop_injective
    exact RingHom.map_add _ _ _
  map_mul' a b := by
    apply MulOpposite.unop_injective
    exact RingHom.map_mul _ (MulOpposite.op b) (MulOpposite.op a)

/-- Every element of a right Ore localization has a right denominator in `S`
which is a unit and clears the fraction. -/
theorem rightOre_clear
    {R : Type u} [Ring R] {S : Submonoid R}
    [OreLocalization.OreSet (oppositeSubmonoid S)]
    (q : RightOreLocalization R S) :
    ∃ a s : R, s ∈ S ∧ IsUnit (rightNumeratorRingHom (S := S) s) ∧
      q * rightNumeratorRingHom (S := S) s = rightNumeratorRingHom (S := S) a := by
  generalize hx : q.unop = x
  induction x using OreLocalization.ind with
  | _ a s =>
      refine ⟨a.unop, s.val.unop, s.property, ?_, ?_⟩
      · exact isUnit_op.mpr (OreLocalization.numerator_isUnit
          (R := Rᵐᵒᵖ) (S := oppositeSubmonoid S) s)
      · apply MulOpposite.unop_injective
        rw [show q = MulOpposite.op (a /ₒ s) by
          apply MulOpposite.unop_injective
          exact hx]
        exact OreLocalization.mul_cancel (R := Rᵐᵒᵖ)
          (S := oppositeSubmonoid S) (r := a) (s := s) (t := 1)


end AlgebraicAnalysis.OreRightLocalization
