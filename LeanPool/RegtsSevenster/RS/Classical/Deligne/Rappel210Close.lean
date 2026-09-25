/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.Rappel210Bridge
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.Rappel210Reduce

/-!
# The local splitting statement, up to unit nonvanishing

The assembly of the local splitting statement: the splitting
algebra of the dualised unit-form point, with its class and the
restriction identity, feeds the reduction.  What remains at each
consumer is the nonvanishing of the algebra's unit, which over an
ind-category follows from the stage units through the filtered
criterion.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The splitting algebra of a short exact sequence: the local
splitting chain of the dualised unit-form point. -/
noncomputable def rappel210Algebra
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [CategoryTheory.Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [HasColimitsOfShape SmallNat.{v} D] (S : ShortComplex D)
    [HasRightDual (S.X₃ : D)] [HasRightDual (unitFormMid S : D)] : D :=
  splitAlgebra ((unitFormMid S)ᘁ) (unitFormPoint S)

/-- **The local splitting statement holds once the unit of the
splitting algebra survives**: the class of the dual middle object
restricts on the point to the unit, so the reduction applies. -/
theorem rappel210_of_unit_nonzero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] [Abelian D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [CategoryTheory.Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ Z : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight Z)]
    (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
    [HasRightDual (unitFormMid S : D)]
    (hS : S.ShortExact)
    (hnz : splitAlgebraUnit ((unitFormMid S)ᘁ)
      (unitFormPoint S) ≠ 0) :
    Rappel210Statement S hS := by
  let : MonObj (rappel210Algebra S) :=
    splitAlgebraMonObj (((unitFormMid S)ᘁ : D))
      (unitFormPoint S)
  have : IsCommMonObj (rappel210Algebra S) :=
    splitAlgebra_isCommMonObj (((unitFormMid S)ᘁ : D))
      (unitFormPoint S)
  exact rappel210_of_class S hS (rappel210Algebra S) hnz
    (splitCls (((unitFormMid S)ᘁ : D)) (unitFormPoint S))
    (splitCls_point (((unitFormMid S)ᘁ : D))
      (unitFormPoint S))

end RS
