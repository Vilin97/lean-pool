/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SplitEverything
import LeanPool.RegtsSevenster.RS.Classical.Deligne.Prop21General

/-!
# The splitting algebra of the doubling

A tensor category need not contain an odd line; the ℤ/2-graded
doubling always does.  Every hypothesis passes to the doubling —
scalar unit endomorphisms, moderate length growth, finite tensor
generation, and finite length of every object — so the single
simple algebra that splits the doubling is available, together with
the complex point of its Γ-algebra.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {A : Type v}

attribute [local instance] Doubled.hasFiniteBiproducts

/-- **The splitting algebra of the doubling.**  Everything the
argument needs passes to `Doubled A`, so one simple algebra splits
every embedded object of the doubling and its Γ-algebra has a
complex point. -/
theorem exists_splitting_simple_algebra_doubled
    [SmallCategory A] [MonoidalCategory A] [SymmetricCategory A] [Abelian A]
    [RigidCategory A] [MonoidalPreadditive A] [CategoryTheory.Linear ℂ A]
    [HasFiniteBiproducts A]
    (P : SchurPackage.{v}) (P₀ : SchurPackage.{0})
    (hu : HasScalarUnit A) (X : A) (hgen : TensorGeneratedBy A X)
    (hgrow : ModerateLengthGrowth A)
    :
    letI := linearOfScalarUnit (doubledScalarUnit hu)
    letI := monoidalLinearOfScalarUnitBraided (doubledScalarUnit hu)
    letI := linearOfScalarUnit (indScalarUnit (doubledScalarUnit hu))
    letI := monoidalLinearOfScalarUnitBraided
      (indScalarUnit (doubledScalarUnit hu))
    ∃ (𝔹 : Ind (Doubled A)) (_ : MonObj 𝔹) (_ : IsCommMonObj 𝔹),
      η[𝔹] ≠ 0 ∧
      (∀ I : Subobject 𝔹, IsIdeal 𝔹 I → I = ⊥ ∨ I = ⊤) ∧
      SplitsOn doubledIndOddLine 𝔹
        (indOf : Doubled A ⥤ Ind (Doubled A)) ∧
      Nonempty (SuperPoint
        (gammaAlgebra (Ind (Doubled A)) doubledIndOddLine 𝔹)) := by
  let := linearOfScalarUnit (doubledScalarUnit hu)
  let := monoidalLinearOfScalarUnitBraided (doubledScalarUnit hu)
  let := linearOfScalarUnit (indScalarUnit (doubledScalarUnit hu))
  let := monoidalLinearOfScalarUnitBraided
    (indScalarUnit (doubledScalarUnit hu))
  exact exists_splitting_simple_algebra (doubledScalarUnit hu) P P₀
    doubledIndOddLine (Doubled.gen X)
    (tensorGeneratedBy_doubled hgen)
    (moderateLengthGrowth_doubled hgrow)
    (fun Z => exists_lengthLE_of_moderateGrowth
      (moderateLengthGrowth_doubled hgrow) Z)

end RS
