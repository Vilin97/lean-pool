/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkSeparableClosure
public import Mathlib.FieldTheory.IntermediateField.Basic
/-!
# Intermediate fields under a small change of base field

The base-field equivalence `Shrink K ≃+* K` does not change the subfields of
the original separable closure.  This file records that fact as an order
isomorphism, with the actual underlying subfields unchanged.
-/

@[expose] public section

noncomputable
section

namespace LocalFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- An intermediate field of the original separable closure, viewed over
the small representative of the base field. -/
def shrinkIntermediateField
    (E : IntermediateField K (SeparableClosure K)) :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : Algebra (Shrink.{0} K) (SeparableClosure K) :=
      shrinkSeparableClosureAlgebra K
    IntermediateField (Shrink.{0} K) (SeparableClosure K) := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  refine E.toSubfield.toIntermediateField ?_
  intro x
  change (algebraMap K (SeparableClosure K)) (Shrink.ringEquiv K x) ∈ E
  exact E.algebraMap_mem _

/-- Undo the base-field change on an intermediate field. -/
def unshrinkIntermediateField :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : Algebra (Shrink.{0} K) (SeparableClosure K) :=
      shrinkSeparableClosureAlgebra K
    IntermediateField (Shrink.{0} K) (SeparableClosure K) →
      IntermediateField K (SeparableClosure K) := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  intro F
  refine F.toSubfield.toIntermediateField ?_
  intro x
  have hx := F.algebraMap_mem ((Shrink.ringEquiv K).symm x)
  change (algebraMap K (SeparableClosure K))
    (Shrink.ringEquiv K ((Shrink.ringEquiv K).symm x)) ∈ F at hx
  simpa using hx

/-- Re-expressing an original intermediate field over `Shrink K` and back
returns the same field. -/
theorem unshrink_shrinkIntermediateField
    (E : IntermediateField K (SeparableClosure K)) :
    unshrinkIntermediateField K (shrinkIntermediateField K E) = E := by
  apply SetLike.coe_injective
  rfl

/-- Re-expressing a small-base intermediate field over `K` and back returns
the same field. -/
theorem shrink_unshrinkIntermediateField :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : Algebra (Shrink.{0} K) (SeparableClosure K) :=
      shrinkSeparableClosureAlgebra K
    ∀ F : IntermediateField (Shrink.{0} K) (SeparableClosure K),
      shrinkIntermediateField K (unshrinkIntermediateField K F) = F := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  intro F
  apply SetLike.coe_injective
  rfl

/-- Intermediate fields of the two equivalent base-field presentations are
order-isomorphic. -/
def shrinkIntermediateFieldOrderIso :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : Algebra (Shrink.{0} K) (SeparableClosure K) :=
      shrinkSeparableClosureAlgebra K
    IntermediateField K (SeparableClosure K) ≃o
      IntermediateField (Shrink.{0} K) (SeparableClosure K) := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  exact {
    toEquiv := {
      toFun := shrinkIntermediateField K
      invFun := unshrinkIntermediateField K
      left_inv := unshrink_shrinkIntermediateField K
      right_inv := shrink_unshrinkIntermediateField K
    }
    map_rel_iff' := by intro E F; rfl
  }

end LocalFieldTheory
