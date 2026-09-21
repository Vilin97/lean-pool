/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport
import Mathlib.FieldTheory.IsSepClosed
/-!
# Separable closures over the small local-field representative

The existing separable closure of `K` is also a separable closure of
`Shrink.{0} K` after transporting the base-field embedding.  This gives a
compatible equivalence with Mathlib's chosen separable closure of `Shrink K`.
-/

noncomputable section

namespace LocalFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The original separable closure, regarded as an extension of the small
representative of its base field. -/
@[reducible]
noncomputable def shrinkSeparableClosureAlgebra :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    Algebra (Shrink.{0} K) (SeparableClosure K) := by
  letI : Small.{0} K := nonarchimedeanLocalField_small K
  exact ((algebraMap K (SeparableClosure K)).comp
    (Shrink.ringEquiv K).toRingHom).toAlgebra

/-- `SeparableClosure K` remains a separable closure after changing the base
field to its small representative. -/
theorem shrinkSeparableClosure_isSepClosure :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : Algebra (Shrink.{0} K) (SeparableClosure K) :=
      shrinkSeparableClosureAlgebra K
    IsSepClosure (Shrink.{0} K) (SeparableClosure K) := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  have hAlg (a : Shrink.{0} K) :
      algebraMap (Shrink.{0} K) (SeparableClosure K) a =
        algebraMap K (SeparableClosure K) (Shrink.ringEquiv K a) := by
    rfl
  have hcomp :
      (algebraMap (Shrink.{0} K) (SeparableClosure K)).comp
        (Shrink.ringEquiv K).symm.toRingHom =
      (RingEquiv.refl (SeparableClosure K)).toRingHom.comp
        (algebraMap K (SeparableClosure K)) := by
    ext x
    simp [hAlg]
  exact ⟨IsSepClosure.sep_closed K,
    Algebra.IsSeparable.of_equiv_equiv
      (Shrink.ringEquiv K).symm
      (RingEquiv.refl (SeparableClosure K)) hcomp⟩

/-- An equivalence between the chosen separable closure of the small base and
the original chosen separable closure, both viewed over the small base. -/
noncomputable def shrinkSeparableClosureEquiv :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : Algebra (Shrink.{0} K) (SeparableClosure K) :=
      shrinkSeparableClosureAlgebra K
    SeparableClosure (Shrink.{0} K) ≃ₐ[Shrink.{0} K]
      SeparableClosure K := by
  letI : Small.{0} K := nonarchimedeanLocalField_small K
  letI : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  letI : IsSepClosure (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosure_isSepClosure K
  exact IsSepClosure.equiv (Shrink.{0} K)
    (SeparableClosure (Shrink.{0} K)) (SeparableClosure K)

end LocalFieldTheory
