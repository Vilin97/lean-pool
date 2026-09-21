/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkIntermediateFields
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
import LeanPool.ClassFieldTheory.ClassFieldTheory.Algebra.AbelianGaloisEquiv
/-!
# Finite abelian intermediate fields under a small change of base

The intermediate field itself is unchanged as a subfield of the original
separable closure.  Its finite-dimensional and abelian Galois properties are
transported along the base-field equivalence.
-/

noncomputable section

namespace LocalFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The same underlying intermediate field, now considered over `Shrink K`. -/
def shrinkIntermediateFieldRingEquiv
    (E : IntermediateField K (SeparableClosure K)) :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : Algebra (Shrink.{0} K) (SeparableClosure K) :=
      shrinkSeparableClosureAlgebra K
    E ≃+* shrinkIntermediateField K E := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  exact RingEquiv.refl E

/-- The base-field and intermediate-field equivalences commute with their
algebra embeddings. -/
theorem shrinkIntermediateFieldRingEquiv_commutes
    (E : IntermediateField K (SeparableClosure K)) :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : Algebra (Shrink.{0} K) (SeparableClosure K) :=
      shrinkSeparableClosureAlgebra K
    (algebraMap (Shrink.{0} K) (shrinkIntermediateField K E)).comp
        (Shrink.ringEquiv K).symm.toRingHom =
      (shrinkIntermediateFieldRingEquiv K E).toRingHom.comp
        (algebraMap K E) := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  ext x
  have hAlg (a : Shrink.{0} K) :
      algebraMap (Shrink.{0} K) (SeparableClosure K) a =
        algebraMap K (SeparableClosure K) (Shrink.ringEquiv K a) := by
    rfl
  have hbase :
      algebraMap (Shrink.{0} K) (SeparableClosure K)
          ((Shrink.ringEquiv K).symm x) =
        algebraMap K (SeparableClosure K) x := by
    rw [hAlg]
    simp
  have hfield :
      algebraMap K (SeparableClosure K) x =
        ((algebraMap K E x : E) : SeparableClosure K) :=
    (IntermediateField.coe_algebraMap_apply E x).symm
  exact congrArg (fun y : SeparableClosure K => (y : AlgebraicClosure K))
    (hbase.trans hfield)

/-- Finite-dimensionality is invariant under the base-field equivalence. -/
theorem shrinkIntermediateField_finiteDimensional
    (E : ClassFieldTheory.FiniteAbelianLocalExtension K) :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : Algebra (Shrink.{0} K) (SeparableClosure K) :=
      shrinkSeparableClosureAlgebra K
    FiniteDimensional (Shrink.{0} K) (shrinkIntermediateField K E.1) := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  let : FiniteDimensional K E.1 := E.2.1
  exact Module.Finite.of_equiv_equiv
    (Shrink.ringEquiv K).symm (shrinkIntermediateFieldRingEquiv K E.1)
    (shrinkIntermediateFieldRingEquiv_commutes K E.1)

/-- The abelian Galois property is invariant under the base-field
equivalence. -/
theorem shrinkIntermediateField_isAbelianGalois
    (E : ClassFieldTheory.FiniteAbelianLocalExtension K) :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : Algebra (Shrink.{0} K) (SeparableClosure K) :=
      shrinkSeparableClosureAlgebra K
    IsAbelianGalois (Shrink.{0} K) (shrinkIntermediateField K E.1) := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  let : IsAbelianGalois K E.1 := E.2.2
  exact ClassFieldTheory.isAbelianGalois_of_equiv_equiv
    (Shrink.ringEquiv K).symm (shrinkIntermediateFieldRingEquiv K E.1)
    (shrinkIntermediateFieldRingEquiv_commutes K E.1)

end LocalFieldTheory
