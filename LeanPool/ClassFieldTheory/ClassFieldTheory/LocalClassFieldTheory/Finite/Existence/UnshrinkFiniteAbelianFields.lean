/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkFiniteAbelianFields
/-!
# Returning finite abelian intermediate fields from the small base

The converse to the small-base transport: an intermediate field over
`Shrink K` in the original separable closure remains finite abelian over `K`.
-/

@[expose] public section

noncomputable
section

namespace LocalFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The same underlying field after undoing the small base change. -/
def unshrinkIntermediateFieldRingEquiv :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : Algebra (Shrink.{0} K) (SeparableClosure K) :=
      shrinkSeparableClosureAlgebra K
    (F : IntermediateField (Shrink.{0} K) (SeparableClosure K)) →
      F ≃+* unshrinkIntermediateField K F := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  intro F
  exact RingEquiv.refl F

/-- The inverse intermediate-field equivalence commutes with the base-field
embeddings. -/
theorem unshrinkIntermediateFieldRingEquiv_commutes :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : Algebra (Shrink.{0} K) (SeparableClosure K) :=
      shrinkSeparableClosureAlgebra K
    ∀ F : IntermediateField (Shrink.{0} K) (SeparableClosure K),
      (algebraMap K (unshrinkIntermediateField K F)).comp
          (Shrink.ringEquiv K).toRingHom =
        (unshrinkIntermediateFieldRingEquiv K F).toRingHom.comp
          (algebraMap (Shrink.{0} K) F) := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  intro F
  ext x
  have hbase :
      algebraMap K (SeparableClosure K) (Shrink.ringEquiv K x) =
        algebraMap (Shrink.{0} K) (SeparableClosure K) x := by
    rfl
  have hfieldK :
      ((algebraMap K (unshrinkIntermediateField K F)
        (Shrink.ringEquiv K x) : unshrinkIntermediateField K F) :
          SeparableClosure K) =
        algebraMap K (SeparableClosure K) (Shrink.ringEquiv K x) :=
    IntermediateField.coe_algebraMap_apply (unshrinkIntermediateField K F) _
  have hfieldS :
      algebraMap (Shrink.{0} K) (SeparableClosure K) x =
        ((algebraMap (Shrink.{0} K) F x : F) : SeparableClosure K) :=
    (IntermediateField.coe_algebraMap_apply F x).symm
  exact congrArg (fun y : SeparableClosure K => (y : AlgebraicClosure K))
    (hfieldK.trans (hbase.trans hfieldS))

/-- Finite-dimensionality is preserved when returning to `K`. -/
theorem unshrinkIntermediateField_finiteDimensional :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : Algebra (Shrink.{0} K) (SeparableClosure K) :=
      shrinkSeparableClosureAlgebra K
    ∀ F : IntermediateField (Shrink.{0} K) (SeparableClosure K),
      FiniteDimensional (Shrink.{0} K) F →
        FiniteDimensional K (unshrinkIntermediateField K F) := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  intro F hF
  let : FiniteDimensional (Shrink.{0} K) F := hF
  exact Module.Finite.of_equiv_equiv
    (Shrink.ringEquiv K) (unshrinkIntermediateFieldRingEquiv K F)
    (unshrinkIntermediateFieldRingEquiv_commutes K F)

/-- The abelian Galois property is preserved when returning to `K`. -/
theorem unshrinkIntermediateField_isAbelianGalois :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : Algebra (Shrink.{0} K) (SeparableClosure K) :=
      shrinkSeparableClosureAlgebra K
    ∀ F : IntermediateField (Shrink.{0} K) (SeparableClosure K),
      IsAbelianGalois (Shrink.{0} K) F →
        IsAbelianGalois K (unshrinkIntermediateField K F) := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  intro F hF
  let : IsAbelianGalois (Shrink.{0} K) F := hF
  exact ClassFieldTheory.isAbelianGalois_of_equiv_equiv
    (Shrink.ringEquiv K) (unshrinkIntermediateFieldRingEquiv K F)
    (unshrinkIntermediateFieldRingEquiv_commutes K F)

end LocalFieldTheory
