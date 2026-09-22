/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldCorrespondence
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
/-!
# Ordinary topology in the finite abelian class-field correspondence

The ordinary norm subgroup attached to a finite abelian subextension is
the genuine determinant-norm range on its canonical actual fixed fields.
Consequently it is open and closed in the ordinary idele-class topology
and has finite index.

The actual fixed fields are exposed below through named carriers with
canonical instances.  This keeps the public topology statements free of
local-instance towers.  The selected class field of a closed finite-index
subgroup, together with its norm-range and degree-index theorems, is provided
by `ClosedFiniteIndexClassField`.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open Reciprocity

open scoped Classical in
/-- Use the same rational algebra structure as the ordinary correspondence
when constructing all named fixed-field carriers below. -/
noncomputable local instance
    finiteAbelianClassFieldCorrespondenceTopologySeparableClosureAlgebra :
    Algebra ℚ (SeparableClosure ℚ) :=
  rationalSeparableClosureAlgebra

attribute [local instance] finiteAbelianClassFieldCorrespondenceTopologySeparableClosureAlgebra

open scoped Classical in
/-- The actual fixed-field base represented by a finite abstract field. -/
abbrev ordinaryIdeleClassNormBase
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) : Type :=
  abstractFixedField ℚ (SeparableClosure ℚ) K.field

open scoped Classical in
/-- The actual relative fixed field represented by a finite abelian
subextension. -/
abbrev ordinaryIdeleClassNormExtension
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) : Type :=
  abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below

open scoped Classical in
noncomputable instance ordinaryIdeleClassNormBaseFiniteDimensional
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    FiniteDimensional ℚ (ordinaryIdeleClassNormBase K) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K.field K.finite

open scoped Classical in
noncomputable instance ordinaryIdeleClassNormExtensionFiniteDimensional
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    FiniteDimensional
      (ordinaryIdeleClassNormBase K)
      (ordinaryIdeleClassNormExtension K L) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    K.field L.field L.below K.finite L.finite

open scoped Classical in
noncomputable instance ordinaryIdeleClassNormScalarTower
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    IsScalarTower ℚ
      (ordinaryIdeleClassNormBase K)
      (ordinaryIdeleClassNormExtension K L) :=
  IsScalarTower.of_algebraMap_eq' rfl

open scoped Classical in
noncomputable instance ordinaryIdeleClassNormExtensionAbsoluteFiniteDimensional
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    FiniteDimensional ℚ
      (ordinaryIdeleClassNormExtension K L) :=
  FiniteDimensional.trans ℚ
    (ordinaryIdeleClassNormBase K)
    (ordinaryIdeleClassNormExtension K L)

open scoped Classical in
noncomputable instance ordinaryIdeleClassNormBaseNumberField
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    NumberField (ordinaryIdeleClassNormBase K) :=
  NumberField.of_module_finite ℚ (ordinaryIdeleClassNormBase K)

open scoped Classical in
noncomputable instance ordinaryIdeleClassNormExtensionNumberField
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    NumberField (ordinaryIdeleClassNormExtension K L) :=
  NumberField.of_module_finite ℚ
    (ordinaryIdeleClassNormExtension K L)

open scoped Classical in
noncomputable instance ordinaryIdeleClassNormExtensionIsAbelianGalois
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    IsAbelianGalois
      (ordinaryIdeleClassNormBase K)
      (ordinaryIdeleClassNormExtension K L) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois L

open scoped Classical in
/-- The represented ordinary norm subgroup is the determinant-norm range on
the named actual fixed fields. -/
theorem ordinaryIdeleClassNormSubgroup_eq_namedNormRange
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    ordinaryIdeleClassNormSubgroup K L =
      (_root_.ideleClassNorm
        (ordinaryIdeleClassNormBase K)
        (ordinaryIdeleClassNormExtension K L)).range.toAddSubgroup := by
  simpa only [ordinaryIdeleClassNormBase,
    ordinaryIdeleClassNormExtension] using
    (ordinaryIdeleClassNormSubgroup_eq_actualNormRange K L)

open scoped Classical in
/-- The ordinary norm subgroup represented by a finite abelian
subextension is open in the natural topology of the idele class group of
the canonical actual fixed field. -/
theorem ordinaryIdeleClassNormSubgroup_isOpen
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    IsOpen
      (ordinaryIdeleClassNormSubgroup K L :
        Set
          (Additive
            (IdeleClassGroup
              (ordinaryIdeleClassNormBase K)))) := by
  rw [ordinaryIdeleClassNormSubgroup_eq_namedNormRange K L]
  exact ideleClassNorm_range_isOpen
    (K := ordinaryIdeleClassNormBase K)
    (L := ordinaryIdeleClassNormExtension K L)

open scoped Classical in
/-- The ordinary norm subgroup represented by a finite abelian
subextension is closed in the natural idele-class topology. -/
theorem ordinaryIdeleClassNormSubgroup_isClosed
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    IsClosed
      (ordinaryIdeleClassNormSubgroup K L :
        Set
          (Additive
            (IdeleClassGroup
              (ordinaryIdeleClassNormBase K)))) := by
  rw [ordinaryIdeleClassNormSubgroup_eq_namedNormRange K L]
  exact ideleClassNorm_range_isClosed
    (K := ordinaryIdeleClassNormBase K)
    (L := ordinaryIdeleClassNormExtension K L)

open scoped Classical in
/-- The ordinary norm subgroup represented by a finite abelian
subextension has finite index. -/
theorem ordinaryIdeleClassNormSubgroup_finiteIndex
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    (ordinaryIdeleClassNormSubgroup K L).FiniteIndex := by
  rw [ordinaryIdeleClassNormSubgroup_eq_namedNormRange K L]
  exact
    (Subgroup.finiteIndex_toAddSubgroup_iff
      (H := (_root_.ideleClassNorm
        (ordinaryIdeleClassNormBase K)
        (ordinaryIdeleClassNormExtension K L)).range)).2
      (ideleClassNorm_rangeFiniteIndex
        (K := ordinaryIdeleClassNormBase K)
        (L := ordinaryIdeleClassNormExtension K L))

open scoped Classical in
/-- The index of the ordinary norm subgroup represented by a finite
abelian subextension is the degree of its actual relative fixed-field
extension. -/
theorem ordinaryIdeleClassNormSubgroup_index_eq_finrank
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    (ordinaryIdeleClassNormSubgroup K L).index =
      Module.finrank
        (ordinaryIdeleClassNormBase K)
        (ordinaryIdeleClassNormExtension K L) := by
  rw [ordinaryIdeleClassNormSubgroup_eq_namedNormRange K L]
  exact
    (Subgroup.index_toAddSubgroup
      (H := (_root_.ideleClassNorm
        (ordinaryIdeleClassNormBase K)
        (ordinaryIdeleClassNormExtension K L)).range)).trans
      (ideleClassNorm_index_eq_finrank_abelian
        (ordinaryIdeleClassNormBase K)
        (ordinaryIdeleClassNormExtension K L))

end GlobalClassFields
end GlobalClassFieldTheory
