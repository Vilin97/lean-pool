/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdealClass
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.AdeleBaseChange
/-!
# Relative and ordinary idele classes

The tensor-product presentation of the ideles of a finite Galois
extension is canonically equivalent to the ordinary restricted-product
presentation.  This file descends that equivalence through principal
ideles and identifies relative class inclusion with the concrete
extension map on ordinary idele classes.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField

noncomputable
section

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- Scalar extension identifies the relative and ordinary principal
idele subgroups. -/
theorem relativeIdelePrincipalSubgroup_map_baseChange :
    (RelativeIdeleGroup.principalSubgroup K L).map
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L)).toMonoidHom =
      IdeleGroup.principalSubgroup L := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx⟩, rfl⟩
    rw [← hx]
    exact
      ⟨x,
        (relativeIdeleBaseChangeMulEquiv_principalIdele
          (K := K) (L := L) x).symm⟩
  · rintro ⟨x, rfl⟩
    refine
      ⟨RelativeIdeleGroup.principalIdele K L x,
        ⟨x, rfl⟩, ?_⟩
    exact
      relativeIdeleBaseChangeMulEquiv_principalIdele
        (K := K) (L := L) x

/-- Scalar extension identifies the relative presentation of the idele
class group with the ordinary idele class group of the extension field. -/
noncomputable def relativeIdeleClassBaseChangeMulEquiv :
    RelativeIdeleGroup.ClassGroup K L ≃*
      IdeleClassGroup L :=
  QuotientGroup.congr
    (RelativeIdeleGroup.principalSubgroup K L)
    (IdeleGroup.principalSubgroup L)
    (relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L))
    (relativeIdelePrincipalSubgroup_map_baseChange
      (K := K) (L := L))

theorem relativeIdeleClassBaseChangeMulEquiv_mk
    (z : RelativeIdeleGroup K L) :
    relativeIdeleClassBaseChangeMulEquiv
        (K := K) (L := L)
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) z) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L)
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z) :=
  rfl

/-- Under the relative-to-ordinary comparison, relative class inclusion
is the concrete extension map on ordinary idele classes. -/
@[simp]
theorem relativeIdeleClassBaseChangeMulEquiv_classInclusion
    (c : IdeleClassGroup K) :
    relativeIdeleClassBaseChangeMulEquiv
        (K := K) (L := L)
        (RelativeIdeleGroup.classInclusion K L c) =
      ideleClassExtension K L c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  rfl

/-- Homomorphism form of the compatibility between relative class
inclusion and ordinary idele-class extension. -/
theorem relativeIdeleClassBaseChange_comp_classInclusion :
    (relativeIdeleClassBaseChangeMulEquiv
        (K := K) (L := L)).toMonoidHom.comp
      (RelativeIdeleGroup.classInclusion K L) =
        ideleClassExtension K L := by
  ext c
  exact
    relativeIdeleClassBaseChangeMulEquiv_classInclusion
      (K := K) (L := L) c
