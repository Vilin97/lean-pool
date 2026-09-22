/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldNormRange
/-!
# Transport to the original number field

This leaf installs the original-field algebra tower and transports the
canonical norm-range computation back to the original idèle class group.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
/-- The canonical fixed-field copy, regarded as an algebra over the
original number field. -/
noncomputable instance closedFiniteIndexClassFieldBaseAlgebraOverOriginal
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Algebra K
      (closedFiniteIndexClassFieldBase
        (K := K) H hclosed) :=
  (closedFiniteIndexClassFieldBaseEquiv
    (K := K) H hclosed).toRingHom.toAlgebra

open scoped Classical in
/-- The base-field identification as an equivalence of algebras over
the original number field. -/
noncomputable def closedFiniteIndexClassFieldBaseEquivOverOriginal
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    K ≃ₐ[K]
      closedFiniteIndexClassFieldBase
        (K := K) H hclosed :=
  AlgEquiv.ofRingEquiv
    (f := (closedFiniteIndexClassFieldBaseEquiv
      (K := K) H hclosed).toRingEquiv)
    (fun _ => rfl)

open scoped Classical in
/-- The selected class field, regarded as an algebra over the original
number field through its canonical fixed-field copy. -/
noncomputable instance closedFiniteIndexClassFieldAlgebraOverOriginal
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Algebra K
      (closedFiniteIndexClassField
        (K := K) H hclosed) :=
  ((algebraMap
      (closedFiniteIndexClassFieldBase
        (K := K) H hclosed)
      (closedFiniteIndexClassField
        (K := K) H hclosed)).comp
    (algebraMap K
      (closedFiniteIndexClassFieldBase
        (K := K) H hclosed))).toAlgebra

open scoped Classical in
/-- The scalar map into the selected class field is the canonical base
equivalence followed by fixed-field inclusion. -/
@[simp]
theorem closedFiniteIndexClassField_algebraMap_original
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (x : K) :
    algebraMap K
        (closedFiniteIndexClassField
          (K := K) H hclosed) x =
      algebraMap
        (closedFiniteIndexClassFieldBase
          (K := K) H hclosed)
        (closedFiniteIndexClassField
          (K := K) H hclosed)
        (closedFiniteIndexClassFieldBaseEquiv
          (K := K) H hclosed x) :=
  rfl

open scoped Classical in
noncomputable instance
    closedFiniteIndexClassFieldBaseFiniteDimensionalOverOriginal
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    FiniteDimensional K
      (closedFiniteIndexClassFieldBase
        (K := K) H hclosed) :=
  (closedFiniteIndexClassFieldBaseEquivOverOriginal
    (K := K) H hclosed).toLinearEquiv.finiteDimensional

open scoped Classical in
noncomputable instance closedFiniteIndexClassFieldScalarTowerOverOriginal
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    IsScalarTower K
      (closedFiniteIndexClassFieldBase
        (K := K) H hclosed)
      (closedFiniteIndexClassField
        (K := K) H hclosed) :=
  IsScalarTower.of_algebraMap_eq' rfl

open scoped Classical in
noncomputable instance
    closedFiniteIndexClassFieldFiniteDimensionalOverOriginal
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    FiniteDimensional K
      (closedFiniteIndexClassField
        (K := K) H hclosed) :=
  FiniteDimensional.trans K
    (closedFiniteIndexClassFieldBase
      (K := K) H hclosed)
    (closedFiniteIndexClassField
      (K := K) H hclosed)

open scoped Classical in
noncomputable instance closedFiniteIndexClassFieldIsGaloisOverOriginal
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    IsGalois K
      (closedFiniteIndexClassField
        (K := K) H hclosed) := by
  let e :=
    closedFiniteIndexClassFieldBaseEquiv
      (K := K) H hclosed
  apply IsGalois.of_equiv_equiv
    (F := closedFiniteIndexClassFieldBase
      (K := K) H hclosed)
    (E := closedFiniteIndexClassField
      (K := K) H hclosed)
    (f := e.symm.toRingEquiv)
    (g := RingEquiv.refl
      (closedFiniteIndexClassField
        (K := K) H hclosed))
  apply RingHom.ext
  intro x
  calc
    ((algebraMap K
        (closedFiniteIndexClassField
          (K := K) H hclosed)).comp e.symm.toRingEquiv) x =
        algebraMap K
          (closedFiniteIndexClassField
            (K := K) H hclosed) (e.symm x) := rfl
    _ = algebraMap
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed)
          (closedFiniteIndexClassField
            (K := K) H hclosed)
          (closedFiniteIndexClassFieldBaseEquiv
            (K := K) H hclosed (e.symm x)) :=
      closedFiniteIndexClassField_algebraMap_original
        (K := K) H hclosed (e.symm x)
    _ = algebraMap
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed)
          (closedFiniteIndexClassField
            (K := K) H hclosed) x := by
      simpa only [e] using
        congrArg
          (algebraMap
            (closedFiniteIndexClassFieldBase
              (K := K) H hclosed)
            (closedFiniteIndexClassField
              (K := K) H hclosed))
          ((closedFiniteIndexClassFieldBaseEquiv
            (K := K) H hclosed).apply_symm_apply x)
    _ = ((RingEquiv.refl
          (closedFiniteIndexClassField
            (K := K) H hclosed)).toRingHom.comp
        (algebraMap
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed)
          (closedFiniteIndexClassField
            (K := K) H hclosed))) x := rfl

open scoped Classical in
noncomputable instance
    closedFiniteIndexClassFieldIsAbelianGaloisOverOriginal
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    IsAbelianGalois K
      (closedFiniteIndexClassField
        (K := K) H hclosed) :=
  IsAbelianGalois.of_base_equiv
    (closedFiniteIndexClassFieldBaseEquiv
      (K := K) H hclosed).toRingEquiv
    (closedFiniteIndexClassField_algebraMap_original
      (K := K) H hclosed)

open scoped Classical in
/-- The selected class field has determinant-norm range exactly `H`
in the idèle class group of the original number field. -/
theorem closedFiniteIndexClassField_ideleClassNorm_range
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    (_root_.ideleClassNorm K
      (closedFiniteIndexClassField
        (K := K) H hclosed)).range = H := by
  let e :=
    closedFiniteIndexClassFieldBaseEquiv
      (K := K) H hclosed
  let g := (ideleClassCongr e).toMonoidHom
  have hCanonical :
      (_root_.ideleClassNorm
        (closedFiniteIndexClassFieldBase
          (K := K) H hclosed)
        (closedFiniteIndexClassField
          (K := K) H hclosed)).range =
        H.map g := by
    simpa only [e, g] using
      (closedFiniteIndexClassField_ideleClassNorm_range_over_base
        (K := K) H hclosed)
  apply
    Subgroup.map_injective
      (f := g) (ideleClassCongr e).injective
  calc
    ((_root_.ideleClassNorm K
      (closedFiniteIndexClassField
        (K := K) H hclosed)).range).map g =
        (_root_.ideleClassNorm
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed)
          (closedFiniteIndexClassField
            (K := K) H hclosed)).range := by
      exact
        ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv
          e
          (AlgEquiv.refl
            (R := ℚ)
            (A₁ := closedFiniteIndexClassField
              (K := K) H hclosed))
          (fun x => by
            exact closedFiniteIndexClassField_algebraMap_original
              (K := K) H hclosed x)
    _ = H.map g := hCanonical
end GlobalClassFields
end GlobalClassFieldTheory
