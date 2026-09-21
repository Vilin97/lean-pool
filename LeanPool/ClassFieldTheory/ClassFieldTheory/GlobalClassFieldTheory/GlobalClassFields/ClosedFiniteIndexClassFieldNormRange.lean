/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldConstruction
/-!
# Norm range over the canonical fixed-field base

This leaf compares the selected abstract norm subgroup with the actual
idèle-class norm range over the canonical fixed-field base.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

variable {K : Type} [Field K] [NumberField K]

/-- Opaque bridge from multiplicative subgroup transport to its additive
presentation.  Keeping this generic prevents concrete fixed-field endpoints
from being unfolded by `rw` while comparing the two presentations. -/
private theorem subgroup_map_toAddSubgroup_mulEquiv
    {G G₂ : Type*} [Group G] [Group G₂]
    (S : Subgroup G) (e : G ≃* G₂) :
    (S.map e.toMonoidHom).toAddSubgroup =
      S.toAddSubgroup.map
        (MulEquiv.toAdditive e).toAddMonoidHom := by
  exact (MonoidHom.coe_toAdditive_map e.toMonoidHom S).symm

/-- The idèle-class transport attached to the selected base equivalence.
Naming this endpoint once keeps the fixed-field instance tower out of
downstream definitional-equality checks. -/
private noncomputable def closedFiniteIndexClassFieldIdeleClassEquiv
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    IdeleClassGroup K ≃*
      IdeleClassGroup
        (closedFiniteIndexClassFieldBase
          (K := K) H hclosed) :=
  ideleClassCongr
    (closedFiniteIndexClassFieldBaseEquiv
      (K := K) H hclosed)

/-- Additive form of the selected class-field norm-range computation, with
the concrete idèle-class endpoint hidden behind one typed definition. -/
private theorem closedFiniteIndexClassField_ideleClassNorm_range_toAddSubgroup
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    (_root_.ideleClassNorm
      (closedFiniteIndexClassFieldBase
        (K := K) H hclosed)
      (closedFiniteIndexClassField
        (K := K) H hclosed)).range.toAddSubgroup =
      H.toAddSubgroup.map
        (MulEquiv.toAdditive
          (closedFiniteIndexClassFieldIdeleClassEquiv
            (K := K) H hclosed)).toAddMonoidHom := by
  simpa only [closedFiniteIndexClassFieldIdeleClassEquiv,
    closedFiniteIndexClassField,
    closedFiniteIndexClassFieldBase,
    closedFiniteIndexClassFieldBaseEquiv] using
    (ordinaryNormClassField_ideleClassNorm_range K
      (closedFiniteIndexClassFieldNormAmbient
        (K := K) H hclosed) H
      (closedFiniteIndexClassFieldNormAmbient_normRange_le
        (K := K) H hclosed))

/-- The represented abstract norm subgroup as the same named actual norm
range.  This wrapper uses the lightweight named-field API, avoiding the
dependent `letI` tower in the raw fixed-field comparison theorem. -/
private theorem
    ordinaryIdeleClassNormSubgroup_closedFiniteIndexClassField_eq_range
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    ordinaryIdeleClassNormSubgroup
        (closedFiniteIndexClassFieldReciprocityFiniteAbstractField
          (K := K) H hclosed)
        (closedFiniteIndexClassFieldSubextension
          (K := K) H hclosed) =
      (_root_.ideleClassNorm
        (closedFiniteIndexClassFieldBase
          (K := K) H hclosed)
        (closedFiniteIndexClassField
          (K := K) H hclosed)).range.toAddSubgroup := by
  simpa only [closedFiniteIndexClassFieldBaseSubgroup,
    closedFiniteIndexClassFieldBase,
    closedFiniteIndexClassField] using
    (ordinaryIdeleClassNormSubgroup_eq_namedNormRange
      (closedFiniteIndexClassFieldReciprocityFiniteAbstractField
        (K := K) H hclosed)
      (closedFiniteIndexClassFieldSubextension
        (K := K) H hclosed))

/-- Over the canonical fixed-field base, the determinant-norm range of
the selected class field is the transport of `H`. -/
theorem closedFiniteIndexClassField_ideleClassNorm_range_over_base
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    (_root_.ideleClassNorm
      (closedFiniteIndexClassFieldBase
        (K := K) H hclosed)
      (closedFiniteIndexClassField
        (K := K) H hclosed)).range =
      H.map
        (ideleClassCongr
          (closedFiniteIndexClassFieldBaseEquiv
            (K := K) H hclosed)).toMonoidHom := by
  change
    (_root_.ideleClassNorm
      (closedFiniteIndexClassFieldBase
        (K := K) H hclosed)
      (closedFiniteIndexClassField
        (K := K) H hclosed)).range =
      H.map
        (closedFiniteIndexClassFieldIdeleClassEquiv
          (K := K) H hclosed).toMonoidHom
  apply
    (Subgroup.toAddSubgroup :
      Subgroup
          (IdeleClassGroup
            (closedFiniteIndexClassFieldBase
              (K := K) H hclosed)) ≃o
        AddSubgroup
          (Additive
            (IdeleClassGroup
            (closedFiniteIndexClassFieldBase
                (K := K) H hclosed)))).injective
  calc
    (_root_.ideleClassNorm
        (closedFiniteIndexClassFieldBase
          (K := K) H hclosed)
        (closedFiniteIndexClassField
          (K := K) H hclosed)).range.toAddSubgroup =
        H.toAddSubgroup.map
          (MulEquiv.toAdditive
            (closedFiniteIndexClassFieldIdeleClassEquiv
              (K := K) H hclosed)).toAddMonoidHom :=
      closedFiniteIndexClassField_ideleClassNorm_range_toAddSubgroup
        (K := K) H hclosed
    _ =
        (H.map
          (closedFiniteIndexClassFieldIdeleClassEquiv
            (K := K) H hclosed).toMonoidHom).toAddSubgroup :=
      (subgroup_map_toAddSubgroup_mulEquiv H
        (closedFiniteIndexClassFieldIdeleClassEquiv
          (K := K) H hclosed)).symm

/-- The selected subextension is a literal preimage of the transported
closed finite-index subgroup under the ordinary norm-subgroup
correspondence. -/
theorem
    ordinaryIdeleClassNormSubgroup_closedFiniteIndexClassFieldSubextension
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    ordinaryIdeleClassNormSubgroup
        (closedFiniteIndexClassFieldReciprocityFiniteAbstractField
          (K := K) H hclosed)
        (closedFiniteIndexClassFieldSubextension
          (K := K) H hclosed) =
      H.toAddSubgroup.map
        (MulEquiv.toAdditive
          (ideleClassCongr
            (closedFiniteIndexClassFieldBaseEquiv
              (K := K) H hclosed))).toAddMonoidHom := by
  change
    ordinaryIdeleClassNormSubgroup
        (closedFiniteIndexClassFieldReciprocityFiniteAbstractField
          (K := K) H hclosed)
        (closedFiniteIndexClassFieldSubextension
          (K := K) H hclosed) =
      H.toAddSubgroup.map
        (MulEquiv.toAdditive
          (closedFiniteIndexClassFieldIdeleClassEquiv
            (K := K) H hclosed)).toAddMonoidHom
  calc
    ordinaryIdeleClassNormSubgroup
        (closedFiniteIndexClassFieldReciprocityFiniteAbstractField
          (K := K) H hclosed)
        (closedFiniteIndexClassFieldSubextension
          (K := K) H hclosed) =
        (_root_.ideleClassNorm
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed)
          (closedFiniteIndexClassField
            (K := K) H hclosed)).range.toAddSubgroup :=
      ordinaryIdeleClassNormSubgroup_closedFiniteIndexClassField_eq_range
        (K := K) H hclosed
    _ =
        H.toAddSubgroup.map
          (MulEquiv.toAdditive
            (closedFiniteIndexClassFieldIdeleClassEquiv
              (K := K) H hclosed)).toAddMonoidHom :=
      closedFiniteIndexClassField_ideleClassNorm_range_toAddSubgroup
        (K := K) H hclosed
end GlobalClassFields
end GlobalClassFieldTheory
