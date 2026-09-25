/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Degree
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.QuotientTransport
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Construction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationValue
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationCore
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Evaluation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Construction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Evaluation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.GlobalNormResidue
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
/-!
# Actual realizations of the Hilbert class fields

The big and small Hilbert norm subgroups are closed and have finite
index.  The finite-index class-field construction therefore supplies
genuine finite abelian subextensions of the rational separable closure.
This file fixes those subextensions once and for all, names their actual
relative fixed fields, and identifies their determinant-norm ranges.

The resulting degrees are the orders of the corresponding reciprocity
quotients: the narrow class number for the big Hilbert class field and
the ordinary class number for the small Hilbert class field.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open NumberField
open Reciprocity

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
/-- The big-Hilbert congruence subgroup has finite index, registered at
the realization layer where the closed finite-index construction uses it. -/
instance bigHilbertClassFieldNormSubgroupFiniteIndex :
    (bigHilbertClassFieldNormSubgroup (K := K)).FiniteIndex := by
  unfold bigHilbertClassFieldNormSubgroup
  infer_instance

open scoped Classical in
/-- The concrete finite Galois norm neighbourhood used to realize the
big Hilbert class field. -/
noncomputable abbrev bigHilbertClassFieldNormAmbient (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassFieldNormAmbient
    (K := K)
    (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

open scoped Classical in
/-- The concrete finite Galois norm neighbourhood used to realize the
small Hilbert class field. -/
noncomputable abbrev smallHilbertClassFieldNormAmbient (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassFieldNormAmbient
    (K := K)
    (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

open scoped Classical in
/-- The compatible abstract base subgroup for the actual big Hilbert
class-field realization. -/
noncomputable abbrev bigHilbertClassFieldBaseSubgroup (K : Type)
    [Field K] [NumberField K] :=
  closedFiniteIndexClassFieldBaseSubgroup
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

open scoped Classical in
/-- The finite abelian subextension selected by the big-Hilbert norm
subgroup.  This is the actual class-field witness, rather than merely an
existence proposition. -/
noncomputable abbrev bigHilbertClassFieldSubextension (K : Type)
    [Field K] [NumberField K] :
    FiniteAbelianSubextension
      (bigHilbertClassFieldBaseSubgroup K) :=
  closedFiniteIndexClassFieldSubextension
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

open scoped Classical in
/-- The compatible actual copy of the original number field occurring
as the base fixed field in the big-Hilbert realization. -/
noncomputable abbrev bigHilbertClassFieldBase (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassFieldBase
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

open scoped Classical in
/-- The actual big Hilbert class field selected inside the rational
separable closure. -/
noncomputable abbrev bigHilbertClassField (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassField
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

open scoped Classical in
/-- The canonical equivalence from `K` to the actual base fixed field
used by the selected big Hilbert class field. -/
noncomputable abbrev bigHilbertClassFieldBaseEquiv :
    K ≃ₐ[ℚ] bigHilbertClassFieldBase K :=
  closedFiniteIndexClassFieldBaseEquiv
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

open scoped Classical in
/-- The big-Hilbert norm subgroup transported to the actual base fixed
field of the selected realization. -/
def bigHilbertClassFieldTransportedNormSubgroup :
    Subgroup (IdeleClassGroup (bigHilbertClassFieldBase K)) :=
  (bigHilbertClassFieldNormSubgroup (K := K)).map
    (ideleClassCongr
      (bigHilbertClassFieldBaseEquiv (K := K))).toMonoidHom

open scoped Classical in
/-- The determinant-norm range of the actual big Hilbert class field is
exactly the transported big-Hilbert norm subgroup. -/
theorem bigHilbertClassField_ideleClassNorm_range :
    (_root_.ideleClassNorm
      (bigHilbertClassFieldBase K)
      (bigHilbertClassField K)).range =
      bigHilbertClassFieldTransportedNormSubgroup (K := K) := by
  simpa only [bigHilbertClassFieldTransportedNormSubgroup,
    bigHilbertClassFieldBaseEquiv, bigHilbertClassField,
    bigHilbertClassFieldBase] using
    (closedFiniteIndexClassField_ideleClassNorm_range_over_base
      (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
      (bigHilbertClassFieldNormSubgroup_isClosed (K := K)))

open scoped Classical in
private theorem
    closedFiniteIndexClassField_finrank_over_base_eq_index
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Module.finrank
        (closedFiniteIndexClassFieldBase
          (K := K) H hclosed)
        (closedFiniteIndexClassField
          (K := K) H hclosed) =
      H.index := by
  calc
    Module.finrank
        (closedFiniteIndexClassFieldBase
          (K := K) H hclosed)
        (closedFiniteIndexClassField
          (K := K) H hclosed) =
        (_root_.ideleClassNorm
          (closedFiniteIndexClassFieldBase
            (K := K) H hclosed)
          (closedFiniteIndexClassField
            (K := K) H hclosed)).range.index :=
      (ideleClassNorm_index_eq_finrank_abelian
        (closedFiniteIndexClassFieldBase
          (K := K) H hclosed)
        (closedFiniteIndexClassField
          (K := K) H hclosed)).symm
    _ = (H.map
          (ideleClassCongr
            (closedFiniteIndexClassFieldBaseEquiv
              (K := K) H hclosed)).toMonoidHom).index :=
      congrArg Subgroup.index
        (closedFiniteIndexClassField_ideleClassNorm_range_over_base
          (K := K) H hclosed)
    _ = H.index :=
      Subgroup.index_map_equiv H
        (ideleClassCongr
          (closedFiniteIndexClassFieldBaseEquiv
            (K := K) H hclosed))

open scoped Classical in
/-- The degree of the actual big Hilbert class field is the narrow
class number. -/
theorem bigHilbertClassField_finrank_eq_narrowClassGroup_card :
    Module.finrank
        (bigHilbertClassFieldBase K)
        (bigHilbertClassField K) =
      Nat.card (RayClass.NarrowClassGroup K) := by
  calc
    Module.finrank
        (bigHilbertClassFieldBase K)
        (bigHilbertClassField K) =
        (bigHilbertClassFieldNormSubgroup (K := K)).index :=
      closedFiniteIndexClassField_finrank_over_base_eq_index
        (bigHilbertClassFieldNormSubgroup (K := K))
        (bigHilbertClassFieldNormSubgroup_isClosed (K := K))
    _ =
        Nat.card
          (IdeleClassGroup K ⧸
            bigHilbertClassFieldNormSubgroup (K := K)) :=
      Subgroup.index_eq_card
        (bigHilbertClassFieldNormSubgroup (K := K))
    _ = Nat.card (RayClass.NarrowClassGroup K) :=
      Nat.card_congr
        (bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := K)).toEquiv

open scoped Classical in
/-- The compatible abstract base subgroup for the actual small Hilbert
class-field realization. -/
noncomputable abbrev smallHilbertClassFieldBaseSubgroup (K : Type)
    [Field K] [NumberField K] :=
  closedFiniteIndexClassFieldBaseSubgroup
    (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

open scoped Classical in
/-- The finite abelian subextension selected by the small-Hilbert norm
subgroup.  This named witness is the input used by principalization. -/
noncomputable abbrev smallHilbertClassFieldSubextension (K : Type)
    [Field K] [NumberField K] :
    FiniteAbelianSubextension
      (smallHilbertClassFieldBaseSubgroup K) :=
  closedFiniteIndexClassFieldSubextension
    (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

open scoped Classical in
/-- The compatible actual copy of the original number field occurring
as the base fixed field in the small-Hilbert realization. -/
noncomputable abbrev smallHilbertClassFieldBase (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassFieldBase
    (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

open scoped Classical in
/-- The actual small Hilbert class field selected inside the rational
separable closure. -/
noncomputable abbrev smallHilbertClassField (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassField
    (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

open scoped Classical in
/-- The canonical equivalence from `K` to the actual base fixed field
used by the selected small Hilbert class field. -/
noncomputable abbrev smallHilbertClassFieldBaseEquiv :
    K ≃ₐ[ℚ] smallHilbertClassFieldBase K :=
  closedFiniteIndexClassFieldBaseEquiv
    (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

open scoped Classical in
/-- The small-Hilbert norm subgroup transported to the actual base fixed
field of the selected realization. -/
def smallHilbertClassFieldTransportedNormSubgroup :
    Subgroup (IdeleClassGroup (smallHilbertClassFieldBase K)) :=
  (smallHilbertClassFieldNormSubgroup (K := K)).map
    (ideleClassCongr
      (smallHilbertClassFieldBaseEquiv (K := K))).toMonoidHom

open scoped Classical in
/-- The determinant-norm range of the actual small Hilbert class field
is exactly the transported small-Hilbert norm subgroup. -/
theorem smallHilbertClassField_ideleClassNorm_range :
    (_root_.ideleClassNorm
      (smallHilbertClassFieldBase K)
      (smallHilbertClassField K)).range =
      smallHilbertClassFieldTransportedNormSubgroup (K := K) := by
  simpa only [smallHilbertClassFieldTransportedNormSubgroup,
    smallHilbertClassFieldBaseEquiv, smallHilbertClassField,
    smallHilbertClassFieldBase] using
    (closedFiniteIndexClassField_ideleClassNorm_range_over_base
      (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
      (smallHilbertClassFieldNormSubgroup_isClosed (K := K)))

open scoped Classical in
/-- The degree of the actual small Hilbert class field is the ordinary
class number. -/
theorem smallHilbertClassField_finrank_eq_classNumber :
    Module.finrank
        (smallHilbertClassFieldBase K)
        (smallHilbertClassField K) =
      NumberField.classNumber K := by
  calc
    Module.finrank
        (smallHilbertClassFieldBase K)
        (smallHilbertClassField K) =
        (smallHilbertClassFieldNormSubgroup (K := K)).index :=
      closedFiniteIndexClassField_finrank_over_base_eq_index
        (smallHilbertClassFieldNormSubgroup (K := K))
        (smallHilbertClassFieldNormSubgroup_isClosed (K := K))
    _ =
        Nat.card
          (IdeleClassGroup K ⧸
            smallHilbertClassFieldNormSubgroup (K := K)) :=
      Subgroup.index_eq_card
        (smallHilbertClassFieldNormSubgroup (K := K))
    _ = NumberField.classNumber K :=
      smallHilbertClassFieldQuotient_card_eq_classNumber
        (K := K)

end GlobalClassFields
end GlobalClassFieldTheory
