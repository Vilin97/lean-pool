/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldCorrespondenceTopology
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteIndexNormClassField
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.OrdinaryNormClassField
/-!
# Construction of a closed finite-index class field

This leaf fixes the finite Galois norm neighbourhood, abstract subextension,
and canonical fixed-field presentation attached to a closed finite-index
idèle-class subgroup. Norm-range and reciprocity statements live in later
leaves so their elaboration environments do not remain resident here.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

variable {K : Type} [Field K] [NumberField K]

/-- The concrete finite Galois norm neighbourhood used to construct
the class field of `H`. -/
noncomputable abbrev closedFiniteIndexClassFieldNormAmbient
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] : Type :=
  closedFiniteIndexNormAmbient (K := K) H hclosed

/-- The named norm-neighbourhood containment used by the selected
ordinary class-field construction. -/
theorem closedFiniteIndexClassFieldNormAmbient_normRange_le
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    (_root_.ideleClassNorm K
      (closedFiniteIndexClassFieldNormAmbient
        (K := K) H hclosed)).range ≤ H := by
  simpa only [closedFiniteIndexClassFieldNormAmbient] using
    (closedFiniteIndexSubgroup_has_finiteGaloisNormNeighborhood
      (K := K) H hclosed)

/-- The compatible abstract base subgroup used by the selected class
field of `H`. -/
noncomputable abbrev closedFiniteIndexClassFieldBaseSubgroup
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :=
  numberFieldTowerBaseSubgroup K
    (closedFiniteIndexClassFieldNormAmbient
      (K := K) H hclosed)

/-- A reducible finite-abstract-field package whose field projection is
definitionally the selected base subgroup.  Keeping this presentation
transparent avoids dependent quotient transports through the opaque tower
package in reciprocity consumers. -/
noncomputable abbrev
    closedFiniteIndexClassFieldReciprocityFiniteAbstractField
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    ClassFormation.FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  numberFieldTowerReciprocityFiniteAbstractField K
    (closedFiniteIndexClassFieldNormAmbient
      (K := K) H hclosed)

/-- The finite abelian subextension selected by a closed finite-index
idèle-class subgroup. -/
noncomputable abbrev closedFiniteIndexClassFieldSubextension
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    ClassFormation.FiniteAbelianSubextension
      (closedFiniteIndexClassFieldBaseSubgroup
        (K := K) H hclosed) :=
  ordinaryNormClassFieldSubextension K
    (closedFiniteIndexClassFieldNormAmbient
      (K := K) H hclosed) H
    (closedFiniteIndexClassFieldNormAmbient_normRange_le
      (K := K) H hclosed)

/-- The canonical fixed-field copy of the original number field used
by the selected class field of `H`. -/
noncomputable abbrev closedFiniteIndexClassFieldBase
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] : Type :=
  ordinaryNormClassFieldBase K
    (closedFiniteIndexClassFieldNormAmbient
      (K := K) H hclosed)

/-- The actual finite abelian class field selected by `H`. -/
noncomputable abbrev closedFiniteIndexClassField
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] : Type :=
  ordinaryNormClassFieldExtension K
    (closedFiniteIndexClassFieldNormAmbient
      (K := K) H hclosed) H
    (closedFiniteIndexClassFieldNormAmbient_normRange_le
      (K := K) H hclosed)

/-- The canonical equivalence from the original number field to the
fixed-field base of its selected class field. -/
noncomputable abbrev closedFiniteIndexClassFieldBaseEquiv
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    K ≃ₐ[ℚ]
      closedFiniteIndexClassFieldBase
        (K := K) H hclosed :=
  ordinaryNormClassFieldBaseEquiv K
    (closedFiniteIndexClassFieldNormAmbient
      (K := K) H hclosed)
end GlobalClassFields
end GlobalClassFieldTheory
