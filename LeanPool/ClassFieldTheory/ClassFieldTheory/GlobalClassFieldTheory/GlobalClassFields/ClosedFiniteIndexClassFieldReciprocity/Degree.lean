/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldOriginalField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.TopologicalGlobalNormResidue
/-!
# Degree of a closed finite-index class field

This leaf derives the degree of the selected class field from its exact
idèle-class norm range.
-/

@[expose] public section

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
/-- The degree of the selected class field over the original number
field is the index of its defining idèle-class subgroup. -/
theorem closedFiniteIndexClassField_finrank_eq_index
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Module.finrank K
        (closedFiniteIndexClassField
          (K := K) H hclosed) =
      H.index := by
  calc
    Module.finrank K
        (closedFiniteIndexClassField
          (K := K) H hclosed) =
        (_root_.ideleClassNorm K
          (closedFiniteIndexClassField
            (K := K) H hclosed)).range.index :=
      (ideleClassNorm_index_eq_finrank_abelian K
        (closedFiniteIndexClassField
          (K := K) H hclosed)).symm
    _ = H.index :=
      congrArg Subgroup.index
        (closedFiniteIndexClassField_ideleClassNorm_range
          (K := K) H hclosed)

end GlobalClassFields
end GlobalClassFieldTheory
