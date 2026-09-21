/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationCore
/-!
# Evaluation of continuous closed finite-index reciprocity

The public theorem uses the named reducible value provider and specializes
the generic transported-reciprocity calculation.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

variable {K : Type} [Field K] [NumberField K]

/-- Evaluation of the selected class-field equivalence is the named inverse
global norm-residue value in the quotient by the defining subgroup. -/
@[simp]
theorem
    closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient_apply
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (σ : Gal((closedFiniteIndexClassField
      (K := K) H hclosed)/K)) :
    closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient
        (K := K) H hclosed σ =
      closedFiniteIndexClassFieldReciprocityValue
        (K := K) H hclosed σ :=
  globalReciprocityContinuousMulEquiv_trans_quotientOfEq_apply
    H
    (closedFiniteIndexClassField_ideleClassNorm_range
      (K := K) H hclosed)
    σ

end GlobalClassFields
end GlobalClassFieldTheory
