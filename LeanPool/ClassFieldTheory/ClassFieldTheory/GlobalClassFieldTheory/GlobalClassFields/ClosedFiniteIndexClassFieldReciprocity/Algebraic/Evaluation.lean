/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Construction
/-!
# Evaluation of algebraic closed finite-index reciprocity

Since the algebraic equivalence is definitionally the underlying
multiplicative equivalence of the continuous provider, its evaluation theorem
is inherited without reconstructing the selected class-field instance tower.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

variable {K : Type} [Field K] [NumberField K]

/-- Evaluation of the direct non-topological reciprocity equivalence. -/
@[simp]
theorem closedFiniteIndexClassFieldGaloisEquivNormQuotient_apply
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (σ : Gal((closedFiniteIndexClassField
      (K := K) H hclosed)/K)) :
    closedFiniteIndexClassFieldGaloisEquivNormQuotient
        (K := K) H hclosed σ =
      closedFiniteIndexClassFieldReciprocityValue
        (K := K) H hclosed σ :=
  closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient_apply
    (K := K) H hclosed σ

end GlobalClassFields
end GlobalClassFieldTheory
