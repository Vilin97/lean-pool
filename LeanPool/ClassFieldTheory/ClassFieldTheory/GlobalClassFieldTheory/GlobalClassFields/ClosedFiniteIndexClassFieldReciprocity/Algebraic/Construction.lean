/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.QuotientTransport
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Construction
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationValue
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationCore
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Evaluation
/-!
# Underlying algebraic closed finite-index reciprocity

The algebraic equivalence is obtained by forgetting topology from the named
continuous provider.  This avoids a second specialization of the full finite
global reciprocity instance tower.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

/-- Canonical class-group commutativity supplies normality of the defining subgroup. -/
private theorem closedFiniteIndexAlgebraicClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] closedFiniteIndexAlgebraicClassGroupIsMulCommutative

variable {K : Type} [Field K] [NumberField K]

/-- Global reciprocity for the selected class field, stated over the original
number field and directly modulo its defining subgroup. -/
noncomputable abbrev closedFiniteIndexClassFieldGaloisEquivNormQuotient
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Gal((closedFiniteIndexClassField
          (K := K) H hclosed) / K) ≃*
      IdeleClassGroup K ⧸ H :=
  (closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient
    (K := K) H hclosed).toMulEquiv

end GlobalClassFields
end GlobalClassFieldTheory
