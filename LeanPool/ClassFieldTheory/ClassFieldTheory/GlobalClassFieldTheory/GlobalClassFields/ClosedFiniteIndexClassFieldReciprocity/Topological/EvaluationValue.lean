/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Construction
/-!
# Named value of closed finite-index reciprocity

The expanded inverse norm-residue expression is kept behind one reducible
value provider.  Public evaluation statements can therefore mention the
selected class-field instance tower once while remaining definitionally
equivalent to the historical formula.
-/

@[expose] public section

open scoped IsMulCommutative NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

open scoped Classical in
/-- Canonical class-group commutativity supplies normality for norm-range transport. -/
private theorem closedFiniteIndexEvaluationValueClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] closedFiniteIndexEvaluationValueClassGroupIsMulCommutative

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
/-- The quotient value prescribed by inverse global norm-residue reciprocity
for a Galois element of the selected closed finite-index class field. -/
noncomputable abbrev closedFiniteIndexClassFieldReciprocityValue
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (σ : Gal((closedFiniteIndexClassField
      (K := K) H hclosed)/K)) :
    IdeleClassGroup K ⧸ H :=
  QuotientGroup.quotientMulEquivOfEq
      (closedFiniteIndexClassField_ideleClassNorm_range
        (K := K) H hclosed)
    (Additive.toMul
      ((globalNormResidueEquiv K
          (closedFiniteIndexClassField
            (K := K) H hclosed)).symm
        (Additive.ofMul σ)))

end GlobalClassFields
end GlobalClassFieldTheory
