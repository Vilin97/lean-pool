/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationValue
/-!
# Generic evaluation core for transported reciprocity

This theorem works for an arbitrary finite abelian extension and subgroup
equality.  It proves the composition formula once without unfolding a
domain-specific selected-field construction.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

/-- Canonical class-group commutativity supplies normality in the transport formula. -/
private theorem closedFiniteIndexEvaluationCoreClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] closedFiniteIndexEvaluationCoreClassGroupIsMulCommutative

variable
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- Evaluation of global reciprocity after continuous transport along an
equality between the actual norm range and a target subgroup. -/
theorem globalReciprocityContinuousMulEquiv_trans_quotientOfEq_apply
    (H : Subgroup (IdeleClassGroup K))
    (hNorm : (_root_.ideleClassNorm K L).range = H)
    (σ : Gal(L/K)) :
    ((globalReciprocityContinuousMulEquiv K L).trans
      (QuotientGroup.quotientContinuousMulEquivOfEq hNorm)) σ =
      QuotientGroup.quotientMulEquivOfEq hNorm
        (Additive.toMul
          ((globalNormResidueEquiv K L).symm
            (Additive.ofMul σ))) := by
  calc
    _ = QuotientGroup.quotientContinuousMulEquivOfEq hNorm
        (globalReciprocityContinuousMulEquiv K L σ) := rfl
    _ = QuotientGroup.quotientMulEquivOfEq hNorm
        (globalReciprocityContinuousMulEquiv K L σ) :=
      QuotientGroup.quotientContinuousMulEquivOfEq_apply _ _
    _ = _ :=
      congrArg
        (QuotientGroup.quotientMulEquivOfEq hNorm)
        (globalReciprocityContinuousMulEquiv_apply K L σ)

end GlobalClassFields
end GlobalClassFieldTheory
