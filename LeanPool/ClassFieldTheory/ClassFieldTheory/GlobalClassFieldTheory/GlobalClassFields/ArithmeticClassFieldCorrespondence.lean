/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Degree
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.QuotientTransport
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Construction
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationValue
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationCore
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Evaluation
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Construction
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Evaluation
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.GlobalNormResidue
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
/-!
# Arithmetic topological class-field correspondence

For a closed finite-index subgroup `H ≤ C_K`, the selected actual
class field has norm range exactly `H`.  This module records the
canonical arithmetic reciprocity homeomorphism
`Gal(L/K) ≃ₜ* C_K/H`, so both the field and the topological group map
are fixed rather than merely asserted to exist.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField
open Reciprocity

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
/-- Fix the commutative idèle-class instance path used by every quotient in
this module, so the norm quotient and the literal quotient share one normality
construction during elaboration. -/
local instance
    arithmeticClassFieldCorrespondenceIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] arithmeticClassFieldCorrespondenceIdeleClassGroupIsMulCommutative

open scoped Classical in
private noncomputable def
    arithmeticClosedFiniteIndexClassFieldReciprocityData
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    {e : Gal((closedFiniteIndexClassField
            (K := K) H hclosed)/K) ≃ₜ*
          IdeleClassGroup K ⧸ H //
      ∀ c : IdeleClassGroup K,
        e (arithmeticGlobalNormResidueMonoidHom K
            (closedFiniteIndexClassField
              (K := K) H hclosed) c) =
          QuotientGroup.mk' H c} := by
  letI : DiscreteTopology
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K
          (closedFiniteIndexClassField
            (K := K) H hclosed)).range) :=
    ideleClassNormQuotient_discreteTopology K
      (closedFiniteIndexClassField
        (K := K) H hclosed)
  letI : DiscreteTopology
      (IdeleClassGroup K ⧸ H) :=
    QuotientGroup.discreteTopology
      (Subgroup.isOpen_of_isClosed_of_finiteIndex H hclosed)
  let quotientTransport :
      (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K
            (closedFiniteIndexClassField
              (K := K) H hclosed)).range) ≃ₜ*
        IdeleClassGroup K ⧸ H :=
    { QuotientGroup.quotientMulEquivOfEq
        (closedFiniteIndexClassField_ideleClassNorm_range
          (K := K) H hclosed) with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  refine
    ⟨(arithmeticGlobalReciprocityContinuousMulEquiv
        K (closedFiniteIndexClassField
          (K := K) H hclosed)).trans quotientTransport, ?_⟩
  intro c
  calc
    ((arithmeticGlobalReciprocityContinuousMulEquiv
        K (closedFiniteIndexClassField
          (K := K) H hclosed)).trans quotientTransport)
          (arithmeticGlobalNormResidueMonoidHom K
            (closedFiniteIndexClassField
              (K := K) H hclosed) c) =
        quotientTransport
          (arithmeticGlobalReciprocityContinuousMulEquiv K
            (closedFiniteIndexClassField
              (K := K) H hclosed)
            (arithmeticGlobalNormResidueMonoidHom K
              (closedFiniteIndexClassField
                (K := K) H hclosed) c)) := rfl
    _ = quotientTransport
          (QuotientGroup.mk'
            (_root_.ideleClassNorm K
              (closedFiniteIndexClassField
                (K := K) H hclosed)).range c) :=
      congrArg quotientTransport
        (arithmeticGlobalReciprocityContinuousMulEquiv_globalNormResidue
          K (closedFiniteIndexClassField
            (K := K) H hclosed) c)
    _ = QuotientGroup.mk' H c :=
      QuotientGroup.quotientMulEquivOfEq_mk
        (closedFiniteIndexClassField_ideleClassNorm_range
          (K := K) H hclosed) c

open scoped Classical in
/-- Arithmetic global reciprocity for the actual class field selected
by a closed finite-index idèle-class subgroup. -/
noncomputable def
    arithmeticClosedFiniteIndexClassFieldGaloisContinuousMulEquivNormQuotient
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Gal((closedFiniteIndexClassField
          (K := K) H hclosed)/K) ≃ₜ*
      IdeleClassGroup K ⧸ H :=
  (arithmeticClosedFiniteIndexClassFieldReciprocityData
    (K := K) H hclosed).1

open scoped Classical in
/-- The arithmetic norm-residue symbol of an idèle class maps to its
literal class modulo the defining subgroup. -/
theorem
    arithmeticClosedFiniteIndexClassFieldGaloisContinuousMulEquivNormQuotient_globalNormResidue
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (c : IdeleClassGroup K) :
    arithmeticClosedFiniteIndexClassFieldGaloisContinuousMulEquivNormQuotient
        (K := K) H hclosed
        (arithmeticGlobalNormResidueMonoidHom K
          (closedFiniteIndexClassField
            (K := K) H hclosed) c) =
      QuotientGroup.mk' H c := by
  exact
    (arithmeticClosedFiniteIndexClassFieldReciprocityData
      (K := K) H hclosed).2 c

open scoped Classical in
/-- The inverse correspondence sends a represented class modulo `H`
to its actual arithmetic global norm-residue automorphism. -/
theorem
    arithmeticClosedFiniteIndexClassFieldGaloisContinuousMulEquivNormQuotient_symm_mk
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (c : IdeleClassGroup K) :
    (arithmeticClosedFiniteIndexClassFieldGaloisContinuousMulEquivNormQuotient
      (K := K) H hclosed).symm
        (QuotientGroup.mk' H c) =
      arithmeticGlobalNormResidueMonoidHom K
        (closedFiniteIndexClassField
          (K := K) H hclosed) c := by
  let d :=
    arithmeticClosedFiniteIndexClassFieldReciprocityData
      (K := K) H hclosed
  change
    d.1.symm (QuotientGroup.mk' H c) =
      arithmeticGlobalNormResidueMonoidHom K
        (closedFiniteIndexClassField
          (K := K) H hclosed) c
  exact d.1.symm_apply_eq.mpr (d.2 c).symm

end GlobalClassFields
end GlobalClassFieldTheory
