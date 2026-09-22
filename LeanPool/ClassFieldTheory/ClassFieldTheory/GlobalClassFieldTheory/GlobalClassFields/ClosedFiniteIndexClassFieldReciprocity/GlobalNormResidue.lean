/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Construction
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Evaluation
/-!
# Norm-residue evaluation for a closed finite-index class field

This leaf proves that the selected class-field reciprocity equivalence sends
the global norm-residue symbol to the corresponding quotient class.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

open scoped Classical in
/-- Canonical class-group commutativity supplies normality for quotient evaluation. -/
private theorem closedFiniteIndexNormResidueClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] closedFiniteIndexNormResidueClassGroupIsMulCommutative

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
private theorem quotientTransport_inverse_apply
    {G A : Type*} [Group G] [Group A]
    (N H : Subgroup G) [N.Normal] [H.Normal]
    (e : Additive (G ⧸ N) ≃+ Additive A)
    (h : N = H) (c : G) :
    QuotientGroup.quotientMulEquivOfEq h
        (Additive.toMul
          (e.symm
            (e (Additive.ofMul (QuotientGroup.mk' N c))))) =
      QuotientGroup.mk' H c := by
  calc
    _ = QuotientGroup.quotientMulEquivOfEq h
          (Additive.toMul
            (Additive.ofMul (QuotientGroup.mk' N c))) :=
      congrArg
        (fun z => QuotientGroup.quotientMulEquivOfEq h
          (Additive.toMul z))
        (e.symm_apply_apply _)
    _ = QuotientGroup.mk' H c :=
      QuotientGroup.quotientMulEquivOfEq_mk h c

open scoped Classical in
/-- Under the direct class-field reciprocity equivalence, the global
norm-residue symbol of an idèle class is its quotient class modulo
`H`. -/
theorem
    closedFiniteIndexClassFieldGaloisEquivNormQuotient_globalNormResidue
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (c : IdeleClassGroup K) :
    closedFiniteIndexClassFieldGaloisEquivNormQuotient
        (K := K) H hclosed
        (globalNormResidueMonoidHom K
          (closedFiniteIndexClassField
            (K := K) H hclosed) c) =
      QuotientGroup.mk' H c := by
  have hNormResidue :
      Additive.ofMul
          (globalNormResidueMonoidHom K
            (closedFiniteIndexClassField
              (K := K) H hclosed) c) =
        globalNormResidueEquiv K
          (closedFiniteIndexClassField
            (K := K) H hclosed)
          (Additive.ofMul
            (QuotientGroup.mk'
              (_root_.ideleClassNorm K
                (closedFiniteIndexClassField
                  (K := K) H hclosed)).range c)) :=
    congrArg (fun σ => Additive.ofMul σ)
      (globalNormResidueMonoidHom_apply K
        (closedFiniteIndexClassField
          (K := K) H hclosed) c)
  calc
    _ = QuotientGroup.quotientMulEquivOfEq
          (closedFiniteIndexClassField_ideleClassNorm_range
            (K := K) H hclosed)
          (Additive.toMul
            ((globalNormResidueEquiv K
                (closedFiniteIndexClassField
                  (K := K) H hclosed)).symm
              (Additive.ofMul
                (globalNormResidueMonoidHom K
                  (closedFiniteIndexClassField
                    (K := K) H hclosed) c)))) :=
      closedFiniteIndexClassFieldGaloisEquivNormQuotient_apply
        (K := K) H hclosed _
    _ = QuotientGroup.quotientMulEquivOfEq
          (closedFiniteIndexClassField_ideleClassNorm_range
            (K := K) H hclosed)
          (Additive.toMul
            ((globalNormResidueEquiv K
                (closedFiniteIndexClassField
                  (K := K) H hclosed)).symm
              (globalNormResidueEquiv K
                (closedFiniteIndexClassField
                  (K := K) H hclosed)
                (Additive.ofMul
                  (QuotientGroup.mk'
                    (_root_.ideleClassNorm K
                      (closedFiniteIndexClassField
                        (K := K) H hclosed)).range c))))) :=
      congrArg
        (fun τ =>
          QuotientGroup.quotientMulEquivOfEq
              (closedFiniteIndexClassField_ideleClassNorm_range
                (K := K) H hclosed)
            (Additive.toMul
              ((globalNormResidueEquiv K
                  (closedFiniteIndexClassField
                    (K := K) H hclosed)).symm τ)))
        hNormResidue
    _ = QuotientGroup.mk' H c :=
      quotientTransport_inverse_apply
      ((_root_.ideleClassNorm K
        (closedFiniteIndexClassField
          (K := K) H hclosed)).range)
      H
      (globalNormResidueEquiv K
        (closedFiniteIndexClassField
          (K := K) H hclosed))
      (closedFiniteIndexClassField_ideleClassNorm_range
        (K := K) H hclosed)
      c

end GlobalClassFields
end GlobalClassFieldTheory
