/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdealClass
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldComparison
import Mathlib.RingTheory.ClassGroup.ExtendedHom
/-!
# The principal ideal theorem

This file descends genuine idele extension to the reciprocity quotients
defining the two small Hilbert class fields and proves that the resulting
map forms the naturality square with the existing ideal-class extension
`ClassGroup.extendedHom`.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField

/-- Canonical class-group commutativity supplies normality for the quotient. -/
private theorem principalIdealTheoremClassGroupIsMulCommutative
    (F : Type*) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] principalIdealTheoremClassGroupIsMulCommutative

section SmallHilbertIdeleExtension

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [IsGalois K L] in
/-- The map on small-Hilbert reciprocity quotients induced by the
concrete extension map on ideles. -/
noncomputable def smallHilbertClassFieldIdeleExtensionMap :
    (IdeleClassGroup K ⧸
        GlobalClassFields.smallHilbertClassFieldNormSubgroup) →*
      (IdeleClassGroup L ⧸
        GlobalClassFields.smallHilbertClassFieldNormSubgroup) :=
  QuotientGroup.map
    GlobalClassFields.smallHilbertClassFieldNormSubgroup
    GlobalClassFields.smallHilbertClassFieldNormSubgroup
    (ideleClassExtension K L)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change
        ideleClassExtension K L
            (QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K) a) ∈
          GlobalClassFields.smallHilbertClassFieldNormSubgroup
      rw [ideleClassExtension_mk]
      exact
        ⟨IdeleGroup.extension K L a,
          IdeleGroup.extension_mem_ordinaryIdealClassSubgroup
            K L ha,
          rfl⟩)

omit [IsGalois K L] in
/-- Evaluation of the small-Hilbert idele-extension map on a quotient
representative. -/
@[simp]
theorem smallHilbertClassFieldIdeleExtensionMap_mk'
    (c : IdeleClassGroup K) :
    smallHilbertClassFieldIdeleExtensionMap K L
        (QuotientGroup.mk'
          (GlobalClassFields.smallHilbertClassFieldNormSubgroup (K := K)) c) =
      QuotientGroup.mk'
        (GlobalClassFields.smallHilbertClassFieldNormSubgroup (K := L))
        (ideleClassExtension K L c) := by
  rfl

omit [IsGalois K L] in
/-- The concrete idele extension and extension of ideal classes form
the naturality square on the small-Hilbert quotients. -/
theorem smallHilbertClassFieldIdeleExtensionMap_naturality
    (q : IdeleClassGroup K ⧸
      GlobalClassFields.smallHilbertClassFieldNormSubgroup) :
    GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
        (K := L)
        (smallHilbertClassFieldIdeleExtensionMap K L q) =
      ClassGroup.extendedHom (𝓞 K) (𝓞 L)
        (GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
          (K := K) q) := by
  induction q using QuotientGroup.induction_on with
  | _ c =>
      induction c using QuotientGroup.induction_on with
      | _ a =>
          change
            GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
                (K := L)
                (QuotientGroup.mk'
                  GlobalClassFields.smallHilbertClassFieldNormSubgroup
                  (QuotientGroup.mk'
                    (IdeleGroup.principalSubgroup L)
                    (IdeleGroup.extension K L a))) =
              ClassGroup.extendedHom (𝓞 K) (𝓞 L)
                (GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
                  (K := K)
                  (QuotientGroup.mk'
                    GlobalClassFields.smallHilbertClassFieldNormSubgroup
                    (QuotientGroup.mk'
                      (IdeleGroup.principalSubgroup K) a)))
          rw [
            GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk,
            GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk,
            IdeleGroup.idealClass_extension]

end SmallHilbertIdeleExtension

end IdealClassFieldTheory
end GlobalClassFieldTheory
