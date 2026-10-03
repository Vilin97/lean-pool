/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.CyclicNormConductor
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormRayClassMaximality
/-!
# Maximal cyclic quotients at the narrow finite conductor

For a finite cyclic extension, the actual idèle-class norm quotient has
order equal to the extension degree.  The ray class group at the exact
narrow finite conductor surjects onto this norm quotient.  This file
identifies the case in which that surjection is an isomorphism: precisely
when the ray class number already equals the extension degree.

Equivalently, the actual norm subgroup is then exactly the ray congruence
subgroup at its narrow finite conductor.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

/-- The canonical idèle-class multiplication makes every subgroup normal. -/
private theorem cyclicRayClassMaximalityClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] cyclicRayClassMaximalityClassGroupIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]

/-- The actual idèle-class norm subgroup of a finite cyclic extension is
the congruence subgroup at its exact narrow finite conductor precisely when
the corresponding ray class number equals the extension degree. -/
theorem
    ideleClassNorm_range_eq_congruenceSubgroup_iff_rayClassGroup_card_eq_extensionDegree :
    (_root_.ideleClassNorm K L).range =
        RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := L))) ↔
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))) =
        Module.finrank K L := by
  simpa only [
    ← Subgroup.index_eq_card,
    ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic K L] using
      (ideleClassNorm_range_eq_congruenceSubgroup_iff_rayClassGroup_card_eq_normQuotient_card
        (K := K) (L := L))

/-- The canonical map from the ray class group at the exact narrow finite
norm conductor to the actual norm quotient is injective precisely when the
ray class number equals the extension degree. -/
theorem
    rayClassToNormQuotient_injective_iff_card_eq_extensionDegree :
    Function.Injective
        (narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
          (K := K) (L := L)) ↔
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))) =
        Module.finrank K L := by
  simpa only [
    ← Subgroup.index_eq_card,
    ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic K L] using
      (rayClassToNormQuotient_injective_iff_card_eq_normQuotient_card
        (K := K) (L := L))

/-- When the ray class number at the exact narrow finite norm conductor
equals the degree of a finite cyclic extension, its actual norm quotient is
canonically the full ray class group at that conductor. -/
def cyclicNormQuotientEquivNarrowFiniteConductorRayClassGroup
    (hcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))) =
        Module.finrank K L) :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃*
      RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite
          (ideleClassNormNarrowFiniteConductor (K := K) (L := L))) :=
  normQuotientEquivNarrowFiniteConductorRayClassGroup
    (K := K) (L := L) <| by
      calc
        Nat.card
            (RayClass.RayClassGroup
              (RayClass.Modulus.narrowOfFinite
                (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))) =
            Module.finrank K L :=
          hcard
        _ = ((_root_.ideleClassNorm K L).range).index :=
          (ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic
            K L).symm
        _ =
            Nat.card
              (IdeleClassGroup K ⧸
                (_root_.ideleClassNorm K L).range) :=
          Subgroup.index_eq_card ((_root_.ideleClassNorm K L).range)

end GlobalClassFields
end GlobalClassFieldTheory
