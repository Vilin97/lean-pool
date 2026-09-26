/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.CyclicRayClassMaximality
/-!
# Uniqueness of maximal cyclic norm subgroups at a narrow finite conductor

Two finite cyclic extensions whose exact narrow finite conductors agree and
whose degrees exhaust the corresponding ray class number determine the same
actual idèle-class norm subgroup.  Thus their concrete norm quotients are
canonically equivalent.  This is the norm-subgroup uniqueness part of the
cyclic class-field correspondence at a fixed narrow finite conductor.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

private theorem cyclicConductorUniquenessIdeleClassIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] cyclicConductorUniquenessIdeleClassIsMulCommutative

variable
    {K L M : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K L] [IsGalois K L]
    [FiniteDimensional K M] [IsGalois K M]
    [IsCyclic (L ≃ₐ[K] L)]
    [IsCyclic (M ≃ₐ[K] M)]

/-- Maximal cyclic extensions with the same exact narrow finite conductor
have the same actual idèle-class norm subgroup. -/
theorem
    cyclicIdeleClassNorm_ranges_eq_of_conductors_eq_of_rayClassGroup_cards_eq_extensionDegrees
    (hconductor :
      ideleClassNormNarrowFiniteConductor (K := K) (L := L) =
        ideleClassNormNarrowFiniteConductor (K := K) (L := M))
    (hLcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))) =
        Module.finrank K L)
    (hMcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := M)))) =
        Module.finrank K M) :
    (_root_.ideleClassNorm K L).range =
      (_root_.ideleClassNorm K M).range := by
  calc
    (_root_.ideleClassNorm K L).range =
        RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := L))) :=
      (ideleClassNorm_range_eq_congruenceSubgroup_iff_rayClassGroup_card_eq_extensionDegree
        (K := K) (L := L)).2 hLcard
    _ =
        RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := M))) :=
      congrArg
        (fun f => RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite f))
        hconductor
    _ = (_root_.ideleClassNorm K M).range :=
      ((ideleClassNorm_range_eq_congruenceSubgroup_iff_rayClassGroup_card_eq_extensionDegree
        (K := K) (L := M)).2 hMcard).symm

/-- The actual norm quotients of two maximal cyclic extensions with the
same exact narrow finite conductor are canonically equivalent. -/
def cyclicNormQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqExtensionDegrees
    (hconductor :
      ideleClassNormNarrowFiniteConductor (K := K) (L := L) =
        ideleClassNormNarrowFiniteConductor (K := K) (L := M))
    (hLcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))) =
        Module.finrank K L)
    (hMcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := M)))) =
        Module.finrank K M) :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K M).range) :=
  QuotientGroup.quotientMulEquivOfEq
    (cyclicIdeleClassNorm_ranges_eq_of_conductors_eq_of_rayClassGroup_cards_eq_extensionDegrees
      (K := K) (L := L) (M := M)
      hconductor hLcard hMcard)

/-- The canonical equivalence between the two maximal cyclic norm quotients
preserves every idèle-class representative. -/
theorem
    cyclicNormQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqExtensionDegrees_mk
    (hconductor :
      ideleClassNormNarrowFiniteConductor (K := K) (L := L) =
        ideleClassNormNarrowFiniteConductor (K := K) (L := M))
    (hLcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))) =
        Module.finrank K L)
    (hMcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := M)))) =
        Module.finrank K M)
    (c : IdeleClassGroup K) :
    cyclicNormQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqExtensionDegrees
        (K := K) (L := L) (M := M)
        hconductor hLcard hMcard
        (QuotientGroup.mk'
          ((_root_.ideleClassNorm K L).range) c) =
      QuotientGroup.mk'
        ((_root_.ideleClassNorm K M).range) c :=
  rfl

/-- If two nested cyclic extensions have the same exact narrow finite
conductor and both exhaust its ray class group, then the upper extension
has relative degree one.  Thus a maximal cyclic class field at a fixed
narrow finite conductor has no proper nested cyclic overextension with the
same conductor. -/
theorem
    nestedMaximalCyclicExtensions_sameNarrowFiniteConductor_relativeDegree_eq_one
    [Algebra M L] [IsScalarTower K M L]
    [FiniteDimensional M L]
    (hconductor :
      ideleClassNormNarrowFiniteConductor (K := K) (L := L) =
        ideleClassNormNarrowFiniteConductor (K := K) (L := M))
    (hLcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))) =
        Module.finrank K L)
    (hMcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := M)))) =
        Module.finrank K M) :
    Module.finrank M L = 1 := by
  have hnorm :
      (_root_.ideleClassNorm K L).range =
        (_root_.ideleClassNorm K M).range :=
    cyclicIdeleClassNorm_ranges_eq_of_conductors_eq_of_rayClassGroup_cards_eq_extensionDegrees
      (K := K) (L := L) (M := M)
      hconductor hLcard hMcard
  have hdegree :
      Module.finrank K L = Module.finrank K M := by
    calc
      Module.finrank K L =
          (_root_.ideleClassNorm K L).range.index :=
        (ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic
          K L).symm
      _ = (_root_.ideleClassNorm K M).range.index :=
        congrArg
          (fun H : Subgroup (IdeleClassGroup K) => H.index)
          hnorm
      _ = Module.finrank K M :=
        ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic K M
  have hmul :
      Module.finrank K M * Module.finrank M L =
        Module.finrank K M := by
    calc
      Module.finrank K M * Module.finrank M L =
          Module.finrank K L :=
        Module.finrank_mul_finrank K M L
      _ = Module.finrank K M := hdegree
  apply
    Nat.mul_left_cancel
      (show 0 < Module.finrank K M from Module.finrank_pos)
  simpa only [mul_one] using hmul

/-- A proper nested cyclic overextension cannot remain maximal at the
same exact narrow finite conductor.  Hence maximal cyclic class fields in a
proper tower have distinct narrow finite conductors. -/
theorem
    nestedMaximalCyclicExtensions_narrowFiniteConductors_ne_of_relativeDegree_ne_one
    [Algebra M L] [IsScalarTower K M L]
    [FiniteDimensional M L]
    (hLcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := L)))) =
        Module.finrank K L)
    (hMcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor (K := K) (L := M)))) =
        Module.finrank K M)
    (hrelativeDegree :
      Module.finrank M L ≠ 1) :
    ideleClassNormNarrowFiniteConductor (K := K) (L := L) ≠
      ideleClassNormNarrowFiniteConductor (K := K) (L := M) := by
  intro hconductor
  exact
    hrelativeDegree
      (nestedMaximalCyclicExtensions_sameNarrowFiniteConductor_relativeDegree_eq_one
        (K := K) (L := L) (M := M)
        hconductor hLcard hMcard)

end GlobalClassFields
end GlobalClassFieldTheory
