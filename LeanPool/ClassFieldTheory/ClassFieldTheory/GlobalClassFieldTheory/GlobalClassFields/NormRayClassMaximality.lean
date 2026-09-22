/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
/-!
# Exact narrow finite ray-class presentations of norm quotients

For every finite Galois extension, the ray class group at the exact narrow
finite conductor surjects onto the actual idèle-class norm quotient.  This
file characterizes when that presentation has no residual kernel: the norm
subgroup is then exactly the congruence subgroup at its narrow finite
conductor, equivalently the two finite quotient groups have the same order.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

/-- Canonical class-group commutativity supplies normality for the quotient. -/
private theorem normRayClassMaximalityClassGroupIsMulCommutative
    (F : Type*) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] normRayClassMaximalityClassGroupIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The actual idèle-class norm subgroup is exactly the ray congruence
subgroup at its narrow finite conductor if and only if the conductor ray
class group and the actual norm quotient have the same order. -/
theorem
    ideleClassNorm_range_eq_narrowFiniteConductorCongruenceSubgroup_iff_rayClassGroup_card_eq_normQuotient_card :
    (_root_.ideleClassNorm K L).range =
        RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := L))) ↔
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) := by
  constructor
  · intro hnorm
    calc
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))) =
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))).index :=
        (Subgroup.index_eq_card _).symm
      _ = ((_root_.ideleClassNorm K L).range).index := by
        rw [← hnorm]
      _ =
          Nat.card
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range) :=
        Subgroup.index_eq_card _
  · intro hcard
    refine
      (eq_of_le_of_not_lt
        (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
          (K := K) (L := L))
        ?_).symm
    intro hlt
    have hstrict := Subgroup.index_strictAnti hlt
    have hstrict' :
        Nat.card
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range) <
          Nat.card
            (RayClass.RayClassGroup
              (RayClass.Modulus.narrowOfFinite
                (ideleClassNormNarrowFiniteConductor
                  (K := K) (L := L)))) := by
      simpa only [Subgroup.index_eq_card] using hstrict
    rw [hcard] at hstrict'
    exact lt_irrefl _ hstrict'

/-- The canonical narrow finite conductor ray-class map to the actual
idèle-class norm quotient is injective if and only if its finite source and
target have the same order. -/
theorem
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_injective_iff_card_eq_normQuotient_card :
    Function.Injective
        (narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
          (K := K) (L := L)) ↔
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) := by
  let f :=
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
      (K := K) (L := L)
  change Function.Injective f ↔ _
  have hfSurjective : Function.Surjective f :=
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_surjective
      (K := K) (L := L)
  constructor
  · intro hfInjective
    exact
      Nat.card_congr
        (Equiv.ofBijective f
          ⟨hfInjective, hfSurjective⟩)
  · intro hcard
    exact
      (hfSurjective.bijective_of_nat_card_le hcard.le).1

/-- If the narrow finite conductor ray class group and the actual
idèle-class norm quotient have the same order, the latter is canonically
the full ray class group at its narrow finite conductor. -/
def normQuotientEquivNarrowFiniteConductorRayClassGroup
    (hcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range)) :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃*
      RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite
          (ideleClassNormNarrowFiniteConductor (K := K) (L := L))) :=
  QuotientGroup.quotientMulEquivOfEq
    ((ideleClassNorm_range_eq_narrowFiniteConductorCongruenceSubgroup_iff_rayClassGroup_card_eq_normQuotient_card
      (K := K) (L := L)).2 hcard)

/-- Two finite Galois extensions with the same exact narrow finite
conductor and maximal ray-class presentations have the same actual
idèle-class norm subgroup. -/
theorem
    ideleClassNorm_ranges_eq_of_narrowFiniteConductors_eq_of_rayClassGroup_cards_eq_normQuotient_cards
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (hconductor :
      ideleClassNormNarrowFiniteConductor (K := K) (L := L) =
        ideleClassNormNarrowFiniteConductor (K := K) (L := M))
    (hLcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range))
    (hMcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := M)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K M).range)) :
    (_root_.ideleClassNorm K L).range =
      (_root_.ideleClassNorm K M).range := by
  calc
    (_root_.ideleClassNorm K L).range =
        RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := L))) :=
      (ideleClassNorm_range_eq_narrowFiniteConductorCongruenceSubgroup_iff_rayClassGroup_card_eq_normQuotient_card
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
      ((ideleClassNorm_range_eq_narrowFiniteConductorCongruenceSubgroup_iff_rayClassGroup_card_eq_normQuotient_card
        (K := K) (L := M)).2 hMcard).symm

/-- The actual norm quotients of two maximal narrow finite conductor
ray-class presentations with the same conductor are canonically equivalent.
-/
def normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (hconductor :
      ideleClassNormNarrowFiniteConductor (K := K) (L := L) =
        ideleClassNormNarrowFiniteConductor (K := K) (L := M))
    (hLcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range))
    (hMcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := M)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K M).range)) :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K M).range) :=
  QuotientGroup.quotientMulEquivOfEq
    (ideleClassNorm_ranges_eq_of_narrowFiniteConductors_eq_of_rayClassGroup_cards_eq_normQuotient_cards
      (K := K) (L := L) (M := M)
      hconductor hLcard hMcard)

/-- The canonical equivalence between maximal narrow finite conductor
ray-class norm quotients preserves every idèle-class representative. -/
theorem
    normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (hconductor :
      ideleClassNormNarrowFiniteConductor (K := K) (L := L) =
        ideleClassNormNarrowFiniteConductor (K := K) (L := M))
    (hLcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range))
    (hMcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := M)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K M).range))
    (c : IdeleClassGroup K) :
    normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards
        (K := K) (L := L) (M := M)
        hconductor hLcard hMcard
        (QuotientGroup.mk'
          ((_root_.ideleClassNorm K L).range) c) =
      QuotientGroup.mk'
        ((_root_.ideleClassNorm K M).range) c :=
  rfl

end GlobalClassFields
end GlobalClassFieldTheory
