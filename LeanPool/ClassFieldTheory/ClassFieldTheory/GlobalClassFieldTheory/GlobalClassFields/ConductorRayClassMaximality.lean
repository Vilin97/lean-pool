/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorLattice
/-!
# Exact narrow finite conductor ray-class presentations

For a conductorial subgroup `H` of the idèle class group, the ray class
group at its exact narrow finite conductor maps canonically onto `C_K / H`.
This file characterizes injectivity of that map by equality of the two
finite orders and proves uniqueness of subgroups whose exact narrow finite
conductor ray-class presentations are maximal.
-/

@[expose] public section

open scoped IsMulCommutative NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable {K : Type} [Field K] [NumberField K]

/-- Fix the canonical commutative structure used to infer normality of
subgroups of the idèle class group in this module. -/
local instance
    conductorRayClassMaximality_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

namespace ConductorialSubgroup

/-- The canonical quotient map from the ray class group at the exact
narrow finite conductor of `H` onto `C_K / H`. -/
noncomputable def narrowFiniteConductorRayClassGroupToQuotient
    (H : ConductorialSubgroup K) :
    RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) →*
      IdeleClassGroup K ⧸ H.1 :=
  QuotientGroup.map
    (RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor))
    H.1
    (MonoidHom.id _)
    (show
      RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) ≤
        Subgroup.comap (MonoidHom.id _) H.1 from by
      intro x hx
      change x ∈ H.1
      exact H.narrowFiniteConductor_isDefiningModulus hx)

/-- The exact narrow finite conductor quotient map preserves every
idèle-class representative. -/
theorem narrowFiniteConductorRayClassGroupToQuotient_mk
    (H : ConductorialSubgroup K)
    (c : IdeleClassGroup K) :
    H.narrowFiniteConductorRayClassGroupToQuotient
      (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) c) =
      QuotientGroup.mk' H.1 c :=
  rfl

/-- The exact narrow finite conductor ray-class map onto `C_K / H` is
surjective. -/
theorem narrowFiniteConductorRayClassGroupToQuotient_surjective
    (H : ConductorialSubgroup K) :
    Function.Surjective H.narrowFiniteConductorRayClassGroupToQuotient := by
  intro q
  obtain ⟨c, rfl⟩ :=
    QuotientGroup.mk'_surjective H.1 q
  exact
    ⟨QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) c,
      rfl⟩

/-- The kernel of the exact narrow finite conductor ray-class map is the
image of `H` modulo the conductor congruence subgroup. -/
theorem narrowFiniteConductorRayClassGroupToQuotient_ker
    (H : ConductorialSubgroup K) :
    MonoidHom.ker H.narrowFiniteConductorRayClassGroupToQuotient =
      Subgroup.map
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)))
        H.1 := by
  unfold narrowFiniteConductorRayClassGroupToQuotient
  let N :=
    RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)
  let M := H.1
  change
    (QuotientGroup.map N M (MonoidHom.id (IdeleClassGroup K)) _).ker =
      Subgroup.map (QuotientGroup.mk' N) M
  simpa only [Subgroup.comap_id] using
    (QuotientGroup.ker_map (N := N) M
      (MonoidHom.id (IdeleClassGroup K))
      (show N ≤ Subgroup.comap (MonoidHom.id (IdeleClassGroup K)) M from
        fun _ hx => H.narrowFiniteConductor_isDefiningModulus hx))

/-- Quotienting the exact narrow finite conductor ray class group by the
image of `H` recovers `C_K / H`. -/
noncomputable def
    narrowFiniteConductorRayClassSubgroupQuotientEquivIdeleClassQuotient
    (H : ConductorialSubgroup K) :
    (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) ⧸
        Subgroup.map
          (QuotientGroup.mk'
            (RayClass.Modulus.congruenceSubgroup
              (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)))
          H.1) ≃*
      IdeleClassGroup K ⧸ H.1 :=
  (QuotientGroup.quotientMulEquivOfEq
      H.narrowFiniteConductorRayClassGroupToQuotient_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      H.narrowFiniteConductorRayClassGroupToQuotient
      H.narrowFiniteConductorRayClassGroupToQuotient_surjective)

/-- The exact narrow finite conductor ray class number factors as the
order of the image of `H` modulo conductor congruence times the order of
`C_K / H`. -/
theorem
    narrowFiniteConductorRayClassGroup_card_eq_subgroupImage_card_mul_quotient_card
    (H : ConductorialSubgroup K) :
    Nat.card (RayClass.RayClassGroup
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
      Nat.card
          (Subgroup.map
            (QuotientGroup.mk'
              (RayClass.Modulus.congruenceSubgroup
                (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)))
            H.1) *
        Nat.card (IdeleClassGroup K ⧸ H.1) := by
  let f := H.narrowFiniteConductorRayClassGroupToQuotient
  have hf : Function.Surjective f :=
    H.narrowFiniteConductorRayClassGroupToQuotient_surjective
  calc
    Nat.card (RayClass.RayClassGroup
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (MonoidHom.ker f) *
          (MonoidHom.ker f).index :=
      (Subgroup.card_mul_index (MonoidHom.ker f)).symm
    _ = Nat.card (MonoidHom.ker f) * Nat.card f.range := by
      rw [Subgroup.index_ker f]
    _ = Nat.card (MonoidHom.ker f) *
        Nat.card (IdeleClassGroup K ⧸ H.1) := by
      rw [f.range_eq_top_of_surjective hf, Subgroup.card_top]
    _ =
        Nat.card
            (Subgroup.map
              (QuotientGroup.mk'
                (RayClass.Modulus.congruenceSubgroup
                  (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)))
              H.1) *
          Nat.card (IdeleClassGroup K ⧸ H.1) := by
      rw [H.narrowFiniteConductorRayClassGroupToQuotient_ker]

/-- The order of `C_K / H` divides the ray class number at the exact
narrow finite conductor of `H`. -/
theorem ideleClassQuotient_card_dvd_narrowFiniteConductorRayClassGroup_card
    (H : ConductorialSubgroup K) :
      Nat.card (IdeleClassGroup K ⧸ H.1) ∣
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) := by
  simpa only [Subgroup.index_eq_card] using
    Subgroup.index_dvd_of_le H.narrowFiniteConductor_isDefiningModulus

/-- The exact narrow finite conductor ray-class map is injective exactly
when its finite source and target have the same order. -/
theorem narrowFiniteConductorRayClassGroupToQuotient_injective_iff_card_eq
    (H : ConductorialSubgroup K) :
    Function.Injective H.narrowFiniteConductorRayClassGroupToQuotient ↔
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1) := by
  let f := H.narrowFiniteConductorRayClassGroupToQuotient
  have hfSurjective : Function.Surjective f :=
    H.narrowFiniteConductorRayClassGroupToQuotient_surjective
  constructor
  · intro hfInjective
    exact
      Nat.card_congr
        (Equiv.ofBijective f
          ⟨hfInjective, hfSurjective⟩)
  · intro hcard
    exact
      (hfSurjective.bijective_of_nat_card_le hcard.le).1

/-- When the exact narrow finite conductor ray class group and `C_K / H`
have the same order, the canonical quotient map is a multiplicative
equivalence. -/
noncomputable def narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq
    (H : ConductorialSubgroup K)
    (hcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1)) :
    RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) ≃*
      IdeleClassGroup K ⧸ H.1 :=
  MulEquiv.ofBijective
    H.narrowFiniteConductorRayClassGroupToQuotient
    ⟨H.narrowFiniteConductorRayClassGroupToQuotient_injective_iff_card_eq.2
        hcard,
      H.narrowFiniteConductorRayClassGroupToQuotient_surjective⟩

/-- The maximal exact narrow finite conductor equivalence preserves every
idèle-class representative. -/
theorem narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk
    (H : ConductorialSubgroup K)
    (hcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1))
    (c : IdeleClassGroup K) :
    H.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq
        hcard
      (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) c) =
      QuotientGroup.mk' H.1 c :=
  rfl

/-- A conductorial subgroup is exactly the congruence subgroup at its
narrow finite conductor precisely when its quotient has the full exact
narrow finite conductor ray class number. -/
theorem
    subgroup_eq_conductorCongruenceSubgroup_iff_rayClass_card_eq_quotient_card
    (H : ConductorialSubgroup K) :
    H.1 = RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) ↔
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1) := by
  constructor
  · intro hH
    calc
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)).index :=
        (Subgroup.index_eq_card _).symm
      _ = H.1.index := by
        rw [← hH]
      _ = Nat.card (IdeleClassGroup K ⧸ H.1) :=
        Subgroup.index_eq_card H.1
  · intro hcard
    let f := H.narrowFiniteConductorRayClassGroupToQuotient
    have hfInjective : Function.Injective f :=
      H.narrowFiniteConductorRayClassGroupToQuotient_injective_iff_card_eq.2
        hcard
    apply le_antisymm
    · intro c hc
      have hfc :
          f
              (QuotientGroup.mk'
                (RayClass.Modulus.congruenceSubgroup
                  (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) c) =
            1 := by
        change QuotientGroup.mk' H.1 c = 1
        exact (QuotientGroup.eq_one_iff _).2 hc
      have hcOne :
          QuotientGroup.mk'
              (RayClass.Modulus.congruenceSubgroup
                (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) c =
            1 :=
        hfInjective (hfc.trans (map_one f).symm)
      exact (QuotientGroup.eq_one_iff _).1 hcOne
    · exact H.narrowFiniteConductor_isDefiningModulus

/-- Conductorial subgroups with the same exact narrow finite conductor
and maximal exact-conductor ray-class presentations have equal underlying
subgroups. -/
theorem
    subgroups_eq_of_narrowFiniteConductors_eq_of_rayClassGroup_cards_eq_quotient_cards
    (H J : ConductorialSubgroup K)
    (hconductor : H.narrowFiniteConductor = J.narrowFiniteConductor)
    (hHcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1))
    (hJcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite J.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ J.1)) :
    H.1 = J.1 := by
  calc
    H.1 = RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) :=
      H.subgroup_eq_conductorCongruenceSubgroup_iff_rayClass_card_eq_quotient_card.2
        hHcard
    _ = RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite J.narrowFiniteConductor) :=
      congrArg
        (fun f => RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite f))
        hconductor
    _ = J.1 :=
      (J.subgroup_eq_conductorCongruenceSubgroup_iff_rayClass_card_eq_quotient_card.2
        hJcard).symm

/-- The quotients by two maximal exact narrow finite conductor subgroups
with the same conductor are canonically equivalent. -/
def ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards
    (H J : ConductorialSubgroup K)
    (hconductor : H.narrowFiniteConductor = J.narrowFiniteConductor)
    (hHcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1))
    (hJcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite J.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ J.1)) :
    (IdeleClassGroup K ⧸ H.1) ≃*
      (IdeleClassGroup K ⧸ J.1) :=
  QuotientGroup.quotientMulEquivOfEq
    (H.subgroups_eq_of_narrowFiniteConductors_eq_of_rayClassGroup_cards_eq_quotient_cards
      J hconductor hHcard hJcard)

/-- The canonical equivalence between maximal exact narrow finite
conductor quotients preserves every idèle-class representative. -/
theorem
    ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk
    (H J : ConductorialSubgroup K)
    (hconductor : H.narrowFiniteConductor = J.narrowFiniteConductor)
    (hHcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1))
    (hJcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite J.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ J.1))
    (c : IdeleClassGroup K) :
    H.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards
        J hconductor hHcard hJcard
        (QuotientGroup.mk' H.1 c) =
      QuotientGroup.mk' J.1 c :=
  rfl

end ConductorialSubgroup

end GlobalClassFields
end GlobalClassFieldTheory
