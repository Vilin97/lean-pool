/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Narrow
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
import Mathlib.NumberTheory.NumberField.ClassNumber
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassField
/-!
# The small Hilbert class field

The small Hilbert class field corresponds to the image in the idele class
group of the ideles integral at every finite place.  Its reciprocity
quotient is canonically the ordinary ideal class group; consequently its
order is the class number.
-/

open scoped NumberField IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Fix the canonical commutative idèle-class structure used by the Hilbert
class-field quotients in this module. -/
local instance smallHilbertClassFieldIdeleClassGroupIsMulCommutative
    {F : Type*} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The norm subgroup defining the small Hilbert class field.  The
principal subgroup is included before passing to the idele class group so
that the third-isomorphism equivalence applies literally. -/
def smallHilbertClassFieldNormSubgroup :
    Subgroup (IdeleClassGroup K) :=
  Subgroup.map
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup K))
    (IdeleGroup.integralAtFinitePlaces (K := K) ⊔
      IdeleGroup.principalSubgroup K)

/-- The quotient by the small-Hilbert norm subgroup is the ordinary ideal
class group. -/
def smallHilbertClassFieldQuotientEquivClassGroup :
    IdeleClassGroup K ⧸
        smallHilbertClassFieldNormSubgroup (K := K) ≃*
      ClassGroup (𝓞 K) :=
  (QuotientGroup.quotientQuotientEquivQuotient
      (IdeleGroup.principalSubgroup K)
      (IdeleGroup.integralAtFinitePlaces (K := K) ⊔
        IdeleGroup.principalSubgroup K)
      le_sup_right).trans
    (IdeleGroup.quotientIntegralSupPrincipalEquiv (K := K))

/-- The small-Hilbert norm subgroup is open. -/
theorem smallHilbertClassFieldNormSubgroup_isOpen :
    IsOpen
      ((smallHilbertClassFieldNormSubgroup (K := K) :
        Subgroup (IdeleClassGroup K)) :
        Set (IdeleClassGroup K)) := by
  have hzero :
      (0 : RayClass.Modulus K).ideleCongruenceSubgroup ≤
        IdeleGroup.integralAtFinitePlaces (K := K) :=
    by
      intro a ha
      change a.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K)
      rw [← RayClass.finiteCongruenceSubgroup_zero (K := K)]
      exact ha.2
  have hden :
      (0 : RayClass.Modulus K).ideleCongruenceSubgroup ≤
        IdeleGroup.integralAtFinitePlaces (K := K) ⊔
          IdeleGroup.principalSubgroup K :=
    hzero.trans le_sup_left
  have hopen :
      IsOpen
        (((IdeleGroup.integralAtFinitePlaces (K := K) ⊔
          IdeleGroup.principalSubgroup K) :
          Subgroup (IdeleGroup K)) :
          Set (IdeleGroup K)) :=
    Subgroup.isOpen_mono hden
      (RayClass.isOpen_ideleCongruenceSubgroup 0)
  rw [smallHilbertClassFieldNormSubgroup, Subgroup.coe_map]
  exact QuotientGroup.isOpenMap_coe _ hopen

/-- The small-Hilbert norm subgroup is closed. -/
theorem smallHilbertClassFieldNormSubgroup_isClosed :
    IsClosed
      ((smallHilbertClassFieldNormSubgroup (K := K) :
        Subgroup (IdeleClassGroup K)) :
        Set (IdeleClassGroup K)) :=
  (smallHilbertClassFieldNormSubgroup (K := K)).isClosed_of_isOpen
    smallHilbertClassFieldNormSubgroup_isOpen

/-- The small-Hilbert norm subgroup has finite index. -/
instance smallHilbertClassFieldNormSubgroupFiniteIndex :
    (smallHilbertClassFieldNormSubgroup (K := K)).FiniteIndex := by
  let : Finite
      (IdeleClassGroup K ⧸
        smallHilbertClassFieldNormSubgroup (K := K)) :=
    Finite.of_equiv (ClassGroup (𝓞 K))
      (smallHilbertClassFieldQuotientEquivClassGroup
        (K := K)).symm.toEquiv
  exact Subgroup.finiteIndex_of_finite_quotient

/-- The order of the small-Hilbert reciprocity quotient is the class
number of `K`. -/
theorem smallHilbertClassFieldQuotient_card_eq_classNumber :
    Nat.card
        (IdeleClassGroup K ⧸
          smallHilbertClassFieldNormSubgroup (K := K)) =
      NumberField.classNumber K := by
  rw [NumberField.classNumber]
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    (smallHilbertClassFieldQuotientEquivClassGroup (K := K)).toEquiv

/-- The big-Hilbert norm subgroup is contained in the small-Hilbert
norm subgroup.  Under class-field duality this is the inclusion of the
small Hilbert class field into the big Hilbert class field. -/
theorem
    bigHilbertClassFieldNormSubgroup_le_smallHilbertClassFieldNormSubgroup :
    bigHilbertClassFieldNormSubgroup (K := K) ≤
      smallHilbertClassFieldNormSubgroup (K := K) := by
  rw [bigHilbertClassFieldNormSubgroup,
    RayClass.Modulus.congruenceSubgroup,
    smallHilbertClassFieldNormSubgroup]
  apply Subgroup.map_mono
  exact sup_le
    ((RayClass.narrowIdeleCongruenceSubgroup_zero_le_integral
      (K := K)).trans le_sup_left)
    le_sup_right

/-- Modulus zero is a defining modulus for the small-Hilbert norm
subgroup. -/
theorem smallHilbertClassFieldNormSubgroup_isDefiningModulus :
    IsDefiningModulus
      (smallHilbertClassFieldNormSubgroup (K := K))
      (0 : RayClass.Modulus K) := by
  have hzero :
      (0 : RayClass.Modulus K).ideleCongruenceSubgroup ≤
        IdeleGroup.integralAtFinitePlaces (K := K) := by
    intro a ha
    change a.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K)
    rw [← RayClass.finiteCongruenceSubgroup_zero (K := K)]
    exact ha.2
  rw [IsDefiningModulus,
    RayClass.Modulus.congruenceSubgroup,
    smallHilbertClassFieldNormSubgroup]
  exact Subgroup.map_mono (sup_le (hzero.trans le_sup_left) le_sup_right)

/-- The conductorial subgroup supplied by the intrinsic small-Hilbert norm
subgroup and its zero defining modulus. -/
noncomputable def smallHilbertClassFieldConductorialSubgroup :
    ConductorialSubgroup K :=
  ⟨smallHilbertClassFieldNormSubgroup (K := K),
    ⟨0, smallHilbertClassFieldNormSubgroup_isDefiningModulus (K := K)⟩⟩

/-- The canonical quotient transition from the big-Hilbert reciprocity
quotient onto the small-Hilbert reciprocity quotient. -/
noncomputable def
    bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient :
    (IdeleClassGroup K ⧸
        bigHilbertClassFieldNormSubgroup (K := K)) →*
      (IdeleClassGroup K ⧸
        smallHilbertClassFieldNormSubgroup (K := K)) :=
  QuotientGroup.map
    (bigHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup (K := K))
    (MonoidHom.id _)
    (show
      bigHilbertClassFieldNormSubgroup (K := K) ≤
        Subgroup.comap (MonoidHom.id _)
          (smallHilbertClassFieldNormSubgroup (K := K)) from by
      intro x hx
      change x ∈ smallHilbertClassFieldNormSubgroup (K := K)
      exact
        bigHilbertClassFieldNormSubgroup_le_smallHilbertClassFieldNormSubgroup
          (K := K) hx)

/-- The big-to-small Hilbert quotient transition sends the class of an
idele class to the same class modulo the larger norm subgroup. -/
theorem bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk
    (x : IdeleClassGroup K) :
    bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
        (K := K)
        (QuotientGroup.mk'
          (bigHilbertClassFieldNormSubgroup (K := K)) x) =
      QuotientGroup.mk'
        (smallHilbertClassFieldNormSubgroup (K := K)) x :=
  rfl

/-- The canonical transition from the big-Hilbert quotient to the
small-Hilbert quotient is surjective. -/
theorem
    bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_surjective :
    Function.Surjective
      (bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
        (K := K)) := by
  intro q
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (smallHilbertClassFieldNormSubgroup (K := K)) q
  exact
    ⟨QuotientGroup.mk'
        (bigHilbertClassFieldNormSubgroup (K := K)) x, rfl⟩

/-- The kernel of the canonical big-to-small Hilbert quotient transition
is the image of the small-Hilbert norm subgroup modulo the big-Hilbert
norm subgroup. -/
theorem
    bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_ker :
    MonoidHom.ker
        (bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
          (K := K)) =
      Subgroup.map
        (QuotientGroup.mk'
          (bigHilbertClassFieldNormSubgroup (K := K)))
        (smallHilbertClassFieldNormSubgroup (K := K)) := by
  unfold bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
  rw [QuotientGroup.ker_map, Subgroup.comap_id]

/-- The order of the small-Hilbert reciprocity quotient divides the
order of the big-Hilbert reciprocity quotient. -/
theorem smallHilbertClassFieldQuotient_card_dvd_bigHilbertClassFieldQuotient_card :
    Nat.card
        (IdeleClassGroup K ⧸
          smallHilbertClassFieldNormSubgroup (K := K)) ∣
      Nat.card
        (IdeleClassGroup K ⧸
          bigHilbertClassFieldNormSubgroup (K := K)) := by
  simpa only [Subgroup.index_eq_card] using
    Subgroup.index_dvd_of_le
      (bigHilbertClassFieldNormSubgroup_le_smallHilbertClassFieldNormSubgroup
        (K := K))

/-- The class number divides the order of the narrow class group. -/
theorem classNumber_dvd_narrowClassGroup_card :
    NumberField.classNumber K ∣
      Nat.card (RayClass.NarrowClassGroup K) := by
  calc
    NumberField.classNumber K =
        Nat.card
          (IdeleClassGroup K ⧸
            smallHilbertClassFieldNormSubgroup (K := K)) :=
      (smallHilbertClassFieldQuotient_card_eq_classNumber
        (K := K)).symm
    _ ∣
        Nat.card
          (IdeleClassGroup K ⧸
            bigHilbertClassFieldNormSubgroup (K := K)) :=
      smallHilbertClassFieldQuotient_card_dvd_bigHilbertClassFieldQuotient_card
        (K := K)
    _ = Nat.card (RayClass.NarrowClassGroup K) :=
      Nat.card_congr
        (bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := K)).toEquiv

/-- The kernel of the big-to-small Hilbert quotient transition measures
the exact difference between the narrow and ordinary class numbers. -/
theorem narrowClassGroup_card_eq_bigToSmallKernel_card_mul_classNumber :
    Nat.card (RayClass.NarrowClassGroup K) =
      Nat.card
          (MonoidHom.ker
            (bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
              (K := K))) *
        NumberField.classNumber K := by
  let f :=
    bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
      (K := K)
  change
    Nat.card (RayClass.NarrowClassGroup K) =
      Nat.card (MonoidHom.ker f) *
        NumberField.classNumber K
  have hf : Function.Surjective f :=
    bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_surjective
      (K := K)
  calc
    Nat.card (RayClass.NarrowClassGroup K) =
        Nat.card
          (IdeleClassGroup K ⧸
            bigHilbertClassFieldNormSubgroup (K := K)) :=
      (Nat.card_congr
        (bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := K)).toEquiv).symm
    _ = Nat.card (MonoidHom.ker f) *
        (MonoidHom.ker f).index :=
      (Subgroup.card_mul_index (MonoidHom.ker f)).symm
    _ = Nat.card (MonoidHom.ker f) *
        Nat.card f.range := by
      rw [Subgroup.index_ker f]
    _ = Nat.card (MonoidHom.ker f) *
        Nat.card
          (IdeleClassGroup K ⧸
            smallHilbertClassFieldNormSubgroup (K := K)) := by
      rw [f.range_eq_top_of_surjective hf, Subgroup.card_top]
    _ = Nat.card (MonoidHom.ker f) *
        NumberField.classNumber K := by
      rw [smallHilbertClassFieldQuotient_card_eq_classNumber]

/-- The exact difference between the narrow and ordinary class numbers
is the order of the image of the small-Hilbert norm subgroup in the
big-Hilbert reciprocity quotient. -/
theorem
    narrowClassGroup_card_eq_smallHilbertNormImage_card_mul_classNumber :
    Nat.card (RayClass.NarrowClassGroup K) =
      Nat.card
          (Subgroup.map
            (QuotientGroup.mk'
              (bigHilbertClassFieldNormSubgroup (K := K)))
            (smallHilbertClassFieldNormSubgroup (K := K))) *
        NumberField.classNumber K := by
  rw [narrowClassGroup_card_eq_bigToSmallKernel_card_mul_classNumber,
    bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_ker]

/-- The narrow finite conductor of the small-Hilbert norm subgroup is zero. -/
@[simp]
theorem smallHilbertClassField_narrowFiniteConductor :
    (smallHilbertClassFieldConductorialSubgroup
      (K := K)).narrowFiniteConductor = 0 := by
  apply le_antisymm
  · exact
      (smallHilbertClassFieldConductorialSubgroup
        (K := K)).narrowFiniteConductor_le
        (smallHilbertClassFieldNormSubgroup_isDefiningModulus (K := K))
  · exact bot_le

end GlobalClassFields
end GlobalClassFieldTheory
