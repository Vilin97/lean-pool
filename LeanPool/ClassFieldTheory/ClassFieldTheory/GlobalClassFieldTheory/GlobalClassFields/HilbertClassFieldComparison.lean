/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassField
/-!
# Comparison of the big and small Hilbert class fields

This file identifies the canonical transition from the big-Hilbert
reciprocity quotient to the small-Hilbert reciprocity quotient with the
canonical map from the narrow class group to the ordinary class group.
It then transports the archimedean sign exact sequence to a precise
description of the kernel of that transition.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Fix the canonical commutativity needed for Hilbert norm-subgroup
quotients in this module. -/
private theorem hilbertClassFieldComparison_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] hilbertClassFieldComparison_ideleClassGroupIsMulCommutative

/-- Keep the real-sign quotient normality instance stable across declarations. -/
local instance
    hilbertClassFieldComparison_realSignGroupIsMulCommutative :
    IsMulCommutative (RayClass.realSignGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- On an idele representative, the big-Hilbert quotient equivalence is
the canonical representative in the narrow class group. -/
@[simp]
theorem bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk
    (a : IdeleGroup K) :
    bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K)
        (QuotientGroup.mk'
          (bigHilbertClassFieldNormSubgroup (K := K))
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      QuotientGroup.mk'
        (RayClass.narrowDenominator (K := K)) a := by
  rfl

/-- On an idele representative, the small-Hilbert quotient equivalence is
the ordinary ideal-class map. -/
@[simp]
theorem smallHilbertClassFieldQuotientEquivClassGroup_mk
    (a : IdeleGroup K) :
    smallHilbertClassFieldQuotientEquivClassGroup
        (K := K)
        (QuotientGroup.mk'
          (smallHilbertClassFieldNormSubgroup (K := K))
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      IdeleGroup.idealClass a := by
  rfl

/-- Under the canonical quotient equivalences, the big-to-small Hilbert
transition is the map from the narrow class group to the ordinary class
group. -/
theorem bigToSmallHilbertQuotient_compatible_with_narrowToClassGroup
    (q : IdeleClassGroup K ⧸
      bigHilbertClassFieldNormSubgroup (K := K)) :
    smallHilbertClassFieldQuotientEquivClassGroup
        (K := K)
        (bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
          (K := K) q) =
      RayClass.narrowToClassGroup
        (bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := K) q) := by
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (bigHilbertClassFieldNormSubgroup (K := K)) q
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (IdeleGroup.principalSubgroup K) x
  rw [bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk,
    smallHilbertClassFieldQuotientEquivClassGroup_mk,
    bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk,
    RayClass.narrowToClassGroup_mk]

/-- Homomorphism form of the compatibility between the Hilbert quotient
transition and the narrow-to-ordinary class-group map. -/
theorem bigToSmallHilbertQuotient_compatibility :
    (smallHilbertClassFieldQuotientEquivClassGroup
        (K := K)).toMonoidHom.comp
        (bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
          (K := K)) =
      (RayClass.narrowToClassGroup (K := K)).comp
        (bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := K)).toMonoidHom := by
  ext q
  exact
    bigToSmallHilbertQuotient_compatible_with_narrowToClassGroup
      (K := K) q

/-- The canonical map from real sign classes to the big-Hilbert
reciprocity quotient. -/
def realSignToBigHilbertClassFieldQuotient :
    RayClass.realSignGroup K →*
      (IdeleClassGroup K ⧸
        bigHilbertClassFieldNormSubgroup (K := K)) :=
  (bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K)).symm.toMonoidHom.comp
    (RayClass.signToNarrow (K := K))

/-- The real-sign map to the big-Hilbert quotient is the composite used in
its definition. -/
@[simp]
theorem realSignToBigHilbertClassFieldQuotient_apply
    (s : RayClass.realSignGroup K) :
    realSignToBigHilbertClassFieldQuotient (K := K) s =
      (bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K)).symm
          (RayClass.signToNarrow (K := K) s) :=
  rfl

/-- The kernel of the real-sign map to the big-Hilbert quotient is the
image of the sign classes of global integral units. -/
theorem
    integralUnitSign_range_eq_realSignToBigHilbertClassFieldQuotient_ker :
    (RayClass.integralUnitSignToRealSign (K := K)).range =
      (realSignToBigHilbertClassFieldQuotient (K := K)).ker := by
  calc
    (RayClass.integralUnitSignToRealSign (K := K)).range =
        (RayClass.signToNarrow (K := K)).ker :=
      RayClass.integralUnitSignToRealSign_range_eq_signToNarrow_ker
        (K := K)
    _ = (realSignToBigHilbertClassFieldQuotient (K := K)).ker := by
      ext s
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      change
        RayClass.signToNarrow (K := K) s = 1 ↔
          (bigHilbertClassFieldQuotientEquivNarrowClassGroup
            (K := K)).symm
              (RayClass.signToNarrow (K := K) s) = 1
      constructor
      · intro hs
        rw [hs, map_one]
      · intro hs
        apply
          (bigHilbertClassFieldQuotientEquivNarrowClassGroup
            (K := K)).symm.injective
        simpa only [map_one] using hs

private theorem
    realSignToBigHilbertClassFieldQuotient_range_le_bigToSmallHilbertKernel :
    (realSignToBigHilbertClassFieldQuotient (K := K)).range ≤
      MonoidHom.ker
        (bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
          (K := K)) := by
  rintro q ⟨s, rfl⟩
  rw [MonoidHom.mem_ker]
  apply
    (smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)).injective
  rw [
    bigToSmallHilbertQuotient_compatible_with_narrowToClassGroup,
    realSignToBigHilbertClassFieldQuotient_apply,
    (bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K)).apply_symm_apply,
    map_one]
  apply MonoidHom.mem_ker.mp
  rw [← RayClass.signToNarrow_range_eq_narrowToClassGroup_ker]
  exact ⟨s, rfl⟩

private theorem
    bigToSmallHilbertKernel_le_realSignToBigHilbertClassFieldQuotient_range :
    MonoidHom.ker
        (bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
          (K := K)) ≤
      (realSignToBigHilbertClassFieldQuotient (K := K)).range := by
  intro q hq
  have hnarrow :
      bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := K) q ∈
        (RayClass.narrowToClassGroup (K := K)).ker := by
    rw [MonoidHom.mem_ker]
    rw [←
      bigToSmallHilbertQuotient_compatible_with_narrowToClassGroup
        (K := K) q]
    rw [MonoidHom.mem_ker.mp hq, map_one]
  have hsign :
      bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := K) q ∈
        (RayClass.signToNarrow (K := K)).range := by
    rw [RayClass.signToNarrow_range_eq_narrowToClassGroup_ker]
    exact hnarrow
  obtain ⟨s, hs⟩ := hsign
  refine ⟨s, ?_⟩
  change
    (bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K)).symm
        (RayClass.signToNarrow (K := K) s) = q
  rw [hs,
    (bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K)).symm_apply_apply]

/-- The image of the real-sign map in the big-Hilbert quotient is
exactly the kernel of the transition to the small-Hilbert quotient. -/
theorem
    realSignToBigHilbertClassFieldQuotient_range_eq_bigToSmallHilbertKernel :
    (realSignToBigHilbertClassFieldQuotient (K := K)).range =
      MonoidHom.ker
        (bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
          (K := K)) := by
  exact le_antisymm
    (realSignToBigHilbertClassFieldQuotient_range_le_bigToSmallHilbertKernel
      (K := K))
    (bigToSmallHilbertKernel_le_realSignToBigHilbertClassFieldQuotient_range
      (K := K))

/-- The archimedean sign exact sequence written directly on the big and
small Hilbert reciprocity quotients:

`1 → unit signs → real signs → big Hilbert quotient
  → small Hilbert quotient → 1`. -/
theorem hilbertClassFieldSign_exact_sequence :
    Function.Injective
        (RayClass.integralUnitSignToRealSign (K := K)) ∧
      (RayClass.integralUnitSignToRealSign (K := K)).range =
        (realSignToBigHilbertClassFieldQuotient (K := K)).ker ∧
      (realSignToBigHilbertClassFieldQuotient (K := K)).range =
        MonoidHom.ker
          (bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
            (K := K)) ∧
      Function.Surjective
        (bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
          (K := K)) := by
  exact
    ⟨RayClass.integralUnitSignToRealSign_injective,
      integralUnitSign_range_eq_realSignToBigHilbertClassFieldQuotient_ker
        (K := K),
      realSignToBigHilbertClassFieldQuotient_range_eq_bigToSmallHilbertKernel
        (K := K),
      bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_surjective
        (K := K)⟩

private theorem bigHilbertQuotientEquiv_mem_narrowClassKernel
    (q : MonoidHom.ker
      (bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
        (K := K))) :
    bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K) q.1 ∈
      MonoidHom.ker (RayClass.narrowToClassGroup (K := K)) := by
  rw [MonoidHom.mem_ker]
  rw [←
    bigToSmallHilbertQuotient_compatible_with_narrowToClassGroup
      (K := K) q.1]
  rw [MonoidHom.mem_ker.mp q.2, map_one]

private theorem bigHilbertQuotientEquiv_symm_mem_bigToSmallKernel
    (c : MonoidHom.ker
      (RayClass.narrowToClassGroup (K := K))) :
    (bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K)).symm c.1 ∈
      MonoidHom.ker
        (bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
          (K := K)) := by
  rw [MonoidHom.mem_ker]
  apply
    (smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)).injective
  rw [
    bigToSmallHilbertQuotient_compatible_with_narrowToClassGroup,
    (bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K)).apply_symm_apply,
    MonoidHom.mem_ker.mp c.2, map_one]

/-- The kernel of the big-to-small Hilbert quotient transition is
canonically the kernel of the map from narrow to ordinary ideal classes. -/
def bigToSmallHilbertKernelEquivNarrowClassKernel :
    MonoidHom.ker
        (bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
          (K := K)) ≃*
      MonoidHom.ker (RayClass.narrowToClassGroup (K := K)) where
  toFun q :=
    ⟨bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K) q.1,
      bigHilbertQuotientEquiv_mem_narrowClassKernel
        (K := K) q⟩
  invFun c :=
    ⟨(bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K)).symm c.1,
      bigHilbertQuotientEquiv_symm_mem_bigToSmallKernel
        (K := K) c⟩
  left_inv q := by
    apply Subtype.ext
    exact
      (bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K)).symm_apply_apply q.1
  right_inv c := by
    apply Subtype.ext
    exact
      (bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K)).apply_symm_apply c.1
  map_mul' q r := by
    apply Subtype.ext
    exact
      (bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K)).map_mul q.1 r.1

private theorem signToNarrow_mem_narrowClassKernel
    (s : RayClass.realSignGroup K) :
    RayClass.signToNarrow (K := K) s ∈
      MonoidHom.ker (RayClass.narrowToClassGroup (K := K)) := by
  rw [←
    RayClass.signToNarrow_range_eq_narrowToClassGroup_ker
      (K := K)]
  exact ⟨s, rfl⟩

/-- The real-sign map with codomain restricted to the kernel of the
narrow-to-ordinary class-group map. -/
def realSignToNarrowClassKernel :
    RayClass.realSignGroup K →*
      MonoidHom.ker (RayClass.narrowToClassGroup (K := K)) where
  toFun s :=
    ⟨RayClass.signToNarrow (K := K) s,
      signToNarrow_mem_narrowClassKernel (K := K) s⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (RayClass.signToNarrow (K := K))
  map_mul' s t := by
    apply Subtype.ext
    exact map_mul (RayClass.signToNarrow (K := K)) s t

/-- The restricted real-sign map has the same underlying narrow ideal class
as `RayClass.signToNarrow`. -/
@[simp]
theorem realSignToNarrowClassKernel_apply
    (s : RayClass.realSignGroup K) :
    (realSignToNarrowClassKernel (K := K) s :
      RayClass.NarrowClassGroup K) =
      RayClass.signToNarrow (K := K) s :=
  rfl

/-- Every narrow ideal class mapping trivially to the ordinary class
group is represented by a real sign class. -/
theorem realSignToNarrowClassKernel_surjective :
    Function.Surjective
      (realSignToNarrowClassKernel (K := K)) := by
  intro c
  have hc :
      c.1 ∈ (RayClass.signToNarrow (K := K)).range := by
    rw [RayClass.signToNarrow_range_eq_narrowToClassGroup_ker]
    exact c.2
  obtain ⟨s, hs⟩ := hc
  refine ⟨s, ?_⟩
  apply Subtype.ext
  exact hs

/-- Restricting the codomain of the real-sign map does not change its
kernel. -/
theorem realSignToNarrowClassKernel_ker :
    (realSignToNarrowClassKernel (K := K)).ker =
      (RayClass.signToNarrow (K := K)).ker := by
  ext s
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro hs
    exact congrArg Subtype.val hs
  · intro hs
    apply Subtype.ext
    exact hs

/-- The kernel of the narrow-to-ordinary class-group map is the quotient
of real sign classes by the sign classes of global integral units. -/
def realSignModuloIntegralUnitSignsEquivNarrowClassKernel :
    RayClass.realSignGroup K ⧸
        (RayClass.integralUnitSignToRealSign (K := K)).range ≃*
      MonoidHom.ker (RayClass.narrowToClassGroup (K := K)) := by
  let f := realSignToNarrowClassKernel (K := K)
  have hf : Function.Surjective f :=
    realSignToNarrowClassKernel_surjective (K := K)
  have hker :
      (RayClass.integralUnitSignToRealSign (K := K)).range =
        f.ker := by
    calc
      (RayClass.integralUnitSignToRealSign (K := K)).range =
          (RayClass.signToNarrow (K := K)).ker :=
        RayClass.integralUnitSignToRealSign_range_eq_signToNarrow_ker
          (K := K)
      _ = f.ker :=
        (realSignToNarrowClassKernel_ker (K := K)).symm
  exact
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (φ := f) hf)

/-- The relative big/small Hilbert kernel is exactly the quotient of real
sign classes by the sign classes contributed by global integral units. -/
def realSignModuloIntegralUnitSignsEquivBigToSmallHilbertKernel :
    RayClass.realSignGroup K ⧸
        (RayClass.integralUnitSignToRealSign (K := K)).range ≃*
      MonoidHom.ker
        (bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
          (K := K)) :=
  (realSignModuloIntegralUnitSignsEquivNarrowClassKernel
      (K := K)).trans
    (bigToSmallHilbertKernelEquivNarrowClassKernel
      (K := K)).symm

/-- The order of the relative big/small Hilbert kernel is the order of
the real-sign quotient modulo signs of global integral units. -/
theorem bigToSmallHilbertKernel_card_eq_realSignQuotient_card :
    Nat.card
        (MonoidHom.ker
          (bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient
            (K := K))) =
      Nat.card
        (RayClass.realSignGroup K ⧸
          (RayClass.integralUnitSignToRealSign (K := K)).range) :=
  (Nat.card_congr
    (realSignModuloIntegralUnitSignsEquivBigToSmallHilbertKernel
      (K := K)).toEquiv).symm

end GlobalClassFields
end GlobalClassFieldTheory
