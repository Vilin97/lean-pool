/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.DivisionModuleEndomorphisms
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
/-!
# LubinTate the explicit norm-subgroup computation: higher units in the Laurent-series model

The power-series coefficient ring `k[[T]]` is the canonical integer ring of
`k((T))`.  The induced equivalence on units carries the explicit kernel used
in the Lubin--Tate construction to the canonical principal-unit filtration.
The construction uses index `n`, while the corresponding division-level
unit group is `U^(n+1)`.
-/

noncomputable section

open scoped LaurentSeries PowerSeries ValuativeRel WithZero

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable {K : Type u} [Field K]

private theorem ringEquiv_map_maximalIdeal
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    Ideal.map e.toRingHom (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change e x ∈ IsLocalRing.maximalIdeal S
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro h
    have h' := h.map e.symm.toRingHom
    exact hx (by simpa using h')
  · intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    intro h
    exact hy (h.map e.toRingHom)

private theorem ringEquiv_map_maximalIdeal_pow
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) :
    Ideal.map e.toRingHom (IsLocalRing.maximalIdeal R ^ n) =
      IsLocalRing.maximalIdeal S ^ n := by
  rw [Ideal.map_pow, ringEquiv_map_maximalIdeal]

private theorem ringEquiv_mem_maximalIdeal_pow_iff
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (x : R) :
    e x ∈ IsLocalRing.maximalIdeal S ^ n ↔
      x ∈ IsLocalRing.maximalIdeal R ^ n := by
  rw [← ringEquiv_map_maximalIdeal_pow e n]
  constructor
  · intro hx
    rcases (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).1 hx with
      ⟨y, hy, hey⟩
    exact e.injective hey ▸ hy
  · exact Ideal.mem_map_of_mem e.toRingHom

/-- The genuine equivalence between power-series units and the units of the
canonical integer ring of the Laurent-series field. -/
noncomputable def equalCharacteristicPowerSeriesUnitsEquivLaurentInteger
    (k : Type u) [Field k] :
    letI : ValuativeRel k⸨X⸩ := ValuativeRel.ofValuation
      (Valued.v : Valuation k⸨X⸩ ℤᵐ⁰)
    k⟦X⟧ˣ ≃* 𝒪[k⸨X⸩]ˣ := by
  letI : ValuativeRel k⸨X⸩ := ValuativeRel.ofValuation
    (Valued.v : Valuation k⸨X⸩ ℤᵐ⁰)
  exact Units.mapEquiv
    (powerSeriesEquivLaurentValuativeInteger k).toMulEquiv

/-- States the theorem `equalCharacteristicPowerSeriesUnitsEquivLaurentInteger_mem_iff`. -/
theorem equalCharacteristicPowerSeriesUnitsEquivLaurentInteger_mem_iff
    (k : Type u) [Field k] (n : ℕ) (a : k⟦X⟧ˣ) :
    letI : ValuativeRel k⸨X⸩ := ValuativeRel.ofValuation
      (Valued.v : Valuation k⸨X⸩ ℤᵐ⁰)
    equalCharacteristicPowerSeriesUnitsEquivLaurentInteger k a ∈
        principalUnits k⸨X⸩ n ↔
      (a : k⟦X⟧) - 1 ∈
        Ideal.span ({PowerSeries.X ^ n} : Set k⟦X⟧) := by
  let : ValuativeRel k⸨X⸩ := ValuativeRel.ofValuation
    (Valued.v : Valuation k⸨X⸩ ℤᵐ⁰)
  rw [mem_principalUnits_iff]
  change powerSeriesEquivLaurentValuativeInteger k
      (a : k⟦X⟧) - 1 ∈
        IsLocalRing.maximalIdeal 𝒪[k⸨X⸩] ^ n ↔ _
  simpa [PowerSeries.maximalIdeal_eq_span_X,
    Ideal.span_singleton_pow] using
    (ringEquiv_mem_maximalIdeal_pow_iff
      (powerSeriesEquivLaurentValuativeInteger k) n
      ((a : k⟦X⟧) - 1))

/-- The explicit Lubin--Tate higher-unit kernel is exactly the canonical
principal-unit group `U^(n+1)` under the integer-unit equivalence. -/
theorem equalCharacteristicLubinTateHigherUnitSubgroup_map_eq_principalUnits
    (F : LocalField.{u, v} K) (n : ℕ) :
    letI : ValuativeRel F.residueField⸨X⸩ :=
      equalCharacteristicLaurentValuativeRel F
    (equalCharacteristicLubinTateHigherUnitSubgroup F n).map
        (equalCharacteristicPowerSeriesUnitsEquivLaurentInteger
          F.residueField).toMonoidHom =
      principalUnits F.residueField⸨X⸩ (n + 1) := by
  let : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  let E := equalCharacteristicPowerSeriesUnitsEquivLaurentInteger
    F.residueField
  ext u
  constructor
  · rintro ⟨a, ha, rfl⟩
    apply
      (equalCharacteristicPowerSeriesUnitsEquivLaurentInteger_mem_iff
        F.residueField (n + 1) a).2
    exact (mem_equalCharacteristicLubinTateHigherUnitSubgroup F n a).1 ha
  · intro hu
    refine ⟨E.symm u, ?_, ?_⟩
    · apply
        (mem_equalCharacteristicLubinTateHigherUnitSubgroup F n
          (E.symm u)).2
      apply
        (equalCharacteristicPowerSeriesUnitsEquivLaurentInteger_mem_iff
          F.residueField (n + 1) (E.symm u)).1
      simpa [E] using hu
    · exact E.apply_symm_apply u

/-- After inclusion of integer units into field units, the explicit higher
unit kernel is the canonical field subgroup `U^(n+1)`. -/
theorem equalCharacteristicLubinTateHigherUnitSubgroup_map_eq_fieldPrincipalUnits
    (F : LocalField.{u, v} K) (n : ℕ) :
    letI : ValuativeRel F.residueField⸨X⸩ :=
      equalCharacteristicLaurentValuativeRel F
    ((equalCharacteristicLubinTateHigherUnitSubgroup F n).map
        (equalCharacteristicPowerSeriesUnitsEquivLaurentInteger
          F.residueField).toMonoidHom).map
        (integerUnitsToFieldUnits F.residueField⸨X⸩) =
      LocalFieldTheory.fieldPrincipalUnits F.residueField⸨X⸩ (n + 1) := by
  let : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  rw [equalCharacteristicLubinTateHigherUnitSubgroup_map_eq_principalUnits]
  rfl

private theorem equalCharacteristicLubinTateAmbientBracket_primitiveRoot_eq_iff_mem_higherUnitSubgroup
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (u : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (u : F.residueField⟦X⟧)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) =
      chosenEqualCharacteristicLubinTatePrimitiveRoot F n ↔
        u ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n := by
  let I : Ideal F.residueField⟦X⟧ :=
    Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧)
  constructor
  · intro hfix
    change equalCharacteristicLubinTateUnitReduction F n u = 1
    apply Units.ext
    change equalCharacteristicLubinTateTruncatedRingMk F n
        (u : F.residueField⟦X⟧) =
      equalCharacteristicLubinTateTruncatedRingMk F n 1
    apply equalCharacteristicLubinTatePrimitiveEvaluation_injective F n
    rw [equalCharacteristicLubinTatePrimitiveEvaluation_mk,
      equalCharacteristicLubinTatePrimitiveEvaluation_mk]
    apply Subtype.ext
    change equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (u : F.residueField⟦X⟧)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1) 1
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
    rw [equalCharacteristicLubinTateAmbientBracket_one_apply_of_torsion F
      (equalCharacteristicSeparableCoefficientHom F)
      (equalCharacteristicSeparableUniformizer F) (n + 1)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n)]
    exact hfix
  · intro hu
    change equalCharacteristicLubinTateUnitReduction F n u = 1 at hu
    have hq := congrArg Units.val hu
    change equalCharacteristicLubinTateTruncatedRingMk F n
        (u : F.residueField⟦X⟧) =
      equalCharacteristicLubinTateTruncatedRingMk F n 1 at hq
    have heval := congrArg
      (equalCharacteristicLubinTatePrimitiveEvaluation F n) hq
    rw [equalCharacteristicLubinTatePrimitiveEvaluation_mk,
      equalCharacteristicLubinTatePrimitiveEvaluation_mk] at heval
    have hval := congrArg Subtype.val heval
    change equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (u : F.residueField⟦X⟧)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1) 1
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) at hval
    exact hval.trans
      (equalCharacteristicLubinTateAmbientBracket_one_apply_of_torsion F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n))

/-- The `[u⁻¹]` action occurring in the completed theta-intertwining theorem fixes the standard primitive
division-level `n + 1` division point exactly when `u` is an `(n + 1)`-st higher
unit.  This is the faithful-action kernel needed in the proof of the explicit norm-subgroup computation. -/
theorem equalCharacteristicLubinTateAmbientBracket_inv_primitiveRoot_eq_iff_mem_higherUnitSubgroup
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (u : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        ((u⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) =
      chosenEqualCharacteristicLubinTatePrimitiveRoot F n ↔
        u ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n := by
  constructor
  · intro hfix
    have hinv :=
      (equalCharacteristicLubinTateAmbientBracket_primitiveRoot_eq_iff_mem_higherUnitSubgroup
        F n u⁻¹).1 hfix
    have hu := (equalCharacteristicLubinTateHigherUnitSubgroup F n).inv_mem hinv
    simpa using hu
  · intro hu
    apply
      (equalCharacteristicLubinTateAmbientBracket_primitiveRoot_eq_iff_mem_higherUnitSubgroup
        F n u⁻¹).2
    exact (equalCharacteristicLubinTateHigherUnitSubgroup F n).inv_mem hu

end EqualCharacteristic
end LubinTate
