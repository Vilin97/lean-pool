/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FreeRankOne
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
/-!
# The endomorphism-ring equivalence: endomorphisms and automorphisms of division modules

For the standard equal-characteristic Lubin--Tate module, scalar brackets
identify the endomorphism ring of the level-`m` division module with
`κ⟦T⟧/(T^m)`, and its automorphism group with the quotient of `κ⟦T⟧ˣ` by
the `m`-th higher unit subgroup.  The division-tower sources use a primitive
polynomial indexed by `n` for division level `m = n + 1`; every statement below
keeps this shift explicit.
-/

@[expose] public section

noncomputable section


open scoped PowerSeries LaurentSeries Polynomial

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

attribute [local instance]
  equalCharacteristicLubinTateTruncatedSelfSMul
  equalCharacteristicLubinTateTruncatedSelfModule

private theorem scalarConjRingEquiv_apply
    {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (e : R ≃ₗ[R] M) (a : R) (x : M) :
    (((RingEquiv.toOpposite R).trans (RingEquiv.moduleEndSelf R)).trans
      e.conjRingEquiv) a x = a • x := by
  change e (e.symm x * a) = a • x
  calc
    e (e.symm x * a) = e (a * e.symm x) :=
      congrArg e (mul_comm (e.symm x) a)
    _ = e (a • e.symm x) :=
      congrArg e (smul_eq_mul a (e.symm x)).symm
    _ = a • e (e.symm x) := e.map_smul a (e.symm x)
    _ = a • x := congrArg (fun y => a • y) (e.apply_symm_apply x)

/-- The public ring isomorphism `a ↦ [a]_F` of the endomorphism-ring equivalence. -/
noncomputable def equalCharacteristicLubinTateScalarEndomorphismRingEquiv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateTruncatedRing F n ≃+*
      Module.End (equalCharacteristicLubinTateTruncatedRing F n)
        (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
          (equalCharacteristicSeparableUniformizer F) (n + 1)) :=
  ((RingEquiv.toOpposite
      (equalCharacteristicLubinTateTruncatedRing F n)).trans
    (RingEquiv.moduleEndSelf
      (equalCharacteristicLubinTateTruncatedRing F n))).trans
    (equalCharacteristicLubinTateFreeRankOneEquiv F n).conjRingEquiv

/-- The orientation printed in the endomorphism-ring equivalence:
`End_{κ⟦T⟧}(F[n+1]) ≃ κ⟦T⟧/(T^(n+1))`. -/
noncomputable def equalCharacteristicLubinTateEndomorphismRingEquiv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Module.End (equalCharacteristicLubinTateTruncatedRing F n)
        (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
          (equalCharacteristicSeparableUniformizer F) (n + 1)) ≃+*
      equalCharacteristicLubinTateTruncatedRing F n :=
  (equalCharacteristicLubinTateScalarEndomorphismRingEquiv F n).symm

/-- The scalar-endomorphism equivalence sends a truncated scalar to its action map. -/
@[simp]
theorem equalCharacteristicLubinTateScalarEndomorphismRingEquiv_apply
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateTruncatedRing F n)
    (x : equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
      (equalCharacteristicSeparableUniformizer F) (n + 1)) :
    equalCharacteristicLubinTateScalarEndomorphismRingEquiv F n a x = a • x := by
  exact scalarConjRingEquiv_apply
    (equalCharacteristicLubinTateFreeRankOneEquiv F n) a x

/-- On a power-series representative, the scalar endomorphism is the
genuine finite Lubin--Tate bracket. -/
theorem equalCharacteristicLubinTateScalarEndomorphismRingEquiv_mk_apply
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧)
    (x : equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
      (equalCharacteristicSeparableUniformizer F) (n + 1)) :
    (equalCharacteristicLubinTateScalarEndomorphismRingEquiv F n
        (equalCharacteristicLubinTateTruncatedRingMk F n a)
        x).1 =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1) a x.1 := by
  rw [equalCharacteristicLubinTateScalarEndomorphismRingEquiv_apply]
  rfl

/-- Units of `κ⟦T⟧/(T^(n+1))` are precisely the linear automorphisms of the
division-level `n + 1` division module. -/
noncomputable def equalCharacteristicLubinTateTruncatedUnitsAutomorphismEquiv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    (equalCharacteristicLubinTateTruncatedRing F n)ˣ ≃*
      (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
          (equalCharacteristicSeparableUniformizer F) (n + 1) ≃ₗ[
        equalCharacteristicLubinTateTruncatedRing F n]
        equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
          (equalCharacteristicSeparableUniformizer F) (n + 1)) :=
  (Units.mapEquiv
      (equalCharacteristicLubinTateScalarEndomorphismRingEquiv F n).toMulEquiv).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv
      (equalCharacteristicLubinTateTruncatedRing F n)
      (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
        (equalCharacteristicSeparableUniformizer F) (n + 1)))

/-- A truncated unit acts on the division module by scalar multiplication. -/
@[simp]
theorem equalCharacteristicLubinTateTruncatedUnitsAutomorphismEquiv_apply
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : (equalCharacteristicLubinTateTruncatedRing F n)ˣ)
    (x : equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
      (equalCharacteristicSeparableUniformizer F) (n + 1)) :
    equalCharacteristicLubinTateTruncatedUnitsAutomorphismEquiv F n a x =
      (a : equalCharacteristicLubinTateTruncatedRing F n) • x := by
  exact equalCharacteristicLubinTateScalarEndomorphismRingEquiv_apply
    F n (a : equalCharacteristicLubinTateTruncatedRing F n) x

/-- Reduction of integral coefficients modulo `T^(n+1)`. -/
noncomputable def equalCharacteristicLubinTateTruncatedQuotientMap
    (F : LocalField.{u, v} K) (n : ℕ) :
    F.residueField⟦X⟧ →+* equalCharacteristicLubinTateTruncatedRing F n :=
  equalCharacteristicLubinTateTruncatedRingMk F n

/-- Reduction of integral units modulo `T^(n+1)`. -/
noncomputable def equalCharacteristicLubinTateUnitReduction
    (F : LocalField.{u, v} K) (n : ℕ) :
    F.residueField⟦X⟧ˣ →*
      (equalCharacteristicLubinTateTruncatedRing F n)ˣ :=
  Units.map (equalCharacteristicLubinTateTruncatedQuotientMap F n)

/-- The value of a reduced unit is the truncated class of its power series. -/
@[simp]
theorem equalCharacteristicLubinTateUnitReduction_val
    (F : LocalField.{u, v} K) (n : ℕ)
    (u : F.residueField⟦X⟧ˣ) :
    (equalCharacteristicLubinTateUnitReduction F n u :
        equalCharacteristicLubinTateTruncatedRing F n) =
      equalCharacteristicLubinTateTruncatedRingMk F n
        (u : F.residueField⟦X⟧) :=
  rfl

/-- The equal-characteristic realization of the higher unit group
`U_K^(n+1)`: units congruent to one modulo `T^(n+1)`. -/
noncomputable def equalCharacteristicLubinTateHigherUnitSubgroup
    (F : LocalField.{u, v} K) (n : ℕ) :
    Subgroup F.residueField⟦X⟧ˣ :=
  MonoidHom.ker (equalCharacteristicLubinTateUnitReduction F n)

/-- A unit is in the higher-unit kernel exactly when it is one modulo `X ^ (n + 1)`. -/
theorem mem_equalCharacteristicLubinTateHigherUnitSubgroup
    (F : LocalField.{u, v} K) (n : ℕ)
    (u : F.residueField⟦X⟧ˣ) :
    u ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n ↔
      (u : F.residueField⟦X⟧) - 1 ∈
        Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧) := by
  constructor
  · intro hu
    have hval := congrArg Units.val hu
    change equalCharacteristicLubinTateTruncatedQuotientMap F n
        (u : F.residueField⟦X⟧) = 1 at hval
    rw [← map_one (equalCharacteristicLubinTateTruncatedQuotientMap F n)] at hval
    exact (equalCharacteristicLubinTateTruncatedRingMk_eq_iff
      F n (u : F.residueField⟦X⟧) 1).mp hval
  · intro hu
    apply Units.ext
    change equalCharacteristicLubinTateTruncatedQuotientMap F n
        (u : F.residueField⟦X⟧) = 1
    rw [← map_one (equalCharacteristicLubinTateTruncatedQuotientMap F n)]
    exact (equalCharacteristicLubinTateTruncatedRingMk_eq_iff
      F n (u : F.residueField⟦X⟧) 1).mpr hu

private theorem equalCharacteristicLubinTateTruncationIdeal_le_constantCoeff_ker
    (F : LocalField.{u, v} K) (n : ℕ) :
    Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧) ≤
      RingHom.ker (PowerSeries.constantCoeff (R := F.residueField)) := by
  rw [Ideal.span_le]
  intro a ha
  rw [Set.mem_singleton_iff.mp ha]
  change PowerSeries.constantCoeff
      (PowerSeries.X ^ (n + 1) : F.residueField⟦X⟧) = 0
  simp

/-- Constant coefficient descends to every positive truncated power-series
ring. -/
noncomputable def equalCharacteristicLubinTateTruncatedConstantCoeff
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicLubinTateTruncatedRing F n →+* F.residueField :=
  equalCharacteristicLubinTateTruncatedRingLift F n
    (PowerSeries.constantCoeff (R := F.residueField))
    fun _ ha => RingHom.mem_ker.mp
      (equalCharacteristicLubinTateTruncationIdeal_le_constantCoeff_ker F n ha)

/-- The descended constant-coefficient map evaluates any truncated representative. -/
@[simp]
theorem equalCharacteristicLubinTateTruncatedConstantCoeff_mk
    (F : LocalField.{u, v} K) (n : ℕ) (f : F.residueField⟦X⟧) :
    equalCharacteristicLubinTateTruncatedConstantCoeff F n
        (equalCharacteristicLubinTateTruncatedRingMk F n f) =
      PowerSeries.constantCoeff f :=
  rfl

/-- Every unit modulo `T^(n+1)` has a power-series unit lift. -/
theorem equalCharacteristicLubinTateUnitReduction_surjective
    (F : LocalField.{u, v} K) (n : ℕ) :
    Function.Surjective (equalCharacteristicLubinTateUnitReduction F n) := by
  intro u
  obtain ⟨f, hf⟩ := equalCharacteristicLubinTateTruncatedRingMk_surjective
    F n (u : equalCharacteristicLubinTateTruncatedRing F n)
  have hconstant : IsUnit (PowerSeries.constantCoeff f) := by
    have hu : IsUnit
        (equalCharacteristicLubinTateTruncatedConstantCoeff F n
          (u : equalCharacteristicLubinTateTruncatedRing F n)) :=
      u.isUnit.map (equalCharacteristicLubinTateTruncatedConstantCoeff F n)
    rw [← hf] at hu
    simpa only [equalCharacteristicLubinTateTruncatedConstantCoeff_mk] using hu
  have hfUnit : IsUnit f :=
    PowerSeries.isUnit_iff_constantCoeff.mpr hconstant
  let fu : F.residueField⟦X⟧ˣ := hfUnit.unit
  refine ⟨fu, ?_⟩
  apply Units.ext
  change equalCharacteristicLubinTateTruncatedQuotientMap F n
      (fu : F.residueField⟦X⟧) =
    (u : equalCharacteristicLubinTateTruncatedRing F n)
  rw [hfUnit.unit_spec]
  exact hf

/-- The canonical first-isomorphism-theorem identification
`U_K/U_K^(n+1) ≃ (κ⟦T⟧/(T^(n+1)))ˣ`. -/
noncomputable def equalCharacteristicLubinTateUnitQuotientEquivTruncatedUnits
    (F : LocalField.{u, v} K) (n : ℕ) :
    F.residueField⟦X⟧ˣ ⧸
        equalCharacteristicLubinTateHigherUnitSubgroup F n ≃*
      (equalCharacteristicLubinTateTruncatedRing F n)ˣ :=
  QuotientGroup.quotientKerEquivOfSurjective
    (equalCharacteristicLubinTateUnitReduction F n)
    (equalCharacteristicLubinTateUnitReduction_surjective F n)

/-- The higher-unit quotient equivalence sends a unit class to its truncation. -/
@[simp]
theorem equalCharacteristicLubinTateUnitQuotientEquivTruncatedUnits_mk
    (F : LocalField.{u, v} K) (n : ℕ)
    (u : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateUnitQuotientEquivTruncatedUnits F n
        (QuotientGroup.mk u) =
      equalCharacteristicLubinTateUnitReduction F n u :=
  rfl

/-- The canonical the endomorphism-ring equivalence map from the higher-unit quotient to linear
automorphisms, induced by `a ↦ [a]_F`. -/
noncomputable def equalCharacteristicLubinTateUnitQuotientAutomorphismEquiv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    F.residueField⟦X⟧ˣ ⧸
        equalCharacteristicLubinTateHigherUnitSubgroup F n ≃*
      (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
          (equalCharacteristicSeparableUniformizer F) (n + 1) ≃ₗ[
        equalCharacteristicLubinTateTruncatedRing F n]
        equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
          (equalCharacteristicSeparableUniformizer F) (n + 1)) :=
  (equalCharacteristicLubinTateUnitQuotientEquivTruncatedUnits F n).trans
    (equalCharacteristicLubinTateTruncatedUnitsAutomorphismEquiv F n)

/-- The orientation printed in the endomorphism-ring equivalence:
`Aut_{κ⟦T⟧}(F[n+1]) ≃ U_K/U_K^(n+1)`. -/
noncomputable def equalCharacteristicLubinTateAutomorphismEquivUnitQuotient
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
          (equalCharacteristicSeparableUniformizer F) (n + 1) ≃ₗ[
        equalCharacteristicLubinTateTruncatedRing F n]
        equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
          (equalCharacteristicSeparableUniformizer F) (n + 1)) ≃*
      F.residueField⟦X⟧ˣ ⧸
        equalCharacteristicLubinTateHigherUnitSubgroup F n :=
  (equalCharacteristicLubinTateUnitQuotientAutomorphismEquiv F n).symm

/-- A representative unit acts through the actual Lubin--Tate bracket, so
the preceding automorphism isomorphism is the canonical one. -/
theorem equalCharacteristicLubinTateUnitQuotientAutomorphismEquiv_mk_apply
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (u : F.residueField⟦X⟧ˣ)
    (x : equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
      (equalCharacteristicSeparableUniformizer F) (n + 1)) :
    (equalCharacteristicLubinTateUnitQuotientAutomorphismEquiv F n
        (QuotientGroup.mk u) x).1 =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (u : F.residueField⟦X⟧) x.1 := by
  rw [equalCharacteristicLubinTateUnitQuotientAutomorphismEquiv,
    MulEquiv.trans_apply,
    equalCharacteristicLubinTateUnitQuotientEquivTruncatedUnits_mk,
    equalCharacteristicLubinTateTruncatedUnitsAutomorphismEquiv_apply]
  rw [equalCharacteristicLubinTateUnitReduction_val]
  have h := equalCharacteristicLubinTateScalarEndomorphismRingEquiv_mk_apply
    F n (u : F.residueField⟦X⟧) x
  rw [equalCharacteristicLubinTateScalarEndomorphismRingEquiv_apply] at h
  exact h

end EqualCharacteristic
end LubinTate
