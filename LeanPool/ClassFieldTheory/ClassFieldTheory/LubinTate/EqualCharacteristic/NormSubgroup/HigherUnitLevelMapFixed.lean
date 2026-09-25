/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFrobeniusFixed
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UniformizerNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
/-!
# LubinTate the explicit norm-subgroup computation: higher-unit Frobenius fixes the standard
  level map
-/

@[expose] public section

noncomputable
section


open scoped LaurentSeries PowerSeries

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type} [Field K]

/-- Two ring homomorphisms out of a power-basis extension agree pointwise
once they agree on the base field and on the power-basis generator. -/
private theorem ringHom_apply_eq_of_powerBasis
    {B L C : Type*} [Field B] [Field L] [Algebra B L] [Field C]
    (pb : PowerBasis B L) (delta : C →+* C) (f : L →+* C)
    (hgen : delta (f pb.gen) = f pb.gen)
    (hbase : ∀ b : B,
      delta (f (algebraMap B L b)) = f (algebraMap B L b))
    (x : L) :
    delta (f x) = f x := by
  let phi : L →+* C := delta.comp f
  let : Algebra B C := (f.comp (algebraMap B L)).toAlgebra
  let phiAlg : L →ₐ[B] C :=
    { phi with commutes' := hbase }
  let fAlg : L →ₐ[B] C :=
    { f with commutes' := fun _ => rfl }
  have h : phiAlg = fAlg := pb.algHom_ext hgen
  exact DFunLike.congr_fun h x

/-- The Laurent-series base acts on the completed unramified field through the coefficient
embedding. -/
@[reducible] noncomputable local instance equalCharacteristicHigherUnitMapBaseAlgebra
    (F : LocalField K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedLevelBaseAlgebra F

/-- The completed level field is a Laurent-series algebra through the completed unramified base. -/
@[reducible] noncomputable local instance equalCharacteristicHigherUnitMapLevelAlgebra
    (F : LocalField K) (n : ℕ) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelLaurentAlgebra F n

local instance equalCharacteristicHigherUnitMapScalarTower
    (F : LocalField K) (n : ℕ) :
    IsScalarTower F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable def higherUnitLevelMapRingHom
    (F : LocalField K) [CharP K F.residueCharacteristic] (n : ℕ) :
    equalCharacteristicLubinTateLevelField F n →+*
      equalCharacteristicCompletedLevelField F n :=
  (equalCharacteristicLubinTateLevelFieldToCompleted F n).toRingHom

private theorem higherUnitLevelMapRingHom_apply
    (F : LocalField K) [CharP K F.residueCharacteristic] (n : ℕ)
    (x : equalCharacteristicLubinTateLevelField F n) :
    higherUnitLevelMapRingHom F n x =
      equalCharacteristicLubinTateLevelFieldToCompleted F n x :=
  rfl

/-- The canonical finite-level embedding into the completed level, regarded
as a ring homomorphism.  This is the lightweight interface used by consumers
that do not need to reconstruct its concrete algebra structures. -/
noncomputable def equalCharacteristicLubinTateLevelFieldToCompletedRingHom
    (F : LocalField K) [CharP K F.residueCharacteristic] (n : ℕ) :
    equalCharacteristicLubinTateLevelField F n →+*
      equalCharacteristicCompletedLevelField F n :=
  (equalCharacteristicLubinTateLevelFieldToCompleted F n).toRingHom

/-- States the theorem `equalCharacteristicLubinTateLevelFieldToCompletedRingHom_algebraMap`. -/
@[simp]
theorem equalCharacteristicLubinTateLevelFieldToCompletedRingHom_algebraMap
    (F : LocalField K) [CharP K F.residueCharacteristic]
    (n : ℕ) (b : F.residueField⸨X⸩) :
    equalCharacteristicLubinTateLevelFieldToCompletedRingHom F n
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n) b) =
      algebraMap F.residueField⸨X⸩
        (equalCharacteristicCompletedLevelField F n) b := by
  change (equalCharacteristicLubinTateLevelFieldToCompleted F n)
    (algebraMap F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) b) = _
  exact (equalCharacteristicLubinTateLevelFieldToCompleted F n).commutes b

private noncomputable def higherUnitFrobeniusRingHom
    (F : LocalField K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicCompletedLevelField F n →+*
      equalCharacteristicCompletedLevelField F n :=
  (equalCharacteristicCompletedFrobeniusAlgEquiv F a n).toRingEquiv.toRingHom

private theorem higherUnitFrobeniusRingHom_apply
    (F : LocalField K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : equalCharacteristicCompletedLevelField F n) :
    higherUnitFrobeniusRingHom F a n x =
      equalCharacteristicCompletedFrobeniusAlgEquiv F a n x :=
  rfl

private theorem higherUnitLevelMapRingHom_gen
    (F : LocalField K) [CharP K F.residueCharacteristic] (n : ℕ) :
    higherUnitLevelMapRingHom F n
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
      equalCharacteristicCompletedPrimitiveRoot F n := by
  change (equalCharacteristicLubinTateLevelFieldToCompleted F n)
    (equalCharacteristicLubinTateLevelPowerBasis F n).gen = _
  rw [equalCharacteristicLubinTateLevelPowerBasis,
    IntermediateField.adjoin.powerBasis_gen,
    equalCharacteristicLubinTateLevelFieldToCompleted_generator]

private theorem higherUnitFrobeniusRingHom_levelMap_algebraMap
    (F : LocalField K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) (b : F.residueField⸨X⸩) :
    higherUnitFrobeniusRingHom F a n
        (higherUnitLevelMapRingHom F n
          (algebraMap F.residueField⸨X⸩
            (equalCharacteristicLubinTateLevelField F n) b)) =
      higherUnitLevelMapRingHom F n
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelField F n) b) := by
  rw [higherUnitFrobeniusRingHom_apply,
    higherUnitLevelMapRingHom_apply]
  rw [(equalCharacteristicLubinTateLevelFieldToCompleted F n).commutes b]
  exact (equalCharacteristicCompletedFrobeniusAlgEquiv F a n).commutes b

private theorem higherUnitLevelMap_fixed_core
    (F : LocalField K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (ha : a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n)
    (x : equalCharacteristicLubinTateLevelField F n) :
    higherUnitFrobeniusRingHom F a n (higherUnitLevelMapRingHom F n x) =
      higherUnitLevelMapRingHom F n x := by
  apply ringHom_apply_eq_of_powerBasis
    (equalCharacteristicLubinTateLevelPowerBasis F n)
    (higherUnitFrobeniusRingHom F a n)
    (higherUnitLevelMapRingHom F n)
  · rw [higherUnitLevelMapRingHom_gen,
      higherUnitFrobeniusRingHom_apply]
    exact
      equalCharacteristicCompletedFrobeniusAlgEquiv_primitiveRoot_fixed_of_mem_higherUnit
        F a n ha
  · exact higherUnitFrobeniusRingHom_levelMap_algebraMap F a n

/-- States the theorem
`equalCharacteristicCompletedFrobeniusAlgEquiv_comp_levelFieldToCompleted_of_mem_higherUnit`. -/
theorem
    equalCharacteristicCompletedFrobeniusAlgEquiv_comp_levelFieldToCompleted_of_mem_higherUnit
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (ha : a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n)
    (x : equalCharacteristicLubinTateLevelField F n) :
    equalCharacteristicCompletedFrobeniusAlgEquiv F a n
        (equalCharacteristicLubinTateLevelFieldToCompleted F n x) =
      equalCharacteristicLubinTateLevelFieldToCompleted F n x := by
  have h := higherUnitLevelMap_fixed_core F a n ha x
  rw [higherUnitFrobeniusRingHom_apply,
    higherUnitLevelMapRingHom_apply] at h
  exact h

end EqualCharacteristic
end LubinTate
