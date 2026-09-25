/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusContinuity
/-!
# The completed theta-intertwining theorem: the completed Frobenius lift over the Laurent base

The prescribed completed lift is semilinear over the completed maximal
unramified field.  Arithmetic Frobenius on that field fixes the embedded
Laurent base `k((T))`; hence the lift is an actual `k((T))`-automorphism.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries PowerSeries

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The Laurent-series algebra structure on the completed unramified base used to construct
Frobenius. -/
noncomputable local instance equalCharacteristicCompletedFrobeniusBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

/-- The completed Lubin–Tate level is an algebra over residue-field Laurent series through its
completed base. -/
noncomputable local instance equalCharacteristicCompletedFrobeniusLevelAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedLevelField F n) :=
  RingHom.toAlgebra
    ((algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)).comp
      (algebraMap F.residueField⸨X⸩
        (equalCharacteristicCompletedUnramifiedField F.residueField)))

local instance equalCharacteristicCompletedFrobeniusScalarTower
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsScalarTower F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The completed theta-intertwining theorem completed lift fixes every element of the embedded
Laurent
base `k((T))`. -/
@[simp]
theorem equalCharacteristicCompletedFrobeniusLiftEquiv_fixesLaurentBase
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (b : F.residueField⸨X⸩) :
    equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicCompletedLevelField F n) b) =
      algebraMap F.residueField⸨X⸩
        (equalCharacteristicCompletedLevelField F n) b := by
  change equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicCompletedUnramifiedField F.residueField) b)) = _
  rw [equalCharacteristicCompletedFrobeniusLiftEquiv_algebraMap,
    (equalCharacteristicCompletedUnramifiedFrobenius F.residueField).commutes]
  rfl

/-- The prescribed the completed theta-intertwining theorem lift, regarded as an automorphism
over the original
Laurent field `k((T))`. -/
noncomputable def equalCharacteristicCompletedFrobeniusAlgEquiv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicCompletedLevelField F n ≃ₐ[F.residueField⸨X⸩]
      equalCharacteristicCompletedLevelField F n :=
  AlgEquiv.ofRingEquiv
    (equalCharacteristicCompletedFrobeniusLiftEquiv_fixesLaurentBase F u n)

/-- States the theorem `equalCharacteristicCompletedFrobeniusAlgEquiv_apply`. -/
@[simp]
theorem equalCharacteristicCompletedFrobeniusAlgEquiv_apply
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : equalCharacteristicCompletedLevelField F n) :
    equalCharacteristicCompletedFrobeniusAlgEquiv F u n x =
      equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹ x :=
  rfl

end EqualCharacteristic
end LubinTate
