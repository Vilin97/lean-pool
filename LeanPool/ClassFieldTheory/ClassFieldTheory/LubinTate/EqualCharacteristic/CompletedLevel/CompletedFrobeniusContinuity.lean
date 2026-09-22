/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusLift
/-!
# The completed theta-intertwining theorem: continuity of the standard completed Frobenius lift

For every prescribed bracket unit `a`, pullback of the completed-level
spectral norm along the semilinear Frobenius lift is a power-multiplicative
algebra norm extending the original norm of the completed maximal-unramified
base.  Spectral-norm uniqueness therefore makes the lift an isometry and in
particular continuous.  We also name the `a = u⁻¹` specialization used
directly in the completed theta-intertwining theorem.
-/

noncomputable section

open scoped LaurentSeries NNReal Polynomial PowerSeries Topology Valued WithZero


universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The Laurent-series algebra structure on the completed unramified base used in Frobenius
continuity. -/
noncomputable local instance equalCharacteristicFrobeniusContinuityBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

noncomputable local instance
    equalCharacteristicFrobeniusContinuityBaseValuationIsNontrivial
    (k : Type v) [Field k] :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰).IsNontrivial :=
  equalCharacteristicCompletedBaseValuationIsNontrivial k

/-- The base valuation in the Frobenius continuity argument has rank one. -/
noncomputable local instance
    equalCharacteristicFrobeniusContinuityBaseValuationRankOne
    (k : Type v) [Field k] :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰).RankOne :=
  equalCharacteristicCompletedBaseValuationRankOne k

/-- The completed unramified base carries the nontrivial norm used in the Frobenius continuity
argument. -/
@[reducible]
noncomputable local instance equalCharacteristicFrobeniusContinuityBaseNormedField
    (k : Type v) [Field k] :
    NontriviallyNormedField
      (equalCharacteristicCompletedUnramifiedField k) :=
  equalCharacteristicCompletedBaseNormedField k

/-- The completed Lubin–Tate level carries its spectral norm for the Frobenius continuity
argument. -/
@[reducible]
noncomputable local instance equalCharacteristicFrobeniusContinuityLevelNormedField
    (F : LocalField.{u, v} K) (n : ℕ) :
    NontriviallyNormedField (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelNormedField F n

/-- Base arithmetic Frobenius preserves the rank-one norm. -/
private theorem equalCharacteristicCompletedFrobeniusBase_norm
    (F : LocalField.{u, v} K)
    (b : equalCharacteristicCompletedUnramifiedField F.residueField) :
    ‖equalCharacteristicCompletedUnramifiedFrobenius F.residueField b‖ =
      ‖b‖ := by
  simp only [Valued.toNormedField.norm_def]
  apply congrArg (fun z =>
    ((Valuation.RankOne.hom
      (Valued.v : Valuation
        (equalCharacteristicCompletedUnramifiedField F.residueField) ℤᵐ⁰) z : ℝ≥0) : ℝ))
  exact ((Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField F.residueField) ℤᵐ⁰).restrict_inj).mpr
    (equalCharacteristicCompletedUnramifiedFrobenius_valuation F.residueField b)

/-- Pullback of the standard completed-level spectral norm by the
prescribed-bracket Frobenius lift. -/
noncomputable def equalCharacteristicCompletedFrobeniusPullbackAlgebraNorm
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    AlgebraNorm
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) where
  toFun x := ‖equalCharacteristicCompletedFrobeniusLiftEquiv F n a x‖
  map_zero' := by simp
  add_le' x y := by
    rw [map_add]
    exact norm_add_le _ _
  neg' x := by simp
  mul_le' x y := by
    rw [map_mul, norm_mul]
  eq_zero_of_map_eq_zero' x hx := by
    apply (equalCharacteristicCompletedFrobeniusLiftEquiv F n a).injective
    rw [map_zero]
    exact norm_eq_zero.mp hx
  smul' b x := by
    rw [Algebra.smul_def, map_mul,
      equalCharacteristicCompletedFrobeniusLiftEquiv_algebraMap,
      norm_mul]
    congr 1
    change spectralNorm
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)
        (algebraMap
          (equalCharacteristicCompletedUnramifiedField F.residueField)
          (equalCharacteristicCompletedLevelField F n)
          (equalCharacteristicCompletedUnramifiedFrobenius
            F.residueField b)) = ‖b‖
    rw [spectralNorm_extends,
      equalCharacteristicCompletedFrobeniusBase_norm]

/-- The pulled-back norm is power-multiplicative. -/
theorem equalCharacteristicCompletedFrobeniusPullbackAlgebraNorm_isPowMul
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    IsPowMul (equalCharacteristicCompletedFrobeniusPullbackAlgebraNorm F n a) := by
  intro x m _hm
  change
    ‖equalCharacteristicCompletedFrobeniusLiftEquiv F n a (x ^ m)‖ =
      ‖equalCharacteristicCompletedFrobeniusLiftEquiv F n a x‖ ^ m
  rw [map_pow, norm_pow]

/-- Spectral-norm uniqueness identifies the pullback norm with the original
completed-level norm. -/
theorem equalCharacteristicCompletedFrobeniusPullbackAlgebraNorm_eq
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicCompletedFrobeniusPullbackAlgebraNorm F n a =
      spectralAlgNorm
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n) :=
  spectralNorm_unique
    (equalCharacteristicCompletedFrobeniusPullbackAlgebraNorm_isPowMul F n a)

/-- Every prescribed-bracket standard completed Frobenius lift preserves
the spectral norm. -/
theorem equalCharacteristicCompletedFrobeniusLiftEquiv_norm
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ)
    (x : equalCharacteristicCompletedLevelField F n) :
    ‖equalCharacteristicCompletedFrobeniusLiftEquiv F n a x‖ = ‖x‖ := by
  have h := DFunLike.congr_fun
    (equalCharacteristicCompletedFrobeniusPullbackAlgebraNorm_eq F n a) x
  change equalCharacteristicCompletedFrobeniusPullbackAlgebraNorm F n a x =
    spectralAlgNorm
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) x
  exact h

/-- Every prescribed-bracket standard completed Frobenius lift is an
isometry. -/
theorem equalCharacteristicCompletedFrobeniusLiftEquiv_isometry
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    Isometry (equalCharacteristicCompletedFrobeniusLiftEquiv F n a) :=
  AddMonoidHomClass.isometry_of_norm
    (equalCharacteristicCompletedFrobeniusLiftEquiv F n a)
    (equalCharacteristicCompletedFrobeniusLiftEquiv_norm F n a)

/-- Every prescribed-bracket standard completed Frobenius lift is
continuous for the spectral-norm topology. -/
theorem equalCharacteristicCompletedFrobeniusLiftEquiv_continuous
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    Continuous (equalCharacteristicCompletedFrobeniusLiftEquiv F n a) :=
  (equalCharacteristicCompletedFrobeniusLiftEquiv_isometry F n a).continuous

/-- The completed theta-intertwining theorem specialization preserves the spectral norm. -/
theorem equalCharacteristicCompletedFrobeniusLift_norm
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : equalCharacteristicCompletedLevelField F n) :
    ‖equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹ x‖ = ‖x‖ :=
  equalCharacteristicCompletedFrobeniusLiftEquiv_norm F n u⁻¹ x

/-- The completed theta-intertwining theorem specialization is an isometry. -/
theorem equalCharacteristicCompletedFrobeniusLift_isometry
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Isometry (equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹) :=
  equalCharacteristicCompletedFrobeniusLiftEquiv_isometry F n u⁻¹

/-- The completed theta-intertwining theorem specialization is continuous for the standard
completed-level
spectral-norm topology. -/
theorem equalCharacteristicCompletedFrobeniusLift_continuous
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Continuous (equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹) :=
  (equalCharacteristicCompletedFrobeniusLift_isometry F u n).continuous

end EqualCharacteristic
end LubinTate
