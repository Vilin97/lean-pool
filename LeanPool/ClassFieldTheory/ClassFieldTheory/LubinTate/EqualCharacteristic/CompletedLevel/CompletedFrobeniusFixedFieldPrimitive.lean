/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedPrimitiveAction
/-!
# The completed theta-intertwining theorem: the fixed-field primitive point over the completed base

The direct theta value has the changed completed primitive polynomial as
its minimal polynomial over the completed maximal-unramified Laurent field.
Comparing degrees shows that this point generates the whole completed level.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries Polynomial PowerSeries


universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The completed base carries the Laurent-series algebra structure used for the completed
primitive element. -/
noncomputable local instance
    equalCharacteristicCompletedFrobeniusFixedFieldCompletedPrimitiveBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

/-- Provides the instance `equalCharacteristicCompletedFrobeniusIdentificationLevelCharP`. -/
instance equalCharacteristicCompletedFrobeniusIdentificationLevelCharP
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    CharP (equalCharacteristicCompletedLevelField F n)
      F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)).injective
    F.residueCharacteristic

private theorem equalCharacteristicDirectTargetCompletedPrimitivePolynomial_eq
    (F : LocalField.{u, v} K)
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicChangedCompletedPrimitivePolynomial F a⁻¹ n =
      (equalCharacteristicChangedPrimitivePolynomial F a n).map
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicCompletedUnramifiedField F.residueField)) := by
  simp [equalCharacteristicChangedCompletedPrimitivePolynomial,
    equalCharacteristicThetaSourceUnit]

private theorem
    equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isRoot_targetCompleted
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    ((equalCharacteristicChangedCompletedPrimitivePolynomial F a⁻¹ n).map
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n))).IsRoot
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
        equalCharacteristicCompletedLevelField F n) := by
  rw [equalCharacteristicDirectTargetCompletedPrimitivePolynomial_eq,
    Polynomial.map_map]
  simpa [equalCharacteristicCompletedLevelBaseHom] using
    equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isRoot_target F a n

/-- States the theorem
`equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isIntegral_completedBase`. -/
theorem
    equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isIntegral_completedBase
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    IsIntegral (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
        equalCharacteristicCompletedLevelField F n) := by
  refine ⟨equalCharacteristicChangedCompletedPrimitivePolynomial F a⁻¹ n,
    equalCharacteristicChangedCompletedPrimitivePolynomial_monic F a⁻¹ n, ?_⟩
  rw [← Polynomial.eval_map]
  exact
    equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isRoot_targetCompleted
      F a n

private theorem
    equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_minpoly_completedBase
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    minpoly (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
          equalCharacteristicCompletedLevelField F n) =
      equalCharacteristicChangedCompletedPrimitivePolynomial F a⁻¹ n := by
  have hroot : Polynomial.aeval
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
        equalCharacteristicCompletedLevelField F n)
      (equalCharacteristicChangedCompletedPrimitivePolynomial F a⁻¹ n) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact
      equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isRoot_targetCompleted
        F a n
  have hmin := minpoly.eq_of_irreducible
    (equalCharacteristicChangedCompletedPrimitivePolynomial_irreducible F a⁻¹ n)
    hroot
  rw [(equalCharacteristicChangedCompletedPrimitivePolynomial_monic F a⁻¹ n).leadingCoeff,
    inv_one, Polynomial.C_1, mul_one] at hmin
  exact hmin.symm

/-- The fixed target primitive point generates the standard completed level
over the completed maximal-unramified Laurent field. -/
theorem
    equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_adjoin_completedBase_eq_top
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    IntermediateField.adjoin
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        ({(equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
          equalCharacteristicCompletedLevelField F n)} :
          Set (equalCharacteristicCompletedLevelField F n)) = ⊤ := by
  apply (Field.primitive_element_iff_minpoly_natDegree_eq
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
      equalCharacteristicCompletedLevelField F n)).2
  rw [equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_minpoly_completedBase,
    equalCharacteristicChangedCompletedPrimitivePolynomial_natDegree]
  let pb := equalCharacteristicCompletedPrimitivePowerBasis F n
  calc
    (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n =
        (equalCharacteristicCompletedPrimitivePolynomial F n).natDegree :=
      (equalCharacteristicCompletedPrimitivePolynomial_natDegree F n).symm
    _ = (minpoly (equalCharacteristicCompletedUnramifiedField F.residueField)
        pb.gen).natDegree := by
      rw [show pb.gen = equalCharacteristicCompletedPrimitiveRoot F n by
        exact equalCharacteristicCompletedPrimitivePowerBasis_gen F n]
      rw [equalCharacteristicCompletedPrimitiveRoot_minpoly]
    _ = pb.dim := pb.natDegree_minpoly
    _ = Module.finrank
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n) := pb.finrank.symm

end EqualCharacteristic
end LubinTate
