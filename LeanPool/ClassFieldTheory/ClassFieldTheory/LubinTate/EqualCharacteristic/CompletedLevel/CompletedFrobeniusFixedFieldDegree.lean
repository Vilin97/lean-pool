/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldGeneration
/-!
# The completed theta-intertwining theorem: degree of the completed Frobenius fixed field

The direct theta value has the changed primitive polynomial over `k((T))`.
Together with the fixed-field generation theorem this gives the exact extension degree `(q - 1) q^n`.
-/

noncomputable section

open scoped LaurentSeries Polynomial PowerSeries

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

noncomputable local instance
    equalCharacteristicCompletedFrobeniusFixedFieldDegreeBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

noncomputable local instance
    equalCharacteristicCompletedFrobeniusFixedFieldDegreeLevelAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedLevelField F n) :=
  RingHom.toAlgebra
    ((algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)).comp
      (algebraMap F.residueField⸨X⸩
        (equalCharacteristicCompletedUnramifiedField F.residueField)))

local instance
    equalCharacteristicCompletedFrobeniusFixedFieldDegreeScalarTower
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsScalarTower F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable local instance
    equalCharacteristicCompletedFrobeniusFixedFieldDegreeAlgebra
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedFrobeniusFixedField F a n) :=
  Subalgebra.algebra
    (equalCharacteristicCompletedFrobeniusFixedField F a n).toSubalgebra

noncomputable local instance
    equalCharacteristicCompletedFrobeniusFixedFieldDegreeSMul
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    SMul F.residueField⸨X⸩
      (equalCharacteristicCompletedFrobeniusFixedField F a n) :=
  @Algebra.toSMul _ _ _ _
    (equalCharacteristicCompletedFrobeniusFixedFieldDegreeAlgebra F a n)

noncomputable local instance
    equalCharacteristicCompletedFrobeniusFixedFieldDegreeModule
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Module F.residueField⸨X⸩
      (equalCharacteristicCompletedFrobeniusFixedField F a n) :=
  @Algebra.toModule _ _ _ _
    (equalCharacteristicCompletedFrobeniusFixedFieldDegreeAlgebra F a n)

private theorem
    equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isIntegral_laurentBase
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    IsIntegral F.residueField⸨X⸩
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
        equalCharacteristicCompletedLevelField F n) := by
  refine ⟨equalCharacteristicChangedPrimitivePolynomial F a n,
    equalCharacteristicChangedPrimitivePolynomial_monic F a n, ?_⟩
  rw [← Polynomial.eval_map]
  exact equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isRoot_target F a n

private theorem
    equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_minpoly_laurentBase
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    minpoly F.residueField⸨X⸩
        (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
          equalCharacteristicCompletedLevelField F n) =
      equalCharacteristicChangedPrimitivePolynomial F a n := by
  have hroot : Polynomial.aeval
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
        equalCharacteristicCompletedLevelField F n)
      (equalCharacteristicChangedPrimitivePolynomial F a n) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isRoot_target F a n
  have hmin := minpoly.eq_of_irreducible
    (equalCharacteristicChangedPrimitivePolynomial_irreducible F a n) hroot
  rw [(equalCharacteristicChangedPrimitivePolynomial_monic F a n).leadingCoeff,
    inv_one, Polynomial.C_1, mul_one] at hmin
  exact hmin.symm

/-- The fixed field has the exact degree of the target division level `n + 1`:
`[Sigma : k((T))] = (q - 1) q^n`. -/
theorem equalCharacteristicCompletedFrobeniusFixedField_finrank
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Module.finrank F.residueField⸨X⸩
        (equalCharacteristicCompletedFrobeniusFixedField F a n) =
      (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n := by
  let E := IntermediateField.adjoin F.residueField⸨X⸩
    ({(equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
      equalCharacteristicCompletedLevelField F n)} :
      Set (equalCharacteristicCompletedLevelField F n))
  let EAlgebra : Algebra F.residueField⸨X⸩ E :=
    Subalgebra.algebra E.toSubalgebra
  let ESMul : SMul F.residueField⸨X⸩ E :=
    @Algebra.toSMul _ _ _ _ EAlgebra
  let EModule : Module F.residueField⸨X⸩ E :=
    @Algebra.toModule _ _ _ _ EAlgebra
  have hfield : equalCharacteristicCompletedFrobeniusFixedField F a n = E :=
    equalCharacteristicCompletedFrobeniusFixedField_eq_adjoin_directTheta F a n
  calc
    Module.finrank F.residueField⸨X⸩
        (equalCharacteristicCompletedFrobeniusFixedField F a n) =
      Module.finrank F.residueField⸨X⸩ E :=
        (IntermediateField.equivOfEq hfield).toLinearEquiv.finrank_eq
    _ = (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n := by
      dsimp only [E]
      rw [IntermediateField.adjoin.finrank
          (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isIntegral_laurentBase
            F a n),
        equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_minpoly_laurentBase,
        equalCharacteristicChangedPrimitivePolynomial_natDegree]

end EqualCharacteristic
end LubinTate
