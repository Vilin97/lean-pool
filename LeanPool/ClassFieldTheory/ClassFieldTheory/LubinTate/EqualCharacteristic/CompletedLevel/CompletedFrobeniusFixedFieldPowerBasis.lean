/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPrimitive
/-!
# The completed theta-intertwining theorem: the fixed primitive completed power basis

The direct theta value supplies the power basis used to descend coefficients
of elements fixed by the prescribed completed Frobenius.
-/

noncomputable section

open scoped LaurentSeries Polynomial PowerSeries


universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The completed base is a Laurent-series algebra through coefficient extension for the
fixed-field power-basis construction. -/
noncomputable local instance
    equalCharacteristicCompletedFrobeniusFixedFieldCompletedPowerBasisBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

/-- Defines `equalCharacteristicDirectThetaCompletedPowerBasis`. -/
noncomputable def equalCharacteristicDirectThetaCompletedPowerBasis
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    PowerBasis (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) := by
  apply PowerBasis.ofAdjoinEqTop
    (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isIntegral_completedBase
      F a n)
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isIntegral_completedBase
        F a n).isAlgebraic,
    equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_adjoin_completedBase_eq_top,
    IntermediateField.top_toSubalgebra]

/-- States the theorem `equalCharacteristicDirectThetaCompletedPowerBasis_gen`. -/
@[simp]
theorem equalCharacteristicDirectThetaCompletedPowerBasis_gen
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicDirectThetaCompletedPowerBasis F a n).gen =
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
        equalCharacteristicCompletedLevelField F n) :=
  PowerBasis.ofAdjoinEqTop_gen _ _

end EqualCharacteristic
end LubinTate
