/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnits
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedField
/-!
# LubinTate the explicit norm-subgroup computation: higher units fix the primitive point

If `a` is congruent to one modulo `T^(n+1)`, the completed the completed theta-intertwining theorem
Frobenius attached to `a` acts trivially on the standard primitive
`(n+1)`-division point.
-/

noncomputable section


open scoped LaurentSeries PowerSeries

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type} [Field K]

/-- The Laurent-series base acts on the completed unramified field through the coefficient
embedding. -/
noncomputable local instance equalCharacteristicHigherUnitFixedBaseAlgebra
    (F : LocalField K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedFrobeniusFixedBaseAlgebra F

/-- States the theorem
`equalCharacteristicCompletedFrobeniusAlgEquiv_primitiveRoot_fixed_of_mem_higherUnit`. -/
theorem
    equalCharacteristicCompletedFrobeniusAlgEquiv_primitiveRoot_fixed_of_mem_higherUnit
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (ha : a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n) :
    equalCharacteristicCompletedFrobeniusAlgEquiv F a n
        (equalCharacteristicCompletedPrimitiveRoot F n) =
      equalCharacteristicCompletedPrimitiveRoot F n := by
  have hainv : a⁻¹ ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n :=
    (equalCharacteristicLubinTateHigherUnitSubgroup F n).inv_mem ha
  have hdvd : PowerSeries.X ^ (n + 1) ∣
      ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧) - 1 := by
    rw [← Ideal.mem_span_singleton]
    exact
      (mem_equalCharacteristicLubinTateHigherUnitSubgroup F n a⁻¹).1 hainv
  have hcoeff : ∀ j < n + 1,
      PowerSeries.coeff j
          ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧) =
        PowerSeries.coeff j (1 : F.residueField⟦X⟧) := by
    intro j hj
    have hz := PowerSeries.X_pow_dvd_iff.mp hdvd j hj
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  have hbracket :
      equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicCompletedLevelResidueHom F n)
          (equalCharacteristicCompletedLevelUniformizer F n) (n + 1)
          ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
          (equalCharacteristicCompletedPrimitiveRoot F n) =
        equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicCompletedLevelResidueHom F n)
          (equalCharacteristicCompletedLevelUniformizer F n) (n + 1) 1
          (equalCharacteristicCompletedPrimitiveRoot F n) :=
    DFunLike.congr_fun
      (equalCharacteristicLubinTateAmbientBracket_eq_of_coeff_eq F
        (equalCharacteristicCompletedLevelResidueHom F n)
        (equalCharacteristicCompletedLevelUniformizer F n) (n + 1)
        ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧) 1 hcoeff)
      (equalCharacteristicCompletedPrimitiveRoot F n)
  rw [equalCharacteristicCompletedFrobeniusAlgEquiv_apply]
  change equalCharacteristicCompletedFrobeniusLiftEquiv F n a⁻¹
      (equalCharacteristicCompletedPrimitiveRoot F n) = _
  rw [equalCharacteristicCompletedFrobeniusLiftEquiv_primitiveRoot,
    equalCharacteristicCompletedUnitRoot]
  exact hbracket.trans
    (equalCharacteristicLubinTateAmbientBracket_one_apply_of_torsion F
      (equalCharacteristicCompletedLevelResidueHom F n)
      (equalCharacteristicCompletedLevelUniformizer F n) (n + 1)
      (equalCharacteristicCompletedPrimitiveRoot F n)
      (equalCharacteristicCompletedPrimitiveRoot_torsion F n))

end EqualCharacteristic
end LubinTate
