/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
import Mathlib.RingTheory.Norm.Basic
/-!
# The uniformizer norm identity: the uniformizer norm in the equal-characteristic level field

For a primitive level-`n+1` division point `λ`, its Eisenstein minimal
polynomial has constant coefficient `T`.  The power-basis norm formula
therefore gives the norm identity `N(-λ) = T`.
-/

noncomputable section


open scoped PowerSeries LaurentSeries Polynomial

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The constant coefficient of the primitive division polynomial is the
Laurent-series uniformizer `T`. -/
theorem equalCharacteristicLubinTatePrimitivePolynomial_coeff_zero
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicLubinTatePrimitivePolynomial F n).coeff 0 =
      equalCharacteristicLaurentUniformizer F := by
  rw [← equalCharacteristicLubinTateIntegralPrimitivePolynomial_map]
  rw [Polynomial.coeff_map,
    equalCharacteristicLubinTateIntegralPrimitivePolynomial_coeff_zero]
  rfl

/-- The chosen primitive point, regarded as the generator of its level
field. -/
noncomputable def equalCharacteristicLubinTateLevelGenerator
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) : equalCharacteristicLubinTateLevelField F n :=
  IntermediateField.AdjoinSimple.gen F.residueField⸨X⸩
    (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)

/-- States the theorem `equalCharacteristicLubinTateLevelGenerator_eq_powerBasis_gen`. -/
theorem equalCharacteristicLubinTateLevelGenerator_eq_powerBasis_gen
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateLevelGenerator F n =
      (IntermediateField.adjoin.powerBasis
        (chosenEqualCharacteristicLubinTatePrimitiveRoot_isIntegral F n)).gen := by
  apply Subtype.ext
  simp [equalCharacteristicLubinTateLevelGenerator,
    equalCharacteristicLubinTateLevelField,
    IntermediateField.adjoin.powerBasis_gen]

/-- The norm of a negative element, isolated from the large concrete
Lubin--Tate level-field expression. -/
private theorem algebraNorm_neg
    {R S : Type*} [Field R] [Field S] [Algebra R S] (x : S) :
    Algebra.norm R (-x) = (-1) ^ Module.finrank R S * Algebra.norm R x := by
  rw [show -x = algebraMap R S (-1) * x by simp]
  rw [map_mul, Algebra.norm_algebraMap]

/-- The uniformizer norm identity, uniformizer part: the norm of the negative primitive
division point is exactly `T`. -/
theorem equalCharacteristicLubinTate_norm_neg_levelGenerator
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Algebra.norm F.residueField⸨X⸩
        (-equalCharacteristicLubinTateLevelGenerator F n) =
      equalCharacteristicLaurentUniformizer F := by
  let pb := IntermediateField.adjoin.powerBasis
    (chosenEqualCharacteristicLubinTatePrimitiveRoot_isIntegral F n)
  have hmin : minpoly F.residueField⸨X⸩ pb.gen =
      equalCharacteristicLubinTatePrimitivePolynomial F n := by
    simpa [pb, IntermediateField.adjoin.powerBasis_gen,
      IntermediateField.minpoly_gen] using
      (equalCharacteristicLubinTatePrimitivePolynomial_eq_minpoly F n).symm
  have hfinrank : Module.finrank F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) = pb.dim := by
    simpa [equalCharacteristicLubinTateLevelField, pb] using pb.finrank
  rw [algebraNorm_neg,
    equalCharacteristicLubinTateLevelGenerator_eq_powerBasis_gen,
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
    hmin, equalCharacteristicLubinTatePrimitivePolynomial_coeff_zero]
  rw [hfinrank]
  simp only [pb, IntermediateField.adjoin.powerBasis_dim]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

end EqualCharacteristic
end LubinTate
