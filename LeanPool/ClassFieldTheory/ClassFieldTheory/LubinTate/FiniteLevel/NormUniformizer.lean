/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveUniformizer
import Mathlib.RingTheory.Norm.Basic
/-!
# Norm of a primitive standard Lubin--Tate point

The minimal polynomial of the chosen primitive level generator is the
standard Eisenstein polynomial, whose constant coefficient is the base
uniformizer.  The power-basis norm formula therefore gives
`N(-lambda) = pi`.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

private theorem algebraNorm_neg
    {R S : Type*} [Field R] [Field S] [Algebra R S] (x : S) :
    Algebra.norm R (-x) =
      (-1) ^ Module.finrank R S * Algebra.norm R x := by
  rw [show -x = algebraMap R S (-1) * x by simp]
  rw [map_mul, Algebra.norm_algebraMap]

/-- The standard primitive polynomial over the base field has constant
coefficient `pi`. -/
@[simp]
theorem standardLubinTatePrimitivePolynomialOverField_coeff_zero
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePrimitivePolynomialOverField F π n).coeff 0 =
      (π : K) := by
  simp [standardLubinTatePrimitivePolynomialOverField]

/-- The norm of the negative primitive level generator is exactly the
chosen base uniformizer. -/
theorem standardLubinTate_norm_neg_levelGenerator
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    Algebra.norm K (-standardLubinTateLevelGenerator hπ n) = (π : K) := by
  let pb := standardLubinTateLevelPowerBasis hπ n
  have hfinrank :
      Module.finrank K (standardLubinTateLevelField hπ n) = pb.dim := by
    simpa [pb] using pb.finrank
  rw [algebraNorm_neg,
    show standardLubinTateLevelGenerator hπ n = pb.gen by rfl,
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
    standardLubinTateLevelPowerBasis_minpoly hπ n,
    standardLubinTatePrimitivePolynomialOverField_coeff_zero]
  rw [hfinrank]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

end LubinTate

end
