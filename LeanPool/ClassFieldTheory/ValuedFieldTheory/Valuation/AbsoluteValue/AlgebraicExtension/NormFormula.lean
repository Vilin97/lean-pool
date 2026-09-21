/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.ValuationSubring
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Completeness
import Mathlib.RingTheory.Norm.Transitivity
/-!
# the finite norm-formula theorem

Algebraic facts about the finite norm formula used in the explicit proof of
The algebraic-extension norm formula, together with restriction of a valued field tower to an
intermediate field.
-/

noncomputable section

universe u v w x y z

namespace AlgebraicNumberTheory
namespace Valuations

private theorem normFormula_real_natPow_rpow_inv_mul_cancel
    {a : ℝ} (ha : 0 ≤ a) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (a ^ n) ^ (1 / ((m * n : ℕ) : ℝ)) = a ^ (1 / (m : ℝ)) := by
  by_cases ha0 : a = 0
  · have hmn_ne : ((m * n : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.mul_ne_zero (Nat.ne_of_gt hm) (Nat.ne_of_gt hn)
    have hm_ne : (m : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hm
    rw [ha0, zero_pow (Nat.ne_of_gt hn),
      Real.zero_rpow (one_div_ne_zero hmn_ne),
      Real.zero_rpow (one_div_ne_zero hm_ne)]
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (fun h => ha0 h.symm)
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha_pos.le]
    have hm_ne : (m : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hm
    have hn_ne : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    congr 1
    field_simp [hm_ne, hn_ne]
    norm_num [Nat.cast_mul, mul_comm]

/-- the finite norm-formula theorem, finite absolute-value norm-formula algebraic source: the
candidate `|N_{L/K}(x)|^(1/[L:K])` reduces to the same constant-term
formula as the spectral construction in the complete case.

This is purely algebraic and does not use Henselianity.  The remaining
the finite norm-formula theorem work is to identify the unique Henselian extension with this
candidate absolute value. -/
theorem normFormula_finiteExtensionNormFormulaValue_eq_minpoly_coeff_zero_rpow
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x : L) :
    finiteExtensionNormFormulaValue v x =
      v ((minpoly K x).coeff 0) ^
        (1 / ((minpoly K x).natDegree : ℝ)) := by
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let : Algebra.IsIntegral K L := Algebra.IsAlgebraic.isIntegral
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  let : FiniteDimensional K (IntermediateField.adjoin K ({x} : Set L)) :=
    IntermediateField.adjoin.finiteDimensional hxint
  let : FiniteDimensional (IntermediateField.adjoin K ({x} : Set L)) L :=
    FiniteDimensional.right K (IntermediateField.adjoin K ({x} : Set L)) L
  have hd_pos : 0 < (minpoly K x).natDegree :=
    minpoly.natDegree_pos hxint
  have hr_pos :
      0 < Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L :=
    Module.finrank_pos
      (R := IntermediateField.adjoin K ({x} : Set L)) (M := L)
  have hnorm :
      v (Algebra.norm K x) =
        v ((minpoly K x).coeff 0) ^
          Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L := by
    rw [Algebra.norm_eq_norm_adjoin K x, map_pow]
    have hgen :
        Algebra.norm K (IntermediateField.AdjoinSimple.gen K x) =
          (-1 : K) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0 := by
      simpa [IntermediateField.adjoin.powerBasis_gen,
        IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim]
        using
          (Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
            (IntermediateField.adjoin.powerBasis hxint))
    rw [hgen, v.map_mul, v.map_pow, AbsoluteValue.map_neg]
    simp
  rw [finiteExtensionNormFormulaValue, hnorm]
  rw [← Module.finrank_mul_finrank K
      (IntermediateField.adjoin K ({x} : Set L)) L,
    IntermediateField.adjoin.finrank hxint]
  exact normFormula_real_natPow_rpow_inv_mul_cancel
    (v.nonneg ((minpoly K x).coeff 0)) hd_pos hr_pos

/-- the finite norm-formula theorem, finite absolute-value norm-formula base-extension source:
the candidate `|N_{L/K}(x)|^(1/[L:K])` restricts to the original
absolute value on the base field.

This verifies the extension part of the finite root-form formula without
using completeness or Henselianity. -/
theorem normFormula_finiteExtensionNormFormulaValue_algebraMap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (a : K) :
    finiteExtensionNormFormulaValue v (algebraMap K L a) = v a := by
  have hn : 0 < Module.finrank K L :=
    Module.finrank_pos (R := K) (M := L)
  rw [finiteExtensionNormFormulaValue, Algebra.norm_algebraMap, v.map_pow]
  simpa using
    (normFormula_real_natPow_rpow_inv_mul_cancel
      (a := v a) (m := 1) (n := Module.finrank K L)
      (v.nonneg a) (by norm_num) hn)

/-- the finite norm-formula theorem, finite absolute-value norm-formula source: raising the
candidate `|N_{L/K}(x)|^(1/[L:K])` to `[L : K]` recovers
`|N_{L/K}(x)|`. -/
theorem normFormula_finiteExtensionNormFormulaValue_pow_finrank_eq_norm
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x : L) :
    finiteExtensionNormFormulaValue v x ^ Module.finrank K L =
      v (Algebra.norm K x) := by
  have hn : Module.finrank K L ≠ 0 :=
    Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))
  simpa [finiteExtensionNormFormulaValue, one_div] using
    (Real.rpow_inv_natCast_pow (v.nonneg (Algebra.norm K x)) hn)

/-- the finite norm-formula theorem, finite absolute-value norm-formula zero source:
the norm-formula candidate vanishes exactly at zero. -/
theorem normFormula_finiteExtensionNormFormulaValue_eq_zero_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x : L) :
    finiteExtensionNormFormulaValue v x = 0 ↔ x = 0 := by
  have hn : (1 / (Module.finrank K L : ℝ)) ≠ 0 := by
    exact ne_of_gt (one_div_pos.mpr (by
      exact_mod_cast (Module.finrank_pos (R := K) (M := L))))
  have hpow :
      v (Algebra.norm K x) ^ (1 / (Module.finrank K L : ℝ)) = 0 ↔
        v (Algebra.norm K x) = 0 :=
    Real.rpow_eq_zero (v.nonneg (Algebra.norm K x)) hn
  have hnorm : v (Algebra.norm K x) = 0 ↔ x = 0 := by
    rw [v.eq_zero]
    exact Algebra.norm_eq_zero_iff
  simpa [finiteExtensionNormFormulaValue] using hpow.trans hnorm

/-- the finite norm-formula theorem, finite absolute-value norm-formula multiplicative source:
the norm-formula candidate is multiplicative. -/
theorem normFormula_finiteExtensionNormFormulaValue_mul
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x y : L) :
    finiteExtensionNormFormulaValue v (x * y) =
      finiteExtensionNormFormulaValue v x *
        finiteExtensionNormFormulaValue v y := by
  rw [finiteExtensionNormFormulaValue, finiteExtensionNormFormulaValue,
    finiteExtensionNormFormulaValue,
    show Algebra.norm K (x * y) = Algebra.norm K x * Algebra.norm K y from
      map_mul (Algebra.norm K) x y,
    v.map_mul]
  exact Real.mul_rpow
    (v.nonneg (Algebra.norm K x)) (v.nonneg (Algebra.norm K y))

/-- the finite norm-formula theorem, finite absolute-value norm-formula inverse source:
the norm-formula candidate sends inverses to inverses. -/
theorem normFormula_finiteExtensionNormFormulaValue_inv
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x : L) :
    finiteExtensionNormFormulaValue v x⁻¹ =
      (finiteExtensionNormFormulaValue v x)⁻¹ := by
  rw [finiteExtensionNormFormulaValue, finiteExtensionNormFormulaValue,
    show Algebra.norm K x⁻¹ = (Algebra.norm K x)⁻¹ from
      Algebra.norm_inv (K := K) x,
    map_inv₀ v (Algebra.norm K x)]
  exact Real.inv_rpow (v.nonneg (Algebra.norm K x))
    (1 / (Module.finrank K L : ℝ))

/-- the finite norm-formula theorem, finite absolute-value norm-formula division source:
the norm-formula candidate is compatible with division. -/
theorem normFormula_finiteExtensionNormFormulaValue_div
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x y : L) :
    finiteExtensionNormFormulaValue v (x / y) =
      finiteExtensionNormFormulaValue v x /
        finiteExtensionNormFormulaValue v y := by
  rw [div_eq_mul_inv, normFormula_finiteExtensionNormFormulaValue_mul,
    normFormula_finiteExtensionNormFormulaValue_inv, div_eq_mul_inv]

/-- the finite norm-formula theorem, finite absolute-value norm-formula closed-unit/minpoly
source: the candidate is at most one exactly when the constant
coefficient of the minimal polynomial has base absolute value at most one. -/
theorem normFormula_finiteExtensionNormFormulaValue_le_one_iff_minpoly_coeff_zero_le_one
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x : L) :
    finiteExtensionNormFormulaValue v x ≤ 1 ↔
      v ((minpoly K x).coeff 0) ≤ 1 := by
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let : Algebra.IsIntegral K L := Algebra.IsAlgebraic.isIntegral
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hd : 0 < (1 / ((minpoly K x).natDegree : ℝ)) := by
    exact one_div_pos.mpr (by
      exact_mod_cast (minpoly.natDegree_pos hxint))
  rw [normFormula_finiteExtensionNormFormulaValue_eq_minpoly_coeff_zero_rpow]
  simpa using
    (Real.rpow_le_rpow_iff
      (v.nonneg ((minpoly K x).coeff 0)) zero_le_one hd)

/-- the finite norm-formula theorem, finite norm-formula/integrality source in the reverse
direction: integrality over the base closed-unit valuation ring forces the
finite norm-formula candidate to be at most one. -/
theorem normFormula_finiteExtensionNormFormulaValue_le_one_of_isIntegral
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {x : L}
    (hx : IsIntegral
      (absoluteValueValuationSubring v hnonarch) x) :
    finiteExtensionNormFormulaValue v x ≤ 1 := by
  let V := absoluteValueValuationSubring v hnonarch
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let : Algebra.IsIntegral K L := Algebra.IsAlgebraic.isIntegral
  have hmin :
      minpoly K x = (minpoly V x).map (algebraMap V K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hx
  have hconst : v ((minpoly K x).coeff 0) ≤ 1 := by
    rw [hmin, Polynomial.coeff_map]
    exact
      (mem_absoluteValueValuationSubring_iff
        v hnonarch (((minpoly V x).coeff 0 : V) : K)).1
        ((minpoly V x).coeff 0).property
  exact
    (normFormula_finiteExtensionNormFormulaValue_le_one_iff_minpoly_coeff_zero_le_one
      v x).2 hconst

end Valuations
end AlgebraicNumberTheory

namespace DiscreteValuationField

namespace Valuation

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {ΓK : Type v} [LinearOrderedCommGroupWithZero ΓK]

/-- Restricting a valuation on the top of a field tower to the middle field
preserves the fact that it extends the bottom valuation. -/
theorem comap_to_middle_hasExtension_of_top_hasExtension
    {M : Type y} [Field M] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    {ΓM : Type z} [LinearOrderedCommGroupWithZero ΓM]
    (vK : _root_.Valuation K ΓK) (vM : _root_.Valuation M ΓM)
    [vK.HasExtension vM] :
    vK.HasExtension (vM.comap (algebraMap L M)) := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext a
  simp only [Subring.mem_comap]
  change
    vM (algebraMap L M ((algebraMap K L) a)) ≤ 1 ↔
      vK a ≤ 1
  rw [← IsScalarTower.algebraMap_apply K L M a]
  exact _root_.Valuation.HasExtension.val_map_le_one_iff
    (vR := vK) (vA := vM) a

end Valuation
end DiscreteValuationField

end
