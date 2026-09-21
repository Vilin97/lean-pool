/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaIntegralClosure
/-!
# the finite norm-formula absolute value

The factorization form of Hensel's lemma makes the closed unit ball of the
finite norm-formula value equal to the integral elements over the base
valuation ring.  This supplies the strong triangle inequality and hence the
absolute value without completeness or separatedness assumptions.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

/-- The closed unit ball of the finite norm-formula value is closed under
addition, using only the primitive factorization form of Hensel's lemma. -/
theorem normFormula_finiteExtensionNormFormulaValue_add_le_one_of_le_one_of_henselFactorization
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    {x y : L}
    (hx : finiteExtensionNormFormulaValue v x ≤ 1)
    (hy : finiteExtensionNormFormulaValue v y ≤ 1) :
    finiteExtensionNormFormulaValue v (x + y) ≤ 1 := by
  exact normFormula_finiteExtensionNormFormulaValue_le_one_of_isIntegral
    v hnonarch
    (IsIntegral.add
      (normFormula_finiteExtensionNormFormulaValue_isIntegral_of_le_one_of_henselFactorization
        v hnonarch hv hx)
      (normFormula_finiteExtensionNormFormulaValue_isIntegral_of_le_one_of_henselFactorization
        v hnonarch hv hy))

/-- The finite norm-formula value satisfies the strong nonarchimedean triangle
inequality under the primitive factorization form of Hensel's lemma. -/
theorem normFormula_finiteExtensionNormFormulaValue_strong_triangle_of_henselFactorization
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    (x y : L) :
    finiteExtensionNormFormulaValue v (x + y) ≤
      max (finiteExtensionNormFormulaValue v x)
        (finiteExtensionNormFormulaValue v y) := by
  have hle_left :
      ∀ {x y : L},
        finiteExtensionNormFormulaValue v y ≤
          finiteExtensionNormFormulaValue v x →
        finiteExtensionNormFormulaValue v (x + y) ≤
          finiteExtensionNormFormulaValue v x := by
    intro x y hyx
    by_cases hx0 : x = 0
    · rw [hx0, zero_add]
      simpa [hx0,
        (normFormula_finiteExtensionNormFormulaValue_eq_zero_iff v
          (0 : L)).2 rfl] using hyx
    · have hxne :
          finiteExtensionNormFormulaValue v x ≠ 0 := by
        intro hxzero
        exact hx0
          ((normFormula_finiteExtensionNormFormulaValue_eq_zero_iff v x).1
            hxzero)
      have hxpos : 0 < finiteExtensionNormFormulaValue v x :=
        lt_of_le_of_ne
          (finiteExtensionNormFormulaValue_nonneg v x)
          (fun h => hxne h.symm)
      have hone :
          finiteExtensionNormFormulaValue v (1 : L) ≤ 1 := by
        rw [← (show algebraMap K L (1 : K) = (1 : L) by simp),
          normFormula_finiteExtensionNormFormulaValue_algebraMap]
        simp
      have hydiv :
          finiteExtensionNormFormulaValue v (y / x) ≤ 1 := by
        rw [normFormula_finiteExtensionNormFormulaValue_div]
        exact (div_le_one hxpos).2 hyx
      have hadd :
          finiteExtensionNormFormulaValue v (1 + y / x) ≤ 1 :=
        normFormula_finiteExtensionNormFormulaValue_add_le_one_of_le_one_of_henselFactorization
          v hnonarch hv hone hydiv
      have hdecomp : x + y = x * (1 + y / x) := by
        rw [mul_add, mul_one, mul_div_cancel₀ y hx0]
      calc
        finiteExtensionNormFormulaValue v (x + y)
            = finiteExtensionNormFormulaValue v (x * (1 + y / x)) := by
              rw [hdecomp]
        _ = finiteExtensionNormFormulaValue v x *
              finiteExtensionNormFormulaValue v (1 + y / x) := by
              rw [normFormula_finiteExtensionNormFormulaValue_mul]
        _ ≤ finiteExtensionNormFormulaValue v x * 1 :=
              mul_le_mul_of_nonneg_left hadd
                (finiteExtensionNormFormulaValue_nonneg v x)
        _ = finiteExtensionNormFormulaValue v x := by simp
  rcases le_total (finiteExtensionNormFormulaValue v y)
      (finiteExtensionNormFormulaValue v x) with hyx | hxy
  · exact (hle_left hyx).trans
      (le_max_left (finiteExtensionNormFormulaValue v x)
        (finiteExtensionNormFormulaValue v y))
  · have hyx_add :
        finiteExtensionNormFormulaValue v (y + x) ≤
          finiteExtensionNormFormulaValue v y :=
      hle_left hxy
    calc
      finiteExtensionNormFormulaValue v (x + y)
          = finiteExtensionNormFormulaValue v (y + x) := by rw [add_comm]
      _ ≤ finiteExtensionNormFormulaValue v y := hyx_add
      _ ≤ max (finiteExtensionNormFormulaValue v x)
            (finiteExtensionNormFormulaValue v y) :=
          le_max_right _ _

/-- the finite norm-formula theorem finite norm formula bundled as an absolute value, assuming
only the primitive factorization form of Hensel's lemma on the base valuation
ring. -/
noncomputable def normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch)) :
    AbsoluteValue L ℝ where
  toFun := finiteExtensionNormFormulaValue v
  map_mul' x y := normFormula_finiteExtensionNormFormulaValue_mul v x y
  nonneg' x := finiteExtensionNormFormulaValue_nonneg v x
  eq_zero' x := normFormula_finiteExtensionNormFormulaValue_eq_zero_iff v x
  add_le' x y := by
    have hstrong :=
      normFormula_finiteExtensionNormFormulaValue_strong_triangle_of_henselFactorization
        v hnonarch hv x y
    have hx_nonneg : 0 ≤ finiteExtensionNormFormulaValue v x :=
      finiteExtensionNormFormulaValue_nonneg v x
    have hy_nonneg : 0 ≤ finiteExtensionNormFormulaValue v y :=
      finiteExtensionNormFormulaValue_nonneg v y
    exact hstrong.trans
      (max_le
        (le_add_of_nonneg_right hy_nonneg)
        (le_add_of_nonneg_left hx_nonneg))

/-- The bundled finite norm-formula absolute value is pointwise the construction's
displayed value. -/
theorem normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_apply
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    (x : L) :
    normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization
        (K := K) (L := L) v hnonarch hv x =
      finiteExtensionNormFormulaValue v x :=
  rfl

/-- The bundled norm-formula absolute value restricts to the original base
absolute value. -/
theorem normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_extends_base
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    (x : K) :
    normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization
        (K := K) (L := L) v hnonarch hv (algebraMap K L x) = v x :=
  normFormula_finiteExtensionNormFormulaValue_algebraMap v x

/-- The bundled finite norm-formula absolute value is nonarchimedean. -/
theorem normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_nonarchimedean
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch)) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue
      (normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization
        (K := K) (L := L) v hnonarch hv) := by
  refine LubinTate.Valuations.nonarchimedean_of_strong_triangle
    (normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization
      (K := K) (L := L) v hnonarch hv) ?_
  intro x y
  exact
    normFormula_finiteExtensionNormFormulaValue_strong_triangle_of_henselFactorization
      v hnonarch hv x y

/-- The closed unit ball of the bundled norm formula consists exactly of the
elements integral over the base valuation ring. -/
theorem normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_mem_valuationSubring_iff_isIntegral
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    (x : L) :
    x ∈ absoluteValueValuationSubring
        (normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization
          (K := K) (L := L) v hnonarch hv)
        (normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_nonarchimedean
          (K := K) (L := L) v hnonarch hv) ↔
      IsIntegral
        (absoluteValueValuationSubring v hnonarch) x := by
  rw [mem_absoluteValueValuationSubring_iff,
    normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_apply]
  constructor
  · exact
      normFormula_finiteExtensionNormFormulaValue_isIntegral_of_le_one_of_henselFactorization
        v hnonarch hv
  · exact normFormula_finiteExtensionNormFormulaValue_le_one_of_isIntegral
      v hnonarch

/-- The valuation ring of the bundled finite norm formula is the actual
integral closure of the base valuation ring in `L`. -/
theorem normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_valuationSubring_eq_integralClosure
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch)) :
    (absoluteValueValuationSubring
        (normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization
          (K := K) (L := L) v hnonarch hv)
        (normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_nonarchimedean
          (K := K) (L := L) v hnonarch hv)).toSubring =
      (integralClosure
        (R := absoluteValueValuationSubring
          v hnonarch) L).toSubring := by
  ext x
  exact
    normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_mem_valuationSubring_iff_isIntegral
      (K := K) (L := L) v hnonarch hv x

end Valuations
end AlgebraicNumberTheory

end
