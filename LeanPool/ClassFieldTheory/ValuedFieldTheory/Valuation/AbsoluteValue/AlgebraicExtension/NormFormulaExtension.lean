/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaAbsoluteValue
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueValuationSubring
/-!
# algebraic extension and integral closure

This file packages the explicit algebraic-extension statement.  A
valuation is represented by its valuation subring, so uniqueness is literal
equality of valuation subrings (equivalently, equivalence of valuations).
-/

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv_hasExtension →
    integralClosureValuationSubringOfMemOrInv_hasExtension


noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

/-- the primitive factorization definition for the valuation subring attached to a nonarchimedean
absolute value, reduced to the exact factorization property used below. -/
theorem henselianValuation_iff_henselFactorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) :
    ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
        (absoluteValueValuationSubring
          v hnonarch).valuation ↔
      ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
        (absoluteValueValuationSubring v hnonarch) := by
  simp only [ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization,
    ValuationSubring.valuationSubring_valuation]

/-- the finite norm-formula theorem: a Henselian nonarchimedean valuation has exactly one
extension to every algebraic extension, and the valuation ring of that
extension is the actual integral closure of the base valuation ring.

The extension is expressed by its valuation subring.  The first conjunct says
that its canonical valuation extends the base valuation; the second is the
integral-closure identification. -/
theorem normFormula_algebraic_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (absoluteValueValuationSubring
        v hnonarch).valuation) :
    let V := absoluteValueValuationSubring v hnonarch
    ∃! W : ValuationSubring L,
      V.valuation.HasExtension W.valuation ∧
        W.toSubring = (integralClosure V L).toSubring := by
  let V := absoluteValueValuationSubring v hnonarch
  have hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty V :=
    (henselianValuation_iff_henselFactorization v hnonarch).1 hhens
  have hvalV :
      ∀ z : L,
        z ∈ (integralClosure V L).toSubring ∨
          z⁻¹ ∈ (integralClosure V L).toSubring :=
    normFormula_algebraic_integralClosure_mem_or_inv_of_henselFactorization
      v hnonarch hv
  have hval :
      ∀ z : L,
        z ∈ (integralClosure V.valuation.valuationSubring L).toSubring ∨
          z⁻¹ ∈
            (integralClosure V.valuation.valuationSubring L).toSubring := by
    rw [ValuationSubring.valuationSubring_valuation]
    exact hvalV
  let B : ValuationSubring L :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) V.valuation hval
  have hBext : V.valuation.HasExtension B.valuation :=
    integralClosureValuationSubringOfMemOrInv_hasExtension
      (L := L) V.valuation hval
  have hBclosure : B.toSubring = (integralClosure V L).toSubring := by
    change
      (integralClosure V.valuation.valuationSubring L).toSubring =
        (integralClosure V L).toSubring
    rw [ValuationSubring.valuationSubring_valuation]
  refine ⟨B, ⟨hBext, hBclosure⟩, ?_⟩
  intro W hW
  let : V.valuation.HasExtension W.valuation := hW.1
  simpa only [ValuationSubring.valuationSubring_valuation] using
    DiscreteValuationField.Valuation.normFormula_extension_valuationSubring_eq_integralClosure_of_mem_or_inv
      (K := K) (L := L) V hval W.valuation

/-- Exact extension of nonarchimedean absolute values supplies extension of
the canonical valuations of their closed unit balls. -/
theorem absoluteValueValuation_hasExtension_of_extends
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hw : LubinTate.Valuations.NonarchimedeanAbsoluteValue w)
    (hext : ∀ a : K, w (algebraMap K L a) = v a) :
    let V := absoluteValueValuationSubring v hv
    let W := absoluteValueValuationSubring w hw
    V.valuation.HasExtension W.valuation := by
  let V := absoluteValueValuationSubring v hv
  let W := absoluteValueValuationSubring w hw
  apply _root_.Valuation.HasExtension.ofComapInteger
  rw [ValuationSubring.integer_valuation, ValuationSubring.integer_valuation]
  have hcomap :=
    comap_absoluteValueUnitBallSubring_eq_of_extends
      v w hv hw hext
  ext x
  change algebraMap K L x ∈ absoluteValueUnitBallSubring w hw ↔
    x ∈ absoluteValueUnitBallSubring v hv
  constructor
  · intro hx
    have hx' : x ∈ Subring.comap (algebraMap K L)
        (absoluteValueUnitBallSubring w hw) := hx
    rw [hcomap] at hx'
    exact hx'
  · intro hx
    have hx' : x ∈ Subring.comap (algebraMap K L)
        (absoluteValueUnitBallSubring w hw) := by
      rw [hcomap]
      exact hx
    exact hx'

/-- Equality of the closed unit balls of an extension absolute value and the
finite norm-formula absolute value forces pointwise equality.  The normalization
is recovered by taking the field norm, so equivalence of valuations is
upgraded to equality of the chosen absolute values. -/
theorem normFormula_finite_normFormulaAbsoluteValue_eq_of_valuationSubring_eq_of_henselFactorization
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    (w : AbsoluteValue L ℝ) (hwnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue w)
    (hw_ext : ∀ a : K, w (algebraMap K L a) = v a)
    (hsub :
      absoluteValueValuationSubring w hwnonarch =
        absoluteValueValuationSubring
          (normFormulaFiniteNormFormulaAbsoluteValueOfHenselFactorization
            (K := K) (L := L) v hnonarch hv)
          (normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_nonarchimedean
            (K := K) (L := L) v hnonarch hv)) :
    w =
      normFormulaFiniteNormFormulaAbsoluteValueOfHenselFactorization
        (K := K) (L := L) v hnonarch hv := by
  ext x
  let rAbs :=
    normFormulaFiniteNormFormulaAbsoluteValueOfHenselFactorization
      (K := K) (L := L) v hnonarch hv
  let hrnonarch :=
    normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_nonarchimedean
      (K := K) (L := L) v hnonarch hv
  by_cases hx : x = 0
  · simp [hx]
  · let n := Module.finrank K L
    have hn_pos : 0 < n := Module.finrank_pos (R := K) (M := L)
    have hn_ne : n ≠ 0 := Nat.ne_of_gt hn_pos
    have hnorm_ne : Algebra.norm K x ≠ 0 :=
      (Algebra.norm_ne_zero_iff).2 hx
    have hbase_norm_ne : algebraMap K L (Algebra.norm K x) ≠ 0 :=
      (map_ne_zero (algebraMap K L)).2 hnorm_ne
    have hxpow_ne : x ^ n ≠ 0 := pow_ne_zero n hx
    let z := x ^ n / algebraMap K L (Algebra.norm K x)
    have hz_ne : z ≠ 0 := by
      dsimp [z]
      exact div_ne_zero hxpow_ne hbase_norm_ne
    have hvnorm_ne : v (Algebra.norm K x) ≠ 0 := by
      intro hzero
      exact hnorm_ne ((v.eq_zero).1 hzero)
    have hr_pow : rAbs x ^ n = v (Algebra.norm K x) := by
      simp [rAbs,
        normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_apply,
        normFormula_finiteExtensionNormFormulaValue_pow_finrank_eq_norm,
        n]
    have hrz : rAbs z = 1 := by
      dsimp [z]
      rw [map_div₀, AbsoluteValue.map_pow]
      rw [hr_pow]
      rw [show rAbs (algebraMap K L (Algebra.norm K x)) =
          v (Algebra.norm K x) from by
        simpa [rAbs] using
          normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_extends_base
            (K := K) (L := L) v hnonarch hv (Algebra.norm K x)]
      exact div_self hvnorm_ne
    have hrzinv : rAbs z⁻¹ = 1 := by
      rw [map_inv₀, hrz]
      simp
    have hzR :
        z ∈ absoluteValueValuationSubring
          rAbs hrnonarch := by
      rw [mem_absoluteValueValuationSubring_iff]
      exact le_of_eq hrz
    have hzinvR :
        z⁻¹ ∈ absoluteValueValuationSubring
          rAbs hrnonarch := by
      rw [mem_absoluteValueValuationSubring_iff]
      exact le_of_eq hrzinv
    have hzW :
        z ∈ absoluteValueValuationSubring
          w hwnonarch := by
      simpa [rAbs, hrnonarch, hsub] using hzR
    have hzinvW :
        z⁻¹ ∈ absoluteValueValuationSubring
          w hwnonarch := by
      simpa [rAbs, hrnonarch, hsub] using hzinvR
    have hwz_le : w z ≤ 1 :=
      (mem_absoluteValueValuationSubring_iff
        w hwnonarch z).1 hzW
    have hwzinv_le : w z⁻¹ ≤ 1 :=
      (mem_absoluteValueValuationSubring_iff
        w hwnonarch z⁻¹).1 hzinvW
    have hwz_pos : 0 < w z := by
      exact lt_of_le_of_ne (w.nonneg z) (by
        intro hzero
        exact hz_ne ((w.eq_zero).1 hzero.symm))
    have hwz_ge : 1 ≤ w z := by
      have hwinv : (w z)⁻¹ ≤ 1 := by
        simpa [map_inv₀] using hwzinv_le
      exact (inv_le_one₀ hwz_pos).1 hwinv
    have hwz_eq : w z = 1 := le_antisymm hwz_le hwz_ge
    have hwz_value :
        w z = w x ^ n / v (Algebra.norm K x) := by
      dsimp [z]
      rw [map_div₀, AbsoluteValue.map_pow, hw_ext]
    have hw_pow : w x ^ n = v (Algebra.norm K x) :=
      (div_eq_one_iff_eq hvnorm_ne).1 (hwz_value ▸ hwz_eq)
    have hpow_eq : w x ^ n = rAbs x ^ n :=
      hw_pow.trans hr_pow.symm
    exact (pow_left_inj₀ (w.nonneg x) (rAbs.nonneg x) hn_ne).1 hpow_eq

/-- The finite-degree part of the finite norm-formula theorem: the unique extended absolute value
is the norm formula `|N(x)|^(1/[L:K])`. -/
theorem normFormula_finite_extension_norm_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (absoluteValueValuationSubring
        v hnonarch).valuation) :
    let hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
        (absoluteValueValuationSubring v hnonarch) :=
      (henselianValuation_iff_henselFactorization v hnonarch).1 hhens
    let extended :=
      normFormulaFiniteNormFormulaAbsoluteValueOfHenselFactorization
        (K := K) (L := L) v hnonarch hv
    LubinTate.Valuations.NonarchimedeanAbsoluteValue extended ∧
      (∀ a : K, extended (algebraMap K L a) = v a) ∧
        (∀ x : L, extended x =
          v (Algebra.norm K x) ^ (1 / (Module.finrank K L : ℝ))) ∧
          ∀ w : AbsoluteValue L ℝ,
            LubinTate.Valuations.NonarchimedeanAbsoluteValue w →
              (∀ a : K, w (algebraMap K L a) = v a) →
                w = extended := by
  let V := absoluteValueValuationSubring v hnonarch
  let hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty V :=
    (henselianValuation_iff_henselFactorization v hnonarch).1 hhens
  let extended :=
    normFormulaFiniteNormFormulaAbsoluteValueOfHenselFactorization
      (K := K) (L := L) v hnonarch hv
  let hextendedNonarch :=
    normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_nonarchimedean
      (K := K) (L := L) v hnonarch hv
  refine ⟨hextendedNonarch, ?_, ?_, ?_⟩
  · exact
      normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_extends_base
        (K := K) (L := L) v hnonarch hv
  · intro x
    exact
      normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_apply
        (K := K) (L := L) v hnonarch hv x
  · intro w hwnonarch hw_ext
    let W := absoluteValueValuationSubring w hwnonarch
    let R := absoluteValueValuationSubring
      extended hextendedNonarch
    let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    have hvalV :
        ∀ z : L,
          z ∈ (integralClosure V L).toSubring ∨
            z⁻¹ ∈ (integralClosure V L).toSubring :=
      normFormula_algebraic_integralClosure_mem_or_inv_of_henselFactorization
        v hnonarch hv
    have hval :
        ∀ z : L,
          z ∈ (integralClosure V.valuation.valuationSubring L).toSubring ∨
            z⁻¹ ∈
              (integralClosure V.valuation.valuationSubring L).toSubring := by
      rw [ValuationSubring.valuationSubring_valuation]
      exact hvalV
    let : V.valuation.HasExtension W.valuation :=
      absoluteValueValuation_hasExtension_of_extends
        v w hnonarch hwnonarch hw_ext
    have hW :=
      DiscreteValuationField.Valuation.normFormula_extension_valuationSubring_eq_integralClosure_of_mem_or_inv
        (K := K) (L := L) V hval W.valuation
    have hextendedBase : ∀ a : K, extended (algebraMap K L a) = v a :=
      normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization_extends_base
        (K := K) (L := L) v hnonarch hv
    let : V.valuation.HasExtension R.valuation :=
      absoluteValueValuation_hasExtension_of_extends
        v extended hnonarch hextendedNonarch hextendedBase
    have hR :=
      DiscreteValuationField.Valuation.normFormula_extension_valuationSubring_eq_integralClosure_of_mem_or_inv
        (K := K) (L := L) V hval R.valuation
    have hsub : W = R := by
      simpa only [ValuationSubring.valuationSubring_valuation] using
        hW.trans hR.symm
    exact
      normFormula_finite_normFormulaAbsoluteValue_eq_of_valuationSubring_eq_of_henselFactorization
        (K := K) (L := L) v hnonarch hv w hwnonarch hw_ext
        (by simpa [W, R, extended, hextendedNonarch] using hsub)

end Valuations
end AlgebraicNumberTheory

end
