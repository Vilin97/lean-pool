/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormula
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaCoefficients
/-!
# the actual integral closure is a valuation ring

The factorization form of Hensel's lemma forces the endpoint coefficient
estimate for every irreducible polynomial.  Applied to the norm-formula value,
this says that every algebraic element or its inverse is integral over the
base valuation ring.  Thus the actual integral closure, rather than an
assumed target ring, satisfies the valuation-ring dichotomy.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

open scoped Polynomial

/-- A closed unit for the finite norm-formula value is integral over the base
valuation ring, using only the primitive factorization definition's primitive factorization
  property. -/
theorem normFormula_finiteExtensionNormFormulaValue_isIntegral_of_le_one_of_henselFactorization
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    {x : L} (hx : finiteExtensionNormFormulaValue v x ≤ 1) :
    IsIntegral
      (absoluteValueValuationSubring v hnonarch) x := by
  let V := absoluteValueValuationSubring v hnonarch
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let : Algebra.IsIntegral K L := Algebra.IsAlgebraic.isIntegral
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hconst : v ((minpoly K x).coeff 0) ≤ 1 :=
    (normFormula_finiteExtensionNormFormulaValue_le_one_iff_minpoly_coeff_zero_le_one
      v x).1 hx
  have hcoeff : ∀ i : ℕ, v ((minpoly K x).coeff i) ≤ 1 :=
    normFormula_monic_coeff_abs_le_one_of_const_abs_le_one_of_henselFactorization
      v hnonarch hv (minpoly.irreducible hxint) (minpoly.monic hxint) hconst
  rcases
      exists_polynomial_over_absoluteValueUnitBallSubringAsValuationSubring_of_coeff_abs_le_one
        v hnonarch (minpoly K x) hcoeff with
    ⟨F, hFmap, hFdegree, _hcoeff⟩
  have hφinj : Function.Injective (algebraMap V K) := by
    intro a b hab
    exact Subtype.ext hab
  have hFmonic : F.Monic := by
    apply Polynomial.monic_of_injective hφinj
    rw [hFmap]
    exact minpoly.monic hxint
  have hFdegree_ne : F.natDegree ≠ 0 := by
    rw [hFdegree]
    exact Nat.ne_of_gt (minpoly.natDegree_pos hxint)
  have hroot : (Polynomial.aeval x) F = 0 := by
    have hmaproot :
        (Polynomial.aeval x) (F.map (algebraMap V K)) = 0 := by
      rw [hFmap]
      exact minpoly.aeval K x
    rwa [Polynomial.aeval_map_algebraMap K x F] at hmaproot
  exact IsIntegral.of_aeval_monic hFmonic hFdegree_ne (by
    rw [hroot]
    exact isIntegral_zero)

/-- In a finite extension, every element or its inverse belongs to the actual
integral closure of the base valuation ring. -/
theorem normFormula_finite_integralClosure_mem_or_inv_of_henselFactorization
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    (x : L) :
    x ∈ (integralClosure
        (absoluteValueValuationSubring v hnonarch) L).toSubring ∨
      x⁻¹ ∈ (integralClosure
        (absoluteValueValuationSubring v hnonarch) L).toSubring := by
  by_cases hx : finiteExtensionNormFormulaValue v x ≤ 1
  · left
    exact
      normFormula_finiteExtensionNormFormulaValue_isIntegral_of_le_one_of_henselFactorization
        v hnonarch hv hx
  · right
    have hx_gt : 1 < finiteExtensionNormFormulaValue v x :=
      lt_of_not_ge hx
    have hx_pos : 0 < finiteExtensionNormFormulaValue v x :=
      zero_lt_one.trans hx_gt
    have hinv : finiteExtensionNormFormulaValue v x⁻¹ ≤ 1 := by
      rw [normFormula_finiteExtensionNormFormulaValue_inv]
      exact (inv_le_one₀ hx_pos).2 hx_gt.le
    exact
      normFormula_finiteExtensionNormFormulaValue_isIntegral_of_le_one_of_henselFactorization
        v hnonarch hv hinv

/-- the finite norm-formula theorem, source-producing algebraic endpoint: for an arbitrary
algebraic extension, the actual integral closure of the Henselian valuation
ring satisfies the valuation-ring dichotomy.  Each element is handled inside
the finite simple subextension that it generates. -/
theorem normFormula_algebraic_integralClosure_mem_or_inv_of_henselFactorization
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    (x : L) :
    x ∈ (integralClosure
        (absoluteValueValuationSubring v hnonarch) L).toSubring ∨
      x⁻¹ ∈ (integralClosure
        (absoluteValueValuationSubring v hnonarch) L).toSubring := by
  let V := absoluteValueValuationSubring v hnonarch
  let E := IntermediateField.adjoin K ({x} : Set L)
  let xE : E :=
    ⟨x, IntermediateField.subset_adjoin K ({x} : Set L)
      (Set.mem_singleton x)⟩
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  let : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional hxint
  have hfinite :=
    normFormula_finite_integralClosure_mem_or_inv_of_henselFactorization
      (K := K) (L := E) v hnonarch hv xE
  rcases hfinite with hxE | hxEinv
  · left
    have hxEint : IsIntegral V xE := hxE
    have hmap := hxEint.map
      ((IntermediateField.val E).restrictScalars V)
    have hxintV : IsIntegral V x := by
      simpa [E, xE] using hmap
    exact (mem_integralClosure_iff (R := V) (A := L)).2 hxintV
  · right
    have hxEinvint : IsIntegral V xE⁻¹ := hxEinv
    have hmap := hxEinvint.map
      ((IntermediateField.val E).restrictScalars V)
    have hxinvintV : IsIntegral V x⁻¹ := by
      simpa [E, xE] using hmap
    exact (mem_integralClosure_iff (R := V) (A := L)).2 hxinvintV

end Valuations
end AlgebraicNumberTheory

end
