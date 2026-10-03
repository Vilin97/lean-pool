/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.CompletedEvaluation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.ParameterCongruence
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueQuotient
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.TeichmullerDecomposition
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumber
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal
/-!
# Evaluating a changed primitive polynomial at the original primitive point

Let `π` be a uniformizer, let `u` be a unit with
`u - 1 ∈ m^(n+1)`, and put `π' = uπ`.  The parameter difference
`π' - π` then lies in `m^(n+2)`.  At the standard primitive level `n + 1`,
whose ramification index is

`d = (q - 1) q^n`,

this difference maps into the `d(n+2)`-th power of the target maximal ideal.
The parameter-congruence theorem consequently shows that the changed
primitive polynomial evaluated at the original primitive point has additive
valuation at least `d(n+2)`.

This is the quantitative algebraic input for the characteristic-independent
Krasner comparison of the original and changed finite levels.
-/

@[expose] public section

noncomputable
section

open scoped Polynomial

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} [Field K]

/-- A depth-`n+1` unit changes a uniformizer only in depth `n+2`. -/
theorem standardLubinTateChangedUniformizer_sub_mem_maximalIdeal_pow
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (hu : u ∈
      CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) :
    standardLubinTateChangedUniformizer F π u - π ∈
      F.maximalIdeal ^ (n + 2) := by
  have hu' :
      (u : F.valuationSubring) - 1 ∈
        F.maximalIdeal ^ (n + 1) :=
    (CompleteDVF.higherPrincipalUnitGroup.mem_iff
      F.toCompleteDVF (n + 1) u).1 hu
  have hπmem : π ∈ F.maximalIdeal :=
    F.toCompleteDVF.uniformizer_mem_maximalIdeal hπ
  have hmul :
      ((u : F.valuationSubring) - 1) * π ∈
        (F.maximalIdeal ^ (n + 1)) * F.maximalIdeal :=
    Ideal.mul_mem_mul hu' hπmem
  have heq :
      standardLubinTateChangedUniformizer F π u - π =
        ((u : F.valuationSubring) - 1) * π := by
    simp only [standardLubinTateChangedUniformizer]
    ring
  rw [heq]
  simpa [pow_succ, Nat.add_assoc] using hmul

/-- In the original standard level, the changed and original parameters
remain congruent through target depth `d(n+2)`. -/
theorem
    standardLubinTateChangedUniformizer_map_sub_mem_levelMaximalIdeal_pow
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (hu : u ∈
      CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) :
    standardLubinTateLevelCoefficientHom hπ n
          (standardLubinTateChangedUniformizer F π u) -
        standardLubinTateLevelCoefficientHom hπ n π ∈
      (standardLubinTateLevelCompleteDVF hπ n).maximalIdeal ^
        (((Nat.card F.residueField - 1) *
          Nat.card F.residueField ^ n) * (n + 2)) := by
  let base := F.toCompleteDVF
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hbase :
      standardLubinTateChangedUniformizer F π u - π ∈
        base.maximalIdeal ^ (n + 2) :=
    standardLubinTateChangedUniformizer_sub_mem_maximalIdeal_pow
      hπ u n hu
  have hmapped :
      integerMap base.toDVF target.toDVF
          (standardLubinTateChangedUniformizer F π u - π) ∈
        target.maximalIdeal ^
          (ramificationIndex base.toDVF target.toDVF * (n + 2)) :=
    integerMap_mem_target_maximalIdeal_pow_mul_ramificationIndex
      base target hbase
  have he :
      ramificationIndex base.toDVF target.toDVF =
        (Nat.card F.residueField - 1) *
          Nat.card F.residueField ^ n := by
    rw [standardLubinTateLevel_ramificationIndex_eq_degree hπ n,
      degree_eq_finrank,
      standardLubinTateLevelField_finrank hπ n]
  rw [he] at hmapped
  simpa [base, target, standardLubinTateLevelCoefficientHom] using hmapped

/-- The changed primitive polynomial, evaluated at the original primitive
point, lies in target depth `d(n+2)`. -/
theorem standardLubinTateChangedPrimitivePolynomial_eval_mem_maximalIdeal_pow
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (hu : u ∈
      CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) :
    Polynomial.eval₂
        (standardLubinTateLevelCoefficientHom hπ n)
        (standardLubinTatePrimitivePointInteger hπ n)
        (standardLubinTatePrimitivePolynomial F
          (standardLubinTateChangedUniformizer F π u) n) ∈
      (standardLubinTateLevelCompleteDVF hπ n).maximalIdeal ^
        (((Nat.card F.residueField - 1) *
          Nat.card F.residueField ^ n) * (n + 2)) := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  let I :=
    target.maximalIdeal ^
      (((Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n) * (n + 2))
  have hparameter :
      standardLubinTateLevelCoefficientHom hπ n
            (standardLubinTateChangedUniformizer F π u) -
          standardLubinTateLevelCoefficientHom hπ n π ∈ I := by
    simpa [target, I] using
      standardLubinTateChangedUniformizer_map_sub_mem_levelMaximalIdeal_pow
        hπ u n hu
  have hcongr :=
    standardLubinTatePrimitivePolynomial_eval₂_sub_mem_of_parameter_sub_mem
      F (standardLubinTateLevelCoefficientHom hπ n) I
      hparameter n (standardLubinTatePrimitivePointInteger hπ n)
  have horiginal :
      Polynomial.eval₂
          (standardLubinTateLevelCoefficientHom hπ n)
          (standardLubinTatePrimitivePointInteger hπ n)
          (standardLubinTatePrimitivePolynomial F π n) = 0 := by
    simpa [Polynomial.aeval_def, standardLubinTateLevelCoefficientHom,
      integerMap] using
      standardLubinTatePrimitivePointInteger_aeval hπ n
  simpa [I, horiginal] using hcongr

/-- Quantitative form of the changed-polynomial evaluation estimate. -/
theorem standardLubinTateChangedPrimitivePolynomial_eval_addVal_ge
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (hu : u ∈
      CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) :
    ((((Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n) * (n + 2) : ℕ) : ℕ∞) ≤
      IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (Polynomial.eval₂
          (standardLubinTateLevelCoefficientHom hπ n)
          (standardLubinTatePrimitivePointInteger hπ n)
          (standardLubinTatePrimitivePolynomial F
            (standardLubinTateChangedUniformizer F π u) n)) := by
  exact
    (IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge
      (Polynomial.eval₂
        (standardLubinTateLevelCoefficientHom hπ n)
        (standardLubinTatePrimitivePointInteger hπ n)
        (standardLubinTatePrimitivePolynomial F
          (standardLubinTateChangedUniformizer F π u) n))
      (((Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n) * (n + 2))).1
      (standardLubinTateChangedPrimitivePolynomial_eval_mem_maximalIdeal_pow
        hπ u n hu)

end LubinTate

end
