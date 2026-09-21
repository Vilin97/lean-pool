/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.ChangedPrimitiveEvaluation
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.ChangedLevelCompositum
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PolynomialRootProximity
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.GaloisStabilizer
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.ValuationKrasner
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.ValuationRestriction
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal
/-!
# Stability of a standard Lubin--Tate level under a deep unit change

This file develops the quantitative inputs for comparing the standard
level attached to a uniformizer `π` with the standard level attached to
`uπ`, when `u` is a sufficiently deep principal unit.

`ChangedPrimitiveEvaluation` supplies the first input: at depth `n + 1`,
the changed primitive polynomial evaluated at the old primitive point has
additive valuation at least `(n + 2) d`.

The new input proved here is the exact additive valuation of the derivative of the
primitive polynomial at the distinguished primitive point.  If

`d = (q - 1) q^n`,

then that valuation is

`n d + (q - 2) q^n = (n + 1) d - q^n`.

Together these are the two numerical terms in the root-product/Krasner
comparison: the evaluation estimate controls the changed polynomial at the
old primitive point, and the derivative exponent controls the product of the
other changed-root displacements.
-/

noncomputable section

open scoped Polynomial IntermediateField

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} [Field K]

/-- Every integral primitive polynomial splits already over the valuation
ring of its standard level.  The finite unit parameters give as many
distinct integral roots as the degree of the polynomial. -/
theorem
    standardLubinTatePrimitivePolynomial_map_levelCoefficientHom_splits
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    ((standardLubinTatePrimitivePolynomial F π n).map
      (standardLubinTateLevelCoefficientHom hπ n)).Splits := by
  classical
  let target := standardLubinTateLevelCompleteDVF hπ n
  let p :=
    (standardLubinTatePrimitivePolynomial F π n).map
      (standardLubinTateLevelCoefficientHom hπ n)
  let root :
      standardLubinTateUnitParameter F n →
        target.valuationSubring :=
    fun a =>
      standardLubinTatePrimitivePointIntegerAction hπ n
        (standardLubinTateUnitParameterChosenRepresentative F n a)
  have hpmonic : p.Monic := by
    exact
      (standardLubinTatePrimitivePolynomial_monic F π n).map
        (standardLubinTateLevelCoefficientHom hπ n)
  have hpne : p ≠ 0 := hpmonic.ne_zero
  have hroot (a : standardLubinTateUnitParameter F n) :
      p.eval (root a) = 0 := by
    apply standardLubinTateLevelIntegerToSeparableClosure_injective hπ n
    rw [map_zero]
    simp only [p, Polynomial.eval_map]
    rw [Polynomial.hom_eval₂,
      standardLubinTateLevelIntegerToSeparableClosure_comp_coefficientHom]
    simpa [p, root, Polynomial.IsRoot,
      standardLubinTatePrimitivePolynomialOverField,
      standardLubinTatePrimitiveRootAction,
      Polynomial.eval_map, Polynomial.eval₂_map] using
        standardLubinTatePrimitiveRootAction_isRoot hπ n
          (standardLubinTateUnitParameterChosenRepresentative F n a)
  have hroot_mem (a : standardLubinTateUnitParameter F n) :
      root a ∈ p.roots :=
    (Polynomial.mem_roots hpne).2 (hroot a)
  have hroot_injective : Function.Injective root := by
    intro a b hab
    apply standardLubinTateUnitParameterLevelRoot_injective F hπ n
    change
      (root a : standardLubinTateLevelField hπ n) =
        (root b : standardLubinTateLevelField hπ n)
    exact congrArg Subtype.val hab
  let := Fintype.ofFinite (standardLubinTateUnitParameter F n)
  let rootEmbedding :
      standardLubinTateUnitParameter F n ↪ target.valuationSubring :=
    ⟨root, hroot_injective⟩
  let roots : Finset target.valuationSubring :=
    Finset.univ.map rootEmbedding
  have hroots_le : roots.1 ≤ p.roots := by
    rw [Finset.val_le_iff_val_subset]
    intro z hz
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hz
    exact hroot_mem a
  have hroots_card :
      roots.card =
        (Nat.card F.residueField - 1) *
          Nat.card F.residueField ^ n := by
    calc
      roots.card =
          Fintype.card (standardLubinTateUnitParameter F n) := by
        simp [roots, rootEmbedding]
      _ = Nat.card (standardLubinTateUnitParameter F n) :=
        Nat.card_eq_fintype_card.symm
      _ = _ := standardLubinTateUnitParameter_natCard F n
  have hpdegree :
      p.natDegree =
        (Nat.card F.residueField - 1) *
          Nat.card F.residueField ^ n := by
    calc
      p.natDegree =
          (standardLubinTatePrimitivePolynomial F π n).natDegree := by
        simpa [p] using
          (standardLubinTatePrimitivePolynomial_monic F π n).natDegree_map
            (standardLubinTateLevelCoefficientHom hπ n)
      _ =
          (Nat.card F.residueField - 1) *
            Nat.card F.residueField ^ n :=
        standardLubinTatePrimitivePolynomial_natDegree F π n
  apply Polynomial.splits_iff_card_roots.mpr
  apply Nat.le_antisymm
  · exact Polynomial.card_roots' p
  · rw [hpdegree, ← hroots_card]
    exact Multiset.card_le_card hroots_le

/-- Evaluation of the derivative of a successor iterate is the old
derivative value multiplied by `q y^(q-1) + π`, where `y` is the old
iterate value. -/
private theorem
    standardLubinTatePolynomialIterate_derivative_eval₂_succ
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n i : ℕ) :
    Polynomial.eval₂
        (standardLubinTateLevelCoefficientHom hπ n)
        (standardLubinTatePrimitivePointInteger hπ n)
        (standardLubinTatePolynomialIterate F π (i + 1)).derivative =
      (standardLubinTateLevelCoefficientHom hπ n
            (Nat.card F.residueField : F.valuationSubring) *
          standardLubinTatePrimitivePointIterateInteger hπ n i ^
            (Nat.card F.residueField - 1) +
        standardLubinTateLevelCoefficientHom hπ n π) *
      Polynomial.eval₂
        (standardLubinTateLevelCoefficientHom hπ n)
        (standardLubinTatePrimitivePointInteger hπ n)
        (standardLubinTatePolynomialIterate F π i).derivative := by
  rw [standardLubinTatePolynomialIterate_succ,
    Polynomial.derivative_comp, Polynomial.eval₂_mul,
    Polynomial.eval₂_comp, standardLubinTatePolynomial,
    Polynomial.derivative_add, Polynomial.derivative_pow,
    Polynomial.derivative_mul, Polynomial.derivative_X,
    Polynomial.derivative_C]
  simp [standardLubinTatePrimitivePointIterateInteger]
  ring

/-- The derivative factor `q y^(q-1) + π` occurring at every iterate has
the same additive valuation as the image of the base uniformizer. -/
private theorem standardLubinTate_iterate_derivative_factor_addVal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n i : ℕ) (hi : i ≤ n) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (standardLubinTateLevelCoefficientHom hπ n
              (Nat.card F.residueField : F.valuationSubring) *
            standardLubinTatePrimitivePointIterateInteger hπ n i ^
              (Nat.card F.residueField - 1) +
          standardLubinTateLevelCoefficientHom hπ n π) =
      (((Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n : ℕ) : ℕ∞) := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  let y := standardLubinTatePrimitivePointIterateInteger hπ n i
  let q := Nat.card F.residueField
  let d := (q - 1) * q ^ n
  have hqres :
      F.residueMap (q : F.valuationSubring) = 0 := by
    let := Fintype.ofFinite F.residueField
    change (Nat.card F.residueField : F.residueField) = 0
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero F.residueField
  have hqmem :
      (q : F.valuationSubring) ∈ F.maximalIdeal :=
    (F.toCompleteDVF.residue_eq_zero_iff
      (q : F.valuationSubring)).1 hqres
  have hqid : π ∣ (q : F.valuationSubring) := by
    simpa using
      (F.toCompleteDVF.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd
        hπ 1).1 (by simpa using hqmem)
  rcases hqid with ⟨c, hc⟩
  have hyval :
      IsDiscreteValuationRing.addVal target.valuationSubring y =
        (q ^ i : ℕ) := by
    simpa [target, y, q] using
      standardLubinTatePrimitivePointIterateInteger_addVal hπ n i hi
  have hymem : y ∈ target.maximalIdeal := by
    have hymemPow : y ∈ target.maximalIdeal ^ 1 := by
      apply
        (IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge y 1).2
      rw [hyval]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (pow_ne_zero i (Nat.ne_of_gt
          (Nat.zero_lt_one.trans
            (Finite.one_lt_card : 1 < Nat.card F.residueField))))
    simpa using hymemPow
  have hqsubpos : 0 < q - 1 :=
    Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField)
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hqsubpos)
  have hypowmem : y ^ (q - 1) ∈ target.maximalIdeal := by
    rw [hr, pow_succ]
    exact target.maximalIdeal.mul_mem_left (y ^ r) hymem
  have hzmem :
      standardLubinTateLevelCoefficientHom hπ n c *
          y ^ (q - 1) ∈ target.maximalIdeal :=
    target.maximalIdeal.mul_mem_left
      (standardLubinTateLevelCoefficientHom hπ n c) hypowmem
  have hunit :
      IsUnit
        (1 + standardLubinTateLevelCoefficientHom hπ n c *
          y ^ (q - 1)) :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.isUnit_one_add_of_mem_maximalIdeal_pow
        target (n := 1) le_rfl
        (standardLubinTateLevelCoefficientHom hπ n c *
          y ^ (q - 1)) (by
            simpa only [pow_one] using hzmem)
  have hfactor :
      standardLubinTateLevelCoefficientHom hπ n
            (q : F.valuationSubring) * y ^ (q - 1) +
          standardLubinTateLevelCoefficientHom hπ n π =
        standardLubinTateLevelCoefficientHom hπ n π *
          (1 + standardLubinTateLevelCoefficientHom hπ n c *
            y ^ (q - 1)) := by
    rw [hc, map_mul]
    ring
  rw [hfactor, IsDiscreteValuationRing.addVal_mul,
    (IsDiscreteValuationRing.addVal_eq_zero_iff).2 hunit, add_zero]
  simpa [target, q, d, standardLubinTateLevelCoefficientHom] using
    standardLubinTateBaseUniformizerInteger_map_addVal hπ n

/-- The derivative of the `i`-fold standard iterate at the primitive point
has additive valuation `i * d`, where `d = (q - 1) q^n`. -/
private theorem
    standardLubinTatePolynomialIterate_derivative_eval₂_addVal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n i : ℕ) (hi : i ≤ n) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (Polynomial.eval₂
          (standardLubinTateLevelCoefficientHom hπ n)
          (standardLubinTatePrimitivePointInteger hπ n)
          (standardLubinTatePolynomialIterate F π i).derivative) =
      ((i * ((Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n) : ℕ) : ℕ∞) := by
  induction i with
  | zero =>
      simp [standardLubinTatePolynomialIterate]
  | succ i ih =>
      have hi' : i ≤ n := Nat.le_trans (Nat.le_succ i) hi
      rw [standardLubinTatePolynomialIterate_derivative_eval₂_succ,
        IsDiscreteValuationRing.addVal_mul,
        standardLubinTate_iterate_derivative_factor_addVal hπ n i hi',
        ih hi']
      exact_mod_cast
        (by
          ring :
          (Nat.card F.residueField - 1) *
                Nat.card F.residueField ^ n +
              i * ((Nat.card F.residueField - 1) *
                Nat.card F.residueField ^ n) =
            (i + 1) * ((Nat.card F.residueField - 1) *
              Nat.card F.residueField ^ n))

/-- Exact derivative valuation of the integral primitive polynomial at the
distinguished primitive point. -/
theorem standardLubinTatePrimitivePolynomial_derivative_eval₂_addVal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (Polynomial.eval₂
          (standardLubinTateLevelCoefficientHom hπ n)
          (standardLubinTatePrimitivePointInteger hπ n)
          (standardLubinTatePrimitivePolynomial F π n).derivative) =
      ((n * ((Nat.card F.residueField - 1) *
              Nat.card F.residueField ^ n) +
          (Nat.card F.residueField - 2) *
              Nat.card F.residueField ^ n : ℕ) : ℕ∞) := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  let q := Nat.card F.residueField
  let y := standardLubinTatePrimitivePointIterateInteger hπ n n
  have hqsubres :
      F.residueMap ((q - 1 : ℕ) : F.valuationSubring) =
        ((q - 1 : ℕ) : F.residueField) := by
    exact map_natCast F.residueMap (q - 1)
  have hqsubres_ne :
      F.residueMap (q - 1 : ℕ) ≠ 0 := by
    let := Fintype.ofFinite F.residueField
    rw [hqsubres]
    have hqzero : (q : F.residueField) = 0 := by
      change (Nat.card F.residueField : F.residueField) = 0
      rw [Nat.card_eq_fintype_card]
      exact Nat.cast_card_eq_zero F.residueField
    rw [Nat.cast_sub
      (Nat.le_of_lt
        (Finite.one_lt_card : 1 < Nat.card F.residueField)), hqzero]
    simp
  have hqsubunitBase :
      IsUnit ((q - 1 : ℕ) : F.valuationSubring) :=
    (F.toCompleteDVF.residue_ne_zero_iff_isUnit
      ((q - 1 : ℕ) : F.valuationSubring)).1 hqsubres_ne
  have hqsubunitTarget :
      IsUnit
        (standardLubinTateLevelCoefficientHom hπ n
          ((q - 1 : ℕ) : F.valuationSubring)) :=
    hqsubunitBase.map
      (standardLubinTateLevelCoefficientHom hπ n)
  have hyval :
      IsDiscreteValuationRing.addVal target.valuationSubring y =
        (q ^ n : ℕ) := by
    simpa [target, q, y] using
      standardLubinTatePrimitivePointIterateInteger_addVal
        hπ n n le_rfl
  rw [standardLubinTatePrimitivePolynomial,
    Polynomial.derivative_add, Polynomial.derivative_pow,
    Polynomial.derivative_C, add_zero, Polynomial.eval₂_mul,
    Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow]
  rw [IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_mul,
    (IsDiscreteValuationRing.addVal_eq_zero_iff).2 hqsubunitTarget,
    zero_add, IsDiscreteValuationRing.addVal_pow]
  change
    (q - 1 - 1) •
          IsDiscreteValuationRing.addVal target.valuationSubring y +
        IsDiscreteValuationRing.addVal target.valuationSubring
          (Polynomial.eval₂
            (standardLubinTateLevelCoefficientHom hπ n)
            (standardLubinTatePrimitivePointInteger hπ n)
            (standardLubinTatePolynomialIterate F π n).derivative) =
      ((n * ((q - 1) * q ^ n) + (q - 2) * q ^ n : ℕ) : ℕ∞)
  rw [hyval,
    standardLubinTatePolynomialIterate_derivative_eval₂_addVal
      hπ n n le_rfl]
  simp only [nsmul_eq_mul]
  exact_mod_cast
    (by
      ring :
      (q - 2) * q ^ n +
          n * ((q - 1) * q ^ n) =
        n * ((q - 1) * q ^ n) +
          (q - 2) * q ^ n)

/-- Every integral root of the primitive polynomial in its standard level
has the same derivative valuation as the distinguished primitive point. -/
theorem
    standardLubinTatePrimitivePolynomial_map_levelCoefficientHom_derivative_addVal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ)
    {y : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring}
    (hy :
      y ∈
        ((standardLubinTatePrimitivePolynomial F π n).map
          (standardLubinTateLevelCoefficientHom hπ n)).roots) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (((standardLubinTatePrimitivePolynomial F π n).map
          (standardLubinTateLevelCoefficientHom hπ n)).derivative.eval y) =
      ((n * ((Nat.card F.residueField - 1) *
              Nat.card F.residueField ^ n) +
          (Nat.card F.residueField - 2) *
              Nat.card F.residueField ^ n : ℕ) : ℕ∞) := by
  let L := standardLubinTateLevelField hπ n
  let target := standardLubinTateLevelCompleteDVF hπ n
  let p :=
    (standardLubinTatePrimitivePolynomial F π n).map
      (standardLubinTateLevelCoefficientHom hπ n)
  let lambda := standardLubinTatePrimitivePointInteger hπ n
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsGalois K L :=
    standardLubinTateLevelField_isGalois (F := F) hπ n
  have hpne : p ≠ 0 :=
    ((standardLubinTatePrimitivePolynomial_monic F π n).map
      (standardLubinTateLevelCoefficientHom hπ n)).ne_zero
  have hyeval : p.eval y = 0 :=
    (Polynomial.mem_roots hpne).1 (by simpa [p] using hy)
  have hymin :
      Polynomial.aeval (y : L)
        (minpoly K (standardLubinTateLevelPowerBasis hπ n).gen) = 0 := by
    rw [standardLubinTateLevelPowerBasis_minpoly]
    let ι : target.valuationSubring →+* L :=
      target.valuation.valuationSubring.subtype
    have hyevalL := congrArg ι hyeval
    rw [map_zero] at hyevalL
    simp only [p, Polynomial.eval_map] at hyevalL
    rw [Polynomial.hom_eval₂] at hyevalL
    have hcomp :
        ι.comp (standardLubinTateLevelCoefficientHom hπ n) =
          (algebraMap K L).comp (algebraMap F.valuationSubring K) := by
      apply RingHom.ext
      intro a
      exact standardLubinTateLevelCoefficientHom_apply hπ n a
    rw [hcomp] at hyevalL
    simpa [ι, p, Polynomial.aeval_def,
      standardLubinTatePrimitivePolynomialOverField,
      Polynomial.eval_map, Polynomial.eval₂_map] using hyevalL
  obtain ⟨sigma, hsigma⟩ :=
    minpoly.exists_algEquiv_of_root'
      (Algebra.IsAlgebraic.isAlgebraic
        (standardLubinTateLevelPowerBasis hπ n).gen)
      hymin
  let r :=
    valuationSubringAutOfUniqueExtension
      (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
        hπ n) sigma
  have r_comp :
      r.toRingHom.comp (standardLubinTateLevelCoefficientHom hπ n) =
        standardLubinTateLevelCoefficientHom hπ n := by
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply]
    apply Subtype.ext
    change
      sigma (algebraMap K L (a : K)) =
        algebraMap K L (a : K)
    exact sigma.commutes (a : K)
  have r_lambda : r lambda = y := by
    apply Subtype.ext
    change
      sigma (standardLubinTateLevelPowerBasis hπ n).gen = (y : L)
    simpa [standardLubinTateLevelGenerator, lambda] using hsigma
  have heval :
      r (p.derivative.eval lambda) =
        p.derivative.eval y := by
    simp only [p, Polynomial.derivative_map, Polynomial.eval_map]
    change
      r.toRingHom
          (Polynomial.eval₂
            (standardLubinTateLevelCoefficientHom hπ n) lambda
            (standardLubinTatePrimitivePolynomial F π n).derivative) =
        Polynomial.eval₂
          (standardLubinTateLevelCoefficientHom hπ n) y
          (standardLubinTatePrimitivePolynomial F π n).derivative
    rw [Polynomial.hom_eval₂, r_comp,
      show r.toRingHom lambda = y from r_lambda]
  calc
    IsDiscreteValuationRing.addVal target.valuationSubring
        (p.derivative.eval y) =
      IsDiscreteValuationRing.addVal target.valuationSubring
        (r (p.derivative.eval lambda)) := by rw [heval]
    _ =
      IsDiscreteValuationRing.addVal target.valuationSubring
        (p.derivative.eval lambda) :=
      addVal_valuationSubringAutOfUniqueExtension
        (standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
          hπ n) sigma (p.derivative.eval lambda)
    _ = _ := by
      simpa [p, lambda, Polynomial.derivative_map,
        Polynomial.eval_map] using
        standardLubinTatePrimitivePolynomial_derivative_eval₂_addVal
          hπ n

/-- Arithmetic form of the derivative exponent used by the
root-product comparison. -/
theorem standardLubinTatePrimitivePolynomial_derivativeExponent_eq
    (F : LocalField.{u, v} K) (n : ℕ) :
    n * ((Nat.card F.residueField - 1) *
          Nat.card F.residueField ^ n) +
        (Nat.card F.residueField - 2) *
          Nat.card F.residueField ^ n =
      (n + 1) * ((Nat.card F.residueField - 1) *
          Nat.card F.residueField ^ n) -
        Nat.card F.residueField ^ n := by
  let q := Nat.card F.residueField
  have hq : 2 ≤ q :=
    (Finite.one_lt_card : 1 < Nat.card F.residueField)
  have hqsub : q - 1 = (q - 2) + 1 := by
    omega
  have hsum :
      (n + 1) * ((q - 1) * q ^ n) =
        q ^ n +
          (n * ((q - 1) * q ^ n) + (q - 2) * q ^ n) := by
    rw [hqsub]
    ring
  change
    n * ((q - 1) * q ^ n) + (q - 2) * q ^ n =
      (n + 1) * ((q - 1) * q ^ n) - q ^ n
  rw [hsum, Nat.add_sub_cancel_left]

/-- The changed primitive polynomial after passing through the changed
level and then into the common compositum valuation ring. -/
noncomputable def
    standardLubinTateChangedPrimitivePolynomialInCompositum
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    (standardLubinTateChangedLevelCompositumCompleteDVF
      hπ u n).valuationSubring[X] :=
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  ((standardLubinTatePrimitivePolynomial F
      (standardLubinTateChangedUniformizer F π u) n).map
    (standardLubinTateLevelCoefficientHom hπ' n)).map
      (standardLubinTateChangedLevelToCompositumIntegerMap hπ u n)

/-- The original distinguished primitive point in the common compositum
valuation ring. -/
noncomputable def
    standardLubinTateOriginalPrimitivePointInChangedLevelCompositum
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    (standardLubinTateChangedLevelCompositumCompleteDVF
      hπ u n).valuationSubring :=
  standardLubinTateLevelToChangedLevelCompositumIntegerMap hπ u n
    (standardLubinTatePrimitivePointInteger hπ n)

/-- The distinguished changed primitive point in the common compositum
valuation ring. -/
noncomputable def
    standardLubinTateChangedPrimitivePointInCompositum
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    (standardLubinTateChangedLevelCompositumCompleteDVF
      hπ u n).valuationSubring :=
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  standardLubinTateChangedLevelToCompositumIntegerMap hπ u n
    (standardLubinTatePrimitivePointInteger hπ' n)

/-- The two routes from base coefficients into the common compositum
valuation ring agree. -/
private theorem
    standardLubinTateChangedLevelCompositum_coefficientHom_eq
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    (standardLubinTateChangedLevelToCompositumIntegerMap hπ u n).comp
        (standardLubinTateLevelCoefficientHom
          (standardLubinTateChangedUniformizer_isUniformizer hπ u) n) =
    (standardLubinTateLevelToChangedLevelCompositumIntegerMap
        hπ u n).comp
        (standardLubinTateLevelCoefficientHom hπ n) := by
  let L := standardLubinTateLevelField hπ n
  let L' := standardLubinTateChangedLevelField hπ u n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let : Algebra L M :=
    standardLubinTateLevelToChangedLevelCompositumAlgebra hπ u n
  let : Algebra L' M :=
    standardLubinTateChangedLevelToCompositumAlgebra hπ u n
  let : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K L' M :=
    IsScalarTower.of_algebraMap_eq' rfl
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply]
  apply Subtype.ext
  rw [
    standardLubinTateChangedLevelToCompositumIntegerMap_apply_coe,
    standardLubinTateLevelToChangedLevelCompositumIntegerMap_apply_coe]
  change
    algebraMap L' M
        (standardLubinTateLevelCoefficientHom
          (standardLubinTateChangedUniformizer_isUniformizer hπ u) n a :
          L') =
      algebraMap L M
        (standardLubinTateLevelCoefficientHom hπ n a : L)
  rw [standardLubinTateLevelCoefficientHom_apply,
    standardLubinTateLevelCoefficientHom_apply]
  rw [← IsScalarTower.algebraMap_apply K L' M,
    ← IsScalarTower.algebraMap_apply K L M]

/-- The changed primitive polynomial is monic in the common valuation
ring. -/
theorem standardLubinTateChangedPrimitivePolynomialInCompositum_monic
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    (standardLubinTateChangedPrimitivePolynomialInCompositum
      hπ u n).Monic := by
  exact
    ((standardLubinTatePrimitivePolynomial_monic F
      (standardLubinTateChangedUniformizer F π u) n).map
        (standardLubinTateLevelCoefficientHom
          (standardLubinTateChangedUniformizer_isUniformizer hπ u)
          n)).map
      (standardLubinTateChangedLevelToCompositumIntegerMap hπ u n)

/-- The changed primitive polynomial splits in the common valuation ring. -/
theorem standardLubinTateChangedPrimitivePolynomialInCompositum_splits
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    (standardLubinTateChangedPrimitivePolynomialInCompositum
      hπ u n).Splits := by
  exact
    (standardLubinTatePrimitivePolynomial_map_levelCoefficientHom_splits
      (standardLubinTateChangedUniformizer_isUniformizer hπ u) n).map
        (standardLubinTateChangedLevelToCompositumIntegerMap hπ u n)

/-- The changed primitive polynomial remains nonconstant in the common
valuation ring. -/
theorem
    standardLubinTateChangedPrimitivePolynomialInCompositum_natDegree_ne_zero
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    (standardLubinTateChangedPrimitivePolynomialInCompositum
      hπ u n).natDegree ≠ 0 := by
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  change
    ((((standardLubinTatePrimitivePolynomial F
        (standardLubinTateChangedUniformizer F π u) n).map
      (standardLubinTateLevelCoefficientHom hπ' n)).map
        (standardLubinTateChangedLevelToCompositumIntegerMap
          hπ u n)).natDegree ≠ 0)
  rw [
    ((standardLubinTatePrimitivePolynomial_monic F
      (standardLubinTateChangedUniformizer F π u) n).map
        (standardLubinTateLevelCoefficientHom hπ' n)).natDegree_map,
    (standardLubinTatePrimitivePolynomial_monic F
      (standardLubinTateChangedUniformizer F π u) n).natDegree_map,
    standardLubinTatePrimitivePolynomial_natDegree]
  exact mul_ne_zero
    (Nat.sub_ne_zero_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
    (pow_ne_zero n
      (Nat.ne_of_gt
        (Nat.zero_lt_one.trans
          (Finite.one_lt_card : 1 < Nat.card F.residueField))))

/-- Evaluation in the common compositum agrees with first evaluating at
the original primitive point and then applying the original-level
valuation-ring inclusion. -/
private theorem
    standardLubinTateChangedPrimitivePolynomialInCompositum_eval_original
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    (standardLubinTateChangedPrimitivePolynomialInCompositum
        hπ u n).eval
        (standardLubinTateOriginalPrimitivePointInChangedLevelCompositum
          hπ u n) =
      standardLubinTateLevelToChangedLevelCompositumIntegerMap hπ u n
        (Polynomial.eval₂
          (standardLubinTateLevelCoefficientHom hπ n)
          (standardLubinTatePrimitivePointInteger hπ n)
          (standardLubinTatePrimitivePolynomial F
            (standardLubinTateChangedUniformizer F π u) n)) := by
  rw [standardLubinTateChangedPrimitivePolynomialInCompositum,
    Polynomial.eval_map, Polynomial.eval₂_map]
  rw [Polynomial.hom_eval₂]
  rw [standardLubinTateChangedLevelCompositum_coefficientHom_eq]
  rfl

/-- The changed-polynomial evaluation lower bound after transport to the
common compositum. -/
theorem
    standardLubinTateChangedPrimitivePolynomialInCompositum_eval_addVal_ge
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (hu : u ∈
      CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) :
    ((standardLubinTateLevelToChangedLevelCompositumRamificationIndex
          hπ u n *
        (((Nat.card F.residueField - 1) *
          Nat.card F.residueField ^ n) * (n + 2)) : ℕ) : ℕ∞) ≤
      IsDiscreteValuationRing.addVal
        (standardLubinTateChangedLevelCompositumCompleteDVF
          hπ u n).valuationSubring
        ((standardLubinTateChangedPrimitivePolynomialInCompositum
          hπ u n).eval
          (standardLubinTateOriginalPrimitivePointInChangedLevelCompositum
            hπ u n)) := by
  let oldValue :=
    Polynomial.eval₂
      (standardLubinTateLevelCoefficientHom hπ n)
      (standardLubinTatePrimitivePointInteger hπ n)
      (standardLubinTatePrimitivePolynomial F
        (standardLubinTateChangedUniformizer F π u) n)
  have hlower :=
    standardLubinTateChangedPrimitivePolynomial_eval_addVal_ge
      hπ u n hu
  have hscaled :=
    nsmul_le_nsmul_right hlower
      (standardLubinTateLevelToChangedLevelCompositumRamificationIndex
        hπ u n)
  have hmap :=
    standardLubinTateLevelToChangedLevelCompositum_addVal
      hπ u n oldValue
  rw [
    standardLubinTateChangedPrimitivePolynomialInCompositum_eval_original]
  rw [hmap]
  simpa [oldValue, nsmul_eq_mul] using hscaled

/-- Every changed root in the compositum has the transported exact
derivative valuation. -/
theorem
    standardLubinTateChangedPrimitivePolynomialInCompositum_derivative_addVal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    {beta :
      (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).valuationSubring}
    (hbeta :
      beta ∈
        (standardLubinTateChangedPrimitivePolynomialInCompositum
          hπ u n).roots) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateChangedLevelCompositumCompleteDVF
          hπ u n).valuationSubring
        ((standardLubinTateChangedPrimitivePolynomialInCompositum
          hπ u n).derivative.eval beta) =
      standardLubinTateChangedLevelToCompositumRamificationIndex hπ u n •
        ((n * ((Nat.card F.residueField - 1) *
                Nat.card F.residueField ^ n) +
            (Nat.card F.residueField - 2) *
                Nat.card F.residueField ^ n : ℕ) : ℕ∞) := by
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  let level := standardLubinTateLevelCompleteDVF hπ' n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let p :=
    (standardLubinTatePrimitivePolynomial F
      (standardLubinTateChangedUniformizer F π u) n).map
        (standardLubinTateLevelCoefficientHom hπ' n)
  let j :=
    standardLubinTateChangedLevelToCompositumIntegerMap hπ u n
  have hj : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    have hfield :=
      congrArg (fun z : target.valuationSubring =>
        (z : standardLubinTateChangedLevelCompositumField hπ u n)) hab
    change
      standardLubinTateChangedLevelToCompositum hπ u n
          (a : standardLubinTateChangedLevelField hπ u n) =
        standardLubinTateChangedLevelToCompositum hπ u n
          (b : standardLubinTateChangedLevelField hπ u n) at hfield
    exact
      (standardLubinTateChangedLevelToCompositum
        hπ u n).injective hfield
  have hroots :
      (p.map j).roots = p.roots.map j :=
    (standardLubinTatePrimitivePolynomial_map_levelCoefficientHom_splits
      hπ' n).roots_map_of_injective hj
  have hbeta' : beta ∈ (p.map j).roots := by
    simpa [p, j,
      standardLubinTateChangedPrimitivePolynomialInCompositum] using
        hbeta
  rw [hroots] at hbeta'
  obtain ⟨y, hy, hxy⟩ := Multiset.mem_map.mp hbeta'
  have hderivative :
      (standardLubinTateChangedPrimitivePolynomialInCompositum
          hπ u n).derivative.eval beta =
        j (p.derivative.eval y) := by
    rw [← hxy]
    simp [standardLubinTateChangedPrimitivePolynomialInCompositum,
      p, j, Polynomial.derivative_map, Polynomial.eval_map]
  rw [hderivative]
  rw [
    standardLubinTateChangedLevelToCompositum_addVal hπ u n
      (p.derivative.eval y)]
  rw [
    standardLubinTatePrimitivePolynomial_map_levelCoefficientHom_derivative_addVal
      hπ' n hy]

/-- The relative ramification index of the original level in the common
compositum is positive. -/
private theorem
    standardLubinTateLevelToChangedLevelCompositumRamificationIndex_pos
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    0 <
      standardLubinTateLevelToChangedLevelCompositumRamificationIndex
        hπ u n := by
  let L := standardLubinTateLevelField hπ n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let : Algebra L M :=
    standardLubinTateLevelToChangedLevelCompositumAlgebra hπ u n
  let : level.valuation.HasExtension target.valuation :=
    standardLubinTateLevelToChangedLevelCompositum_hasExtension
      hπ u n
  let : Module.IsTorsionFree
      level.valuationSubring target.valuationSubring :=
    Module.IsTorsionFree.of_smul_eq_zero fun a b hab => by
      rw [Algebra.smul_def] at hab
      rcases mul_eq_zero.mp hab with ha | hb
      · exact Or.inl (integerMap_injective level.toDVF target.toDVF ha)
      · exact Or.inr hb
  change
    0 <
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        level.toDVF target.toDVF
  exact
    LocalFieldTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_pos
      level target

/-- At principal-unit depth `n + 1`, the changed primitive polynomial has
a root in the common compositum which is closer to the old primitive point
than the transported level-`n` Galois displacement bound.

The root-product estimate first gives the stronger lower bound
`e * q^(n+1)` for the distance.  Here `e` is the relative ramification
index of the original level in the compositum. -/
theorem
    exists_standardLubinTateChangedPrimitiveRootInCompositum_close
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (hu : u ∈
      CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) :
    ∃ beta :
        (standardLubinTateChangedLevelCompositumCompleteDVF
          hπ u n).valuationSubring,
      beta ∈
          (standardLubinTateChangedPrimitivePolynomialInCompositum
            hπ u n).roots ∧
        ((standardLubinTateLevelToChangedLevelCompositumRamificationIndex
              hπ u n *
            Nat.card F.residueField ^ n : ℕ) : ℕ∞) <
          IsDiscreteValuationRing.addVal
            (standardLubinTateChangedLevelCompositumCompleteDVF
              hπ u n).valuationSubring
            (standardLubinTateOriginalPrimitivePointInChangedLevelCompositum
                hπ u n -
              beta) := by
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let p :=
    standardLubinTateChangedPrimitivePolynomialInCompositum hπ u n
  let alpha :=
    standardLubinTateOriginalPrimitivePointInChangedLevelCompositum
      hπ u n
  let q := Nat.card F.residueField
  let d := (q - 1) * q ^ n
  let derivativeExponent :=
    n * d + (q - 2) * q ^ n
  let e :=
    standardLubinTateLevelToChangedLevelCompositumRamificationIndex
      hπ u n
  obtain ⟨beta, hbeta, hproximity⟩ :=
    Polynomial.Splits.exists_root_addVal_eval_le_sub_add_derivative
      p
      (standardLubinTateChangedPrimitivePolynomialInCompositum_splits
        hπ u n)
      (standardLubinTateChangedPrimitivePolynomialInCompositum_monic
        hπ u n)
      (standardLubinTateChangedPrimitivePolynomialInCompositum_natDegree_ne_zero
        hπ u n)
      alpha
  refine ⟨beta, hbeta, ?_⟩
  have hevaluation :
      ((e * (d * (n + 2)) : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal target.valuationSubring
          (p.eval alpha) := by
    simpa [target, p, alpha, q, d, e] using
      standardLubinTateChangedPrimitivePolynomialInCompositum_eval_addVal_ge
        hπ u n hu
  have hderivative :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (p.derivative.eval beta) =
        ((e * derivativeExponent : ℕ) : ℕ∞) := by
    rw [
      standardLubinTateChangedPrimitivePolynomialInCompositum_derivative_addVal
        hπ u n hbeta,
      ←
        standardLubinTateLevelToChangedLevelCompositumRamificationIndex_eq
          hπ u n]
    simp [q, d, derivativeExponent, e, nsmul_eq_mul]
    ring
  have hcombined :
      ((e * (d * (n + 2)) : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal target.valuationSubring
            (alpha - beta) +
          ((e * derivativeExponent : ℕ) : ℕ∞) := by
    exact hevaluation.trans (hproximity.trans_eq (by rw [hderivative]))
  have hsubtracted :
      ((e * (d * (n + 2)) : ℕ) : ℕ∞) -
          ((e * derivativeExponent : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal target.valuationSubring
          (alpha - beta) := by
    rw [tsub_le_iff_right]
    exact hcombined
  have hq : 2 ≤ q :=
    (Finite.one_lt_card : 1 < Nat.card F.residueField)
  have hqPred : q = (q - 1) + 1 := by
    omega
  have hqPredPred : q - 1 = (q - 2) + 1 := by
    omega
  have hqPower :
      q ^ (n + 1) = d + q ^ n := by
    calc
      q ^ (n + 1) = q ^ n * q := by
        rw [pow_succ]
      _ = q ^ n * ((q - 1) + 1) :=
        congrArg (fun z => q ^ n * z) hqPred
      _ = d + q ^ n := by
        dsimp [d]
        ring
  have hdSplit :
      d = (q - 2) * q ^ n + q ^ n := by
    calc
      d = (q - 1) * q ^ n := rfl
      _ = ((q - 2) + 1) * q ^ n :=
        congrArg (fun z => z * q ^ n) hqPredPred
      _ = (q - 2) * q ^ n + q ^ n := by
        ring
  have hdepth :
      d * (n + 2) = q ^ (n + 1) + derivativeExponent := by
    calc
      d * (n + 2) =
          n * d + d + d := by
        ring
      _ =
          (d + q ^ n) +
            (n * d + (q - 2) * q ^ n) := by
        rw [hdSplit]
        ring
      _ = q ^ (n + 1) + derivativeExponent := by
        rw [hqPower]
  have hdepthScaled :
      e * (d * (n + 2)) =
        e * q ^ (n + 1) + e * derivativeExponent := by
    rw [hdepth]
    ring
  have hnatSub :
      e * (d * (n + 2)) - e * derivativeExponent =
        e * q ^ (n + 1) := by
    rw [hdepthScaled, Nat.add_sub_cancel_right]
  have hdeep :
      ((e * q ^ (n + 1) : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal target.valuationSubring
          (alpha - beta) := by
    have h := hsubtracted
    rw [← ENat.natCast_sub, hnatSub] at h
    exact h
  have hqpow : q ^ n < q ^ (n + 1) :=
    pow_lt_pow_right₀
      (Finite.one_lt_card : 1 < Nat.card F.residueField)
      (Nat.lt_succ_self n)
  have hepos : 0 < e := by
    simpa [e] using
      standardLubinTateLevelToChangedLevelCompositumRamificationIndex_pos
        hπ u n
  have hstrictNat : e * q ^ n < e * q ^ (n + 1) :=
    Nat.mul_lt_mul_of_pos_left hqpow hepos
  have hstrict :
      ((e * q ^ n : ℕ) : ℕ∞) <
        ((e * q ^ (n + 1) : ℕ) : ℕ∞) := by
    exact (ENat.natCast_lt_natCast).2 hstrictNat
  exact hstrict.trans_le hdeep

/-- A nontrivial displacement of the old primitive point by a Galois
automorphism of the common compositum is bounded by the old level-`n`
bound, scaled by the relative ramification index. -/
private theorem
    standardLubinTateOriginalPrimitivePointInChangedLevelCompositum_displacement_addVal_le
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (σ :
      Gal(standardLubinTateChangedLevelCompositumField hπ u n/K))
    (hne :
      valuationSubringAutOfUniqueExtension
          (standardLubinTateChangedLevelCompositumCompleteDVF_hasUniqueDVFValuationExtension
            hπ u n)
          σ
          (standardLubinTateOriginalPrimitivePointInChangedLevelCompositum
            hπ u n) ≠
        standardLubinTateOriginalPrimitivePointInChangedLevelCompositum
          hπ u n) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateChangedLevelCompositumCompleteDVF
          hπ u n).valuationSubring
        (valuationSubringAutOfUniqueExtension
            (standardLubinTateChangedLevelCompositumCompleteDVF_hasUniqueDVFValuationExtension
              hπ u n)
            σ
            (standardLubinTateOriginalPrimitivePointInChangedLevelCompositum
              hπ u n) -
          standardLubinTateOriginalPrimitivePointInChangedLevelCompositum
            hπ u n) ≤
      ((standardLubinTateLevelToChangedLevelCompositumRamificationIndex
            hπ u n *
          Nat.card F.residueField ^ n : ℕ) : ℕ∞) := by
  let L := standardLubinTateLevelField hπ n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let level := standardLubinTateLevelCompleteDVF hπ n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let lambda := standardLubinTatePrimitivePointInteger hπ n
  let alpha :=
    standardLubinTateOriginalPrimitivePointInChangedLevelCompositum
      hπ u n
  have hmiddle :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        F.toCompleteDVF.toDVF level.toDVF :=
    standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension
      hπ n
  have htarget :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        F.toCompleteDVF.toDVF target.toDVF :=
    standardLubinTateChangedLevelCompositumCompleteDVF_hasUniqueDVFValuationExtension
      hπ u n
  let : Algebra L M :=
    standardLubinTateLevelToChangedLevelCompositumAlgebra hπ u n
  let : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsGalois K L :=
    standardLubinTateLevelField_isGalois (F := F) hπ n
  let : level.valuation.HasExtension target.valuation :=
    standardLubinTateLevelToChangedLevelCompositum_hasExtension
      hπ u n
  let tau : Gal(L / K) := σ.restrictNormal L
  have hrestrict :=
    valuationSubringAutOfUniqueExtension_integerMap_restrictNormal
      (base := F.toCompleteDVF.toDVF)
      (middle := level.toDVF)
      (target := target.toDVF)
      hmiddle htarget σ lambda
  have hneLevel :
      valuationSubringAutOfUniqueExtension hmiddle tau lambda ≠
        lambda := by
    intro heq
    apply hne
    change
      valuationSubringAutOfUniqueExtension htarget σ
          (integerMap level.toDVF target.toDVF lambda) =
        integerMap level.toDVF target.toDVF lambda
    rw [hrestrict, heq]
  have hlevel :=
    standardLubinTateGal_displacement_addVal_le_of_ne
      F hπ n tau hneLevel
  have hdisplacement :
      valuationSubringAutOfUniqueExtension htarget σ alpha - alpha =
        integerMap level.toDVF target.toDVF
          (valuationSubringAutOfUniqueExtension hmiddle tau lambda -
            lambda) := by
    change
      valuationSubringAutOfUniqueExtension htarget σ
            (integerMap level.toDVF target.toDVF lambda) -
          integerMap level.toDVF target.toDVF lambda =
        integerMap level.toDVF target.toDVF
          (valuationSubringAutOfUniqueExtension hmiddle tau lambda -
            lambda)
    rw [hrestrict, map_sub]
  rw [hdisplacement]
  change
    IsDiscreteValuationRing.addVal target.valuationSubring
        (standardLubinTateLevelToChangedLevelCompositumIntegerMap hπ u n
          (valuationSubringAutOfUniqueExtension hmiddle tau lambda -
            lambda)) ≤
      ((standardLubinTateLevelToChangedLevelCompositumRamificationIndex
            hπ u n *
          Nat.card F.residueField ^ n : ℕ) : ℕ∞)
  rw [
    standardLubinTateLevelToChangedLevelCompositum_addVal
      hπ u n
      (valuationSubringAutOfUniqueExtension hmiddle tau lambda - lambda)]
  have hscaled :=
    nsmul_le_nsmul_right hlevel
      (standardLubinTateLevelToChangedLevelCompositumRamificationIndex
        hπ u n)
  simpa [nsmul_eq_mul] using hscaled

/-- A changed primitive root in the compositum lies in the restricted copy
of the changed standard level. -/
private theorem
    standardLubinTateChangedPrimitiveRootInCompositum_mem_changedRestrict
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    {beta :
      (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).valuationSubring}
    (hbeta :
      beta ∈
        (standardLubinTateChangedPrimitivePolynomialInCompositum
          hπ u n).roots) :
    (beta : standardLubinTateChangedLevelCompositumField hπ u n) ∈
      IntermediateField.restrict
        (le_sup_right :
          standardLubinTateChangedLevelField hπ u n ≤
            standardLubinTateChangedLevelCompositumField hπ u n) := by
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  let level := standardLubinTateLevelCompleteDVF hπ' n
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  let p :=
    (standardLubinTatePrimitivePolynomial F
      (standardLubinTateChangedUniformizer F π u) n).map
        (standardLubinTateLevelCoefficientHom hπ' n)
  let j :=
    standardLubinTateChangedLevelToCompositumIntegerMap hπ u n
  have hj : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    have hfield :=
      congrArg (fun z : target.valuationSubring =>
        (z : standardLubinTateChangedLevelCompositumField hπ u n)) hab
    change
      standardLubinTateChangedLevelToCompositum hπ u n
          (a : standardLubinTateChangedLevelField hπ u n) =
        standardLubinTateChangedLevelToCompositum hπ u n
          (b : standardLubinTateChangedLevelField hπ u n) at hfield
    exact
      (standardLubinTateChangedLevelToCompositum
        hπ u n).injective hfield
  have hroots :
      (p.map j).roots = p.roots.map j :=
    (standardLubinTatePrimitivePolynomial_map_levelCoefficientHom_splits
      hπ' n).roots_map_of_injective hj
  have hbeta' : beta ∈ (p.map j).roots := by
    simpa [p, j,
      standardLubinTateChangedPrimitivePolynomialInCompositum] using
        hbeta
  rw [hroots] at hbeta'
  obtain ⟨y, -, hy⟩ := Multiset.mem_map.mp hbeta'
  rw [IntermediateField.mem_restrict]
  change
    (((beta :
        standardLubinTateChangedLevelCompositumField hπ u n) :
      SeparableClosure K)) ∈
        standardLubinTateChangedLevelField hπ u n
  rw [← hy,
    standardLubinTateChangedLevelToCompositumIntegerMap_apply_coe,
    standardLubinTateChangedLevelToCompositum_coe]
  exact (y : standardLubinTateChangedLevelField hπ u n).property

/-- A compositum automorphism fixing a sufficiently close changed root also
fixes the old primitive point. -/
private theorem
    standardLubinTateOriginalPrimitivePointInChangedLevelCompositum_fixed_of_fixed_close
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    {beta :
      (standardLubinTateChangedLevelCompositumCompleteDVF
        hπ u n).valuationSubring}
    (hclose :
      ((standardLubinTateLevelToChangedLevelCompositumRamificationIndex
              hπ u n *
            Nat.card F.residueField ^ n : ℕ) : ℕ∞) <
        IsDiscreteValuationRing.addVal
          (standardLubinTateChangedLevelCompositumCompleteDVF
            hπ u n).valuationSubring
          (standardLubinTateOriginalPrimitivePointInChangedLevelCompositum
              hπ u n -
            beta))
    (σ :
      Gal(standardLubinTateChangedLevelCompositumField hπ u n/K))
    (hfix :
      σ (beta :
        standardLubinTateChangedLevelCompositumField hπ u n) =
        (beta :
          standardLubinTateChangedLevelCompositumField hπ u n)) :
    σ
        (standardLubinTateOriginalPrimitivePointInChangedLevelCompositum
          hπ u n :
          standardLubinTateChangedLevelCompositumField hπ u n) =
      (standardLubinTateOriginalPrimitivePointInChangedLevelCompositum
        hπ u n :
        standardLubinTateChangedLevelCompositumField hπ u n) := by
  let target :=
    standardLubinTateChangedLevelCompositumCompleteDVF hπ u n
  have htarget :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        F.toCompleteDVF.toDVF target.toDVF :=
    standardLubinTateChangedLevelCompositumCompleteDVF_hasUniqueDVFValuationExtension
      hπ u n
  let alpha :=
    standardLubinTateOriginalPrimitivePointInChangedLevelCompositum
      hπ u n
  have hfixInteger :
      valuationSubringAutOfUniqueExtension htarget σ beta = beta := by
    apply Subtype.ext
    simpa only [
      valuationSubringAutOfUniqueExtension_apply_coe] using hfix
  have hfixedInteger :
      valuationSubringAutOfUniqueExtension htarget σ alpha = alpha := by
    apply
      valuationSubringAutOfUniqueExtension_eq_of_fixed_of_close
        htarget σ alpha beta hfixInteger
    intro hne
    exact
      (standardLubinTateOriginalPrimitivePointInChangedLevelCompositum_displacement_addVal_le
        hπ u n σ hne).trans_lt hclose
  have hfixedField := congrArg Subtype.val hfixedInteger
  simpa only [
    valuationSubringAutOfUniqueExtension_apply_coe] using hfixedField

/-- Inside the common compositum, the restricted copies of the original and
changed standard levels coincide at principal-unit depth `n + 1`. -/
private theorem
    standardLubinTateHigherUnit_restrict_changedLevel_eq_originalLevel
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (hu : u ∈
      CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) :
    IntermediateField.restrict
        (le_sup_right :
          standardLubinTateChangedLevelField hπ u n ≤
            standardLubinTateChangedLevelCompositumField hπ u n) =
      IntermediateField.restrict
        (le_sup_left :
          standardLubinTateLevelField hπ n ≤
            standardLubinTateChangedLevelCompositumField hπ u n) := by
  let hπ' :=
    standardLubinTateChangedUniformizer_isUniformizer hπ u
  let L := standardLubinTateLevelField hπ n
  let L' := standardLubinTateChangedLevelField hπ u n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let oldLevel : IntermediateField K M :=
    IntermediateField.restrict (le_sup_left : L ≤ M)
  let changedLevel : IntermediateField K M :=
    IntermediateField.restrict (le_sup_right : L' ≤ M)
  let alpha :=
    standardLubinTateOriginalPrimitivePointInChangedLevelCompositum
      hπ u n
  let : FiniteDimensional K M :=
    standardLubinTateChangedLevelCompositumField_finiteDimensional
      hπ u n
  let : IsGalois K M :=
    standardLubinTateChangedLevelCompositumField_isGalois hπ u n
  obtain ⟨beta, hbeta, hclose⟩ :=
    exists_standardLubinTateChangedPrimitiveRootInCompositum_close
      hπ u n hu
  have hstabilizer :
      ∀ σ : Gal(M / K),
        σ (beta : M) = (beta : M) →
          σ (alpha : M) = (alpha : M) := by
    intro σ hfix
    exact
      standardLubinTateOriginalPrimitivePointInChangedLevelCompositum_fixed_of_fixed_close
        hπ u n hclose σ hfix
  have hadjoin :
      K⟮(alpha : M)⟯ ≤ K⟮(beta : M)⟯ :=
    adjoin_le_adjoin_of_forall_fixed_imp_fixed
      (alpha : M) (beta : M) hstabilizer
  have hbetaChanged : (beta : M) ∈ changedLevel := by
    exact
      standardLubinTateChangedPrimitiveRootInCompositum_mem_changedRestrict
        hπ u n hbeta
  have hbetaAdjoinLe : K⟮(beta : M)⟯ ≤ changedLevel := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hbetaChanged
  have halphaChanged : (alpha : M) ∈ changedLevel := by
    exact
      hbetaAdjoinLe
        (hadjoin
          (IntermediateField.mem_adjoin_simple_self K (alpha : M)))
  let oldEquiv : L ≃ₐ[K] oldLevel :=
    IntermediateField.restrictAlgEquiv (le_sup_left : L ≤ M)
  let changedEquiv : L' ≃ₐ[K] changedLevel :=
    IntermediateField.restrictAlgEquiv (le_sup_right : L' ≤ M)
  let oldPowerBasis : PowerBasis K oldLevel :=
    (standardLubinTateLevelPowerBasis hπ n).map oldEquiv
  let oldInclusion : oldLevel →ₐ[K] M := oldLevel.val
  have hgen :
      oldInclusion oldPowerBasis.gen = (alpha : M) := by
    simp only [oldPowerBasis, PowerBasis.map_gen]
    change
      standardLubinTateLevelToChangedLevelCompositum hπ u n
          (standardLubinTateLevelGenerator hπ n) =
        ((standardLubinTateLevelToChangedLevelCompositumIntegerMap
              hπ u n
              (standardLubinTatePrimitivePointInteger hπ n) :
            (standardLubinTateChangedLevelCompositumCompleteDVF
              hπ u n).valuationSubring) :
          M)
    rw [
      standardLubinTateLevelToChangedLevelCompositumIntegerMap_apply_coe]
    rfl
  have hgenComap :
      oldPowerBasis.gen ∈
        changedLevel.toSubalgebra.comap oldInclusion := by
    change oldInclusion oldPowerBasis.gen ∈ changedLevel
    rw [hgen]
    exact halphaChanged
  have hadjoinLe :
      Algebra.adjoin K ({oldPowerBasis.gen} : Set oldLevel) ≤
        changedLevel.toSubalgebra.comap oldInclusion := by
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hgenComap
  have holdLeChanged : oldLevel ≤ changedLevel := by
    intro x hx
    let xOld : oldLevel := ⟨x, hx⟩
    have hxAdjoin :
        xOld ∈ Algebra.adjoin K
          ({oldPowerBasis.gen} : Set oldLevel) := by
      rw [oldPowerBasis.adjoin_gen_eq_top]
      trivial
    have hxComap := hadjoinLe hxAdjoin
    change oldInclusion xOld ∈ changedLevel at hxComap
    simpa [oldInclusion, xOld] using hxComap
  let q := Nat.card F.residueField
  let d := (q - 1) * q ^ n
  have hfinrankOld :
      Module.finrank K oldLevel = d := by
    calc
      Module.finrank K oldLevel =
          Module.finrank K L :=
        oldEquiv.toLinearEquiv.finrank_eq.symm
      _ = d := by
        simpa [L, q, d] using
          standardLubinTateLevelField_finrank hπ n
  have hfinrankChanged :
      Module.finrank K changedLevel = d := by
    calc
      Module.finrank K changedLevel =
          Module.finrank K L' :=
        changedEquiv.toLinearEquiv.finrank_eq.symm
      _ = d := by
        simpa [L', hπ', q, d] using
          standardLubinTateLevelField_finrank hπ' n
  have heq : oldLevel = changedLevel :=
    IntermediateField.eq_of_le_of_finrank_eq
      holdLeChanged (hfinrankOld.trans hfinrankChanged.symm)
  exact heq.symm

/-- The changed standard level is `K`-isomorphic to the original standard
level when the unit factor is congruent to one at depth `n + 1`. -/
noncomputable def standardLubinTateHigherUnitChangedLevelAlgEquiv
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (hu : u ∈
      CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) :
    standardLubinTateChangedLevelField hπ u n ≃ₐ[K]
      standardLubinTateLevelField hπ n := by
  let L := standardLubinTateLevelField hπ n
  let L' := standardLubinTateChangedLevelField hπ u n
  let M := standardLubinTateChangedLevelCompositumField hπ u n
  let oldLevel : IntermediateField K M :=
    IntermediateField.restrict (le_sup_left : L ≤ M)
  let changedLevel : IntermediateField K M :=
    IntermediateField.restrict (le_sup_right : L' ≤ M)
  let oldEquiv : L ≃ₐ[K] oldLevel :=
    IntermediateField.restrictAlgEquiv (le_sup_left : L ≤ M)
  let changedEquiv : L' ≃ₐ[K] changedLevel :=
    IntermediateField.restrictAlgEquiv (le_sup_right : L' ≤ M)
  have heq : changedLevel = oldLevel := by
    exact
      standardLubinTateHigherUnit_restrict_changedLevel_eq_originalLevel
        hπ u n hu
  exact
    changedEquiv.trans
      ((IntermediateField.equivOfEq heq).trans oldEquiv.symm)

/-- A unit factor congruent to one at depth `n + 1` is a norm from the
original standard level. -/
theorem
    standardLubinTateUnitFactorFieldUnit_mem_standardNormSubgroup_of_mem_higher
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ)
    (hu : u ∈
      CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) :
    standardLubinTateUnitFactorFieldUnit F u ∈
      standardLubinTateNormSubgroup hπ n :=
  standardLubinTateUnitFactorFieldUnit_mem_standardNormSubgroup_of_algEquiv
    hπ u n
      (standardLubinTateHigherUnitChangedLevelAlgEquiv
        hπ u n hu)

end LubinTate

end
