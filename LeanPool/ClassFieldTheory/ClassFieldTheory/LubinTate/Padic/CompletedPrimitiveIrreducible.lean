/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedLevel
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
/-!
# Irreducibility of the completed p-adic primitive polynomial

The standard multiplicative Lubin--Tate primitive polynomial remains
Eisenstein after extending its integer coefficients to the valuation ring of
the completed maximal unramified field.  In particular it remains
irreducible over the completed-unramified fraction field.
-/

noncomputable section

open scoped Polynomial

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField

/-- The image of the canonical p-adic uniformizer is a uniformizer of the
completed-unramified coefficient field. -/
theorem padicCompletedUnramifiedIntegerMap_isUniformizer
    (p : ℕ) [Fact p.Prime] :
    let π :=
      padicIntEquivValuationSubring p (p : ℤ_[p])
    (padicCompletedUnramifiedCompleteDVF p).valuation.IsUniformizer
      ((padicCompletedUnramifiedIntegerMap p π :
        (padicCompletedUnramifiedCompleteDVF p).valuationSubring) :
          padicCompletedUnramifiedField p) := by
  let F := padicLocalField p
  let base := F.toCompleteDVF
  let target := padicCompletedUnramifiedCompleteDVF p
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let πE : target.valuationSubring :=
    padicCompletedUnramifiedIntegerMap p π
  have hπ : base.valuation.IsUniformizer (π : ℚ_[p]) := by
    simpa only [F, base, π] using
      padicMultiplicativeLubinTateSeries_isUniformizer p
  obtain ⟨ϖ, hϖ⟩ := target.exists_uniformizer
  apply hϖ.of_associated
  rw [← Ideal.span_singleton_eq_span_singleton]
  calc
    Ideal.span ({ϖ} : Set target.valuationSubring) =
        target.maximalIdeal :=
      (target.maximalIdeal_eq_span_uniformizer hϖ).symm
    _ =
        Ideal.map (padicCompletedUnramifiedIntegerMap p)
          base.maximalIdeal := by
      simpa only [F, base, target] using
        (padicCompletedUnramifiedIntegerMap_map_maximalIdeal p).symm
    _ =
        Ideal.map (padicCompletedUnramifiedIntegerMap p)
          (Ideal.span
            ({π} : Set (padicLocalField p).valuationSubring)) := by
      exact congrArg (Ideal.map (padicCompletedUnramifiedIntegerMap p))
        (base.maximalIdeal_eq_span_uniformizer hπ)
    _ = Ideal.span ({πE} : Set target.valuationSubring) := by
      rw [Ideal.map_span, Set.image_singleton]

/-- The completed integral primitive polynomial has the same positive degree
as the original finite multiplicative Lubin--Tate polynomial. -/
theorem padicCompletedPrimitivePolynomialInteger_natDegree
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedPrimitivePolynomialInteger p n).natDegree =
      (p - 1) * p ^ n := by
  exact ((padicCompletedPrimitivePolynomialInteger_monic p n).natDegree_map
    (algebraMap
      (padicCompletedUnramifiedCompleteDVF p).valuationSubring
      (padicCompletedUnramifiedField p))).symm.trans
    ((congrArg Polynomial.natDegree
      (padicCompletedPrimitivePolynomialInteger_map p n)).trans
      (padicCompletedPrimitivePolynomial_natDegree p n))

/-- The completed integral primitive polynomial is genuinely Eisenstein at
the maximal ideal of the completed-unramified valuation ring. -/
theorem padicCompletedPrimitivePolynomialInteger_isEisensteinAt
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedPrimitivePolynomialInteger p n).IsEisensteinAt
      (padicCompletedUnramifiedCompleteDVF p).maximalIdeal := by
  let target := padicCompletedUnramifiedCompleteDVF p
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let πE : target.valuationSubring :=
    padicCompletedUnramifiedIntegerMap p π
  have hmonic :
      (padicCompletedPrimitivePolynomialInteger p n).Monic :=
    padicCompletedPrimitivePolynomialInteger_monic p n
  refine hmonic.isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal target.valuationSubring).ne_top
    ?_ ?_
  · intro i hi
    exact
      (padicCompletedPrimitivePolynomialInteger_isWeaklyEisensteinAt
        p n).mem hi
  · have hπE :
        target.valuation.IsUniformizer
          (πE : padicCompletedUnramifiedField p) := by
      simpa only [target, π, πE] using
        padicCompletedUnramifiedIntegerMap_isUniformizer p
    have hnotMem :
        πE ∉ target.maximalIdeal ^ 2 :=
      target.uniformizer_not_mem_maximalIdeal_sq hπE
    change ((standardLubinTatePrimitivePolynomial (padicLocalField p) π n).map
      (padicCompletedUnramifiedIntegerMap p)).coeff 0 ∉ target.maximalIdeal ^ 2
    rw [Polynomial.coeff_map, standardLubinTatePrimitivePolynomial_coeff_zero]
    exact hnotMem

/-- The completed integral primitive polynomial is irreducible in the
completed-unramified valuation ring. -/
theorem padicCompletedPrimitivePolynomialInteger_irreducible
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Irreducible (padicCompletedPrimitivePolynomialInteger p n) := by
  apply
    (padicCompletedPrimitivePolynomialInteger_isEisensteinAt p n).irreducible
      (IsLocalRing.maximalIdeal.isMaximal
        (padicCompletedUnramifiedCompleteDVF p).valuationSubring).isPrime
      (padicCompletedPrimitivePolynomialInteger_monic p n).isPrimitive
  rw [padicCompletedPrimitivePolynomialInteger_natDegree]
  exact Nat.mul_pos
    (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
    (Nat.pow_pos (Fact.out : p.Prime).pos)

/-- The primitive polynomial remains irreducible over the completed maximal
unramified p-adic field. -/
theorem padicCompletedPrimitivePolynomial_irreducible
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Irreducible (padicCompletedPrimitivePolynomial p n) := by
  have hmap :
      Irreducible
        ((padicCompletedPrimitivePolynomialInteger p n).map
          (algebraMap
            (padicCompletedUnramifiedCompleteDVF p).valuationSubring
            (padicCompletedUnramifiedField p))) :=
    (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
      (padicCompletedPrimitivePolynomialInteger_monic p n)).mp
      (padicCompletedPrimitivePolynomialInteger_irreducible p n)
  rwa [padicCompletedPrimitivePolynomialInteger_map] at hmap

end LubinTate

end
