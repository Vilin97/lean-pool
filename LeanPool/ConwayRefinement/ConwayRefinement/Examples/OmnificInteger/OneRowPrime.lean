/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Primality.IrreducibleOmnificIntegers
public import LeanPool.ConwayRefinement.ConwayRefinement.Examples.OmnificInteger.OneRowNormalForm

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CharZero
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Degree
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OneRow
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ArchimedeanAssumptions
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.DegreeTransfer
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.IntegerPart
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.RealLeadingSplit

/-!
# Conway's one-row prime

Consider Conway's normal form

`1 + Σ n : ℕ, ω ^ (1 / (n + 1))`.

It is the omnific integer `ofRealSeries` of Berarducci's coefficient-one row with constant term.
The row remains irreducible after extending coefficients to the infinitesimal Hahn field, so the
residue-one case of LM24, Proposition 8.3.6(5) makes the omnific integer irreducible. It is
reduced, and its support has exact order type `ω + 1`, below `ω ^ ω`. The finite-degree primality
theorem then makes it prime.

## References

* A. Berarducci, *Factorization in generalized power series*, Trans. Amer. Math. Soc. 352
  (2000), 553–577, cited as [Ber00].
* S. L'Innocente, V. Mantova, *A factorisation theory for generalised power series and omnific
  integers*, Adv. Math. 442 (2024) 109513, cited as [LM24].
-/

open scoped HahnSeries

noncomputable section

namespace Surreal.OmnificInteger.OneRowExample

open Berarducci.OneRow HahnSeries.Nonpositive

private theorem withConstant_ne_zero : withConstant (K := ℝ) ≠ 0 := by
  intro hzero
  have hcoeff := withConstant_coeff_zero (K := ℝ)
  rw [hzero] at hcoeff
  norm_num at hcoeff

private theorem withConstant_constantCoeff_mem :
    constantCoeff (withConstant (K := ℝ)) ∈ Surreal.realIntegerSubring := by
  rw [withConstant_constantCoeff]
  exact Surreal.realIntegerSubring.one_mem

private theorem signedOneRow_order_neg :
    (mapRealDomainToSurreal (withConstant (K := ℝ)) : ℝ⟦Surreal.{0}⟧).order < 0 := by
  have hcoeff : (mapRealDomainToSurreal (withConstant (K := ℝ)) : ℝ⟦Surreal.{0}⟧).coeff
      ((Berarducci.OneRow.exponent 0 : ℝ) : Surreal) ≠ 0 := by
    rw [mapRealDomainToSurreal_coeff_real, withConstant_coeff_exponent]
    exact one_ne_zero
  refine (HahnSeries.order_le_of_coeff_ne_zero hcoeff).trans_lt ?_
  exact_mod_cast (show Berarducci.OneRow.exponent 0 < 0 by
    rw [Berarducci.OneRow.exponent_apply]
    norm_num)

private theorem signedOneRow_order_ne_zero :
    (mapRealDomainToSurreal (withConstant (K := ℝ)) : ℝ⟦Surreal.{0}⟧).order ≠ 0 :=
  signedOneRow_order_neg.ne

private theorem signedExponent_eq_neg_normalExponent (n : ℕ) :
    Berarducci.OneRow.exponent n =
      -OneRowExample.exponent n := by
  rw [Berarducci.OneRow.exponent_apply,
    OneRowExample.exponent_apply]

public section

/-- Conway's one-row omnific integer in the cut presentation. -/
def oneRowOz : Surreal.OmnificInteger.{0} :=
  ofRealSeries (withConstant (K := ℝ)) withConstant_constantCoeff_mem

private theorem oneRowOz_signed :
    oneRowOz.1.toSignedFullHahnSeries = mapRealDomainToSurreal (withConstant (K := ℝ)) :=
  toSignedFullHahnSeries_ofRealSeries _ _

/-- Conway's one-row omnific integer is irreducible. -/
theorem oneRowOz_irreducible : Irreducible oneRowOz := by
  apply irreducible_ofRealSeries
  apply irreducible_mapRealDomainToSurrealIntegerPart Surreal.archimedeanStrata
    Surreal.realIntegerSubring (withConstant (K := ℝ)) withConstant_ne_zero
    signedOneRow_order_ne_zero withConstant_constantCoeff
  rw [nonpositiveCoefficientMap_withConstant]
  exact (irreducible_withoutConstant_and_withConstant
    (K := ℝ⟦FiniteArchimedeanClass.ball ℝ Surreal.realFiniteClass⟧)).2

/-- The cut-defined omnific integer has the prescribed literal Conway normal form. -/
theorem oneRowOz_toHahnSeries : oneRowOz.1.toHahnSeries =
    OneRowExample.normalForm := by
  apply Surreal.toHahnSeries_eq_of_toSignedFullHahnSeries_eq oneRowOz_signed
  · intro r
    by_cases hr : r ∈ Set.range exponentEmbedding
    · obtain ⟨n, rfl⟩ := hr
      rw [exponentEmbedding_apply, withConstant_coeff_exponent,
        signedExponent_eq_neg_normalExponent, Real.toSurreal_neg, neg_neg,
        OneRowExample.normalForm_coeff_exponent]
    · by_cases hr0 : r = 0
      · subst hr0
        rw [withConstant_coeff_zero]
        simpa using OneRowExample.normalForm_coeff_zero
      · have hzero : (withConstant (K := ℝ) : ℝ⟦ℝ⟧).coeff r = 0 := by
          rw [← not_ne_iff, ← HahnSeries.mem_support, withConstant_support]
          rintro (hrange | hrzero)
          · exact hr hrange
          · exact hr0 (Set.mem_singleton_iff.mp hrzero)
        rw [hzero, ← not_ne_iff, ← SurrealHahnSeries.mem_support_iff,
          OneRowExample.normalForm_support]
        rintro ⟨p, hp⟩
        induction p using WithTop.recTopCoe with
        | top =>
            apply hr0
            have h0 : (0 : Surreal) = -(r : Surreal) := hp
            exact_mod_cast (neg_eq_zero.mp h0.symm)
        | coe n =>
            apply hr
            refine ⟨n, ?_⟩
            have hn : ((OneRowExample.exponent n : ℝ) : Surreal) =
              -(r : Surreal) := hp
            rw [← Real.toSurreal_neg, Real.toSurreal_inj] at hn
            rw [exponentEmbedding_apply, signedExponent_eq_neg_normalExponent, hn, neg_neg]
  · rw [OneRowExample.normalForm_support]
    rintro _ ⟨p, rfl⟩
    induction p using WithTop.recTopCoe with
    | top =>
        refine ⟨0, ?_⟩
        change -((0 : ℝ) : Surreal) = (0 : Surreal)
        simp
    | coe n =>
        refine ⟨-OneRowExample.exponent n, ?_⟩
        change -((-OneRowExample.exponent n : ℝ) : Surreal) =
          ((OneRowExample.exponent n : ℝ) : Surreal)
        rw [Real.toSurreal_neg, neg_neg]

/-- The Conway support is exactly the displayed positive row followed by zero. -/
theorem oneRowOz_support : oneRowOz.1.support =
    Set.range OneRowExample.exponentAtIndex := by
  rw [← Surreal.support_toHahnSeries, oneRowOz_toHahnSeries,
    OneRowExample.normalForm_support]

/-- The one-row Conway normal form has exact support order type `ω + 1`. -/
theorem oneRowOz_length : oneRowOz.1.length = Ordinal.omega0 + 1 := by
  rw [oneRowOz, length_ofRealSeries, withConstant_supportOrderType, Ordinal.lift_id]

/-- Conway's one-row omnific integer is reduced. -/
theorem oneRowOz_isReduced :
    HahnSeries.Nonpositive.IsReduced oneRowOz.toSignedNonpositiveHahn :=
  isReduced_ofRealSeries _ _ signedOneRow_order_ne_zero
    withConstant_constantCoeff

/-- Conway's one-row omnific integer is prime. -/
theorem oneRowOz_prime : Prime oneRowOz :=
  Surreal.OmnificInteger.prime_of_irreducible _ oneRowOz_irreducible

end

end Surreal.OmnificInteger.OneRowExample
