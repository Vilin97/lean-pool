/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.NormalFormMul
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.NormalForm

/-!
# Hahn multiplication of omnific-integer normal forms

This module records the multiplicative Conway-normal-form bridge needed for the omnific-integer
application in LM24. It proves that the formal Hahn product of two omnific-integer normal forms
again satisfies Conway's support-and-constant characterization of an omnific integer.

The resulting `normalFormProduct` is the transported multiplication, and multiplicativity of the
Conway normal form identifies it with the ordinary surreal product.
-/

universe u

open Set

public noncomputable section

namespace Surreal

/-- The surreal represented by the Hahn product of two omnific-integer normal forms is an omnific
integer. -/
theorem IsOmnificInteger.toHahnSeries_mul_toSurreal {x y : Surreal.{u}}
    (hx : IsOmnificInteger x) (hy : IsOmnificInteger y) :
    IsOmnificInteger ((x.toHahnSeries * y.toHahnSeries).toSurreal) := by
  obtain ⟨hxSupport, m, hm⟩ := isOmnificInteger_iff_normalForm.mp hx
  obtain ⟨hySupport, n, hn⟩ := isOmnificInteger_iff_normalForm.mp hy
  have hxSeriesSupport : x.toHahnSeries.support ⊆ Ici 0 := by
    simpa only [support_toHahnSeries] using hxSupport
  have hySeriesSupport : y.toHahnSeries.support ⊆ Ici 0 := by
    simpa only [support_toHahnSeries] using hySupport
  rw [isOmnificInteger_iff_normalForm]
  constructor
  · simpa only [SurrealHahnSeries.support_toSurreal] using
      SurrealHahnSeries.support_mul_subset_Ici hxSeriesSupport hySeriesSupport
  · rw [SurrealHahnSeries.coeff_toSurreal,
      SurrealHahnSeries.coeff_zero_mul_of_support_subset_Ici hxSeriesSupport hySeriesSupport]
    rw [congrFun (coeff_toHahnSeries x) 0, congrFun (coeff_toHahnSeries y) 0,
      ← hm, ← hn]
    exact ⟨m * n, by simp⟩

/-- For omnific integers, Conway/Hahn multiplication compatibility reduces to the product of the
two strictly positive truncations. Integer constant terms and both cross terms are already
handled by additive compatibility. -/
theorem IsOmnificInteger.toHahnSeries_mul_of_trunc_zero {x y : Surreal.{u}}
    (hx : IsOmnificInteger x) (hy : IsOmnificInteger y)
    (hpositive : (x.trunc 0 * y.trunc 0).toHahnSeries =
      x.toHahnSeries.trunc 0 * y.toHahnSeries.trunc 0) :
    (x * y).toHahnSeries = x.toHahnSeries * y.toHahnSeries := by
  obtain ⟨hxSupport, m, hm⟩ := isOmnificInteger_iff_normalForm.mp hx
  obtain ⟨hySupport, n, hn⟩ := isOmnificInteger_iff_normalForm.mp hy
  have hmSurreal : (m : Surreal) = (x.coeff 0 : Surreal) := by
    exact_mod_cast hm
  have hnSurreal : (n : Surreal) = (y.coeff 0 : Surreal) := by
    exact_mod_cast hn
  have hxSplit : x.trunc 0 + (m : Surreal) = x := by
    rw [hmSurreal, ← sub_trunc_zero_eq_realCast_of_support_subset_Ici hxSupport]
    abel
  have hySplit : y.trunc 0 + (n : Surreal) = y := by
    rw [hnSurreal, ← sub_trunc_zero_eq_realCast_of_support_subset_Ici hySupport]
    abel
  have hxSeriesSplit : x.toHahnSeries.trunc 0 +
      SurrealHahnSeries.single 0 (m : ℝ) = x.toHahnSeries := by
    rw [← toHahnSeries_trunc, ← toHahnSeries_intCast,
      ← toHahnSeries_add, hxSplit]
  have hySeriesSplit : y.toHahnSeries.trunc 0 +
      SurrealHahnSeries.single 0 (n : ℝ) = y.toHahnSeries := by
    rw [← toHahnSeries_trunc, ← toHahnSeries_intCast,
      ← toHahnSeries_add, hySplit]
  conv_lhs => rw [← hxSplit, ← hySplit]
  rw [add_mul, mul_add, mul_add, toHahnSeries_add, toHahnSeries_add,
    toHahnSeries_add, hpositive, toHahnSeries_mul_intCast,
    toHahnSeries_intCast_mul, toHahnSeries_mul_intCast,
    toHahnSeries_trunc x 0, toHahnSeries_trunc y 0,
    toHahnSeries_intCast]
  calc
    _ = (x.toHahnSeries.trunc 0 + SurrealHahnSeries.single 0 (m : ℝ)) *
        (y.toHahnSeries.trunc 0 + SurrealHahnSeries.single 0 (n : ℝ)) := by ring
    _ = x.toHahnSeries * y.toHahnSeries := by rw [hxSeriesSplit, hySeriesSplit]

namespace OmnificInteger

/-- Multiplication transported from formal Hahn multiplication through Conway normal forms. -/
def normalFormProduct (x y : OmnificInteger.{u}) : OmnificInteger.{u} :=
  ⟨(x.1.toHahnSeries * y.1.toHahnSeries).toSurreal,
    (mem_omnificIntegers.mpr
      ((mem_omnificIntegers.mp x.2).toHahnSeries_mul_toSurreal
        (mem_omnificIntegers.mp y.2)))⟩

/-- The surreal underlying the transported normal-form product. -/
theorem coe_normalFormProduct (x y : OmnificInteger.{u}) :
    (normalFormProduct x y : Surreal) =
      (x.1.toHahnSeries * y.1.toHahnSeries).toSurreal :=
  (rfl)

/-- The Conway normal form of the transported product is the formal Hahn product. -/
theorem toHahnSeries_normalFormProduct (x y : OmnificInteger.{u}) :
    (normalFormProduct x y : Surreal).toHahnSeries =
      x.1.toHahnSeries * y.1.toHahnSeries := by
  rw [coe_normalFormProduct, SurrealHahnSeries.toHahnSeries_toSurreal]

/-- Multiplication transported through Conway normal forms is ordinary omnific-integer
multiplication. -/
@[simp]
theorem normalFormProduct_eq_mul (x y : OmnificInteger.{u}) :
    normalFormProduct x y = x * y := by
  apply Subtype.ext
  change (x.1.toHahnSeries * y.1.toHahnSeries).toSurreal = x.1 * y.1
  rw [SurrealHahnSeries.toSurreal_mul, Surreal.toSurreal_toHahnSeries,
    Surreal.toSurreal_toHahnSeries]

end OmnificInteger

end Surreal
