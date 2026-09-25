/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.Reduction
/-!
# Recursive coefficients for Lubin--Tate intertwiners

This module connects the two coefficient-level inputs for the recursive
construction of a same-uniformizer Lubin--Tate intertwiner.  Reduction makes
every coefficient of the current defect divisible by the uniformizer.  In
total degree `m ≥ 2`, the remaining scalar equation has factor
`1 - π ^ (m - 1)`, which is a unit.
-/

@[expose] public section

noncomputable
section

universe u v w

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- The coefficient of an intertwining defect after removing one factor of
the chosen uniformizer. -/
noncomputable def normalizedDefectCoefficient
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) :
    F.valuationSubring :=
  Classical.choose (uniformizer_dvd_coeff_defect hπ e ebar hH d)

/-- Multiplying the normalized defect coefficient by the uniformizer recovers
the original coefficient. -/
theorem uniformizer_mul_normalizedDefectCoefficient
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) :
    π * normalizedDefectCoefficient hπ e ebar hH d =
      MvPowerSeries.coeff d (defect e ebar H) := by
  exact
    (Classical.choose_spec
      (uniformizer_dvd_coeff_defect hπ e ebar hH d)).symm

/-- The coefficient added in total degree `d.degree` by the recursive
same-uniformizer intertwiner construction.

Its defining equation is the one which cancels the normalized defect in that
degree.  The hypothesis `2 ≤ d.degree` ensures that the exponent
`d.degree - 1` is positive. -/
noncomputable def correctionCoefficient
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    F.valuationSubring :=
  Classical.choose
    (existsUnique_one_sub_uniformizer_pow_mul_eq hπ
      (by omega : d.degree - 1 ≠ 0)
      (-normalizedDefectCoefficient hπ e ebar hH d))

/-- The recursive correction coefficient satisfies its defining scalar
equation. -/
theorem correctionCoefficient_spec
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    (1 - π ^ (d.degree - 1)) *
        correctionCoefficient hπ e ebar hH d hd =
      -normalizedDefectCoefficient hπ e ebar hH d := by
  exact
    (Classical.choose_spec
      (existsUnique_one_sub_uniformizer_pow_mul_eq hπ
        (by omega : d.degree - 1 ≠ 0)
        (-normalizedDefectCoefficient hπ e ebar hH d))).1

/-- The defining scalar equation determines the recursive correction
coefficient uniquely. -/
theorem correctionCoefficient_unique
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree)
    {c : F.valuationSubring}
    (hc :
      (1 - π ^ (d.degree - 1)) * c =
        -normalizedDefectCoefficient hπ e ebar hH d) :
    c = correctionCoefficient hπ e ebar hH d hd := by
  exact
    (Classical.choose_spec
      (existsUnique_one_sub_uniformizer_pow_mul_eq hπ
        (by omega : d.degree - 1 ≠ 0)
        (-normalizedDefectCoefficient hπ e ebar hH d))).2 c hc

end SameUniformizer
end LubinTate

end
