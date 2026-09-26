/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.StandardSeries
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedUnramifiedField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeSeries
/-!
# Completed p-adic Lubin--Tate series

This module extends the multiplicative and changed-standard Lubin--Tate series to the completed
unramified Witt ring and records their coefficients and residue reductions.
-/

@[expose] public section

noncomputable
section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open SameUniformizer

/-- The multiplicative Lubin--Tate series after extending its coefficients
to the completed unramified Witt ring. -/
noncomputable def padicCompletedMultiplicativeSeries
    (p : ℕ) [Fact p.Prime] :
    PowerSeries (padicCompletedUnramifiedWittRing p) :=
  PowerSeries.map
    (padicValuationSubringToCompletedUnramifiedWittRing p)
    (padicMultiplicativeLubinTateSeries p).toPowerSeries

/-- The standard Lubin--Tate series for the changed uniformizer `u p`,
after extending its coefficients to the completed unramified Witt ring. -/
noncomputable def padicCompletedChangedStandardSeries
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries (padicCompletedUnramifiedWittRing p) :=
  PowerSeries.map
    (padicValuationSubringToCompletedUnramifiedWittRing p)
    (standardLubinTateSeries
      (standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u)).toPowerSeries

/-- The completed multiplicative Lubin--Tate series is the binomial series
`(1 + X) ^ p - 1`. -/
theorem padicCompletedMultiplicativeSeries_eq
    (p : ℕ) [Fact p.Prime] :
    padicCompletedMultiplicativeSeries p =
      (1 + PowerSeries.X) ^ p - 1 := by
  rw [padicCompletedMultiplicativeSeries,
    LubinTateSeries.padicMultiplicativeLubinTateSeries_toPowerSeries,
    PowerSeries.binomialSeries_nat]
  simp only [map_sub, map_pow, map_add, map_one, PowerSeries.map_X]

/-- The completed changed-standard series has linear coefficient `u p` and
degree-`p` term `X ^ p`. -/
theorem padicCompletedChangedStandardSeries_eq
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedChangedStandardSeries p u =
      PowerSeries.C
          (((padicValuationUnitToCompletedUnramifiedWittUnit p u :
              (padicCompletedUnramifiedWittRing p)ˣ) : padicCompletedUnramifiedWittRing p) *
            (p : padicCompletedUnramifiedWittRing p)) *
          PowerSeries.X +
        PowerSeries.X ^ p := by
  have hcard :
      Nat.card (padicLocalField p).residueField = p := by
    simpa [padicLocalField] using
      padicCompleteDVF_residueField_card p
  rw [padicCompletedChangedStandardSeries,
    LubinTateSeries.standardLubinTateSeries_toPowerSeries]
  simp only [standardLubinTatePowerSeries,
    standardLubinTateChangedUniformizer,
    map_add, map_mul, map_pow, PowerSeries.map_C,
    PowerSeries.map_X, hcard]
  have hcoeff :
      padicValuationSubringToCompletedUnramifiedWittRing p
          ((u : (padicLocalField p).valuationSubring) *
            (show (padicLocalField p).valuationSubring from
              padicIntEquivValuationSubring p (p : ℤ_[p]))) =
        padicValuationSubringToCompletedUnramifiedWittRing p u *
          (p : padicCompletedUnramifiedWittRing p) :=
    (map_mul (padicValuationSubringToCompletedUnramifiedWittRing p)
      (u : (padicLocalField p).valuationSubring)
      (show (padicLocalField p).valuationSubring from
        padicIntEquivValuationSubring p (p : ℤ_[p]))).trans
      (congrArg (fun z : padicCompletedUnramifiedWittRing p =>
        padicValuationSubringToCompletedUnramifiedWittRing p u * z)
        (padicValuationSubringToCompletedUnramifiedWittRing_uniformizer p))
  exact congrArg (fun z : PowerSeries (padicCompletedUnramifiedWittRing p) =>
      z * PowerSeries.X + PowerSeries.X ^ p)
    ((congrArg PowerSeries.C hcoeff).trans
      (map_mul PowerSeries.C
        (padicValuationSubringToCompletedUnramifiedWittRing p u)
        (p : padicCompletedUnramifiedWittRing p)))

theorem padicCompletedMultiplicativeSeries_constantCoeff
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.constantCoeff
        (padicCompletedMultiplicativeSeries p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,
    padicCompletedMultiplicativeSeries,
    PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact
    (congrArg (padicValuationSubringToCompletedUnramifiedWittRing p)
      (padicMultiplicativeLubinTateSeries p).constantCoeff_eq_zero).trans
      (map_zero (padicValuationSubringToCompletedUnramifiedWittRing p))

/-- The linear coefficient of the completed multiplicative series is `p`. -/
theorem padicCompletedMultiplicativeSeries_coeff_one
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.coeff 1
        (padicCompletedMultiplicativeSeries p) =
      (p : padicCompletedUnramifiedWittRing p) := by
  rw [padicCompletedMultiplicativeSeries,
    PowerSeries.coeff_map]
  exact
    (congrArg (padicValuationSubringToCompletedUnramifiedWittRing p)
      (padicMultiplicativeLubinTateSeries p).coeff_one_eq_uniformizer).trans
      (padicValuationSubringToCompletedUnramifiedWittRing_uniformizer p)

theorem padicCompletedChangedStandardSeries_constantCoeff
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries.constantCoeff
        (padicCompletedChangedStandardSeries p u) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,
    padicCompletedChangedStandardSeries,
    PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    LubinTateSeries.constantCoeff_eq_zero,
    map_zero]

/-- The completed multiplicative Lubin--Tate series admits formal
substitution. -/
theorem padicCompletedMultiplicativeSeries_hasSubst
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.HasSubst (padicCompletedMultiplicativeSeries p) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (padicCompletedMultiplicativeSeries_constantCoeff p)

/-- The completed changed standard Lubin--Tate series admits formal
substitution. -/
theorem padicCompletedChangedStandardSeries_hasSubst
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries.HasSubst (padicCompletedChangedStandardSeries p u) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (padicCompletedChangedStandardSeries_constantCoeff p u)

/-- Reduction of the completed multiplicative series modulo `p` is `X ^ p`. -/
theorem padicCompletedMultiplicativeSeries_map_constantCoeff
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.map WittVector.constantCoeff
        (padicCompletedMultiplicativeSeries p) =
      (PowerSeries.X :
        PowerSeries (AlgebraicClosure (ZMod p))) ^ p := by
  let : CharP (PowerSeries (AlgebraicClosure (ZMod p))) p :=
    charP_of_injective_ringHom PowerSeries.C_injective p
  rw [padicCompletedMultiplicativeSeries_eq]
  simp only [map_sub, map_pow, map_add, map_one, PowerSeries.map_X]
  rw [add_pow_char]
  simp

/-- Reduction of the completed changed-standard series modulo `p` is
`X ^ p`. -/
theorem padicCompletedChangedStandardSeries_map_constantCoeff
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries.map WittVector.constantCoeff
        (padicCompletedChangedStandardSeries p u) =
      (PowerSeries.X :
        PowerSeries (AlgebraicClosure (ZMod p))) ^ p := by
  let : CharP (PowerSeries (AlgebraicClosure (ZMod p))) p :=
    charP_of_injective_ringHom PowerSeries.C_injective p
  rw [padicCompletedChangedStandardSeries_eq]
  simp only [map_add, map_mul, map_pow, PowerSeries.map_C,
    PowerSeries.map_X, map_natCast]
  rw [CharP.cast_eq_zero (PowerSeries (AlgebraicClosure (ZMod p))) p]
  simp

/-- Coefficientwise Witt-vector Frobenius preserves a zero constant
coefficient. -/
theorem padicChangedUniformizerFrobenius_constantCoeff_eq_zero
    (p : ℕ) [Fact p.Prime]
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hH : PowerSeries.constantCoeff H = 0) :
    PowerSeries.constantCoeff
        (PowerSeries.map WittVector.frobenius H) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    hH, map_zero]

end LubinTate

end
