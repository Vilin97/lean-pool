/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.Series
import Mathlib.RingTheory.PowerSeries.Binomial
/-!
# The multiplicative Lubin--Tate series over `ℚ_p`

Mathlib's binomial series at the natural exponent `p` is

`(1 + X) ^ p`.

After subtracting `1`, this has zero constant coefficient, linear
coefficient `p`, and reduction `X ^ p`.  Thus it is the Lubin--Tate series
attached to the multiplicative formal group and the canonical prime
uniformizer of `ℚ_p`.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

/-- The multiplicative Lubin--Tate series `(1 + X) ^ p - 1` over `ℚ_p`,
represented by mathlib's binomial series. -/
noncomputable def padicMultiplicativeLubinTateSeries
    (p : ℕ) [Fact p.Prime] :
    LubinTateSeries (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) where
  toPowerSeries :=
    PowerSeries.binomialSeries
        (padicLocalField p).valuationSubring (p : ℤ) -
      1
  constantCoeff_eq_zero := by
    simp
  coeff_one_eq_uniformizer := by
    have hcoeff : PowerSeries.coeff 1
        (PowerSeries.binomialSeries
            (padicLocalField p).valuationSubring (p : ℤ) - 1) =
        (p : (padicLocalField p).valuationSubring) := by
      simp only [PowerSeries.binomialSeries_nat, map_sub,
        PowerSeries.coeff_one]
      rw [PowerSeries.coeff_one_pow]
      simp
    exact hcoeff.trans (map_natCast (padicIntEquivValuationSubring p) p).symm
  map_residue_eq_frobenius := by
    let eO : ℤ_[p] ≃+*
        (padicDVRValuation p).valuationSubring :=
      padicIntEquivValuationSubring p
    let eRes :
        (padicLocalField p).residueField ≃+* ZMod p := by
      change
        IsLocalRing.ResidueField
            (padicDVRValuation p).valuationSubring ≃+*
          ZMod p
      exact
        (IsLocalRing.ResidueField.mapEquiv eO).symm.trans
          (padicIntResidueFieldEquivZMod p)
    let : CharP (padicLocalField p).residueField p :=
      charP_of_injective_ringHom
        (f := eRes.symm.toRingHom) eRes.symm.injective p
    let : CharP (PowerSeries (padicLocalField p).residueField) p :=
      CharP.of_ringHom_of_ne_zero
        PowerSeries.C p ((Fact.out : p.Prime).ne_zero)
    have hcard :
        Nat.card (padicLocalField p).residueField = p := by
      simpa [padicLocalField] using
        padicCompleteDVF_residueField_card p
    rw [hcard, PowerSeries.binomialSeries_nat (R := ℤ)]
    simp only [map_sub, map_pow, map_add, map_one, PowerSeries.map_X]
    rw [add_pow_char]
    simp

namespace LubinTateSeries

/-- The underlying series is literally mathlib's binomial series minus one. -/
@[simp]
theorem padicMultiplicativeLubinTateSeries_toPowerSeries
    (p : ℕ) [Fact p.Prime] :
    (padicMultiplicativeLubinTateSeries p).toPowerSeries =
      PowerSeries.binomialSeries
          (padicLocalField p).valuationSubring (p : ℤ) -
        1 :=
  rfl

end LubinTateSeries

/-- The prime occurring as the linear coefficient of the multiplicative
Lubin--Tate series is a uniformizer for the chosen valuation on `ℚ_p`. -/
theorem padicMultiplicativeLubinTateSeries_isUniformizer
    (p : ℕ) [Fact p.Prime] :
    (padicLocalField p).toCompleteDVF.valuation.IsUniformizer
      ((padicIntEquivValuationSubring p (p : ℤ_[p]) :
          (padicLocalField p).valuationSubring) : ℚ_[p]) := by
  change
    (padicDVRValuation p).IsUniformizer
      ((padicIntEquivValuationSubring p (p : ℤ_[p]) :
          (padicDVRValuation p).valuationSubring) : ℚ_[p])
  simpa using padicDVRValuation_isUniformizer_p p

end LubinTate

end
