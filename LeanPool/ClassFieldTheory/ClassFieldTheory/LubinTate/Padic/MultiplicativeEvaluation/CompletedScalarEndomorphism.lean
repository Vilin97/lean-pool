/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.CompletedCoefficientEvaluation
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.CompletedSeries
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.DefectCorrection
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.IntertwinerConstruction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.ScalarCompatibility
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.ScalarEndomorphisms
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeIntertwiner
/-!
# Completed standard and multiplicative scalar endomorphisms

This module extends the standard-to-multiplicative comparison and scalar
endomorphisms to the completed unramified Witt ring.  It proves the genuine
composition, torsion, and injectivity identities for their analytic actions.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open SameUniformizer

attribute [local instance 50]
  padicCompletedMultiplicativeWittUniformSpace

attribute [local instance]
  padicCompletedMultiplicativeTargetWithIdeal
  padicCompletedMultiplicativeTargetCompleteSpace
  padicCompletedMultiplicativeTargetT2Space

/-- The standard-to-multiplicative intertwiner after extending its
`ℚ_p`-integral coefficients to the completed unramified Witt ring. -/
noncomputable def padicCompletedStandardToMultiplicativeIntertwiner
    (p : ℕ) [Fact p.Prime] :
    PowerSeries (padicCompletedUnramifiedWittRing p) :=
  PowerSeries.map
    (padicValuationSubringToCompletedUnramifiedWittRing p)
    (padicStandardToMultiplicativeIntertwiner p)

/-- Witt Frobenius fixes the completed standard-to-multiplicative
intertwiner because all of its coefficients descend from the p-adic
valuation ring. -/
theorem padicCompletedStandardToMultiplicativeIntertwiner_frobenius
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.map WittVector.frobenius
        (padicCompletedStandardToMultiplicativeIntertwiner p) =
      padicCompletedStandardToMultiplicativeIntertwiner p := by
  apply PowerSeries.ext
  intro m
  simp [padicCompletedStandardToMultiplicativeIntertwiner,
    PowerSeries.coeff_map,
    padicValuationSubringToCompletedUnramifiedWittRing_frobenius]

/-- The completed standard-to-multiplicative intertwiner has zero constant
coefficient. -/
theorem padicCompletedStandardToMultiplicativeIntertwiner_constantCoeff
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.constantCoeff
        (padicCompletedStandardToMultiplicativeIntertwiner p) = 0 := by
  have hconstant :=
    (padicStandardToMultiplicativeIntertwiner_hasLinearTerm p).constantCoeff_eq_zero
  change
    padicValuationSubringToCompletedUnramifiedWittRing p
        (PowerSeries.constantCoeff
          (padicStandardToMultiplicativeIntertwiner p)) = 0
  rw [PowerSeries.constantCoeff_eq, hconstant, map_zero]

/-- The completed standard-to-multiplicative intertwiner admits formal
substitution and convergent evaluation at topologically nilpotent points. -/
theorem padicCompletedStandardToMultiplicativeIntertwiner_hasSubst
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.HasSubst
      (padicCompletedStandardToMultiplicativeIntertwiner p) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (padicCompletedStandardToMultiplicativeIntertwiner_constantCoeff p)

/-- Evaluation of the completed standard-to-multiplicative comparison is
injective on topologically nilpotent completed-level integers. -/
theorem padicCompletedStandardToMultiplicativeIntertwiner_eval_injective
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    {x y : (padicCompletedLevelCompleteDVF p n).valuationSubring}
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy :
      padicCompletedLevelPowerSeriesEval p n x hx
          (padicCompletedStandardToMultiplicativeIntertwiner p) =
        padicCompletedLevelPowerSeriesEval p n y hy
          (padicCompletedStandardToMultiplicativeIntertwiner p)) :
    x = y := by
  apply
    padicCompletedLevelPowerSeriesEval_injective_of_unitLinearCoefficient
      p n (padicCompletedStandardToMultiplicativeIntertwiner p)
      (padicCompletedStandardToMultiplicativeIntertwiner_constantCoeff p)
      ?_ hx hy hxy
  rw [padicCompletedStandardToMultiplicativeIntertwiner,
    PowerSeries.coeff_map,
    padicStandardToMultiplicativeIntertwiner_coeff_one,
    map_one]
  exact isUnit_one

/-- A standard p-adic Lubin--Tate scalar endomorphism after extending its
coefficients to the completed unramified Witt ring. -/
noncomputable def padicCompletedStandardScalarEndomorphism
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries (padicCompletedUnramifiedWittRing p) :=
  PowerSeries.map
    (padicValuationSubringToCompletedUnramifiedWittRing p)
    (standardLubinTateEndomorphism
      (padicMultiplicativeLubinTateSeries_isUniformizer p) a)

/-- Completed standard scalar endomorphisms have zero constant
coefficient. -/
theorem padicCompletedStandardScalarEndomorphism_constantCoeff
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.constantCoeff
        (padicCompletedStandardScalarEndomorphism p a) =
      0 := by
  have hconstant :=
    (standardLubinTateEndomorphism_hasLinearTerm
      (padicMultiplicativeLubinTateSeries_isUniformizer p) a
      ).constantCoeff_eq_zero
  change
    padicValuationSubringToCompletedUnramifiedWittRing p
        (PowerSeries.constantCoeff
          (standardLubinTateEndomorphism
            (padicMultiplicativeLubinTateSeries_isUniformizer p) a)) =
      0
  rw [PowerSeries.constantCoeff_eq, hconstant, map_zero]

/-- Completed standard scalar endomorphisms support formal substitution. -/
theorem padicCompletedStandardScalarEndomorphism_hasSubst
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.HasSubst
      (padicCompletedStandardScalarEndomorphism p a) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (padicCompletedStandardScalarEndomorphism_constantCoeff p a)

/-- Multiplication of standard p-adic scalars is composition after
completed coefficient extension. -/
theorem padicCompletedStandardScalarEndomorphism_mul
    (p : ℕ) [Fact p.Prime]
    (a b : (padicLocalField p).valuationSubring) :
    padicCompletedStandardScalarEndomorphism p (a * b) =
      PowerSeries.subst
        (padicCompletedStandardScalarEndomorphism p b)
        (padicCompletedStandardScalarEndomorphism p a) := by
  let f :=
    padicValuationSubringToCompletedUnramifiedWittRing p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let A := standardLubinTateEndomorphism hπ a
  let B := standardLubinTateEndomorphism hπ b
  calc
    padicCompletedStandardScalarEndomorphism p (a * b) =
        PowerSeries.map f (PowerSeries.subst B A) := by
      exact congrArg (PowerSeries.map f)
        (standardLubinTateEndomorphism_mul hπ a b)
    _ =
        PowerSeries.subst (PowerSeries.map f B)
          (PowerSeries.map f A) := by
      change
        MvPowerSeries.map f (PowerSeries.subst B A) =
          PowerSeries.subst (PowerSeries.map f B)
            (PowerSeries.map f A)
      exact
        PowerSeries.map_subst
          (standardLubinTateEndomorphism_hasLinearTerm hπ b
            ).hasSubst A
    _ =
        PowerSeries.subst
          (padicCompletedStandardScalarEndomorphism p b)
          (padicCompletedStandardScalarEndomorphism p a) := by
      rfl

/-- The completed standard-to-multiplicative comparison intertwines the
actual completed scalar endomorphisms. -/
theorem
    padicCompletedStandardToMultiplicativeIntertwiner_endomorphism
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.subst
        (padicCompletedStandardScalarEndomorphism p a)
        (padicCompletedStandardToMultiplicativeIntertwiner p) =
      PowerSeries.subst
        (padicCompletedStandardToMultiplicativeIntertwiner p)
        (padicCompletedMultiplicativeScalarEndomorphism p a) := by
  let f :=
    padicValuationSubringToCompletedUnramifiedWittRing p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let S := standardLubinTateEndomorphism hπ a
  let H := padicStandardToMultiplicativeIntertwiner p
  let M :=
    recursiveIntertwiner hπ
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeLubinTateSeries p)
      (fun _ : Unit => a)
  calc
    PowerSeries.subst
        (padicCompletedStandardScalarEndomorphism p a)
        (padicCompletedStandardToMultiplicativeIntertwiner p) =
        PowerSeries.map f (PowerSeries.subst S H) := by
      change
        PowerSeries.subst (PowerSeries.map f S)
            (PowerSeries.map f H) =
          PowerSeries.map f (PowerSeries.subst S H)
      symm
      change
        MvPowerSeries.map f (PowerSeries.subst S H) =
          PowerSeries.subst (PowerSeries.map f S)
            (PowerSeries.map f H)
      exact
        PowerSeries.map_subst
          (standardLubinTateEndomorphism_hasLinearTerm hπ a
            ).hasSubst H
    _ = PowerSeries.map f (PowerSeries.subst H M) := by
      rw [padicStandardToMultiplicativeIntertwiner_endomorphism]
    _ =
        PowerSeries.subst
          (padicCompletedStandardToMultiplicativeIntertwiner p)
          (padicCompletedMultiplicativeScalarEndomorphism p a) := by
      change
        MvPowerSeries.map f (PowerSeries.subst H M) =
          PowerSeries.subst (PowerSeries.map f H)
            (PowerSeries.map f M)
      exact
        PowerSeries.map_subst
          (padicStandardToMultiplicativeIntertwiner_hasSubst p) M

/-- Analytic action of a completed standard scalar endomorphism on a
topologically nilpotent point. -/
noncomputable def padicCompletedStandardScalarEndomorphismValue
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a : (padicLocalField p).valuationSubring) :
    (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  padicCompletedLevelPowerSeriesEval p n x hx
    (padicCompletedStandardScalarEndomorphism p a)

/-- A completed standard scalar value remains a convergent evaluation
point. -/
theorem padicCompletedStandardScalarEndomorphismValue_hasEval
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.HasEval
      (padicCompletedStandardScalarEndomorphismValue p n x hx a) :=
  padicCompletedLevelPowerSeriesEval_hasEval p n x hx
    (padicCompletedStandardScalarEndomorphism p a)
    (padicCompletedStandardScalarEndomorphism_hasSubst p a)

/-- Multiplication of standard scalars is composition of their completed
analytic actions. -/
theorem padicCompletedStandardScalarEndomorphismValue_mul
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a b : (padicLocalField p).valuationSubring) :
    padicCompletedStandardScalarEndomorphismValue p n x hx (a * b) =
      padicCompletedStandardScalarEndomorphismValue p n
        (padicCompletedStandardScalarEndomorphismValue p n x hx b)
        (padicCompletedStandardScalarEndomorphismValue_hasEval
          p n x hx b) a := by
  rw [padicCompletedStandardScalarEndomorphismValue,
    padicCompletedStandardScalarEndomorphism_mul]
  exact
    padicCompletedLevelPowerSeriesEval_subst p n x hx
      (padicCompletedStandardScalarEndomorphism p b)
      (padicCompletedStandardScalarEndomorphism p a)
      (padicCompletedStandardScalarEndomorphism_hasSubst p b)
      (padicCompletedStandardScalarEndomorphismValue_hasEval
        p n x hx b)

/-- The scalar `1` acts by the identity series after completed coefficient
extension. -/
@[simp]
theorem padicCompletedStandardScalarEndomorphism_one
    (p : ℕ) [Fact p.Prime] :
    padicCompletedStandardScalarEndomorphism p 1 =
      PowerSeries.X := by
  exact (congrArg
    (PowerSeries.map (padicValuationSubringToCompletedUnramifiedWittRing p))
    (standardLubinTateEndomorphism_one
      (padicMultiplicativeLubinTateSeries_isUniformizer p))).trans
    (PowerSeries.map_X _)

/-- The standard uniformizer acts by the defining standard Lubin--Tate
series after completed coefficient extension. -/
theorem padicCompletedStandardScalarEndomorphism_uniformizer
    (p : ℕ) [Fact p.Prime] :
    padicCompletedStandardScalarEndomorphism p
        (padicIntEquivValuationSubring p (p : ℤ_[p])) =
      PowerSeries.map
        (padicValuationSubringToCompletedUnramifiedWittRing p)
        (standardLubinTateSeries
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          ).toPowerSeries := by
  exact congrArg
    (PowerSeries.map (padicValuationSubringToCompletedUnramifiedWittRing p))
    (SameUniformizer.standardLubinTateEndomorphism_uniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p))

/-- The completed analytic action of scalar `1` fixes its input. -/
@[simp]
theorem padicCompletedStandardScalarEndomorphismValue_one
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    padicCompletedStandardScalarEndomorphismValue p n x hx 1 =
      x := by
  rw [padicCompletedStandardScalarEndomorphismValue,
    padicCompletedStandardScalarEndomorphism_one,
    padicCompletedLevelPowerSeriesEval_X]

/-- Every completed standard scalar endomorphism fixes the zero point. -/
theorem padicCompletedStandardScalarEndomorphismValue_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : (padicLocalField p).valuationSubring) :
    padicCompletedStandardScalarEndomorphismValue p n
        0 PowerSeries.HasEval.zero a =
      0 := by
  obtain ⟨B, hB⟩ :
      (PowerSeries.X :
          PowerSeries (padicCompletedUnramifiedWittRing p)) ∣
        padicCompletedStandardScalarEndomorphism p a := by
    rw [PowerSeries.X_dvd_iff]
    exact padicCompletedStandardScalarEndomorphism_constantCoeff p a
  rw [padicCompletedStandardScalarEndomorphismValue,
    hB, map_mul, padicCompletedLevelPowerSeriesEval_X, zero_mul]

/-- Evaluating a coefficient-extended polynomial as a completed power
series agrees with integral polynomial evaluation. -/
theorem padicCompletedLevelPowerSeriesEval_map_polynomial
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (P : Polynomial (padicLocalField p).valuationSubring) :
    padicCompletedLevelPowerSeriesEval p n x hx
        (PowerSeries.map
          (padicValuationSubringToCompletedUnramifiedWittRing p)
          (P : PowerSeries (padicLocalField p).valuationSubring)) =
      Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x P := by
  rw [← Polynomial.polynomial_map_coe,
    padicCompletedLevelPowerSeriesEval_coe,
    Polynomial.eval₂_map]
  rfl

/-- Evaluating the scalar `π ^ r` on any completed-level nilpotent point
is evaluation of the `r`-fold standard division-polynomial iterate. -/
theorem padicCompletedStandardScalarEndomorphismValue_uniformizer_pow
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) (r : ℕ) :
    padicCompletedStandardScalarEndomorphismValue p n x hx
        ((padicIntEquivValuationSubring p (p : ℤ_[p])) ^ r) =
      Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) r) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  change
    padicCompletedStandardScalarEndomorphismValue p n x hx (π ^ r) =
      Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x
        (standardLubinTatePolynomialIterate
          (padicLocalField p) π r)
  induction r with
  | zero =>
      rw [pow_zero,
        padicCompletedStandardScalarEndomorphismValue_one,
        standardLubinTatePolynomialIterate_zero,
        Polynomial.eval₂_X]
  | succ r ih =>
      rw [pow_succ',
        padicCompletedStandardScalarEndomorphismValue_mul]
      rw [padicCompletedStandardScalarEndomorphismValue,
        padicCompletedStandardScalarEndomorphism_uniformizer,
        ← standardLubinTatePolynomial_toPowerSeries_eq_series hπ,
        padicCompletedLevelPowerSeriesEval_map_polynomial,
        ih,
        standardLubinTatePolynomialIterate_succ,
        Polynomial.eval₂_comp]

/-- Analytic action of a completed multiplicative scalar endomorphism. -/
noncomputable def padicCompletedMultiplicativeScalarEndomorphismValue
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a : (padicLocalField p).valuationSubring) :
    (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  padicCompletedLevelPowerSeriesEval p n x hx
    (padicCompletedMultiplicativeScalarEndomorphism p a)

/-- A completed multiplicative scalar value remains a convergent
evaluation point. -/
theorem padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.HasEval
      (padicCompletedMultiplicativeScalarEndomorphismValue
        p n x hx a) :=
  padicCompletedLevelPowerSeriesEval_hasEval p n x hx
    (padicCompletedMultiplicativeScalarEndomorphism p a)
    (padicCompletedMultiplicativeScalarEndomorphism_hasSubst p a)

/-- Multiplication of multiplicative scalars is composition of their
completed analytic actions. -/
theorem padicCompletedMultiplicativeScalarEndomorphismValue_mul
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a b : (padicLocalField p).valuationSubring) :
    padicCompletedMultiplicativeScalarEndomorphismValue
        p n x hx (a * b) =
      padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativeScalarEndomorphismValue
          p n x hx b)
        (padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
          p n x hx b) a := by
  rw [padicCompletedMultiplicativeScalarEndomorphismValue,
    padicCompletedMultiplicativeScalarEndomorphism_mul]
  exact
    padicCompletedLevelPowerSeriesEval_subst p n x hx
      (padicCompletedMultiplicativeScalarEndomorphism p b)
      (padicCompletedMultiplicativeScalarEndomorphism p a)
      (padicCompletedMultiplicativeScalarEndomorphism_hasSubst p b)
      (padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
        p n x hx b)

/-- Every completed multiplicative scalar endomorphism fixes the zero
point. -/
theorem padicCompletedMultiplicativeScalarEndomorphismValue_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : (padicLocalField p).valuationSubring) :
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        0 PowerSeries.HasEval.zero a =
      0 := by
  obtain ⟨B, hB⟩ :
      (PowerSeries.X :
          PowerSeries (padicCompletedUnramifiedWittRing p)) ∣
        padicCompletedMultiplicativeScalarEndomorphism p a := by
    rw [PowerSeries.X_dvd_iff]
    exact
      padicCompletedMultiplicativeScalarEndomorphism_constantCoeff p a
  rw [padicCompletedMultiplicativeScalarEndomorphismValue,
    hB, map_mul, padicCompletedLevelPowerSeriesEval_X, zero_mul]

/-- A p-adic unit scalar acts injectively on all topologically nilpotent
completed-level integers. -/
theorem
    padicCompletedMultiplicativeScalarEndomorphismValue_unit_injective
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    {x y : (padicCompletedLevelCompleteDVF p n).valuationSubring}
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy :
      padicCompletedMultiplicativeScalarEndomorphismValue p n x hx
          (u : (padicLocalField p).valuationSubring) =
        padicCompletedMultiplicativeScalarEndomorphismValue p n y hy
          (u : (padicLocalField p).valuationSubring)) :
    x = y := by
  apply
    padicCompletedLevelPowerSeriesEval_injective_of_unitLinearCoefficient
      p n
      (padicCompletedMultiplicativeScalarEndomorphism p
        (u : (padicLocalField p).valuationSubring))
      (padicCompletedMultiplicativeScalarEndomorphism_constantCoeff p
        (u : (padicLocalField p).valuationSubring))
      ?_ hx hy hxy
  rw [padicCompletedMultiplicativeScalarEndomorphism_coeff_one]
  change IsUnit
    (((padicValuationUnitToCompletedUnramifiedWittUnit p u :
      (padicCompletedUnramifiedWittRing p)ˣ) :
        padicCompletedUnramifiedWittRing p))
  exact (padicValuationUnitToCompletedUnramifiedWittUnit p u).isUnit

/-- The scalar-one completed multiplicative endomorphism fixes every
topologically nilpotent completed-level integer. -/
@[simp]
theorem padicCompletedMultiplicativeScalarEndomorphismValue_one
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    padicCompletedMultiplicativeScalarEndomorphismValue p n x hx 1 =
      x := by
  apply
    padicCompletedMultiplicativeScalarEndomorphismValue_unit_injective
      p n (1 : (padicLocalField p).valuationSubringˣ)
      (padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
        p n x hx 1) hx
  simpa only [Units.val_one, one_mul] using
    (padicCompletedMultiplicativeScalarEndomorphismValue_mul
      p n x hx
        (1 : (padicLocalField p).valuationSubring)
        (1 : (padicLocalField p).valuationSubring)).symm

/-- Acting first by the inverse of a p-adic unit and then by the unit
itself recovers every topologically nilpotent completed-level integer. -/
theorem
    padicCompletedMultiplicativeScalarEndomorphismValue_unit_after_inverse
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativeScalarEndomorphismValue p n x hx
          ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
            (padicLocalField p).valuationSubring))
        (padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
          p n x hx
          ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
            (padicLocalField p).valuationSubring))
        (u : (padicLocalField p).valuationSubring) =
      x := by
  calc
    _ =
        padicCompletedMultiplicativeScalarEndomorphismValue p n x hx
          ((u : (padicLocalField p).valuationSubring) *
            ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
              (padicLocalField p).valuationSubring)) :=
      (padicCompletedMultiplicativeScalarEndomorphismValue_mul
        p n x hx
          (u : (padicLocalField p).valuationSubring)
          ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
            (padicLocalField p).valuationSubring)).symm
    _ = x := by
      rw [show
        (u : (padicLocalField p).valuationSubring) *
            ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
              (padicLocalField p).valuationSubring) = 1 by
          simp,
        padicCompletedMultiplicativeScalarEndomorphismValue_one]

/-- Completed analytic evaluation of the standard-to-multiplicative
comparison carries every standard scalar action to the actual
multiplicative scalar action. -/
theorem
    padicCompletedStandardToMultiplicativeIntertwiner_eval_endomorphism
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a : (padicLocalField p).valuationSubring) :
    padicCompletedLevelPowerSeriesEval p n
        (padicCompletedStandardScalarEndomorphismValue p n x hx a)
        (padicCompletedStandardScalarEndomorphismValue_hasEval
          p n x hx a)
        (padicCompletedStandardToMultiplicativeIntertwiner p) =
      padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedLevelPowerSeriesEval p n x hx
          (padicCompletedStandardToMultiplicativeIntertwiner p))
        (padicCompletedLevelPowerSeriesEval_hasEval p n x hx
          (padicCompletedStandardToMultiplicativeIntertwiner p)
          (padicCompletedStandardToMultiplicativeIntertwiner_hasSubst p))
        a := by
  let S := padicCompletedStandardScalarEndomorphism p a
  let H := padicCompletedStandardToMultiplicativeIntertwiner p
  let M := padicCompletedMultiplicativeScalarEndomorphism p a
  let xS := padicCompletedStandardScalarEndomorphismValue p n x hx a
  let xH := padicCompletedLevelPowerSeriesEval p n x hx H
  let hxS : PowerSeries.HasEval xS :=
    padicCompletedStandardScalarEndomorphismValue_hasEval p n x hx a
  let hxH : PowerSeries.HasEval xH :=
    padicCompletedLevelPowerSeriesEval_hasEval p n x hx H
      (padicCompletedStandardToMultiplicativeIntertwiner_hasSubst p)
  calc
    padicCompletedLevelPowerSeriesEval p n xS hxS H =
        padicCompletedLevelPowerSeriesEval p n x hx
          (PowerSeries.subst S H) := by
      exact
        (padicCompletedLevelPowerSeriesEval_subst p n x hx
          S H (padicCompletedStandardScalarEndomorphism_hasSubst p a)
          hxS).symm
    _ =
        padicCompletedLevelPowerSeriesEval p n x hx
          (PowerSeries.subst H M) := by
      rw [
        padicCompletedStandardToMultiplicativeIntertwiner_endomorphism]
    _ =
        padicCompletedLevelPowerSeriesEval p n xH hxH M := by
      exact
        padicCompletedLevelPowerSeriesEval_subst p n x hx
          H M
          (padicCompletedStandardToMultiplicativeIntertwiner_hasSubst p)
          hxH

/-- A p-adic unit scalar acts injectively through the completed standard
Lubin--Tate endomorphism on all topologically nilpotent completed-level
integers. -/
theorem
    padicCompletedStandardScalarEndomorphismValue_unit_injective
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    {x y : (padicCompletedLevelCompleteDVF p n).valuationSubring}
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy :
      padicCompletedStandardScalarEndomorphismValue p n x hx
          (u : (padicLocalField p).valuationSubring) =
        padicCompletedStandardScalarEndomorphismValue p n y hy
          (u : (padicLocalField p).valuationSubring)) :
    x = y := by
  let H := padicCompletedStandardToMultiplicativeIntertwiner p
  let xH := padicCompletedLevelPowerSeriesEval p n x hx H
  let yH := padicCompletedLevelPowerSeriesEval p n y hy H
  let hxH : PowerSeries.HasEval xH :=
    padicCompletedLevelPowerSeriesEval_hasEval p n x hx H
      (padicCompletedStandardToMultiplicativeIntertwiner_hasSubst p)
  let hyH : PowerSeries.HasEval yH :=
    padicCompletedLevelPowerSeriesEval_hasEval p n y hy H
      (padicCompletedStandardToMultiplicativeIntertwiner_hasSubst p)
  have hmult :
      padicCompletedMultiplicativeScalarEndomorphismValue p n xH hxH
          (u : (padicLocalField p).valuationSubring) =
        padicCompletedMultiplicativeScalarEndomorphismValue p n yH hyH
          (u : (padicLocalField p).valuationSubring) := by
    calc
      _ =
          padicCompletedLevelPowerSeriesEval p n
            (padicCompletedStandardScalarEndomorphismValue
              p n x hx (u : (padicLocalField p).valuationSubring))
            (padicCompletedStandardScalarEndomorphismValue_hasEval
              p n x hx (u : (padicLocalField p).valuationSubring))
            H := by
        symm
        exact
          padicCompletedStandardToMultiplicativeIntertwiner_eval_endomorphism
            p n x hx (u : (padicLocalField p).valuationSubring)
      _ =
          padicCompletedLevelPowerSeriesEval p n
            (padicCompletedStandardScalarEndomorphismValue
              p n y hy (u : (padicLocalField p).valuationSubring))
            (padicCompletedStandardScalarEndomorphismValue_hasEval
              p n y hy (u : (padicLocalField p).valuationSubring))
            H := by
        exact
          padicCompletedLevelPowerSeriesEval_congr_point p n
            (padicCompletedStandardScalarEndomorphismValue_hasEval
              p n x hx (u : (padicLocalField p).valuationSubring))
            (padicCompletedStandardScalarEndomorphismValue_hasEval
              p n y hy (u : (padicLocalField p).valuationSubring))
            hxy H
      _ =
          padicCompletedMultiplicativeScalarEndomorphismValue p n yH hyH
            (u : (padicLocalField p).valuationSubring) :=
        padicCompletedStandardToMultiplicativeIntertwiner_eval_endomorphism
          p n y hy (u : (padicLocalField p).valuationSubring)
  have hH : xH = yH := by
    exact
      padicCompletedMultiplicativeScalarEndomorphismValue_unit_injective
        p n u hxH hyH hmult
  exact
    padicCompletedStandardToMultiplicativeIntertwiner_eval_injective
      p n hx hy hH

/-- The completed standard-to-multiplicative comparison evaluates to zero
at the zero point. -/
theorem padicCompletedStandardToMultiplicativeIntertwiner_eval_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicCompletedLevelPowerSeriesEval p n
        0 PowerSeries.HasEval.zero
        (padicCompletedStandardToMultiplicativeIntertwiner p) =
      0 := by
  obtain ⟨B, hB⟩ :
      (PowerSeries.X :
          PowerSeries (padicCompletedUnramifiedWittRing p)) ∣
        padicCompletedStandardToMultiplicativeIntertwiner p := by
    rw [PowerSeries.X_dvd_iff]
    exact
      padicCompletedStandardToMultiplicativeIntertwiner_constantCoeff p
  rw [hB, map_mul,
    padicCompletedLevelPowerSeriesEval_X, zero_mul]

end LubinTate

end
