/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ZetaNumeratorSpectral
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown

namespace BGS.HasseWeil

open Polynomial
open scoped BigOperators PowerSeries

noncomputable section

def negativeXLogDerivative (f : PowerSeries ℂ) : PowerSeries ℂ :=
  -PowerSeries.X * PowerSeries.derivative (R := ℂ) f * f⁻¹

def linearPowerSeriesFactor (a : ℂ) : PowerSeries ℂ :=
  1 - PowerSeries.C a * PowerSeries.X

@[simp] theorem constantCoeff_linearPowerSeriesFactor (a : ℂ) :
    PowerSeries.constantCoeff (linearPowerSeriesFactor a) = 1 := by
  simp [linearPowerSeriesFactor]

theorem linearPowerSeriesFactor_inv (a : ℂ) :
    (linearPowerSeriesFactor a)⁻¹ =
      PowerSeries.rescale a (PowerSeries.mk 1) := by
  apply (PowerSeries.inv_eq_iff_mul_eq_one (by simp)).2
  have h := congrArg (PowerSeries.rescale a)
    (PowerSeries.mk_one_mul_one_sub_eq_one ℂ)
  simpa [linearPowerSeriesFactor, mul_comm] using h

theorem derivative_linearPowerSeriesFactor (a : ℂ) :
    PowerSeries.derivative (R := ℂ) (linearPowerSeriesFactor a) = -PowerSeries.C a := by
  change PowerSeries.derivativeFun (linearPowerSeriesFactor a) = -PowerSeries.C a
  rw [linearPowerSeriesFactor, sub_eq_add_neg]
  rw [show -(PowerSeries.C a * PowerSeries.X) =
      (-1 : ℂ) • (PowerSeries.C a * PowerSeries.X) by simp]
  rw [PowerSeries.derivativeFun_add, PowerSeries.derivativeFun_one,
    PowerSeries.derivativeFun_smul, PowerSeries.derivativeFun_mul]
  have hX : PowerSeries.derivativeFun (PowerSeries.X : PowerSeries ℂ) = 1 :=
    PowerSeries.derivative_X
  have hC : PowerSeries.derivativeFun (PowerSeries.C a) = 0 :=
    PowerSeries.derivative_C
  rw [hX, hC]
  simp

@[simp] theorem coeff_negativeXLogDerivative_linearPowerSeriesFactor
    (a : ℂ) (n : ℕ) :
    PowerSeries.coeff (n + 1)
      (negativeXLogDerivative (linearPowerSeriesFactor a)) = a ^ (n + 1) := by
  rw [negativeXLogDerivative, linearPowerSeriesFactor_inv]
  rw [derivative_linearPowerSeriesFactor]
  simp only [neg_mul_neg]
  rw [mul_assoc, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, PowerSeries.coeff_mk]
  simp [pow_succ, mul_comm]

theorem inverse_mul_of_constantCoeff_ne_zero
    (f g : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f ≠ 0)
    (hg : PowerSeries.constantCoeff g ≠ 0) :
    (f * g)⁻¹ = f⁻¹ * g⁻¹ := by
  apply (PowerSeries.inv_eq_iff_mul_eq_one (by simpa using mul_ne_zero hf hg)).2
  calc
    (f⁻¹ * g⁻¹) * (f * g) = (f⁻¹ * f) * (g⁻¹ * g) := by ring
    _ = 1 := by rw [PowerSeries.inv_mul_cancel f hf,
      PowerSeries.inv_mul_cancel g hg, one_mul]

theorem negativeXLogDerivative_mul
    (f g : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f ≠ 0)
    (hg : PowerSeries.constantCoeff g ≠ 0) :
    negativeXLogDerivative (f * g) =
      negativeXLogDerivative f + negativeXLogDerivative g := by
  unfold negativeXLogDerivative
  change -PowerSeries.X * PowerSeries.derivativeFun (f * g) * (f * g)⁻¹ =
    -PowerSeries.X * PowerSeries.derivativeFun f * f⁻¹ +
      -PowerSeries.X * PowerSeries.derivativeFun g * g⁻¹
  rw [PowerSeries.derivativeFun_mul,
    inverse_mul_of_constantCoeff_ne_zero f g hf hg]
  simp only [smul_eq_mul]
  calc
    -PowerSeries.X * (f * PowerSeries.derivativeFun g +
        g * PowerSeries.derivativeFun f) * (f⁻¹ * g⁻¹) =
      (-PowerSeries.X * PowerSeries.derivativeFun g * g⁻¹) * (f * f⁻¹) +
        (-PowerSeries.X * PowerSeries.derivativeFun f * f⁻¹) * (g * g⁻¹) := by ring
    _ = -PowerSeries.X * PowerSeries.derivativeFun f * f⁻¹ +
        -PowerSeries.X * PowerSeries.derivativeFun g * g⁻¹ := by
      rw [PowerSeries.mul_inv_cancel f hf, PowerSeries.mul_inv_cancel g hg]
      ring

theorem negativeXLogDerivative_prod_linearPowerSeriesFactor
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℂ) :
    negativeXLogDerivative (∏ i, linearPowerSeriesFactor (a i)) =
      ∑ i, negativeXLogDerivative (linearPowerSeriesFactor (a i)) := by
  classical
  refine Finset.induction_on (Finset.univ : Finset I) ?_ ?_
  · simp [negativeXLogDerivative]
  · intro i s hi hs
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      negativeXLogDerivative_mul]
    · rw [hs]
    · simp
    · simp

theorem coeff_negativeXLogDerivative_prod_linearPowerSeriesFactor
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℂ) (n : ℕ) :
    PowerSeries.coeff (n + 1)
      (negativeXLogDerivative (∏ i, linearPowerSeriesFactor (a i))) =
        ∑ i, a i ^ (n + 1) := by
  rw [negativeXLogDerivative_prod_linearPowerSeriesFactor]
  simp

/-- The formal series whose coefficient at `n` is the point count over the
extension of degree `n + 1`. -/
def pointCountDerivativeSeries (pointCount : ℕ → ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (pointCount (n + 1) : ℂ)

/-- Euler's logarithmic-derivative identity for a point-count zeta series. -/
def HasFormalZetaPointCountDerivative
    (Z : PowerSeries ℂ) (pointCount : ℕ → ℕ) : Prop :=
  PowerSeries.derivative (R := ℂ) Z = Z * pointCountDerivativeSeries pointCount

/-- The formal logarithm `∑ₙ Nₙ Tⁿ/n` attached to extension point counts. -/
def pointCountLogSeries (pointCount : ℕ → ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else (pointCount n : ℂ) / (n : ℂ)

@[simp] theorem constantCoeff_pointCountLogSeries (pointCount : ℕ → ℕ) :
    PowerSeries.constantCoeff (pointCountLogSeries pointCount) = 0 := by
  simp [pointCountLogSeries]

theorem pointCountLogSeries_hasSubst (pointCount : ℕ → ℕ) :
    PowerSeries.HasSubst (pointCountLogSeries pointCount) :=
  PowerSeries.HasSubst.of_constantCoeff_zero
    (constantCoeff_pointCountLogSeries pointCount)

/-- The formal exponential definition
`exp(∑ₙ Nₙ Tⁿ/n)` of the point-count zeta series. -/
def formalPointCountZeta (pointCount : ℕ → ℕ) : PowerSeries ℂ :=
  (PowerSeries.exp ℂ).subst (pointCountLogSeries pointCount)

theorem derivative_pointCountLogSeries (pointCount : ℕ → ℕ) :
    PowerSeries.derivative (R := ℂ) (pointCountLogSeries pointCount) =
      pointCountDerivativeSeries pointCount := by
  ext n
  rw [PowerSeries.coeff_derivative]
  simp [pointCountLogSeries, pointCountDerivativeSeries,
    Nat.cast_add, Nat.cast_one]
  field_simp

theorem formalPointCountZeta_hasPointCountDerivative
    (pointCount : ℕ → ℕ) :
    HasFormalZetaPointCountDerivative
      (formalPointCountZeta pointCount) pointCount := by
  rw [HasFormalZetaPointCountDerivative, formalPointCountZeta,
    PowerSeries.derivative_subst (pointCountLogSeries_hasSubst pointCount),
    PowerSeries.derivative_exp, derivative_pointCountLogSeries]

/-- The denominator `(1 - T)(1 - qT)` of the zeta function of a curve over
the field with `q` elements. -/
def curveZetaDenominator (q : ℕ) : PowerSeries ℂ :=
  linearPowerSeriesFactor 1 * linearPowerSeriesFactor (q : ℂ)

@[simp] theorem constantCoeff_curveZetaDenominator (q : ℕ) :
    PowerSeries.constantCoeff (curveZetaDenominator q) = 1 := by
  simp [curveZetaDenominator]

/-- Rationality in the normalized curve form. -/
def HasCurveZetaRationalForm
    (Z : PowerSeries ℂ) (q : ℕ) (P : Polynomial ℂ) : Prop :=
  Z * curveZetaDenominator q = (P : PowerSeries ℂ)

theorem coeff_negativeXLogDerivative_polynomial
    (P : Polynomial ℂ) (hP0 : P.coeff 0 = 1) (n : ℕ) :
    PowerSeries.coeff (n + 1)
      (negativeXLogDerivative (P : PowerSeries ℂ)) =
        ∑ i, reciprocalRootParameter P i ^ (n + 1) := by
  let a : Fin P.natDegree → ℂ := reciprocalRootParameter P
  have hfactor : P = ∏ i, (1 - Polynomial.C (a i) * Polynomial.X) := by
    simpa only [a] using polynomial_eq_prod_reciprocalRootParameter P hP0
  have hfactorSeries :=
    congrArg (Polynomial.coeToPowerSeries.ringHom :
      Polynomial ℂ →+* PowerSeries ℂ) hfactor
  have hseries :
      (P : PowerSeries ℂ) =
        ∏ i, linearPowerSeriesFactor (a i) := by
    simpa [linearPowerSeriesFactor] using hfactorSeries
  rw [hseries]
  simpa only [a] using
    coeff_negativeXLogDerivative_prod_linearPowerSeriesFactor a n

theorem coeff_negativeXLogDerivative_curveZetaDenominator
    (q n : ℕ) :
    PowerSeries.coeff (n + 1)
      (negativeXLogDerivative (curveZetaDenominator q)) =
        1 + (q : ℂ) ^ (n + 1) := by
  rw [curveZetaDenominator,
    negativeXLogDerivative_mul _ _ (by simp) (by simp), map_add]
  rw [coeff_negativeXLogDerivative_linearPowerSeriesFactor,
    coeff_negativeXLogDerivative_linearPowerSeriesFactor]
  simp

theorem coeff_negativeXLogDerivative_of_pointCountDerivative
    (Z : PowerSeries ℂ) (pointCount : ℕ → ℕ)
    (hZ0 : PowerSeries.constantCoeff Z = 1)
    (htrace : HasFormalZetaPointCountDerivative Z pointCount)
    (n : ℕ) :
    PowerSeries.coeff (n + 1) (negativeXLogDerivative Z) =
      -(pointCount (n + 1) : ℂ) := by
  have hZne : PowerSeries.constantCoeff Z ≠ 0 := by simp [hZ0]
  have hcancel := PowerSeries.mul_inv_cancel Z hZne
  have hseries :
      negativeXLogDerivative Z =
        -PowerSeries.X * pointCountDerivativeSeries pointCount := by
    rw [negativeXLogDerivative, htrace]
    calc
      -PowerSeries.X *
          (Z * pointCountDerivativeSeries pointCount) * Z⁻¹ =
          (-PowerSeries.X * pointCountDerivativeSeries pointCount) * (Z * Z⁻¹) := by
            ring
      _ = -PowerSeries.X * pointCountDerivativeSeries pointCount := by
        rw [hcancel, mul_one]
  rw [hseries]
  simp [pointCountDerivativeSeries]

/-- A normalized rational zeta series satisfying Euler's derivative identity
produces the reciprocal-root extension point-count formula. -/
theorem hasZetaNumeratorPointCountFormula_of_formalZeta
    (q : ℕ) (pointCount : ℕ → ℕ)
    (Z : PowerSeries ℂ) (P : Polynomial ℂ)
    (hP0 : P.coeff 0 = 1)
    (htrace : HasFormalZetaPointCountDerivative Z pointCount)
    (hrational : HasCurveZetaRationalForm Z q P) :
    HasZetaNumeratorPointCountFormula q pointCount P := by
  have hZ0 : PowerSeries.constantCoeff Z = 1 := by
    have h := congrArg PowerSeries.constantCoeff hrational
    simpa [HasCurveZetaRationalForm, hP0] using h
  have hZne : PowerSeries.constantCoeff Z ≠ 0 := by simp [hZ0]
  have hDne : PowerSeries.constantCoeff (curveZetaDenominator q) ≠ 0 := by simp
  have hlog :
      negativeXLogDerivative Z +
          negativeXLogDerivative (curveZetaDenominator q) =
        negativeXLogDerivative (P : PowerSeries ℂ) := by
    rw [← negativeXLogDerivative_mul Z (curveZetaDenominator q) hZne hDne]
    exact congrArg negativeXLogDerivative hrational
  refine ⟨hP0, ?_⟩
  intro m hm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hcoeff := congrArg (PowerSeries.coeff (n + 1)) hlog
  rw [map_add,
    coeff_negativeXLogDerivative_of_pointCountDerivative Z pointCount hZ0 htrace,
    coeff_negativeXLogDerivative_curveZetaDenominator,
    coeff_negativeXLogDerivative_polynomial P hP0] at hcoeff
  rw [← sum_reciprocalRootParameter_pow]
  simp only [pow_succ] at hcoeff ⊢
  linear_combination -hcoeff

/-- For the canonical exponential point-count zeta series, rationality in
curve form is the only remaining premise needed for the numerator trace
formula. -/
theorem hasZetaNumeratorPointCountFormula_of_formalPointCountZeta_rational
    (q : ℕ) (pointCount : ℕ → ℕ) (P : Polynomial ℂ)
    (hP0 : P.coeff 0 = 1)
    (hrational :
      HasCurveZetaRationalForm (formalPointCountZeta pointCount) q P) :
    HasZetaNumeratorPointCountFormula q pointCount P :=
  hasZetaNumeratorPointCountFormula_of_formalZeta q pointCount
    (formalPointCountZeta pointCount) P hP0
    (formalPointCountZeta_hasPointCountDerivative pointCount) hrational

end

end BGS.HasseWeil
