/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderSobolev
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SpatialSobolevInverse
import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedWeakDerivative
import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet
import Mathlib.Algebra.Order.Star.Real

import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Dissipation of the genuine cylinder Laplacian in a variable positive metric. -/

@[expose] public section


noncomputable section

namespace EulerMetricHeatEnergy

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerLiftedWeakDerivative EulerLiftedPressure
  EulerPressureSpatialRegularity EulerSpatialSobolevInverse EulerCylinderSobolev
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual multiplier by a directional derivative of a smooth metric coefficient. -/
def directionalCoefficientOperator (K : SmoothCoefficient period) (a : LiftTangent) :
    LiftL2 period →L[ℝ] LiftL2 period :=
  coefficientOperator (translatedCoefficientDerivative period a K.coefficient 0)
    (translatedCoefficientDerivative_measurable period a K.coefficient K.smooth)
    (K.firstBound * ‖a‖₊)
    (fun x => translatedCoefficientDerivative_bound period a K.coefficient K.firstBound
        K.norm_first x)

/-- The directional coefficient multiplier has the expected first-derivative norm bound. -/
theorem directionalCoefficientOperator_bound (K : SmoothCoefficient period) (a : LiftTangent)
    (f : LiftL2 period) :
    ‖directionalCoefficientOperator period K a f‖ ≤ (K.firstBound : ℝ) * ‖a‖ * ‖f‖ := by
  have h := coefficientOperator_norm_le (translatedCoefficientDerivative period a K.coefficient 0)
    (translatedCoefficientDerivative_measurable period a K.coefficient K.smooth)
    (K.firstBound * ‖a‖₊)
    (fun x => translatedCoefficientDerivative_bound period a K.coefficient K.firstBound
        K.norm_first x)
  have h' : ‖directionalCoefficientOperator period K a‖ ≤ (K.firstBound : ℝ) * ‖a‖ := by
    simpa only [directionalCoefficientOperator, NNReal.coe_mul, coe_nnnorm] using h
  exact ((directionalCoefficientOperator period K a).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right h' (norm_nonneg f))

/-- Strong translation differentiation of an actual coefficient product. -/
theorem metric_product_hasDerivAt (K : SmoothCoefficient period) (a : LiftTangent)
    (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    HasDerivAt (fun t => translation period (translationPath period a t) (K.operator f))
      (K.operator f' + directionalCoefficientOperator period K a f) 0 := by
  have hprod := (K.operator_translation_hasDerivAt a).clm_apply hf
  have hcov : (fun t => coefficientOperator
      (translatedCoefficient period (translationPath period a t) K.coefficient)
      (translatedCoefficient_measurable period (translationPath period a t) K.coefficient
          K.measurable)
      K.bound (fun x => K.norm_bound (x + translationPath period a t))
      (translation period (translationPath period a t) f)) =
      fun t => translation period (translationPath period a t) (K.operator f) := by
    funext t
    exact (coefficientOperator_translation period (translationPath period a t) K.coefficient
      K.measurable K.bound K.norm_bound f).symm
  rw [hcov] at hprod
  have hop0 : coefficientOperator
      (translatedCoefficient period (translationPath period a 0) K.coefficient)
      (translatedCoefficient_measurable period (translationPath period a 0) K.coefficient
          K.measurable)
      K.bound (fun x => K.norm_bound (x + translationPath period a 0)) = K.operator := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [coefficientOperator_ae
      (translatedCoefficient period (translationPath period a 0) K.coefficient)
      (translatedCoefficient_measurable period (translationPath period a 0) K.coefficient
          K.measurable)
      K.bound (fun x => K.norm_bound (x + translationPath period a 0)) u,
      K.operator_ae u] with x hx hy
    rw [hx, hy]
    simp [translatedCoefficient]
  rw [hop0] at hprod
  simp only [translationPath_zero, translation_zero] at hprod
  convert hprod using 1 <;> first | rfl | exact add_comm _ _

/-- Exact metric integration by parts for one genuine second translation derivative. -/
theorem metric_second_derivative_identity (K : SmoothCoefficient period) (a : LiftTangent)
    (f f' f'' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0)
    (hf' : HasDerivAt (fun t => translation period (translationPath period a t) f') f'' 0) :
    ⟪K.operator f, f''⟫_ℝ = -⟪K.operator f', f'⟫_ℝ -
      ⟪directionalCoefficientOperator period K a f, f'⟫_ℝ := by
  have h := translation_derivative_pairing period a (K.operator f)
    (K.operator f' + directionalCoefficientOperator period K a f) f' f''
    (metric_product_hasDerivAt period K a f f' hf) hf'
  rw [inner_add_left] at h
  linarith

omit [Fact (0 < period)] in
/-- The scalar Young inequality with the precise coercivity constant used in heat energy. -/
theorem metric_cross_young (c D x y : ℝ) (hc : 0 < c) :
    D * x * y ≤ (c ^ 2 / 2) * y ^ 2 + (D ^ 2 / (2 * c ^ 2)) * x ^ 2 := by
  have hs := sq_nonneg (c ^ 2 * y - D * x)
  have hden : 0 < 2 * c ^ 2 := by positivity
  have heq : (c ^ 2 / 2) * y ^ 2 + (D ^ 2 / (2 * c ^ 2)) * x ^ 2 - D * x * y =
      (c ^ 2 * y - D * x) ^ 2 / (2 * c ^ 2) := by
    field_simp
    ring
  have h := div_nonneg hs hden.le
  rw [← heq] at h
  linarith

/-- A positive metric absorbs half of the second-derivative dissipation, leaving an explicit L²
error. -/
theorem metric_second_derivative_bound (K : SmoothCoefficient period) (a : LiftTangent)
    (f f' f'' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0)
    (hf' : HasDerivAt (fun t => translation period (translationPath period a t) f') f'' 0)
    (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪K.coefficient x v, v⟫_ℝ) :
    ⟪K.operator f, f''⟫_ℝ ≤ -(c ^ 2 / 2) * ‖f'‖ ^ 2 +
      (((K.firstBound : ℝ) * ‖a‖) ^ 2 / (2 * c ^ 2)) * ‖f‖ ^ 2 := by
  rw [metric_second_derivative_identity period K a f f' f'' hf hf']
  have hcoer : c ^ 2 * ‖f'‖ ^ 2 ≤ ⟪K.operator f', f'⟫_ℝ :=
    coefficientOperator_coercive K.coefficient K.measurable K.bound K.norm_bound (c ^ 2) hpos f'
  have hcross : -⟪directionalCoefficientOperator period K a f, f'⟫_ℝ ≤
      ((K.firstBound : ℝ) * ‖a‖) * ‖f‖ * ‖f'‖ := by
    have h := norm_inner_le_norm (𝕜 := ℝ) (directionalCoefficientOperator period K a f) f'
    have hb := mul_le_mul_of_nonneg_right (directionalCoefficientOperator_bound period K a f)
      (norm_nonneg f')
    have ha := neg_le_abs ⟪directionalCoefficientOperator period K a f, f'⟫_ℝ
    rw [Real.norm_eq_abs] at h
    exact ha.trans (h.trans hb)
  have hy := metric_cross_young c ((K.firstBound : ℝ) * ‖a‖) ‖f‖ ‖f'‖ hc
  linarith

/-- Every standard angular or spatial cylinder coordinate vector has norm one. -/
theorem standardDirection_norm (i : Fin 4) : ‖standardDirection i‖ = 1 := by
  cases i using Fin.cases <;> simp [Prod.norm_def]

/-- The actual cylinder Laplacian assembled from strong second coordinate derivatives. -/
def jetLaplacian {f : LiftL2 period} (J : SpatialJet period standardDirection 2 f) : LiftL2 period
    :=
  ∑ i : Fin 4, J.word (fun _ : Fin 2 => i)

/-- The L² metric heat estimate for an actual second-order cylinder jet. -/
theorem metric_heat_bound (K : SmoothCoefficient period) (f : LiftL2 period)
    (J : SpatialJet period standardDirection 2 f) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪K.coefficient x v, v⟫_ℝ) :
    ⟪K.operator f, jetLaplacian period J⟫_ℝ ≤
      -(c ^ 2 / 2) * ∑ i : Fin 4, ‖J.word (fun _ : Fin 1 => i)‖ ^ 2 +
      (2 * (K.firstBound : ℝ) ^ 2 / c ^ 2) * ‖f‖ ^ 2 := by
  have hfirst (i : Fin 4) : HasDerivAt
      (fun t => translation period (translationPath period (standardDirection i) t) f)
      (J.word (fun _ : Fin 1 => i)) 0 := by
    have hw : Fin.cons i (Fin.elim0 : Fin 0 → Fin 4) = (fun _ : Fin 1 => i) := by
      funext j
      fin_cases j
      rfl
    simpa only [SpatialJet.word_zero, hw] using
      J.word_hasDerivAt (by omega : 0 < 2) (Fin.elim0 : Fin 0 → Fin 4) i
  have hsecond (i : Fin 4) : HasDerivAt
      (fun t => translation period (translationPath period (standardDirection i) t)
        (J.word (fun _ : Fin 1 => i))) (J.word (fun _ : Fin 2 => i)) 0 := by
    convert J.word_hasDerivAt (by omega : 1 < 2) (fun _ : Fin 1 => i) i using 1
    congr 1
    funext j
    cases j using Fin.cases <;> rfl
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    metric_second_derivative_bound period K (standardDirection i) f
      (J.word (fun _ : Fin 1 => i)) (J.word (fun _ : Fin 2 => i)) (hfirst i) (hsecond i) c hc hpos)
  simp only [standardDirection_norm, mul_one] at hsum
  simp only [jetLaplacian, inner_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum ⊢
  have harith : (K.firstBound : ℝ) ^ 2 / (2 * c ^ 2) * ((4 : ℝ) * ‖f‖ ^ 2) =
      (2 * (K.firstBound : ℝ) ^ 2 / c ^ 2) * ‖f‖ ^ 2 := by ring
  simpa only [Nat.cast_ofNat, harith] using hsum

/-- The sum of the four actual classical second coordinate derivatives on the cylinder. -/
def classicalLaplacian (g : LiftDomain period → Vector3) : LiftDomain period → Vector3 :=
  fun x => ∑ i : Fin 4, fieldDerivative period (standardDirection i)
    (fieldDerivative period (standardDirection i) g) x

/-- The jet Laplacian is represented by the actual classical Laplacian of every smooth
representative. -/
theorem jetLaplacian_ae {f : LiftL2 period} (J : SpatialJet period standardDirection 2 f)
    (g : LiftDomain period → Vector3)
    (hrep : (f : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    (jetLaplacian period J : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      classicalLaplacian period g := by
  have hword (i : Fin 4) : (J.word (fun _ : Fin 2 => i) : LiftDomain period → Vector3)
      =ᵐ[liftMeasure period] fieldDerivative period (standardDirection i)
        (fieldDerivative period (standardDirection i) g) := by
    simpa only [iteratedFieldDerivative_succ, iteratedFieldDerivative_zero, Fin.tail]
      using EulerStrongSmoothJet.jet_word_ae period (le_refl 2) f J (fun _ : Fin 2 => i) g hrep hg
  have hall : ∀ᵐ x ∂liftMeasure period, ∀ i : Fin 4,
      (J.word (fun _ : Fin 2 => i)) x = fieldDerivative period (standardDirection i)
        (fieldDerivative period (standardDirection i) g) x := ae_all_iff.mpr hword
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin 4))
    (fun i => J.word (fun _ : Fin 2 => i)), hall] with x hx hh
  rw [jetLaplacian, hx]
  exact Finset.sum_congr rfl (fun i _ => hh i)

/-- The metric heat bound is an actual integral estimate for a smooth cylinder representative. -/
theorem classical_metric_heat_bound (K : SmoothCoefficient period) (f : LiftL2 period)
    (J : SpatialJet period standardDirection 2 f) (g : LiftDomain period → Vector3)
    (hrep : (f : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪K.coefficient x v, v⟫_ℝ) :
    (∫ x, ⟪K.coefficient x (g x), classicalLaplacian period g x⟫_ℝ ∂liftMeasure period) ≤
      -(c ^ 2 / 2) * ∑ i : Fin 4, ‖J.word (fun _ : Fin 1 => i)‖ ^ 2 +
      (2 * (K.firstBound : ℝ) ^ 2 / c ^ 2) * ‖f‖ ^ 2 := by
  have hi : ⟪K.operator f, jetLaplacian period J⟫_ℝ =
      ∫ x, ⟪K.coefficient x (g x), classicalLaplacian period g x⟫_ℝ ∂liftMeasure period := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [K.operator_ae f, jetLaplacian_ae period J g hrep hg, hrep] with x hK hΔ he
    rw [hK, hΔ, he]
  rw [← hi]
  exact metric_heat_bound period K f J c hc hpos

end EulerMetricHeatEnergy
