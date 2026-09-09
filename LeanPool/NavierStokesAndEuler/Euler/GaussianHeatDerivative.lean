/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GaussianCylinderHeat
import LeanPool.NavierStokesAndEuler.Euler.ClosedTranslationGraph
import Mathlib.Algebra.Order.Star.Real

/-! A genuine one-derivative Gaussian smoothing estimate for cylinder L² fields. -/

@[expose] public section


noncomputable section

namespace EulerGaussianCylinderHeat

open MeasureTheory ProbabilityTheory InnerProductSpace EulerLiftedGradientSpace
  EulerPressureSpatialRegularity
  EulerClosedTranslationGraph
open scoped ENNReal NNReal Topology ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- Multiplying the isometric orbit by an L¹ scalar kernel gives a Bochner integrable field. -/
theorem kernelOrbit_integrable (a : LiftTangent) (f : LiftL2 period)
    (k : ℝ → ℝ) (hk : Integrable k) : Integrable (fun x => k x • lineOrbit period a f x) := by
  apply (hk.norm.mul_const ‖f‖).mono'
    (hk.1.smul (lineOrbit_continuous period a f).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖k x • lineOrbit period a f x‖ ≤ ‖k x‖ * ‖f‖
  rw [norm_smul, lineOrbit_norm]

/-- The actual derivative of the real Gaussian density. -/
theorem gaussianPDF_hasDerivAt (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 v) (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) x := by
  have h := ((((hasDerivAt_id x).pow 2).neg.div_const (2*(v : ℝ))).exp).const_mul
    (Real.sqrt (2*Real.pi*(v : ℝ)))⁻¹
  convert! h using 1
  · ext y
    simp [gaussianPDFReal]
  · simp only [gaussianPDFReal, sub_zero, Pi.neg_apply, Pi.pow_apply, id_eq,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring

/-- The Gaussian first-moment kernel is integrable against Lebesgue measure. -/
theorem gaussianMomentKernel_integrable (v : ℝ≥0) :
    Integrable (fun x : ℝ => (x / (v : ℝ)) * gaussianPDFReal 0 v x) := by
  by_cases hv : v = 0
  · subst v
    simp
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have h := (integrable_mul_exp_neg_mul_sq (by positivity : 0 < (2*(v : ℝ))⁻¹)).const_mul
    ((Real.sqrt (2*Real.pi*(v : ℝ)))⁻¹ / (v : ℝ))
  convert! h using 1
  ext x
  simp only [gaussianPDFReal, sub_zero]
  have he : -(x ^ 2) / (2*(v : ℝ)) = -(2*(v : ℝ))⁻¹ * x ^ 2 := by ring
  rw [he]
  ring

/-- The first absolute moment of a centered Gaussian. -/
def gaussianAbsMoment (v : ℝ≥0) : ℝ := ∫ x : ℝ, |x| ∂gaussianReal 0 v

theorem gaussianAbsMoment_nonneg (v : ℝ≥0) : 0 ≤ gaussianAbsMoment v :=
  integral_nonneg (fun x => abs_nonneg x)

theorem gaussianId_integrable (v : ℝ≥0) : Integrable (fun x : ℝ => x) (gaussianReal 0 v) := by
  exact (memLp_one_iff_integrable).mp (memLp_id_gaussianReal (μ := 0) (v := v) 1)

/-- Absolute Gaussian moments scale by the standard deviation. -/
theorem gaussianAbsMoment_scale (v : ℝ≥0) :
    gaussianAbsMoment v = Real.sqrt (v : ℝ) * gaussianAbsMoment 1 := by
  have hmap : Measure.map (fun x => Real.sqrt (v : ℝ) * x) (gaussianReal 0 1) = gaussianReal 0 v :=
      by
    have h := gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) (Real.sqrt (v : ℝ))
    convert h using 2
    · simp
    · ext
      simp [Real.sq_sqrt v.coe_nonneg]
  rw [gaussianAbsMoment, ← hmap, integral_map_of_stronglyMeasurable (by
      fun_prop) continuous_abs.stronglyMeasurable]
  simp_rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [integral_const_mul]
  rfl

theorem gaussianMomentOrbit_integrable (a : LiftTangent) (v : ℝ≥0) (f : LiftL2 period) :
    Integrable (fun x : ℝ => x • lineOrbit period a f x) (gaussianReal 0 v) := by
  apply ((gaussianId_integrable v).norm.mul_const ‖f‖).mono'
    ((gaussianId_integrable v).1.smul (lineOrbit_continuous period a f).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖x • lineOrbit period a f x‖ ≤ ‖x‖ * ‖f‖
  rw [norm_smul, lineOrbit_norm]

/-- The bounded candidate generator after Gaussian smoothing. -/
def lineHeatDerivative (a : LiftTangent) (v : ℝ≥0) (f : LiftL2 period) : LiftL2 period :=
  (v : ℝ)⁻¹ • ∫ x : ℝ, x • lineOrbit period a f x ∂gaussianReal 0 v

theorem lineHeatDerivative_norm_le (a : LiftTangent) (v : ℝ≥0) (f : LiftL2 period) :
    ‖lineHeatDerivative period a v f‖ ≤ (v : ℝ)⁻¹ * gaussianAbsMoment v * ‖f‖ := by
  have hi := norm_integral_le_of_norm_le
    ((gaussianId_integrable v).norm.mul_const ‖f‖)
    (f := fun x : ℝ => x • lineOrbit period a f x)
    (Filter.Eventually.of_forall (fun x => by simp only [norm_smul, lineOrbit_norm]; exact le_rfl))
  have hb : ‖∫ x : ℝ, x • lineOrbit period a f x ∂gaussianReal 0 v‖ ≤ gaussianAbsMoment v * ‖f‖ :=
      by
    simpa only [integral_mul_const, Real.norm_eq_abs, gaussianAbsMoment] using hi
  rw [lineHeatDerivative, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr v.coe_nonneg)]
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr v.coe_nonneg)).trans_eq (mul_assoc ..).symm

/-- The true parabolic one-derivative bound, with inverse square root of variance. -/
theorem lineHeatDerivative_smoothing_bound (a : LiftTangent) {v : ℝ≥0} (hv : 0 < v) (f : LiftL2
    period) :
    ‖lineHeatDerivative period a v f‖ ≤
      (gaussianAbsMoment 1 / Real.sqrt (v : ℝ)) * ‖f‖ := by
  have hvR : 0 < (v : ℝ) := NNReal.coe_pos.mpr hv
  have hs : Real.sqrt (v : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hvR).ne'
  have hvne : (v : ℝ) ≠ 0 := hvR.ne'
  have he : (v : ℝ)⁻¹ * gaussianAbsMoment v = gaussianAbsMoment 1 / Real.sqrt (v : ℝ) := by
    rw [gaussianAbsMoment_scale]
    field_simp
    rw [Real.sq_sqrt v.coe_nonneg]
  simpa only [he] using lineHeatDerivative_norm_le period a v f

/-- Strong derivatives commute with Gaussian averaging. -/
theorem lineHeat_strongDerivative (a b : LiftTangent) (v : ℝ≥0) (f g : LiftL2 period)
    (hD : HasDerivAt (lineOrbit period b f) g 0) :
    HasDerivAt (lineOrbit period b (lineHeat period a v f)) (lineHeat period a v g) 0 := by
  have h := (lineHeatOperator period a v).hasFDerivAt.comp_hasDerivAt 0 hD
  have he : (fun t => lineHeatOperator period a v (lineOrbit period b f t)) =
      lineOrbit period b (lineHeat period a v f) := by
    funext t
    exact (lineHeat_translation period a v (translationPath period b t) f).symm
  change HasDerivAt (fun t => lineHeatOperator period a v (lineOrbit period b f t))
    (lineHeatOperator period a v g) 0 at h
  rw [he] at h
  exact h

/-- Gaussian integration by parts identifies the averaged strong derivative with the bounded moment
operator. -/
theorem lineHeat_derivative_identity (a : LiftTangent) {v : ℝ≥0} (hv : v ≠ 0)
    (f g : LiftL2 period) (hD : HasDerivAt (lineOrbit period a f) g 0) :
    lineHeat period a v g = lineHeatDerivative period a v f := by
  have hp := kernelOrbit_integrable period a f (gaussianPDFReal 0 v) (integrable_gaussianPDFReal 0
      v)
  have hpg := kernelOrbit_integrable period a g (gaussianPDFReal 0 v) (integrable_gaussianPDFReal 0
      v)
  have hdp := kernelOrbit_integrable period a f
    (fun x => -(x/(v : ℝ)) * gaussianPDFReal 0 v x) ((gaussianMomentKernel_integrable v).neg.congr
      (Filter.Eventually.of_forall (fun x => by simp only [Pi.neg_apply]; ring)))
  have hIBP := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (fun x _ => gaussianPDF_hasDerivAt v x)
    (fun x _ => translation_hasDerivAt_all period a f g hD x) hpg hdp hp
  rw [lineHeat, integral_gaussianReal_eq_integral_smul hv]
  change (∫ x, gaussianPDFReal 0 v x • lineOrbit period a g x) = _
  rw [show (∫ x, gaussianPDFReal 0 v x • lineOrbit period a g x) =
      -(∫ x, (-(x/(v : ℝ)) * gaussianPDFReal 0 v x) • lineOrbit period a f x) from hIBP]
  rw [lineHeatDerivative, integral_gaussianReal_eq_integral_smul hv, ← integral_smul, ←
      integral_neg]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change -((-(x / (v : ℝ)) * gaussianPDFReal 0 v x) • lineOrbit period a f x) =
    (v : ℝ)⁻¹ • (gaussianPDFReal 0 v x • (x • lineOrbit period a f x))
  rw [← neg_smul]
  simp only [smul_smul]
  congr 1
  ring

end EulerGaussianCylinderHeat
