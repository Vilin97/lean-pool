/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.ForMathlib.StronglyMeasurable

import LeanPool.NavierStokesAndEuler.Euler.ClosedTranslationGraph
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Probability.Distributions.Gaussian.Real
public import LeanPool.NavierStokesAndEuler.Euler.GaussianKernels
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PressureSpatialRegularity
import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderMollifier
import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedWeakDerivative

/-! A genuine one-derivative Gaussian smoothing estimate for cylinder L² fields. -/

section

/-! Gaussian heat averaging in the genuine cylinder L² translation representation. -/

@[expose] public section

noncomputable section

namespace EulerGaussianCylinderHeat

open MeasureTheory ProbabilityTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerLiftedWeakDerivative EulerCylinderMollifier EulerSpatialSobolevInverse
open scoped ENNReal NNReal Topology

private theorem gaussianMeasure_eq_real (μ : ℝ) (v : ℝ≥0) :
    gaussianMeasure μ v = gaussianReal μ v := rfl

variable (period : ℝ) [Fact (0 < period)]

/-- The actual one-parameter cylinder translation orbit. -/
def lineOrbit (a : LiftTangent) (f : LiftL2 period) (x : ℝ) : LiftL2 period :=
  translation period (translationPath period a x) f

theorem lineOrbit_continuous (a : LiftTangent) (f : LiftL2 period) :
    Continuous (lineOrbit period a f) :=
  (translation_continuous period f).comp (translationPath_continuous period a)

@[simp] theorem lineOrbit_norm (a : LiftTangent) (f : LiftL2 period) (x : ℝ) :
    ‖lineOrbit period a f x‖ = ‖f‖ := translation_norm period _ f

@[simp] theorem lineOrbit_zero (a : LiftTangent) (f : LiftL2 period) : lineOrbit period a f 0 = f
    := by
  rw [lineOrbit, translationPath_zero, translation_zero]

theorem lineOrbit_integrable (a : LiftTangent) (f : LiftL2 period) (μ : Measure ℝ) [IsFiniteMeasure
    μ] :
    Integrable (lineOrbit period a f) μ :=
  Integrable.of_bound (lineOrbit_continuous period a f).aestronglyMeasurable_of_secondCountable ‖f‖
    (Filter.Eventually.of_forall (fun x => (lineOrbit_norm period a f x).le))

/-- Gaussian averaging with variance v along a cylinder direction. -/
def lineHeat (a : LiftTangent) (v : ℝ≥0) (f : LiftL2 period) : LiftL2 period :=
  ∫ x, lineOrbit period a f x ∂gaussianMeasure 0 v

@[simp] theorem lineHeat_zero (a : LiftTangent) (f : LiftL2 period) : lineHeat period a 0 f = f :=
    by
  simp [lineHeat]

/-- Gaussian averaging is contractive, including variance zero. -/
theorem lineHeat_norm_le (a : LiftTangent) (v : ℝ≥0) (f : LiftL2 period) :
    ‖lineHeat period a v f‖ ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le (integrable_const ‖f‖ : Integrable (fun _ : ℝ => ‖f‖)
      (gaussianMeasure 0 v))
    (f := lineOrbit period a f) (Filter.Eventually.of_forall (fun x => (lineOrbit_norm period a f
        x).le))
  simpa [lineHeat, measureReal_def] using h

theorem lineHeat_add (a : LiftTangent) (v : ℝ≥0) (f g : LiftL2 period) :
    lineHeat period a v (f+g) = lineHeat period a v f + lineHeat period a v g := by
  simp only [lineHeat, lineOrbit, map_add]
  exact integral_add (lineOrbit_integrable period a f _) (lineOrbit_integrable period a g _)

theorem lineHeat_smul (a : LiftTangent) (v : ℝ≥0) (c : ℝ) (f : LiftL2 period) :
    lineHeat period a v (c • f) = c • lineHeat period a v f := by
  simp only [lineHeat, lineOrbit, map_smul, integral_smul]

/-- The actual bounded Gaussian averaging operator. -/
def lineHeatOperator (a : LiftTangent) (v : ℝ≥0) : LiftL2 period →L[ℝ] LiftL2 period :=
  LinearMap.mkContinuous
    { toFun := lineHeat period a v
      map_add' := lineHeat_add period a v
      map_smul' := lineHeat_smul period a v }
    1 (fun f => by simpa using lineHeat_norm_le period a v f)

@[simp] theorem lineHeatOperator_apply (a : LiftTangent) (v : ℝ≥0) (f : LiftL2 period) :
    lineHeatOperator period a v f = lineHeat period a v f := rfl

theorem lineHeatOperator_norm_le (a : LiftTangent) (v : ℝ≥0) : ‖lineHeatOperator period a v‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
      simpa using lineHeat_norm_le period a v f)

/-- The heat average commutes with every cylinder translation. -/
theorem lineHeat_translation (a : LiftTangent) (v : ℝ≥0) (b : LiftDomain period) (f : LiftL2
    period) :
    translation period b (lineHeat period a v f) = lineHeat period a v (translation period b f) :=
        by
  change (translation period b).toContinuousLinearMap (∫ x, lineOrbit period a f x
      ∂gaussianMeasure 0 v) = _
  rw [← (translation period b).toContinuousLinearMap.integral_comp_comm (lineOrbit_integrable
      period a f _)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change translation period b (translation period (translationPath period a x) f) =
    translation period (translationPath period a x) (translation period b f)
  rw [translation_add, translation_add, add_comm b]

/-- A joint translation orbit is integrable against the product of two finite measures. -/
theorem jointOrbit_integrable (a : LiftTangent) (f : LiftL2 period)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun p : ℝ × ℝ => lineOrbit period a f (p.1 + p.2)) (μ.prod ν) := by
  apply Integrable.of_bound ((lineOrbit_continuous period a f).comp
    (continuous_fst.add continuous_snd)).aestronglyMeasurable_of_secondCountable ‖f‖
  exact Filter.Eventually.of_forall (fun p => (lineOrbit_norm period a f (p.1+p.2)).le)

/-- Addition of Gaussian variances gives the semigroup law on actual cylinder L² fields. -/
theorem lineHeat_semigroup (a : LiftTangent) (v w : ℝ≥0) (f : LiftL2 period) :
    lineHeat period a v (lineHeat period a w f) = lineHeat period a (v+w) f := by
  have hconv : (gaussianMeasure 0 v) ∗ (gaussianMeasure 0 w) = gaussianMeasure 0 (v+w) := by
    simpa only [gaussianMeasure_eq_real, zero_add] using
      (gaussianReal_conv_gaussianReal (m₁ := 0) (m₂ := 0) (v₁ := v) (v₂ := w))
  calc
    _ = ∫ x, ∫ y, lineOrbit period a f (x+y) ∂gaussianMeasure 0 w ∂gaussianMeasure 0 v := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      rw [lineOrbit, lineHeat_translation]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      simp only [lineOrbit, translationPath_add, translation_add]
      rw [add_comm (translationPath period a y)]
    _ = ∫ p : ℝ × ℝ, lineOrbit period a f (p.1+p.2)
        ∂(gaussianMeasure 0 v).prod (gaussianMeasure 0 w) :=
      (integral_prod _ (jointOrbit_integrable period a f _ _)).symm
    _ = ∫ x, lineOrbit period a f x ∂(gaussianMeasure 0 v ∗ gaussianMeasure 0 w) := by
      rw [Measure.conv]
      exact (integral_map_of_stronglyMeasurable
        (show Measurable (fun p : ℝ × ℝ => p.1 + p.2) by fun_prop)
        (lineOrbit_continuous period a f).stronglyMeasurable).symm
    _ = _ := by rw [hconv]; rfl

/-- Different coordinate heat averages commute, since all cylinder translations commute. -/
theorem lineHeat_commute (a b : LiftTangent) (v w : ℝ≥0) (f : LiftL2 period) :
    lineHeat period a v (lineHeat period b w f) = lineHeat period b w (lineHeat period a v f) := by
  change (lineHeatOperator period a v) (∫ x, lineOrbit period b f x ∂gaussianMeasure 0 w) = _
  rw [← (lineHeatOperator period a v).integral_comp_comm (lineOrbit_integrable period b f _)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact (lineHeat_translation period a v (translationPath period b x) f).symm

/-- Fixed standard-Gaussian representation of every nonnegative-variance average. -/
theorem lineHeat_eq_standardGaussian (a : LiftTangent) (v : ℝ≥0) (f : LiftL2 period) :
    lineHeat period a v f =
      ∫ x, lineOrbit period a f (Real.sqrt (v : ℝ) * x) ∂gaussianMeasure 0 1 := by
  have hvar : (⟨Real.sqrt (v : ℝ) ^ 2, sq_nonneg _⟩ : ℝ≥0) * 1 = v := by
    ext
    simp [Real.sq_sqrt v.coe_nonneg]
  have hmap := gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) (Real.sqrt (v : ℝ))
  have hmap' : Measure.map (fun x => Real.sqrt (v : ℝ) * x) (gaussianMeasure 0 1) =
      gaussianMeasure 0 v := by
    simp only [gaussianMeasure_eq_real]
    convert hmap using 2
    · simp
    · ext
      simp [Real.sq_sqrt v.coe_nonneg]
  clear hmap hvar
  rw [lineHeat, ← hmap', integral_map_of_stronglyMeasurable (by fun_prop)
    (lineOrbit_continuous period a f).stronglyMeasurable]

/-- The Gaussian operators are strongly continuous in their nonnegative variance parameter. -/
theorem lineHeat_continuous (a : LiftTangent) (f : LiftL2 period) :
    Continuous (fun v : ℝ≥0 => lineHeat period a v f) := by
  simp_rw [lineHeat_eq_standardGaussian]
  apply continuous_of_dominated
    (bound := fun _ : ℝ => ‖f‖)
  · intro v
    exact ((lineOrbit_continuous period a f).comp (continuous_const.mul
        continuous_id)).aestronglyMeasurable_of_secondCountable
  · intro v
    exact Filter.Eventually.of_forall (fun x => (lineOrbit_norm period a f _).le)
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro x
    exact (lineOrbit_continuous period a f).comp
      ((Real.continuous_sqrt.comp continuous_subtype_val).mul_const x)

end EulerGaussianCylinderHeat

end
end

end

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
    (hk.1.smul (lineOrbit_continuous period a f).aestronglyMeasurable_of_secondCountable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖k x • lineOrbit period a f x‖ ≤ ‖k x‖ * ‖f‖
  rw [norm_smul, lineOrbit_norm]

/-- The actual derivative of the real Gaussian density. -/
theorem gaussianPDF_hasDerivAt (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (gaussianDensity 0 v) (-(x / (v : ℝ)) * gaussianDensity 0 v x) x := by
  have h := ((((hasDerivAt_id x).pow 2).neg.div_const (2*(v : ℝ))).exp).const_mul
    (Real.sqrt (2*Real.pi*(v : ℝ)))⁻¹
  convert! h using 1
  · ext y
    simp [gaussianDensity]
  · simp only [gaussianDensity, sub_zero, Pi.neg_apply, Pi.pow_apply, id_eq,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring

/-- The Gaussian first-moment kernel is integrable against Lebesgue measure. -/
theorem gaussianMomentKernel_integrable (v : ℝ≥0) :
    Integrable (fun x : ℝ => (x / (v : ℝ)) * gaussianDensity 0 v x) := by
  by_cases hv : v = 0
  · subst v
    simp
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have h := (integrable_mul_exp_neg_mul_sq (by positivity : 0 < (2*(v : ℝ))⁻¹)).const_mul
    ((Real.sqrt (2*Real.pi*(v : ℝ)))⁻¹ / (v : ℝ))
  convert! h using 1
  ext x
  simp only [gaussianDensity, sub_zero]
  have he : -(x ^ 2) / (2*(v : ℝ)) = -(2*(v : ℝ))⁻¹ * x ^ 2 := by ring
  rw [he]
  ring

/-- The first absolute moment of a centered Gaussian. -/
def gaussianAbsMoment (v : ℝ≥0) : ℝ := ∫ x : ℝ, |x| ∂gaussianMeasure 0 v

theorem gaussianAbsMoment_nonneg (v : ℝ≥0) : 0 ≤ gaussianAbsMoment v :=
  integral_nonneg (fun x => abs_nonneg x)

theorem gaussianId_integrable (v : ℝ≥0) : Integrable (fun x : ℝ => x) (gaussianMeasure 0 v) := by
  exact (memLp_one_iff_integrable).mp (memLp_id_gaussianReal (μ := 0) (v := v) 1)

/-- Absolute Gaussian moments scale by the standard deviation. -/
theorem gaussianAbsMoment_scale (v : ℝ≥0) :
    gaussianAbsMoment v = Real.sqrt (v : ℝ) * gaussianAbsMoment 1 := by
  have hmap : Measure.map (fun x => Real.sqrt (v : ℝ) * x) (gaussianMeasure 0 1) =
      gaussianMeasure 0 v := by
    have h := gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) (Real.sqrt (v : ℝ))
    simp only [gaussianMeasure_eq_real]
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
    Integrable (fun x : ℝ => x • lineOrbit period a f x) (gaussianMeasure 0 v) := by
  apply ((gaussianId_integrable v).norm.mul_const ‖f‖).mono'
    ((gaussianId_integrable v).1.smul (lineOrbit_continuous period a
      f).aestronglyMeasurable_of_secondCountable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖x • lineOrbit period a f x‖ ≤ ‖x‖ * ‖f‖
  rw [norm_smul, lineOrbit_norm]

/-- The bounded candidate generator after Gaussian smoothing. -/
def lineHeatDerivative (a : LiftTangent) (v : ℝ≥0) (f : LiftL2 period) : LiftL2 period :=
  (v : ℝ)⁻¹ • ∫ x : ℝ, x • lineOrbit period a f x ∂gaussianMeasure 0 v

theorem lineHeatDerivative_norm_le (a : LiftTangent) (v : ℝ≥0) (f : LiftL2 period) :
    ‖lineHeatDerivative period a v f‖ ≤ (v : ℝ)⁻¹ * gaussianAbsMoment v * ‖f‖ := by
  have hi := norm_integral_le_of_norm_le
    ((gaussianId_integrable v).norm.mul_const ‖f‖)
    (f := fun x : ℝ => x • lineOrbit period a f x)
    (Filter.Eventually.of_forall (fun x => by simp only [norm_smul, lineOrbit_norm]; exact le_rfl))
  have hb : ‖∫ x : ℝ, x • lineOrbit period a f x ∂gaussianMeasure 0 v‖ ≤
      gaussianAbsMoment v * ‖f‖ :=
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
  have hp := kernelOrbit_integrable period a f (gaussianDensity 0 v) (integrable_gaussianPDFReal 0
      v)
  have hpg := kernelOrbit_integrable period a g (gaussianDensity 0 v) (integrable_gaussianPDFReal 0
      v)
  have hdp := kernelOrbit_integrable period a f
    (fun x => -(x/(v : ℝ)) * gaussianDensity 0 v x) ((gaussianMomentKernel_integrable v).neg.congr
      (Filter.Eventually.of_forall (fun x => by simp only [Pi.neg_apply]; ring)))
  have hIBP := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (fun x _ => gaussianPDF_hasDerivAt v x)
    (fun x _ => translation_hasDerivAt_all period a f g hD x) hpg hdp hp
  rw [lineHeat, gaussianMeasure_eq_real, integral_gaussianReal_eq_integral_smul hv]
  change (∫ x, gaussianDensity 0 v x • lineOrbit period a g x) = _
  rw [show (∫ x, gaussianDensity 0 v x • lineOrbit period a g x) =
      -(∫ x, (-(x/(v : ℝ)) * gaussianDensity 0 v x) • lineOrbit period a f x) from hIBP]
  rw [lineHeatDerivative, gaussianMeasure_eq_real, integral_gaussianReal_eq_integral_smul hv,
    ← integral_smul, ← integral_neg]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change -((-(x / (v : ℝ)) * gaussianDensity 0 v x) • lineOrbit period a f x) =
    (v : ℝ)⁻¹ • (gaussianDensity 0 v x • (x • lineOrbit period a f x))
  rw [← neg_smul]
  simp only [smul_smul]
  congr 1
  ring

end EulerGaussianCylinderHeat
