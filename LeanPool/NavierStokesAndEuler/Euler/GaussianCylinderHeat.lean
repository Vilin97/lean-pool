/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PressureSpatialRegularity
import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderMollifier
import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedWeakDerivative
import Mathlib.Algebra.Order.Star.Real

/-! Gaussian heat averaging in the genuine cylinder L² translation representation. -/

@[expose] public section


noncomputable section

namespace EulerGaussianCylinderHeat

open MeasureTheory ProbabilityTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerLiftedWeakDerivative EulerCylinderMollifier EulerSpatialSobolevInverse
open scoped ENNReal NNReal Topology

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
  Integrable.of_bound (lineOrbit_continuous period a f).aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall (fun x => (lineOrbit_norm period a f x).le))

/-- Gaussian averaging with variance v along a cylinder direction. -/
def lineHeat (a : LiftTangent) (v : ℝ≥0) (f : LiftL2 period) : LiftL2 period :=
  ∫ x, lineOrbit period a f x ∂gaussianReal 0 v

@[simp] theorem lineHeat_zero (a : LiftTangent) (f : LiftL2 period) : lineHeat period a 0 f = f :=
    by
  simp [lineHeat]

/-- Gaussian averaging is contractive, including variance zero. -/
theorem lineHeat_norm_le (a : LiftTangent) (v : ℝ≥0) (f : LiftL2 period) :
    ‖lineHeat period a v f‖ ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le (integrable_const ‖f‖ : Integrable (fun _ : ℝ => ‖f‖)
      (gaussianReal 0 v))
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
  change (translation period b).toContinuousLinearMap (∫ x, lineOrbit period a f x ∂gaussianReal 0
      v) = _
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
    (continuous_fst.add continuous_snd)).aestronglyMeasurable ‖f‖
  exact Filter.Eventually.of_forall (fun p => (lineOrbit_norm period a f (p.1+p.2)).le)

/-- Addition of Gaussian variances gives the semigroup law on actual cylinder L² fields. -/
theorem lineHeat_semigroup (a : LiftTangent) (v w : ℝ≥0) (f : LiftL2 period) :
    lineHeat period a v (lineHeat period a w f) = lineHeat period a (v+w) f := by
  have hconv : (gaussianReal 0 v) ∗ (gaussianReal 0 w) = gaussianReal 0 (v+w) := by
    simpa using (gaussianReal_conv_gaussianReal (m₁ := 0) (m₂ := 0) (v₁ := v) (v₂ := w))
  calc
    _ = ∫ x, ∫ y, lineOrbit period a f (x+y) ∂gaussianReal 0 w ∂gaussianReal 0 v := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      rw [lineOrbit, lineHeat_translation]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      simp only [lineOrbit, translationPath_add, translation_add]
      rw [add_comm (translationPath period a y)]
    _ = ∫ p : ℝ × ℝ, lineOrbit period a f (p.1+p.2) ∂(gaussianReal 0 v).prod (gaussianReal 0 w) :=
      (integral_prod _ (jointOrbit_integrable period a f _ _)).symm
    _ = ∫ x, lineOrbit period a f x ∂(gaussianReal 0 v ∗ gaussianReal 0 w) := by
      rw [Measure.conv]
      exact (integral_map_of_stronglyMeasurable
        (show Measurable (fun p : ℝ × ℝ => p.1 + p.2) by fun_prop)
        (lineOrbit_continuous period a f).stronglyMeasurable).symm
    _ = _ := by rw [hconv]; rfl

/-- Different coordinate heat averages commute, since all cylinder translations commute. -/
theorem lineHeat_commute (a b : LiftTangent) (v w : ℝ≥0) (f : LiftL2 period) :
    lineHeat period a v (lineHeat period b w f) = lineHeat period b w (lineHeat period a v f) := by
  change (lineHeatOperator period a v) (∫ x, lineOrbit period b f x ∂gaussianReal 0 w) = _
  rw [← (lineHeatOperator period a v).integral_comp_comm (lineOrbit_integrable period b f _)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact (lineHeat_translation period a v (translationPath period b x) f).symm

/-- Fixed standard-Gaussian representation of every nonnegative-variance average. -/
theorem lineHeat_eq_standardGaussian (a : LiftTangent) (v : ℝ≥0) (f : LiftL2 period) :
    lineHeat period a v f = ∫ x, lineOrbit period a f (Real.sqrt (v : ℝ) * x) ∂gaussianReal 0 1 :=
        by
  have hvar : (⟨Real.sqrt (v : ℝ) ^ 2, sq_nonneg _⟩ : ℝ≥0) * 1 = v := by
    ext
    simp [Real.sq_sqrt v.coe_nonneg]
  have hmap := gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) (Real.sqrt (v : ℝ))
  have hmap' : Measure.map (fun x => Real.sqrt (v : ℝ) * x) (gaussianReal 0 1) = gaussianReal 0 v
      := by
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
        continuous_id)).aestronglyMeasurable
  · intro v
    exact Filter.Eventually.of_forall (fun x => (lineOrbit_norm period a f _).le)
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro x
    exact (lineOrbit_continuous period a f).comp
      ((Real.continuous_sqrt.comp continuous_subtype_val).mul_const x)

end EulerGaussianCylinderHeat
