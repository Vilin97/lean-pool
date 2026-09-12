/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Explicit Gaussian kernels used by the heat operators. The probability theory needed to
establish their mass stays in the proofs, while the kernel formulas remain transparent. -/

@[expose] public section

noncomputable section

namespace EulerGaussianCylinderHeat

open MeasureTheory
open scoped NNReal

/-- The real Gaussian density with mean `μ` and variance `v`. -/
def gaussianDensity (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x - μ) ^ 2 / (2 * v))

/-- The Gaussian measure, with a point mass when its variance is zero. -/
def gaussianMeasure (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  if v = 0 then Measure.dirac μ else volume.withDensity
    (fun x => ENNReal.ofReal (gaussianDensity μ v x))

private theorem gaussianDensity_eq (μ : ℝ) (v : ℝ≥0) :
    gaussianDensity μ v = ProbabilityTheory.gaussianPDFReal μ v := rfl

private theorem gaussianMeasure_eq (μ : ℝ) (v : ℝ≥0) :
    gaussianMeasure μ v = ProbabilityTheory.gaussianReal μ v := rfl

instance (μ : ℝ) (v : ℝ≥0) : IsProbabilityMeasure (gaussianMeasure μ v) := by
  rw [gaussianMeasure_eq]
  infer_instance

@[simp] theorem gaussianMeasure_zero_var (μ : ℝ) : gaussianMeasure μ 0 = Measure.dirac μ :=
  ite_eq_left rfl

end EulerGaussianCylinderHeat
