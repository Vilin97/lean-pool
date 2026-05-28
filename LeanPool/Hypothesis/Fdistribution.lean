/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian.Real


import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# F distribution

-/

open Real
/-- The numerator of the F-distribution density with parameters `d₁`, `d₂`. -/
noncomputable def FDistributionNumerator (d₁ d₂ : ℝ) : ℝ → ℝ := fun x =>
  (√(((d₁ ^ d₁ * d₂ ^ d₂) * x ^ d₁) / ((d₁ * x + d₂) ^ (d₁ + d₂))))

/-- The Beta function `B(d₁, d₂) = Γ(d₁) Γ(d₂) / Γ(d₁ + d₂)`. -/
noncomputable def Real.Beta (d₁ d₂ : ℝ) := Gamma (d₁) * Gamma (d₂) / Gamma (d₁ + d₂)

/-- The probability density function of the F-distribution with parameters `d₁`, `d₂`. -/
noncomputable def FDistribution (d₁ d₂ : ℝ) : ℝ → ℝ :=
  (fun x =>
  FDistributionNumerator d₁ d₂ x) /
  (fun x => (x * Beta (d₁ / 2) (d₂ / 2)))

example (d₁ d₂ : ℝ) (hd₁ : d₁ ≠ 0) : FDistributionNumerator d₁ d₂ 0 = 0 := by
  simp only [FDistributionNumerator, mul_zero, zero_add]
  refine sqrt_eq_zero'.mpr ?_
  apply le_of_eq
  simp only [div_eq_zero_iff, mul_eq_zero]
  left
  right
  exact zero_rpow hd₁

example (d₁ d₂ : ℝ) : FDistribution d₁ d₂ 0 = 0 := by
  simp [FDistribution]
