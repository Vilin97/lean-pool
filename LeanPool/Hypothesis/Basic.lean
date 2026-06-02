/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Hypothesis testing

 -/

open MeasureTheory ProbabilityTheory

/-- One-sided p-value of an observation `a` under the measure `p`: the probability
of observing a value at least as extreme as `a`, on the same side of the mean. -/
noncomputable def oneSidedPval (a : ℝ)
  (p : Measure ℝ) :=
  let μ := moment id 1 p
  p {x | |x - μ| ≥ |a - μ| ∧ Real.sign (x - μ) = Real.sign (a - μ)}

/-- The one-sided p-value of `a` under a probability mass function `p`. -/
noncomputable def oneSidedPvalPMF (a : ℝ)
  (p : PMF ℝ) :=
  -- let μ := ∫ (x : ℝ), x ∂ p.toMeasure
  let μ := moment id 1 p.toMeasure
  p.toMeasure {x | |x - μ| ≥ |a - μ| ∧ Real.sign (x - μ) = Real.sign (a - μ)}


/-- Two-sided p-value of an observation `a` under the measure `p`: the probability
of observing a value at least as far from the mean as `a` in either direction. -/
noncomputable def twoSidedPval (a : ℝ)
  (p : Measure ℝ) :=
  let μ := moment id 1 p
  p {x |  |x - μ| ≥ |a - μ|}

/-- One-sided p-value expressed via tail intervals `Ici`/`Iic` of the mean. -/
noncomputable def oneSidedPval' (a : ℝ)
  (p : Measure ℝ) :=
  let μ := moment id 1 p
  ite (a > μ)
    (p (Set.Ici a))
  (ite (a < μ)
    (p (Set.Iic a)) 1)

/-- Two-sided p-value expressed via symmetric tail intervals around the mean. -/
noncomputable def twoSidedPval' (a : ℝ)
  (p : Measure ℝ) :=
  let μ := moment id 1 p
  ite (a > μ)
    (p (Set.Ici a) + p (Set.Iic (μ - (a - μ))))
  (ite (a < μ)
    (p (Set.Iic a) + p (Set.Ici (μ + (μ - a)))) 1)

/-- The rejection region of a two-sided test at the given significance `threshold`. -/
def twoSidedRejectionRegion (p : Measure ℝ)
  (threshold : ENNReal) := {observed | ¬ twoSidedPval observed p ≥ threshold}

/-- Type 1 error when testing
H₀ : θ = hypθ
Incorrectly reject H₀.
-/
def type1err (f : ℝ → Measure ℝ)
  (hypθ realθ observed : ℝ) (threshold : ENNReal) :=
    observed ∈ twoSidedRejectionRegion (f hypθ) threshold
    ∧ hypθ = realθ

/-- Type 2 error: incorrectly fail to reject H₀. -/
def type2err (f : ℝ → Measure ℝ)
  (hypθ realθ observed : ℝ) (threshold : ENNReal) :=
    observed ∉ twoSidedRejectionRegion (f hypθ) threshold
    ∧ hypθ ≠ realθ

/-- Correctly failing to reject `H₀`: the observation is outside the rejection
region and the null hypothesis is in fact true. -/
def correctFailToReject (f : ℝ → Measure ℝ)
  (hypθ realθ observed : ℝ) (threshold : ENNReal) :=
    observed ∉ twoSidedRejectionRegion (f hypθ) threshold
    ∧ hypθ = realθ

/-- Correctly rejecting `H₀`: the observation is in the rejection region and the
null hypothesis is in fact false. -/
def correctReject (f : ℝ → Measure ℝ)
  (hypθ realθ observed : ℝ) (threshold : ENNReal) :=
    observed ∈ twoSidedRejectionRegion (f hypθ) threshold
    ∧ hypθ ≠ realθ
