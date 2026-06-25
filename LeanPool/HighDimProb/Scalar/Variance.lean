/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Scalar.Centering
import Mathlib.Probability.Moments.Variance

/-!
# Scalar variance and covariance

Thin HighDimProb aliases around Mathlib scalar variance, covariance, and second moments.

Verified Wikipedia references:
* Variance: https://en.wikipedia.org/wiki/Variance
* Covariance: https://en.wikipedia.org/wiki/Covariance
-/

namespace HighDimProb

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

/--
Variance of a real random variable, reusing Mathlib's definition.

Formula reference: `Var(X) = E[(X - E[X])^2]`; see
https://en.wikipedia.org/wiki/Variance
-/
abbrev variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : ℝ :=
  ProbabilityTheory.variance X P

/--
Covariance of two real random variables, reusing Mathlib's definition.

Formula reference: `Cov(X,Y) = E[(X - E[X]) * (Y - E[Y])]`; see
https://en.wikipedia.org/wiki/Covariance
-/
abbrev covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : RealRandomVariable Ω) : ℝ :=
  ProbabilityTheory.covariance X Y P

/--
Uncentered second moment of two real random variables.

Formula reference: second moments are expectations of degree-two products; see
https://en.wikipedia.org/wiki/Moment_(mathematics)
-/
abbrev secondMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : RealRandomVariable Ω) : ℝ :=
  expect P (fun ω => X ω * Y ω)

theorem covariance_def {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : RealRandomVariable Ω) :
    covariance P X Y = ProbabilityTheory.covariance X Y P :=
  rfl

@[simp]
theorem variance_def {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) :
    variance P X = ProbabilityTheory.variance X P :=
  rfl

theorem covariance_eq_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : RealRandomVariable Ω) :
    covariance P X Y = ∫ ω, (X ω - mean P X) * (Y ω - mean P Y) ∂P :=
  rfl

theorem secondMoment_def {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : RealRandomVariable Ω) :
    secondMoment P X Y = expect P (fun ω => X ω * Y ω) :=
  rfl

/--
Scalar variance is nonnegative.

Formula reference: variance is an expected square and is therefore nonnegative;
see https://en.wikipedia.org/wiki/Variance
-/
theorem variance_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) :
    0 <= variance P X := by
  exact ProbabilityTheory.variance_nonneg X P

/-- Centering a measurable scalar random variable preserves its variance. -/
theorem variance_centered_eq_variance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : RealRandomVariable Ω)
    (hX : IsRealRandomVariable P X) :
    variance P (centered P X) = variance P X := by
  change ProbabilityTheory.variance (fun omega => X omega - mean P X) P =
    ProbabilityTheory.variance X P
  exact ProbabilityTheory.variance_sub_const hX.aestronglyMeasurable (mean P X)

end

end HighDimProb
