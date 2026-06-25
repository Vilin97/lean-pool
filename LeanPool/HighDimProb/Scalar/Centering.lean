/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Expectation
import LeanPool.HighDimProb.Lp

/-!
# Scalar centering

Verified Wikipedia reference:
* Expected value: https://en.wikipedia.org/wiki/Expected_value

Note: central moments are related background, but this file only defines
mean-zero centering and does not develop central-moment formulas.

Scalar mean, centering, and centeredness vocabulary for real random variables.
-/

namespace HighDimProb

open MeasureTheory

noncomputable section

/-- Mean of a real random variable, as the HighDimProb expectation alias. -/
abbrev mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : ℝ :=
  expect P X

/-- Centered version of a real random variable. -/
def centered {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : RealRandomVariable Ω :=
  fun ω => X ω - mean P X

/-- A real random variable is centered when its mean is zero. -/
abbrev Centered {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : Prop :=
  mean P X = 0

theorem mean_def {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) :
    mean P X = expect P X :=
  rfl

theorem mean_eq_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) :
    mean P X = ∫ ω, X ω ∂P :=
  rfl

theorem centered_apply {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (ω : Ω) :
    centered P X ω = X ω - mean P X :=
  rfl

/-- Centering preserves real-random-variable measurability. -/
theorem isRealRandomVariable_centered {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω} (hX : IsRealRandomVariable P X) :
    IsRealRandomVariable P (centered P X) := by
  dsimp [IsRealRandomVariable, IsRandomVariable, centered]
  exact hX.sub measurable_const

/-- Centering preserves integrability over a finite measure. -/
theorem integrable_centered {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] (X : RealRandomVariable Ω)
    (hX : IntegrableRealRandomVariable P X) :
    IntegrableRealRandomVariable P (centered P X) := by
  dsimp [IntegrableRealRandomVariable, IntegrableRandomVariable, centered, mean, expect]
  exact hX.sub (integrable_const _)

/-- Subtracting the mean centers an integrable real random variable. -/
theorem centered_centered {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : RealRandomVariable Ω)
    (hX : IntegrableRealRandomVariable P X) :
    Centered P (centered P X) := by
  change (∫ ω, (X ω - (∫ ω, X ω ∂P)) ∂P) = 0
  rw [integral_sub hX (integrable_const (∫ ω, X ω ∂P))]
  rw [integral_const]
  rw [measureReal_def]
  rw [measure_univ]
  rw [ENNReal.toReal_one]
  rw [one_smul]
  rw [sub_self]

end

end HighDimProb
