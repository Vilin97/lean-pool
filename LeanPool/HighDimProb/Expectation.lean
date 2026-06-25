/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomVariable

/-!
# Expectation

HighDimProb uses Mathlib integral notation for expectations. The alias in this file is only a
lightweight ergonomic wrapper for real-valued random variables.

Verified Wikipedia references:
* Expected value: https://en.wikipedia.org/wiki/Expected_value
* Law of the unconscious statistician:
  https://en.wikipedia.org/wiki/Law_of_the_unconscious_statistician
-/

namespace HighDimProb

open MeasureTheory

noncomputable section

/--
Expectation of a real-valued random variable, as a Mathlib integral.

Formula reference: expectation is represented as an integral,
`E[X] = integral X dP`; see https://en.wikipedia.org/wiki/Expected_value
-/
abbrev expect {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : ℝ :=
  ∫ ω, X ω ∂P

@[simp]
theorem expect_def {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) :
    expect P X = ∫ ω, X ω ∂P :=
  rfl

end

end HighDimProb
