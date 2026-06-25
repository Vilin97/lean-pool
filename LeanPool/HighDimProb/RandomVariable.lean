/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.ProbabilitySpace

/-!
# Random variables

Random variables are functions plus Mathlib measurability assumptions.

Verified Wikipedia reference:
https://en.wikipedia.org/wiki/Random_variable
-/

namespace HighDimProb

open MeasureTheory

/--
A random variable as a bare function. Measurability is tracked separately.

Formula reference: a random variable is a measurable function from the sample
space to another measurable space; see
https://en.wikipedia.org/wiki/Random_variable
-/
abbrev RandomVariable (Ω E : Type*) := Ω → E

/--
A real-valued random variable.

Formula reference: this is the real-valued case `X : Omega -> R`; see
https://en.wikipedia.org/wiki/Random_variable
-/
abbrev RealRandomVariable (Ω : Type*) := RandomVariable Ω ℝ

/--
Measurability predicate for a random variable under a measure.

Formula reference: measurability is the defining structural condition for
random variables; see https://en.wikipedia.org/wiki/Random_variable

The measure argument is intentionally present for probability-facing APIs, even though this
measurable version does not depend on null sets.
-/
abbrev IsRandomVariable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : RandomVariable Ω E) : Prop :=
  let _ := P
  Measurable X

/-- User-facing predicate for real-valued measurable random variables. -/
abbrev IsRealRandomVariable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : Prop :=
  IsRandomVariable P X

@[simp]
theorem isRandomVariable_iff {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : RandomVariable Ω E) : IsRandomVariable P X ↔ Measurable X :=
  Iff.rfl

theorem isRealRandomVariable_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : IsRealRandomVariable P X ↔ Measurable X :=
  Iff.rfl

end HighDimProb
