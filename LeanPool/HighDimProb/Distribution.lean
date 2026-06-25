/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomVariable

/-!
# Distributions and laws

The law of a random variable is `Measure.map X P`.

Verified Wikipedia references:
* Probability distribution: https://en.wikipedia.org/wiki/Probability_distribution
* Random variable: https://en.wikipedia.org/wiki/Random_variable
-/

namespace HighDimProb

open MeasureTheory

/--
Distribution/law of a random variable under a measure.

Formula reference: the law is the push-forward distribution of `P` by `X`,
implemented here as `Measure.map X P`; see
https://en.wikipedia.org/wiki/Probability_distribution
-/
noncomputable abbrev law {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : RandomVariable Ω E) : Measure E :=
  Measure.map X P

@[simp]
theorem law_def {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : RandomVariable Ω E) :
    law P X = Measure.map X P :=
  rfl

/--
Distribution/law of a real-valued random variable.

Formula reference: real-valued probability distributions are laws of real
random variables; see https://en.wikipedia.org/wiki/Probability_distribution
-/
noncomputable abbrev realLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : Measure ℝ :=
  law P X

@[simp]
theorem realLaw_def {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) :
    realLaw P X = Measure.map X P :=
  rfl

end HighDimProb
