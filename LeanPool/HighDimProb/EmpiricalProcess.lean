/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomProcess

/-!
# Empirical process vocabulary

Verified Wikipedia reference:
https://en.wikipedia.org/wiki/Empirical_process
-/

namespace HighDimProb

open MeasureTheory

/--
A finite sample of `E`-valued random variables.

Formula reference: empirical-process vocabulary is built from samples of
random variables; see https://en.wikipedia.org/wiki/Empirical_process
-/
abbrev RandomSample (Ω E : Type*) (n : ℕ) :=
  Fin n → RandomVariable Ω E

/-- Pointwise measurability predicate for finite random samples. -/
abbrev IsRandomSample {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) {n : ℕ} (X : RandomSample Ω E n) : Prop :=
  IsRandomFamily P X

/--
Evaluation of a test function over a finite random sample.

Formula reference: empirical processes evaluate classes of functions on
sample points; see https://en.wikipedia.org/wiki/Empirical_process
-/
def sampleEvaluation {Ω E : Type*} {n : ℕ}
    (X : RandomSample Ω E n) (f : E → ℝ) (ω : Ω) : Fin n → ℝ :=
  fun i => f (X i ω)

@[simp]
theorem sampleEvaluation_apply {Ω E : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : RandomSample Ω E n) (f : E → ℝ) (ω : Ω) (i : Fin n) :
    sampleEvaluation X f ω i = f (X i ω) :=
  rfl

end HighDimProb
