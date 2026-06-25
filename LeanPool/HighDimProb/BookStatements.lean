/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Distribution
import LeanPool.HighDimProb.Expectation
import LeanPool.HighDimProb.Tail

/-!
# Book statement specifications

Verified Wikipedia references:
* Pushforward measure: https://en.wikipedia.org/wiki/Pushforward_measure
* Expected value: https://en.wikipedia.org/wiki/Expected_value
* Probability distribution: https://en.wikipedia.org/wiki/Probability_distribution

This module contains typechecked `Prop` specifications for book-adjacent statements whose objects
already exist in HighDimProb. These are specifications only, not proofs of book theorems.
-/

namespace HighDimProb

open MeasureTheory

noncomputable section

/-- Specification: a measurable real random variable has measurable tail events. -/
abbrev tailEventMeasurabilityStatement {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : Prop :=
  IsRealRandomVariable P X →
    ∀ t : ℝ,
      MeasurableSet (upperTailEvent X t) ∧
        MeasurableSet (lowerTailEvent X t) ∧
          MeasurableSet (absTailEvent X t)

/-- The tail-event measurability specification follows from the Stage 1B bridge lemmas. -/
theorem tailEventMeasurabilityStatement_holds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) :
    tailEventMeasurabilityStatement P X := by
  intro hX t
  exact ⟨measurableSet_upperTailEvent hX t, measurableSet_lowerTailEvent hX t,
    measurableSet_absTailEvent hX t⟩

/-- Specification: `law` is Mathlib's pushforward measure on measurable sets. -/
abbrev lawMapApplyStatement {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : RandomVariable Ω E) : Prop :=
  Measurable X → ∀ s : Set E, MeasurableSet s → law P X s = P (X ⁻¹' s)

/-- Specification: `realLaw` is Mathlib's pushforward measure on measurable sets. -/
abbrev realLawMapApplyStatement {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : Prop :=
  IsRealRandomVariable P X →
    ∀ s : Set ℝ, MeasurableSet s → realLaw P X s = P (X ⁻¹' s)

/-- Specification: `expect` is the raw Mathlib integral notation. -/
abbrev expectAliasStatement {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : Prop :=
  expect P X = ∫ ω, X ω ∂P

/-- Specification: tail probability wrappers are direct measure applications. -/
abbrev tailProbabilityWrapperStatement {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) : Prop :=
  ∀ t : ℝ,
    upperTailProb P X t = P (upperTailEvent X t) ∧
      lowerTailProb P X t = P (lowerTailEvent X t) ∧
        absTailProb P X t = P (absTailEvent X t)

end

end HighDimProb
