/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Init

/-!
# HighDimProb basic vocabulary

This package is a thin ergonomic layer over Mathlib probability.

Verified Wikipedia reference:
https://en.wikipedia.org/wiki/Probability_space
-/

namespace HighDimProb

open MeasureTheory

/--
An event on a measurable space, represented by a set.

Formula reference: in a probability space `(Omega, F, P)`, events are subsets
of the sample space belonging to the event space; see
https://en.wikipedia.org/wiki/Probability_space
-/
abbrev Event (Ω : Type*) := Set Ω

/--
A measurable event on a measurable space.

Formula reference: this corresponds to membership in the event sigma-algebra
`F` of a probability space `(Omega, F, P)`; see
https://en.wikipedia.org/wiki/Probability_space
-/
abbrev IsMeasurableEvent {Ω : Type*} [MeasurableSpace Ω] (s : Event Ω) : Prop :=
  MeasurableSet s

@[simp]
theorem measurableEvent_iff {Ω : Type*} [MeasurableSpace Ω] (s : Event Ω) :
    IsMeasurableEvent s ↔ MeasurableSet s :=
  Iff.rfl

end HighDimProb
