/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.ProbabilitySpace

/-!
# Basic usage examples
-/

namespace HighDimProb

open MeasureTheory

example {Ω : Type*} [MeasurableSpace Ω] (s : Event Ω) :
    IsMeasurableEvent s ↔ MeasurableSet s :=
  Iff.rfl

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] :
    IsProbability P :=
  inferInstance

end HighDimProb
