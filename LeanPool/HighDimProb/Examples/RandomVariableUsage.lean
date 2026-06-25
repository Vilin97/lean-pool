/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Distribution
import LeanPool.HighDimProb.Expectation

/-!
# Random variable usage examples
-/

namespace HighDimProb

open MeasureTheory

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : RealRandomVariable Ω) (hX : IsRealRandomVariable P X) :
    Measurable X :=
  hX

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : RealRandomVariable Ω) :
    realLaw P X = Measure.map X P :=
  rfl

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : RealRandomVariable Ω) :
    expect P X = ∫ ω, X ω ∂P :=
  rfl

end HighDimProb
