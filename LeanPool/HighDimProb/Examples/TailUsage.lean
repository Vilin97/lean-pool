/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Tail

/-!
# Tail usage examples
-/

namespace HighDimProb

open MeasureTheory

example {Ω : Type*} [MeasurableSpace Ω] (X : RealRandomVariable Ω) (t : ℝ) (ω : Ω) :
    ω ∈ upperTailEvent X t ↔ t ≤ X ω :=
  Iff.rfl

example {Ω : Type*} [MeasurableSpace Ω] (X : RealRandomVariable Ω) (t : ℝ) (ω : Ω) :
    ω ∈ lowerTailEvent X t ↔ X ω ≤ t :=
  Iff.rfl

example {Ω : Type*} [MeasurableSpace Ω] (X : RealRandomVariable Ω) (t : ℝ) (ω : Ω) :
    ω ∈ absTailEvent X t ↔ t ≤ |X ω| :=
  Iff.rfl

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : RealRandomVariable Ω) (t : ℝ) :
    absTailProb P X t = P (absTailEvent X t) :=
  rfl

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} (hX : IsRealRandomVariable P X) (t : ℝ) :
    MeasurableSet (upperTailEvent X t) :=
  measurableSet_upperTailEvent hX t

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} (hX : IsRealRandomVariable P X) (t : ℝ) :
    MeasurableSet (lowerTailEvent X t) :=
  measurableSet_lowerTailEvent hX t

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} (hX : IsRealRandomVariable P X) (t : ℝ) :
    IsMeasurableEvent (absTailEvent X t) :=
  isMeasurableEvent_absTailEvent hX t

end HighDimProb
