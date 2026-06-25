/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomVariable

/-!
# Tail events

Verified Wikipedia references:
* Tail probabilities / fat tails: https://en.wikipedia.org/wiki/Fat-tailed_distribution
* Concentration inequalities: https://en.wikipedia.org/wiki/Concentration_inequality
-/

namespace HighDimProb

open MeasureTheory

/--
Upper-tail event `{ω | t ≤ X ω}` for a real random variable.

Formula reference: tail probabilities study events of the form `P(X >= t)`;
see https://en.wikipedia.org/wiki/Fat-tailed_distribution
-/
def upperTailEvent {Ω : Type*}
    (X : RealRandomVariable Ω) (t : ℝ) : Event Ω :=
  {ω | t ≤ X ω}

/--
Lower-tail event `{ω | X ω ≤ t}` for a real random variable.

Formula reference: this is the left-tail analogue of a tail event; see
https://en.wikipedia.org/wiki/Fat-tailed_distribution
-/
def lowerTailEvent {Ω : Type*}
    (X : RealRandomVariable Ω) (t : ℝ) : Event Ω :=
  {ω | X ω ≤ t}

/--
Absolute-tail event `{ω | t ≤ |X ω|}` for a real random variable.

Formula reference: two-sided tails are commonly written as `P(|X| >= t)`; see
https://en.wikipedia.org/wiki/Concentration_inequality
-/
def absTailEvent {Ω : Type*}
    (X : RealRandomVariable Ω) (t : ℝ) : Event Ω :=
  {ω | t ≤ |X ω|}

/--
Upper-tail probability `P {ω | t ≤ X ω}`.

Formula reference: `P(X >= t)` is the upper-tail probability notation used by
tail bounds; see https://en.wikipedia.org/wiki/Concentration_inequality
-/
def upperTailProb {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (t : ℝ) : ENNReal :=
  P (upperTailEvent X t)

/--
Lower-tail probability `P {ω | X ω ≤ t}`.

Formula reference: lower-tail bounds control `P(X <= t)`; see
https://en.wikipedia.org/wiki/Concentration_inequality
-/
def lowerTailProb {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (t : ℝ) : ENNReal :=
  P (lowerTailEvent X t)

/--
Absolute-tail probability `P {ω | t ≤ |X ω|}`.

Formula reference: two-sided bounds control `P(|X| >= t)`; see
https://en.wikipedia.org/wiki/Concentration_inequality
-/
def absTailProb {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (t : ℝ) : ENNReal :=
  P (absTailEvent X t)

@[simp]
theorem mem_upperTailEvent {Ω : Type*} [MeasurableSpace Ω]
    (X : RealRandomVariable Ω) (t : ℝ) (ω : Ω) :
    ω ∈ upperTailEvent X t ↔ t ≤ X ω :=
  Iff.rfl

@[simp]
theorem mem_lowerTailEvent {Ω : Type*} [MeasurableSpace Ω]
    (X : RealRandomVariable Ω) (t : ℝ) (ω : Ω) :
    ω ∈ lowerTailEvent X t ↔ X ω ≤ t :=
  Iff.rfl

@[simp]
theorem mem_absTailEvent {Ω : Type*} [MeasurableSpace Ω]
    (X : RealRandomVariable Ω) (t : ℝ) (ω : Ω) :
    ω ∈ absTailEvent X t ↔ t ≤ |X ω| :=
  Iff.rfl

/-- A measurable real random variable has measurable upper-tail events. -/
theorem measurableSet_upperTailEvent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : RealRandomVariable Ω} (hX : IsRealRandomVariable P X) (t : ℝ) :
    MeasurableSet (upperTailEvent X t) :=
  hX measurableSet_Ici

/-- A measurable real random variable has measurable lower-tail events. -/
theorem measurableSet_lowerTailEvent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : RealRandomVariable Ω} (hX : IsRealRandomVariable P X) (t : ℝ) :
    MeasurableSet (lowerTailEvent X t) :=
  hX measurableSet_Iic

/-- A measurable real random variable has measurable absolute-tail events. -/
theorem measurableSet_absTailEvent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : RealRandomVariable Ω} (hX : IsRealRandomVariable P X) (t : ℝ) :
    MeasurableSet (absTailEvent X t) :=
  (continuous_abs.measurable.comp hX) measurableSet_Ici

/-- HighDimProb event-form version of `measurableSet_upperTailEvent`. -/
theorem isMeasurableEvent_upperTailEvent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : RealRandomVariable Ω} (hX : IsRealRandomVariable P X) (t : ℝ) :
    IsMeasurableEvent (upperTailEvent X t) :=
  measurableSet_upperTailEvent hX t

/-- HighDimProb event-form version of `measurableSet_lowerTailEvent`. -/
theorem isMeasurableEvent_lowerTailEvent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : RealRandomVariable Ω} (hX : IsRealRandomVariable P X) (t : ℝ) :
    IsMeasurableEvent (lowerTailEvent X t) :=
  measurableSet_lowerTailEvent hX t

/-- HighDimProb event-form version of `measurableSet_absTailEvent`. -/
theorem isMeasurableEvent_absTailEvent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : RealRandomVariable Ω} (hX : IsRealRandomVariable P X) (t : ℝ) :
    IsMeasurableEvent (absTailEvent X t) :=
  measurableSet_absTailEvent hX t

@[simp]
theorem upperTailProb_def {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (t : ℝ) :
    upperTailProb P X t = P (upperTailEvent X t) :=
  rfl

@[simp]
theorem lowerTailProb_def {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (t : ℝ) :
    lowerTailProb P X t = P (lowerTailEvent X t) :=
  rfl

@[simp]
theorem absTailProb_def {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (t : ℝ) :
    absTailProb P X t = P (absTailEvent X t) :=
  rfl

theorem upperTailProb_antitone {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) {s t : ℝ} (hst : s ≤ t) :
    upperTailProb P X t ≤ upperTailProb P X s :=
  measure_mono fun _ hω => hst.trans hω

theorem lowerTailProb_monotone {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) {s t : ℝ} (hst : s ≤ t) :
    lowerTailProb P X s ≤ lowerTailProb P X t :=
  measure_mono fun _ hω => hω.trans hst

theorem absTailProb_antitone {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) {s t : ℝ} (hst : s ≤ t) :
    absTailProb P X t ≤ absTailProb P X s :=
  measure_mono fun _ hω => hst.trans hω

end HighDimProb
