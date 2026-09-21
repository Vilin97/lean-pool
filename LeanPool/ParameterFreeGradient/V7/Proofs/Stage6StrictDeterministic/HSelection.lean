/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage6StrictDeterministic.AffineTrace

/-!
Selection of a hard-family scale beyond every query and output in a finite transcript.
-/

namespace V7.Stage6StrictDeterministic

/-- Oriented finite displacement maximum, with zero included explicitly. -/
def traceDisplacementBound (x0 : StrictPoint) : StrictTranscript → ℝ
  | [] => 0
  | obs :: trace => max (obs.point 0 - x0 0) (traceDisplacementBound x0 trace)

@[simp] theorem traceDisplacementBound_nil (x0 : StrictPoint) :
    traceDisplacementBound x0 [] = 0 := rfl

@[simp] theorem traceDisplacementBound_cons (x0 : StrictPoint)
    (obs : StrictObservation) (trace : StrictTranscript) :
    traceDisplacementBound x0 (obs :: trace) =
      max (obs.point 0 - x0 0) (traceDisplacementBound x0 trace) := rfl

theorem traceDisplacementBound_nonneg (x0 : StrictPoint) (trace : StrictTranscript) :
    0 ≤ traceDisplacementBound x0 trace := by
  induction trace with
  | nil => simp
  | cons obs trace ih =>
      exact ih.trans (le_max_right _ _)

theorem displacement_le_traceDisplacementBound (x0 : StrictPoint)
    {trace : StrictTranscript} {obs : StrictObservation} (hobs : obs ∈ trace) :
    obs.point 0 - x0 0 ≤ traceDisplacementBound x0 trace := by
  induction trace with
  | nil => simp at hobs
  | cons head tail ih =>
      simp only [List.mem_cons] at hobs
      rcases hobs with rfl | hobs
      · exact le_max_left _ _
      · exact (ih hobs).trans (le_max_right _ _)

/-- The transition is selected only after the complete trace and finite output
are fixed.  Adding one makes all frozen oriented bounds strict. -/
def postTranscriptH (method : StrictLocalMethod) (N : ℕ)
    (trace : StrictTranscript) : ℝ :=
  max (traceDisplacementBound method.x0 trace)
      (method.output N trace 0 - method.x0 0) + 1

theorem postTranscriptH_pos (method : StrictLocalMethod) (N : ℕ)
    (trace : StrictTranscript) : 0 < postTranscriptH method N trace := by
  have hnonneg : 0 ≤ max (traceDisplacementBound method.x0 trace)
      (method.output N trace 0 - method.x0 0) :=
    (traceDisplacementBound_nonneg method.x0 trace).trans (le_max_left _ _)
  unfold postTranscriptH
  linarith

theorem trace_displacement_lt_postTranscriptH (method : StrictLocalMethod)
    (N : ℕ) (trace : StrictTranscript) :
    ∀ obs ∈ trace, obs.point 0 - method.x0 0 < postTranscriptH method N trace := by
  intro obs hobs
  have hbound := displacement_le_traceDisplacementBound method.x0 hobs
  have hmax : traceDisplacementBound method.x0 trace ≤
      max (traceDisplacementBound method.x0 trace)
        (method.output N trace 0 - method.x0 0) := le_max_left _ _
  unfold postTranscriptH
  linarith

theorem output_displacement_lt_postTranscriptH (method : StrictLocalMethod)
    (N : ℕ) (trace : StrictTranscript) :
    method.output N trace 0 - method.x0 0 < postTranscriptH method N trace := by
  have hmax : method.output N trace 0 - method.x0 0 ≤
      max (traceDisplacementBound method.x0 trace)
        (method.output N trace 0 - method.x0 0) := le_max_right _ _
  unfold postTranscriptH
  linarith

end V7.Stage6StrictDeterministic
