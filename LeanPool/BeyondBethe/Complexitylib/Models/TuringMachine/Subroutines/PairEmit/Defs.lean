/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators

/-!
# Pair emission from the input and a work tape

This file defines a small deterministic transducer that emits `pair first second`.
The first component is scanned on a designated work tape and doubled on the
output; the second component is then copied verbatim from the real input tape.
Both sources are consumed only through their first blank delimiter.

## Main definitions

- `TM.PairInputWorkPhase` — the five control phases of the emitter
- `TM.pairInputWorkTM` — emit a pair from one work tape and the input
- `TM.pairInputWorkTime` — the exact running time on canonical sources
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Control phases for `pairInputWorkTM`. `firstAgain bit` remembers the first
component bit while emitting its second copy. -/
inductive PairInputWorkPhase where
  | first
  | firstAgain (bit : Bool)
  | separator
  | second
  | done
  deriving DecidableEq

/-- `PairInputWorkPhase` is finite, as required for a Turing-machine state
space. -/
instance : Fintype PairInputWorkPhase where
  elems := {.first, .firstAgain false, .firstAgain true, .separator, .second, .done}
  complete := by
    intro state
    cases state with
    | first => simp
    | firstAgain bit => cases bit <;> simp
    | separator => simp
    | second => simp
    | done => simp

/-- Emit `pair first second`, reading `first` from work tape `firstIdx` and
`second` from the real input. Sources begin at cell one and advance to their
first blank delimiters. The output is the fresh empty tape parked at cell one
and is left immediately after the emitted pair, without a rewind. -/
def pairInputWorkTM {n : ℕ} (firstIdx : Fin n) : TM n where
  Q := PairInputWorkPhase
  qstart := .first
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .first =>
        match wHeads firstIdx with
        | .zero =>
            (.firstAgain false, fun i => readBackWrite (wHeads i), .zero,
              idleDir iHead, fun i => idleDir (wHeads i), .right)
        | .one =>
            (.firstAgain true, fun i => readBackWrite (wHeads i), .one,
              idleDir iHead, fun i => idleDir (wHeads i), .right)
        | .blank =>
            (.separator, fun i => readBackWrite (wHeads i), .zero,
              idleDir iHead, fun i => idleDir (wHeads i), .right)
        | .start => allIdle .first iHead wHeads oHead
    | .firstAgain bit =>
        (.first, fun i => readBackWrite (wHeads i), Γw.ofBool bit,
          idleDir iHead,
          fun i => if i = firstIdx then .right else idleDir (wHeads i),
          .right)
    | .separator =>
        (.second, fun i => readBackWrite (wHeads i), .one,
          idleDir iHead, fun i => idleDir (wHeads i), .right)
    | .second =>
        match iHead with
        | .zero =>
            (.second, fun i => readBackWrite (wHeads i), .zero,
              .right, fun i => idleDir (wHeads i), .right)
        | .one =>
            (.second, fun i => readBackWrite (wHeads i), .one,
              .right, fun i => idleDir (wHeads i), .right)
        | .blank =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
        | .start => allIdle .second iHead wHeads oHead
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    cases state with
    | first =>
        cases hfirst : wHeads firstIdx
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
            fun _ => rfl⟩
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
            fun _ => rfl⟩
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
            fun _ => rfl⟩
        · exact rightOfStart_allIdle iHead wHeads oHead
    | firstAgain bit =>
        refine ⟨idleDir_right_of_start, ?_, fun _ => rfl⟩
        intro i hi
        by_cases hidx : i = firstIdx
        · simp [hidx]
        · simp [hidx, idleDir_right_of_start hi]
    | separator =>
        exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
          fun _ => rfl⟩
    | second =>
        cases iHead
        · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
        · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
        · exact rightOfStart_allIdle Γ.blank wHeads oHead
        · exact rightOfStart_allIdle Γ.start wHeads oHead
    | done => exact rightOfStart_allIdle iHead wHeads oHead

/-- Exact running time of `pairInputWorkTM` on components `first` and
`second`: two steps per first-component bit, two separator steps, one step per
second-component bit, and one final blank-detection step. -/
def pairInputWorkTime (first second : List Bool) : ℕ :=
  2 * first.length + second.length + 3

end TM

end Complexity
