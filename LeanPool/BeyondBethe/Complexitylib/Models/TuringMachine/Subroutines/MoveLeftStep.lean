/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.WipeStep

/-!
# Moving left unconditionally

Before scratch tapes can be wiped (`TM.wipeStepTM` scans rightward), every head
needs to be at a *known* position. The `▷` marker at cell `0` is immutable, so
moving left far enough always reaches it whatever the content:
`TM.moveLeftStepTM`, run enough times, is a content-agnostic bulk rewind for a
whole list of tapes, exactly as `TM.wipeStepTM` is a content-agnostic bulk wipe.

## Main results

- `TM.moveLeftStepTM` — move every targeted tape one cell left
- `TM.moveLeftStepTM_hoareTime` — its one-step contract
-/


public section

namespace Complexity

namespace TM

/-- Unconditional write-then-move collapses to a pure move whenever the
tape's only possible `▷` is at cell `0` — regardless of whether the head is
currently on it. -/
theorem writeAndMove_readBack_of_startInvariant (t : Tape) (h : Tape.StartInvariant t)
    (d : Dir3) : t.writeAndMove (readBackWrite t.read) d = t.move d := by
  by_cases hh : t.head = 0
  · show (t.write _).move d = t.move d
    congr 1
    rw [Tape.write, ite_eq_left hh]
  · exact writeAndMove_readBack t (h.read_ne_start (by omega)) d

/-- One unconditional step: every work tape named in `targets` moves left
(bouncing off `▷` via `moveLeftDir`); every other work tape, the input, and
the output are held by `readBackWrite`/`idleDir`. Content is always preserved. -/
def moveLeftStepTM {n : ℕ} (targets : List (Fin n)) : TM n where
  Q := WipeStepPhase
  qstart := .running
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .running =>
        (.done,
          fun i => readBackWrite (wHeads i),
          readBackWrite oHead, idleDir iHead,
          fun i => if i ∈ targets then moveLeftDir (wHeads i) else idleDir (wHeads i),
          idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .running =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only
        split
        · exact moveLeftDir_right_of_start hi
        · exact idleDir_right_of_start hi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- **`moveLeftStepTM`'s exact one-step Hoare contract.** Targeted tapes need
only `StartInvariant` (their `▷`, if any, is at cell `0` — true regardless of
current head position); every other work tape, the input, and the output
must be `Parked`. -/
theorem moveLeftStepTM_hoareTime {n : ℕ} (targets : List (Fin n))
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : Parked inp₀) (hout : Parked out₀)
    (htarget : ∀ i, i ∈ targets → Tape.StartInvariant (work₀ i))
    (hother : ∀ i, i ∉ targets → Parked (work₀ i)) :
    (moveLeftStepTM targets).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        ∀ i, work i = if i ∈ targets then (work₀ i).move (moveLeftDir (work₀ i).read)
          else work₀ i)
      1 := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨(⟨WipeStepPhase.done,
      inp.move (idleDir inp.read),
      (fun i => if i ∈ targets then (work i).move (moveLeftDir (work i).read)
        else (work i).writeAndMove (readBackWrite (work i).read) (idleDir (work i).read)),
      out.writeAndMove (readBackWrite out.read) (idleDir out.read)⟩ :
      Cfg n (moveLeftStepTM targets).Q),
    1, le_refl 1, ?_, rfl, hinp.move_idle, hout.writeAndMove_readBack_idle, fun i => ?_⟩
  · refine TM.reachesIn.step ?_ .zero
    simp only [TM.step, moveLeftStepTM,
      ite_eq_right (show WipeStepPhase.running ≠ WipeStepPhase.done by decide)]
    congr 1
    congr 1
    funext i
    by_cases hi : i ∈ targets
    · simp only [ite_eq_left hi]
      exact writeAndMove_readBack_of_startInvariant (work i) (htarget i hi) _
    · simp only [ite_eq_right hi]
  · dsimp only
    split
    · rfl
    · next hi => exact (hother i hi).writeAndMove_readBack_idle

end TM

end Complexity
