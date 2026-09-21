/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Frame

/-!
# An unconditional, content-agnostic wipe step

Reusing an opaque machine's scratch tapes across calls needs them genuinely
blank in between, but an arbitrary machine may leave *gaps* — an isolated blank
cell with more content beyond it — and a content-driven scanner
(`TM.blankWorkTM` stops at the first blank) under-wipes there. `TM.wipeStepTM`
writes `Γ.blank` to every targeted tape and advances, unconditionally, never
reading what it overwrites; iterated a known number of times it blanks an exact
number of cells whatever was there.

## Main results

- `TM.wipeStepTM` — blank one cell of every targeted tape and advance
- `TM.wipeStepTM_hoareTime` — its one-step contract
-/


public section

namespace Complexity

namespace TM

/-- Control states of the unconditional wipe-step machine. -/
inductive WipeStepPhase where
  /-- Write blank to every targeted tape and advance; then halt. -/
  | running
  /-- Halted. -/
  | done
  deriving DecidableEq

instance instFintypeWipeStepPhase : Fintype WipeStepPhase where
  elems := {.running, .done}
  complete := fun p => by cases p <;> simp

/-- One unconditional step: every work tape named in `targets` is written
`Γ.blank` and its head advances right; every other work tape, the input, and
the output are held by `readBackWrite`/`idleDir`. Does not inspect the
targeted tapes' contents at all. -/
def wipeStepTM {n : ℕ} (targets : List (Fin n)) : TM n where
  Q := WipeStepPhase
  qstart := .running
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .running =>
        (.done,
          fun i => if i ∈ targets then Γw.blank else readBackWrite (wHeads i),
          readBackWrite oHead, idleDir iHead,
          fun i => if i ∈ targets then Dir3.right else idleDir (wHeads i),
          idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .running =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only
        split
        · rfl
        · exact idleDir_right_of_start hi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- **`wipeStepTM`'s exact one-step Hoare contract.** From tapes where every
non-targeted work tape, the input, and the output are `Parked`, one step
unconditionally blanks and advances every targeted work tape and preserves
everything else exactly. -/
theorem wipeStepTM_hoareTime {n : ℕ} (targets : List (Fin n))
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : Parked inp₀) (hout : Parked out₀)
    (hother : ∀ i, i ∉ targets → Parked (work₀ i)) :
    (wipeStepTM targets).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        ∀ i, work i = if i ∈ targets then (work₀ i).writeAndMove Γw.blank.toΓ Dir3.right
          else work₀ i)
      1 := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨(⟨WipeStepPhase.done,
      inp.move (idleDir inp.read),
      (fun i => if i ∈ targets then (work i).writeAndMove Γw.blank.toΓ Dir3.right
        else (work i).writeAndMove (readBackWrite (work i).read) (idleDir (work i).read)),
      out.writeAndMove (readBackWrite out.read) (idleDir out.read)⟩ :
      Cfg n (wipeStepTM targets).Q),
    1, le_refl 1, ?_, rfl, hinp.move_idle, hout.writeAndMove_readBack_idle, fun i => ?_⟩
  · refine TM.reachesIn.step ?_ .zero
    simp only [TM.step, wipeStepTM,
      if_neg (show WipeStepPhase.running ≠ WipeStepPhase.done by decide)]
    congr 1
    congr 1
    funext i
    split <;> rfl
  · dsimp only
    split
    · rfl
    · next hi => exact (hother i hi).writeAndMove_readBack_idle

end TM

end Complexity
