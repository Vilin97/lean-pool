/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines

/-!
# Testing a leading bit — proof internals

Every other `FP` primitive the Cobham proof uses — `Complexity.takeLen`,
`List.reverse`, `Complexity.pair`, `Cobham.mulUnpair` — fixes its output's
*length* from its inputs' lengths alone, so none of them can react to a bit's
value. `Complexity.headFlag` closes that gap by turning a bit test into a length:
the answer is carried by whether the result is empty. Its two-state transducer
moves off the left-end marker, then emits one bit exactly when the first input
bit matches.

## Main results

- `Complexity.headFlag_mem_FP` — the leading-bit test is in `FP`
-/


@[expose] public section

namespace Complexity

open Complexity.TM

/-- `[false]` when `x` begins with `target`, and `[]` otherwise: a bit test whose
answer is carried by the *length* of the result. -/
def headFlag (target : Bool) (x : List Bool) : List Bool :=
  if x.head? = some target then [false] else []

/-- Control states of the head-bit flag machine. -/
inductive HeadPhase where
  /-- Advance past the left-end markers. -/
  | skip
  /-- Read the first input bit. -/
  | test
  /-- Halted. -/
  | done
  deriving DecidableEq

instance instFintypeHeadPhase : Fintype HeadPhase where
  elems := {.skip, .test, .done}
  complete := fun p => by cases p <;> simp

/-- Read the first input bit and emit one output bit exactly when it is
`target`. Two steps: `skip` moves off the left-end markers, `test` reads the bit
and either writes or not. -/
def headFlagTM (target : Bool) : TM 0 where
  Q := HeadPhase
  qstart := .skip
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .skip =>
        (.test, fun i => readBackWrite (wHeads i), readBackWrite oHead, Dir3.right,
          fun i => idleDir (wHeads i), Dir3.right)
    | .test =>
        if iHead = Γ.ofBool target then
          (.done, fun i => readBackWrite (wHeads i), Γw.zero, idleDir iHead,
            fun i => idleDir (wHeads i), Dir3.right)
        else
          (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .skip => exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .test =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, fun _ => rfl⟩
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
            idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- Writing back the symbol already under the head changes nothing. -/
private theorem write_read_self' (t : Tape) : t.write t.read = t := by
  rw [Tape.write]
  split
  · rfl
  · exact Tape.ext rfl (Function.update_eq_self _ _)

/-- The input's first cell after the marker holds the first bit, or blank. -/
private theorem headFlagTM_read (x : List Bool) :
    ((Tape.init (x.map Γ.ofBool)).move Dir3.right).read
      = (x.head?).elim Γ.blank Γ.ofBool := by
  cases x with
  | nil => simp [Tape.read, Tape.move, Tape.init]
  | cons a t => cases a <;> simp [Tape.read, Tape.move, Tape.init, Γ.ofBool]

/-- `headFlagTM target` computes `headFlag target` in two steps. -/
theorem headFlagTM_computesInTime (target : Bool) :
    (headFlagTM target).ComputesInTime (headFlag target) (fun _ => 2) := by
  intro x
  let c1 : Cfg 0 (headFlagTM target).Q :=
    { state := HeadPhase.test
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right
      work := fun _ => (Tape.init []).writeAndMove
        (readBackWrite (Tape.init []).read) (idleDir (Tape.init []).read)
      output := (Tape.init []).move Dir3.right }
  have hstep1 : (headFlagTM target).step ((headFlagTM target).initCfg x) = some c1 := by
    simp [TM.step, headFlagTM, c1, Tape.read, Tape.init, idleDir, Tape.writeAndMove,
      Tape.write, Tape.move]
  have hread : c1.input.read = (x.head?).elim Γ.blank Γ.ofBool :=
    headFlagTM_read x
  by_cases hb : x.head? = some target
  · -- The bit matches: one output cell is written.
    have hri : c1.input.read = Γ.ofBool target := by rw [hread, hb]; rfl
    let c2 : Cfg 0 (headFlagTM target).Q :=
      { state := HeadPhase.done
        input := c1.input.move (idleDir c1.input.read)
        work := fun i => (c1.work i).writeAndMove
          (readBackWrite (c1.work i).read) (idleDir (c1.work i).read)
        output := c1.output.writeAndMove Γw.zero.toΓ Dir3.right }
    have hstep2 : (headFlagTM target).step c1 = some c2 := by
      simp [TM.step, headFlagTM, c1, c2, hri]
    refine ⟨c2, 2, le_rfl, .step hstep1 (.step hstep2 .zero), rfl, ?_⟩
    rw [headFlag, ite_eq_left hb]
    refine ⟨fun i hi => ?_, ?_⟩
    · have hi0 : i = 0 := by simpa using hi
      subst hi0
      simp [c2, c1, Tape.write, Tape.move, Tape.init, Γw.toΓ, Γ.ofBool]
    · simp [c2, c1, Tape.write, Tape.move, Tape.init, Γw.toΓ]
  · -- The bit does not match: nothing is written.
    have hri : c1.input.read ≠ Γ.ofBool target := by
      rw [hread]
      cases hx : x.head? with
      | none => cases target <;> simp [Γ.ofBool]
      | some a =>
          rw [hx] at hb
          simp only [Option.elim]
          cases a <;> cases target <;> simp_all [Γ.ofBool]
    let c2 : Cfg 0 (headFlagTM target).Q :=
      { state := HeadPhase.done
        input := c1.input.move (idleDir c1.input.read)
        work := fun i => (c1.work i).writeAndMove
          (readBackWrite (c1.work i).read) (idleDir (c1.work i).read)
        output := c1.output.writeAndMove (readBackWrite c1.output.read).toΓ
          (idleDir c1.output.read) }
    have hstep2 : (headFlagTM target).step c1 = some c2 := by
      simp [TM.step, headFlagTM, c1, c2, hri]
    refine ⟨c2, 2, le_rfl, .step hstep1 (.step hstep2 .zero), rfl, ?_⟩
    rw [headFlag, ite_eq_right hb]
    refine ⟨fun i hi => by simp at hi, ?_⟩
    have hoc : c1.output.read = Γ.blank := by
      simp [c1, Tape.read, Tape.move, Tape.init]
    have hcells : c2.output.cells = c1.output.cells := by
      show ((c1.output.write ((readBackWrite c1.output.read).toΓ)).move
        (idleDir c1.output.read)).cells = c1.output.cells
      rw [Tape.move_cells,
        show (readBackWrite c1.output.read).toΓ = c1.output.read from by rw [hoc]; rfl,
        write_read_self']
    rw [hcells]
    simp [c1, Tape.move, Tape.init]

/-- **A bit test, as a length.** -/
theorem headFlag_mem_FP (target : Bool) : headFlag target ∈ FP :=
  ⟨1, 0, headFlagTM target, (fun _ => 2), headFlagTM_computesInTime target,
    BigO.const_le_pow 2 1⟩

end Complexity
