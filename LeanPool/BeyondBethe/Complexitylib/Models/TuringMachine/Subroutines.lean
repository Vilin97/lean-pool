/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators

/-!
# TM Subroutines

Small concrete Turing machines used as composable building blocks for
constructing larger machines via `seqTM`, `ifTM`, and `loopTM`.

Subroutine correctness theorems live in the proof modules under
`Complexitylib.Models.TuringMachine.Subroutines.Internal`; reusable public
statements are re-exported by focused surface modules when needed.

## Main definitions

- `TM.writeTM` — write a symbol to output cell 1 and halt
- `TM.rewindWorkTM` — rewind a work tape head to cell 1
- `TM.rewindInputTM` — rewind the input tape head to cell 1
- `TM.scanRightTM` — scan a work tape right until blank
- `TM.blankWorkTM` — blank a started work tape while scanning right
- `TM.clearWorkTM` — blank a started work tape and rewind it to cell 1
- `TM.copyInputToWorkTM` — copy input tape contents to a work tape
- `TM.copyInputToOutputTM` — copy input tape contents to the output tape
- `TM.copyWorkToWorkTM` — copy one work tape's contents to another
- `TM.compareWorkTapesTM` — compare two work tapes cell by cell
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- writeTM: write a symbol to output cell 1 and halt
-- ════════════════════════════════════════════════════════════════════════

/-- State space of `writeTM`: rewind the output head to `▷`, step right to
cell 1, write the symbol, then halt. -/
inductive WritePhase where
  | rewind | goRight | write | done
  deriving DecidableEq

instance : Fintype WritePhase where
  elems := {.rewind, .goRight, .write, .done}
  complete := fun x => by cases x <;> simp

/-- Write `sym` to output cell 1 and halt.
    Phases: rewind output to ▷ → move right to cell 1 → write → halt. -/
def writeTM (sym : Γw) : TM n where
  Q := WritePhase
  qstart := .rewind
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .rewind =>
      if oHead = Γ.start then
        (.goRight, fun _ => .blank, .blank,
         idleDir iHead, fun i => idleDir (wHeads i), Dir3.right)
      else
        (.rewind, fun _ => .blank, readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), Dir3.left)
    | .goRight =>
      (.write, fun _ => .blank, .blank,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .write =>
      (.done, fun _ => .blank, sym,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .rewind =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, fun _ => rfl⟩
      · refine ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, ?_⟩
        intro h; next hn => exact absurd h hn
    | .goRight =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .write =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- `writeTM` specialized to write `Γw.one` to output cell 1 (accept). -/
abbrev writeOneTM : TM n := writeTM .one

/-- `writeTM` specialized to write `Γw.zero` to output cell 1 (reject). -/
abbrev writeZeroTM : TM n := writeTM .zero

-- ════════════════════════════════════════════════════════════════════════
-- rewindWorkTM: rewind a work tape to cell 1
-- ════════════════════════════════════════════════════════════════════════

/-- State space of `rewindWorkTM`/`rewindInputTM`: move the head left until it
reads `▷`, then move right once to land on cell 1 and halt. -/
inductive RewindPhase where
  | moveLeft | moveRight | done
  deriving DecidableEq

instance : Fintype RewindPhase where
  elems := {.moveLeft, .moveRight, .done}
  complete := fun x => by cases x <;> simp

/-- Rewind work tape `idx` to cell 1 (first data cell after ▷). -/
def rewindWorkTM (idx : Fin n) : TM n where
  Q := RewindPhase
  qstart := .moveLeft
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .moveLeft =>
      if wHeads idx = Γ.start then
        (.moveRight, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = idx then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.moveLeft,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = idx then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    | .moveRight =>
        (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .moveLeft =>
      dsimp only []; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rename_i heq; subst heq; contradiction
        · exact idleDir_right_of_start hwi
    | .moveRight =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- rewindInputTM: rewind the input tape to cell 1
-- ════════════════════════════════════════════════════════════════════════

/-- Rewind the input tape to cell 1 (first data cell after ▷). Work and
    output tapes are only written with `readBackWrite`, so their contents are
    preserved under the usual no-start-under-head side conditions. -/
def rewindInputTM : TM n where
  Q := RewindPhase
  qstart := .moveLeft
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .moveLeft =>
      if iHead = Γ.start then
        (.moveRight, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
      else
        (.moveLeft,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, moveLeftDir iHead,
         fun i => idleDir (wHeads i),
         idleDir oHead)
    | .moveRight =>
        (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .moveLeft =>
      dsimp only []; split
      · refine ⟨fun _ => rfl, ?_, idleDir_right_of_start⟩
        intro i hwi
        exact idleDir_right_of_start hwi
      · rename_i hne
        refine ⟨?_, ?_, idleDir_right_of_start⟩
        · intro hi; exact (hne hi).elim
        · intro i hwi; exact idleDir_right_of_start hwi
    | .moveRight =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- scanRightTM: scan a work tape right until blank
-- ════════════════════════════════════════════════════════════════════════

/-- State space of `scanRightTM`/`blankWorkTM`: scan right until reading
`Γ.blank`, then halt. -/
inductive ScanPhase where
  | scanning | done
  deriving DecidableEq

instance : Fintype ScanPhase where
  elems := {.scanning, .done}
  complete := fun x => by cases x <;> simp

/-- Scan work tape `idx` right until finding `Γ.blank`. On canonical binary
tapes, its exact content- and frame-preserving behavior is specified by
`scanRightTM_reachesIn_frame` and `scanRightTM_hoareTime_frame`. -/
def scanRightTM (idx : Fin n) : TM n where
  Q := ScanPhase
  qstart := .scanning
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .scanning =>
      if wHeads idx = Γ.blank then
        (.done,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else
        (.scanning,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = idx then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .done =>
        (.done,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .scanning =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
          idleDir_right_of_start⟩
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
    | .done =>
        exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
          idleDir_right_of_start⟩

-- ════════════════════════════════════════════════════════════════════════
-- blankWorkTM: blank a work tape while scanning right
-- ════════════════════════════════════════════════════════════════════════

/-- Scan work tape `idx` right until finding `Γ.blank`, overwriting every
visited nonblank cell with `Γ.blank`. This consumes a started Boolean string
and leaves the tape blank to the right of the current head. -/
def blankWorkTM (idx : Fin n) : TM n where
  Q := ScanPhase
  qstart := .scanning
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .scanning =>
      if wHeads idx = Γ.blank then
        (.done,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => idleDir (wHeads i),
         idleDir oHead)
      else
        (.scanning,
         fun i => if i = idx then .blank else readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = idx then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .scanning =>
      dsimp only []; split
      · exact rightOfStart_allIdle iHead wHeads oHead
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- Blank a started work tape and rewind it to cell `1`, yielding the standard
started blank tape shape. -/
def clearWorkTM (idx : Fin n) : TM n :=
  seqTM (blankWorkTM idx) (rewindWorkTM idx)

-- ════════════════════════════════════════════════════════════════════════
-- copyInputToWorkTM: copy input tape to a work tape
-- ════════════════════════════════════════════════════════════════════════

/-- State space shared by the input/work/output copy machines: copy symbols
rightward until the source reads `Γ.blank`, then halt. -/
inductive CopyPhase where
  | copying | done
  deriving DecidableEq

instance : Fintype CopyPhase where
  elems := {.copying, .done}
  complete := fun x => by cases x <;> simp

/-- Copy input tape data to work tape `idx`. Reads input right, writes to work tape.
    Stops when input reads `Γ.blank`. Skips ▷ at cell 0. -/
def copyInputToWorkTM (idx : Fin n) : TM n where
  Q := CopyPhase
  qstart := .copying
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .copying =>
      if iHead = Γ.blank then
        allIdle .done iHead wHeads oHead
      else
        let w : Γw := match iHead with
          | .zero => .zero | .one => .one | .blank => .blank | .start => .blank
        (.copying,
         fun i => if i = idx then w else .blank,
         .blank, Dir3.right,
         fun i => if i = idx then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .copying =>
      dsimp only []; split
      · exact rightOfStart_allIdle iHead wHeads oHead
      · refine ⟨fun _ => rfl, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- Copy the Boolean input to the output tape while scanning both tapes
rightward. The first transition skips the left-end markers, each subsequent
nonblank input symbol is written to the output, and the machine halts at the
first input blank. Work-tape contents are preserved; heads reading the
left-end marker take their required one-cell rightward bounce. -/
def copyInputToOutputTM : TM n where
  Q := CopyPhase
  qstart := .copying
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .copying =>
      if iHead = Γ.blank then
        (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else
        (.copying, fun i => readBackWrite (wHeads i), readBackWrite iHead,
         Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .copying =>
      dsimp only []
      split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
          idleDir_right_of_start⟩
      · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- Copy the contents of work tape `src` to work tape `dst`. Reads `src`
right, writes the same bits to `dst`, and stops when `src` reads `Γ.blank`.
The source tape contents are preserved by writing the currently read symbol
back before moving right. -/
def copyWorkToWorkTM (src dst : Fin n) : TM n where
  Q := CopyPhase
  qstart := .copying
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .copying =>
      if wHeads src = Γ.blank then
        (.done,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => idleDir (wHeads i),
         idleDir oHead)
      else
        let w : Γw := match wHeads src with
          | .zero => .zero | .one => .one | .blank => .blank | .start => .blank
        (.copying,
         fun i => if i = dst then w else readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = dst then Dir3.right
                  else if i = src then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .copying =>
      dsimp only []; split
      · exact rightOfStart_allIdle iHead wHeads oHead
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi
        simp only []
        split
        · rfl
        · split
          · rfl
          · exact idleDir_right_of_start hwi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- compareWorkTapesTM: compare two work tapes cell by cell
-- ════════════════════════════════════════════════════════════════════════

/-- State space of `compareWorkTapesTM`: compare cells while both tapes agree,
ending in `matchDone` (equal) or `mismatch` (unequal) before halting. -/
inductive ComparePhase where
  | comparing | mismatch | matchDone | done
  deriving DecidableEq

instance : Fintype ComparePhase where
  elems := {.comparing, .mismatch, .matchDone, .done}
  complete := fun x => by cases x <;> simp

/-- Compare work tapes `idx₁` and `idx₂` cell by cell.
    Both advance right together. Stops when both read `Γ.blank`.
    Writes `Γ.one` to output if match, `Γ.zero` if mismatch.
    Assumes output head is at cell 1. -/
def compareWorkTapesTM (idx₁ idx₂ : Fin n) : TM n where
  Q := ComparePhase
  qstart := .comparing
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .comparing =>
      if wHeads idx₁ = Γ.blank ∧ wHeads idx₂ = Γ.blank then
        (.matchDone, fun _ => .blank, .one,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else if wHeads idx₁ = wHeads idx₂ then
        (.comparing,
         fun i => if i = idx₁ then readBackWrite (wHeads idx₁)
                  else if i = idx₂ then readBackWrite (wHeads idx₂)
                  else .blank,
         .blank, idleDir iHead,
         fun i => if i = idx₁ then Dir3.right
                  else if i = idx₂ then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
      else
        (.mismatch, fun _ => .blank, .zero,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .mismatch => allIdle .done iHead wHeads oHead
    | .matchDone => allIdle .done iHead wHeads oHead
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .comparing =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      · split
        · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
          intro i hwi; simp only []; split
          · rfl
          · split
            · rfl
            · exact idleDir_right_of_start hwi
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
    | .mismatch => exact rightOfStart_allIdle iHead wHeads oHead
    | .matchDone => exact rightOfStart_allIdle iHead wHeads oHead
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

end TM

end Complexity
