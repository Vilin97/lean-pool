/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine
public import Mathlib.Data.Fintype.Sum

/-!
# TM Combinators

This file provides TM constructions for composing machines, used to prove
closure properties of complexity classes.

## Main definitions

- `TM.unionTM` — Given `tm₁ : TM n₁` deciding `L₁` and `tm₂ : TM n₂` deciding `L₂`,
  construct a `TM (n₁ + 1 + n₂)` that decides `L₁ ∪ L₂`.
- `TM.complementTM` — Given a TM deciding `L`, construct a TM (with the same
  number of work tapes) deciding `Lᶜ` by flipping the output bit.
- `TM.seqTM` — Sequential composition: run `tm₁` to completion, then `tm₂`
  on the same tapes.
- `TM.ifTM` — Conditional branching: run a test machine, then branch to a
  "then" or "else" machine based on its output.
- `TM.loopTM` — Loop combinator: repeatedly run a body machine then a test
  machine, halting when the test outputs `Γ.one`.
- `TM.scannerTM` — Generic finite-state scanner: fold a finite-state
  transition function over the input bits and emit a final symbol.
- `TM.retargetInput` — Given `M : TM k`, construct a `TM (k + 1)` that runs
  `M` but reads its "input" from work tape `k` instead of the input tape.

## Design

The union machine has three phases:

1. **Phase 1**: Simulate `tm₁`, redirecting its output to work tape `n₁`
   (a "fake output" tape). The real output tape stays pristine.
2. **Transition**: Rewind the fake output to cell 1 and check the result.
   If `Γ.one` (tm₁ accepted), write `Γ.one` to the real output and halt.
   Otherwise rewind the input tape and reset Phase-2 tapes to cell 0.
3. **Phase 2**: Simulate `tm₂` using work tapes `n₁+1..n₁+n₂`
   and the real output tape.

### Work tape layout (0-indexed)

- `0 .. n₁-1` — Phase 1's work tapes (mirrors `tm₁.work`)
- `n₁` — Phase 1's redirected output (mirrors `tm₁.output`)
- `n₁+1 .. n₁+n₂` — Phase 2's work tapes (mirrors `tm₂.work`)

### State space

`Q₁ ⊕ UnionPhase ⊕ Q₂` where `UnionPhase` encodes the four transition states
between Phase 1 and Phase 2.
-/


@[expose] public section

namespace Complexity

variable {n₁ n₂ : ℕ}

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Helpers
-- ════════════════════════════════════════════════════════════════════════

/-- Direction for an idle tape: move right if reading `▷`, else stay.
    Satisfies `δ_right_of_start` for tapes not involved in the current phase. -/
def idleDir (head : Γ) : Dir3 :=
  if head = Γ.start then .right else .stay

/-- Direction for a tape we want to move left: move left unless reading `▷`,
    in which case move right to satisfy `δ_right_of_start`. During actual
    execution the tape won't be at cell 0, so this always moves left. -/
def moveLeftDir (head : Γ) : Dir3 :=
  if head = Γ.start then .right else .left

/-- `idleDir` moves right when reading the start symbol `▷`. -/
theorem idleDir_start : idleDir Γ.start = Dir3.right := rfl
private theorem moveLeftDir_start : moveLeftDir Γ.start = Dir3.right := rfl

/-- If the head reads `▷`, then `idleDir` moves right — the shape of the
    `δ_right_of_start` obligation for idle tapes. -/
theorem idleDir_right_of_start {head : Γ} (h : head = Γ.start) : idleDir head = Dir3.right := by
  subst h; rfl

/-- If the head reads `▷`, then `moveLeftDir` moves right — the shape of the
    `δ_right_of_start` obligation for tapes being rewound. -/
theorem moveLeftDir_right_of_start {head : Γ} (h : head = Γ.start) : moveLeftDir head = Dir3.right :=
  by subst h; rfl

/-- Write back the same symbol read from a tape, preserving cell contents.
    Maps `▷` to `□` since `Tape.write` at position 0 is a no-op anyway. -/
def readBackWrite (g : Γ) : Γw :=
  match g with
  | .zero => .zero
  | .one => .one
  | .blank => .blank
  | .start => .blank

/-- `readBackWrite` recovers the original symbol away from the left-end marker. -/
theorem toΓ_readBackWrite_of_ne_start {g : Γ} (h : g ≠ Γ.start) :
    (readBackWrite g).toΓ = g := by
  cases g <;> simp_all [readBackWrite, Γw.toΓ]

/-- Writing back the symbol under an off-start head is a no-op. -/
theorem write_readBack (t : Tape) (hread : t.read ≠ Γ.start) :
    t.write (readBackWrite t.read) = t := by
  rw [Tape.write]
  split
  · rfl
  · refine Tape.ext rfl ?_
    show Function.update t.cells t.head (readBackWrite t.read).toΓ = t.cells
    rw [toΓ_readBackWrite_of_ne_start hread, Tape.read, Function.update_eq_self]

/-- Writing back the symbol under an off-start head and moving is just the move. -/
theorem writeAndMove_readBack (t : Tape) (hread : t.read ≠ Γ.start) (d : Dir3) :
    t.writeAndMove (readBackWrite t.read) d = t.move d := by
  show (t.write _).move d = t.move d
  rw [write_readBack t hread]

/-- The "do nothing" transition output: all writes are `□`, all directions
    are `idleDir`. Used for states that only change the control state. -/
def allIdle {σ : Type} {k : ℕ}
    (newState : σ) (iHead : Γ) (wHeads : Fin k → Γ) (oHead : Γ) :
    σ × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3 :=
  (newState, fun _ => .blank, .blank, idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)

/-- The content-preserving driver action: write every currently read work and
output symbol back, and use `idleDir` on every tape. Every off-start tape is
preserved exactly; a head on `▷` takes the structurally mandatory move right. -/
def allReadBack {σ : Type} {k : ℕ}
    (newState : σ) (iHead : Γ) (wHeads : Fin k → Γ) (oHead : Γ) :
    σ × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3 :=
  (newState, fun i => readBackWrite (wHeads i), readBackWrite oHead,
    idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)

/-- Proof that all-idle directions satisfy `δ_right_of_start`. -/
theorem rightOfStart_allIdle (iHead : Γ) (wHeads : Fin k → Γ) (oHead : Γ) :
    (iHead = Γ.start → idleDir iHead = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → idleDir (wHeads i) = Dir3.right) ∧
    (oHead = Γ.start → idleDir oHead = Dir3.right) :=
  ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩

/-- `allReadBack` satisfies the one-sided-tape direction invariant. -/
theorem rightOfStart_allReadBack (iHead : Γ) (wHeads : Fin k → Γ) (oHead : Γ) :
    (iHead = Γ.start → idleDir iHead = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → idleDir (wHeads i) = Dir3.right) ∧
    (oHead = Γ.start → idleDir oHead = Dir3.right) :=
  ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩

-- ════════════════════════════════════════════════════════════════════════
-- State type
-- ════════════════════════════════════════════════════════════════════════

/-- Intermediate states between Phase 1 and Phase 2 of the union machine. -/
inductive UnionPhase where
  | rewindOut    -- rewind fake output (work tape n₁) to cell 0
  | checkResult  -- at fake output cell 1: read and decide accept/continue
  | rewindIn     -- rewind input tape to cell 0
  | setup2       -- move Phase-2 tapes from cell 1 to cell 0
  deriving DecidableEq

instance : Fintype UnionPhase where
  elems := {.rewindOut, .checkResult, .rewindIn, .setup2}
  complete := fun x => by cases x <;> simp

/-- The state type for the union TM. -/
abbrev UnionQ (Q₁ Q₂ : Type) := Q₁ ⊕ UnionPhase ⊕ Q₂

-- ════════════════════════════════════════════════════════════════════════
-- Index helpers for the n₁ + 1 + n₂ work tapes
-- ════════════════════════════════════════════════════════════════════════

/-- Index of the fake output tape (work tape `n₁`). -/
def fakeOutIdx : Fin (n₁ + 1 + n₂) := ⟨n₁, by omega⟩

/-- Read tm₁'s work tapes from the composite work tapes. -/
def phase1WorkReads (wHeads : Fin (n₁ + 1 + n₂) → Γ) (i : Fin n₁) : Γ :=
  wHeads ⟨i.val, by omega⟩

/-- Read tm₂'s work tapes from the composite work tapes. -/
def phase2WorkReads (wHeads : Fin (n₁ + 1 + n₂) → Γ) (j : Fin n₂) : Γ :=
  wHeads ⟨n₁ + 1 + j.val, by omega⟩

-- ════════════════════════════════════════════════════════════════════════
-- The union TM
-- ════════════════════════════════════════════════════════════════════════

/-- Construct a TM deciding `L₁ ∪ L₂` from TMs deciding `L₁` and `L₂`.

    The composite machine has `n₁ + 1 + n₂` work tapes:
    - `0 .. n₁-1` for `tm₁`'s work tapes
    - `n₁` for `tm₁`'s redirected output
    - `n₁+1 .. n₁+n₂` for `tm₂`'s work tapes -/
def unionTM (tm₁ : TM n₁) (tm₂ : TM n₂) : TM (n₁ + 1 + n₂) :=
  haveI : Fintype tm₁.Q := tm₁.finQ
  haveI : DecidableEq tm₁.Q := tm₁.decEq
  haveI : Fintype tm₂.Q := tm₂.finQ
  haveI : DecidableEq tm₂.Q := tm₂.decEq
  { Q := UnionQ tm₁.Q tm₂.Q,
    qstart := Sum.inl tm₁.qstart,
    qhalt := Sum.inr (Sum.inr tm₂.qhalt),
    δ := fun state iHead wHeads oHead =>
    match state with
    -- ══════════════════════════════════════════════════════════════════
    -- Phase 1: simulate tm₁ with output redirected to work tape n₁
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inl q =>
      if q = tm₁.qhalt then
        -- Transition to rewind; preserve fake output value to avoid corrupting cell 1
        ( Sum.inr (Sum.inl .rewindOut),
          fun i => if i.val = n₁ then readBackWrite (wHeads fakeOutIdx) else .blank,
          .blank,
          idleDir iHead,
          fun i => idleDir (wHeads i),
          idleDir oHead )
      else
        let (q', wW, oW, iD, wD, oD) :=
          tm₁.δ q iHead (phase1WorkReads wHeads) (wHeads fakeOutIdx)
        ( Sum.inl q',
          fun i =>
            if h : i.val < n₁ then wW ⟨i.val, h⟩
            else if i.val = n₁ then oW
            else .blank,
          .blank, iD,
          fun i =>
            if h : i.val < n₁ then wD ⟨i.val, h⟩
            else if i.val = n₁ then oD
            else idleDir (wHeads i),
          idleDir oHead )
    -- ══════════════════════════════════════════════════════════════════
    -- Transition states between phases
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inr (Sum.inl m) =>
      match m with
      | .rewindOut =>
        if wHeads fakeOutIdx = Γ.start then
          -- At cell 0 → move right to cell 1
          ( Sum.inr (Sum.inl .checkResult),
            fun _ => .blank, .blank, idleDir iHead,
            fun i => if i.val = n₁ then Dir3.right else idleDir (wHeads i),
            idleDir oHead )
        else
          -- Not at cell 0 → keep moving left; preserve fake output to avoid corrupting cell 1
          ( Sum.inr (Sum.inl .rewindOut),
            fun i => if i.val = n₁ then readBackWrite (wHeads fakeOutIdx) else .blank,
            .blank, idleDir iHead,
            fun i => if i.val = n₁ then Dir3.left else idleDir (wHeads i),
            idleDir oHead )
      | .checkResult =>
        if wHeads fakeOutIdx = Γ.one then
          -- tm₁ accepted → write Γ.one to real output (at cell 1), halt
          ( Sum.inr (Sum.inr tm₂.qhalt),
            fun _ => .blank, .one, idleDir iHead,
            fun i => idleDir (wHeads i),
            idleDir oHead )
        else
          -- tm₁ rejected → proceed to rewind input
          allIdle (Sum.inr (Sum.inl .rewindIn)) iHead wHeads oHead
      | .rewindIn =>
        if iHead = Γ.start then
          -- At cell 0 → forced right by δ_right_of_start, then setup2
          ( Sum.inr (Sum.inl .setup2),
            fun _ => .blank, .blank, Dir3.right,
            fun i => idleDir (wHeads i),
            idleDir oHead )
        else
          -- Not at cell 0 → keep moving left
          ( Sum.inr (Sum.inl .rewindIn),
            fun _ => .blank, .blank, Dir3.left,
            fun i => idleDir (wHeads i),
            idleDir oHead )
      | .setup2 =>
        -- Move input, Phase-2 work tapes, and real output from cell 1 to cell 0
        ( Sum.inr (Sum.inr tm₂.qstart),
          fun _ => .blank, .blank, moveLeftDir iHead,
          fun i => if i.val ≤ n₁ then idleDir (wHeads i) else moveLeftDir (wHeads i),
          moveLeftDir oHead )
    -- ══════════════════════════════════════════════════════════════════
    -- Phase 2: simulate tm₂ with the real output tape
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inr (Sum.inr q) =>
      if q = tm₂.qhalt then
        -- Unreachable (step returns none), but δ is total
        allIdle (Sum.inr (Sum.inr tm₂.qhalt)) iHead wHeads oHead
      else
        let (q', wW, oW, iD, wD, oD) :=
          tm₂.δ q iHead (phase2WorkReads wHeads) oHead
        ( Sum.inr (Sum.inr q'),
          fun i =>
            if h : i.val ≤ n₁ then .blank
            else wW ⟨i.val - (n₁ + 1), by omega⟩,
          oW, iD,
          fun i =>
            if h : i.val ≤ n₁ then idleDir (wHeads i)
            else wD ⟨i.val - (n₁ + 1), by omega⟩,
          oD ),
    δ_right_of_start := by
      intro state iHead wHeads oHead
      match state with
      | Sum.inl q =>
        dsimp only []
        split
        · exact rightOfStart_allIdle iHead wHeads oHead
        · next hne =>
          have hδ := tm₁.δ_right_of_start q iHead (phase1WorkReads wHeads) (wHeads fakeOutIdx)
          simp only [phase1WorkReads, fakeOutIdx] at hδ
          refine ⟨hδ.1, ?_, idleDir_right_of_start⟩
          intro i hwi; simp only []
          split
          · next hi =>
            exact hδ.2.1 ⟨i.val, hi⟩ (by
              rwa [show wHeads ⟨↑i, by omega⟩ = wHeads i from by congr 1])
          · split
            · next hi hn =>
              exact hδ.2.2 (by
                rwa [show wHeads ⟨n₁, by omega⟩ = wHeads i from by congr 1; ext; simp [hn]])
            · exact idleDir_right_of_start hwi
      | Sum.inr (Sum.inl m) =>
        match m with
        | .rewindOut =>
          dsimp only [fakeOutIdx]
          by_cases hphase : wHeads fakeOutIdx = Γ.start
          all_goals simp only [fakeOutIdx] at hphase
          all_goals simp only [hphase, ite_true, ite_false]
          · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
            intro i hwi; split
            · rfl
            · exact idleDir_right_of_start hwi
          · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
            intro i hwi; split
            · next heq =>
              exfalso; apply hphase
              rwa [show wHeads ⟨n₁, by omega⟩ = wHeads i from by congr 1; ext; simp [heq]]
            · exact idleDir_right_of_start hwi
        | .checkResult =>
          dsimp only [fakeOutIdx]
          by_cases hphase : wHeads fakeOutIdx = Γ.one
          all_goals simp only [fakeOutIdx] at hphase
          all_goals simp only [hphase, ite_true, ite_false]
          · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
          · exact rightOfStart_allIdle iHead wHeads oHead
        | .rewindIn =>
          dsimp only []
          split
          · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
          · refine ⟨?_, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
            intro hiHead; next hn => exact absurd hiHead hn
        | .setup2 =>
          refine ⟨moveLeftDir_right_of_start, ?_, moveLeftDir_right_of_start⟩
          intro i hwi; simp only []; split
          · exact idleDir_right_of_start hwi
          · exact moveLeftDir_right_of_start hwi
      | Sum.inr (Sum.inr q) =>
        dsimp only []
        split
        · exact rightOfStart_allIdle iHead wHeads oHead
        · next hne =>
          have hδ := tm₂.δ_right_of_start q iHead (phase2WorkReads wHeads) oHead
          simp only [phase2WorkReads] at hδ
          refine ⟨hδ.1, ?_, hδ.2.2⟩
          intro i hwi; simp only []; split
          · exact idleDir_right_of_start hwi
          · next hi =>
            exact hδ.2.1 ⟨i.val - (n₁ + 1), by omega⟩ (by
              rwa [show wHeads ⟨n₁ + 1 + (↑i - (n₁ + 1)), by omega⟩ = wHeads i from by
                congr 1; ext; simp; omega]) }

-- ════════════════════════════════════════════════════════════════════════
-- Complement TM
-- ════════════════════════════════════════════════════════════════════════

/-- Intermediate states for the complement machine's output-flipping phase. -/
inductive ComplementPhase where
  | rewind  -- rewind output head left to cell 0, then right to cell 1
  | flip    -- at cell 1: flip the output bit and halt
  | done    -- halt state
  deriving DecidableEq

instance : Fintype ComplementPhase where
  elems := {.rewind, .flip, .done}
  complete := fun x => by cases x <;> simp

/-- The state type for the complement TM. -/
abbrev ComplementQ (Q : Type) := Q ⊕ ComplementPhase

/-- Flip a readable symbol: `1 ↔ 0`, blanks stay blank. -/
def flipBit (g : Γ) : Γw :=
  match g with
  | .one => .zero
  | .zero => .one
  | .blank => .blank
  | .start => .blank

/-- Construct a TM deciding `Lᶜ` from a TM deciding `L`.

    The complement machine has the same number of work tapes as the original.
    It runs in three stages:

    1. **Simulate**: Run the original TM. When it halts, transition to `rewind`.
    2. **Rewind**: Move the output head left to `▷` (cell 0), then right to cell 1.
    3. **Flip**: Read output cell 1, write the flipped bit, and halt. -/
def complementTM (tm : TM n) : TM n :=
  haveI : Fintype tm.Q := tm.finQ
  haveI : DecidableEq tm.Q := tm.decEq
  { Q := ComplementQ tm.Q,
    qstart := Sum.inl tm.qstart,
    qhalt := Sum.inr .done,
    δ := fun state iHead wHeads oHead =>
    match state with
    -- ══════════════════════════════════════════════════════════════════
    -- Simulation phase: run original TM
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inl q =>
      if q = tm.qhalt then
        -- Original TM halted → begin rewinding output
        -- Write back the current output symbol to preserve cell contents
        ( Sum.inr .rewind,
          fun _ => .blank,
          readBackWrite oHead,
          idleDir iHead,
          fun i => idleDir (wHeads i),
          idleDir oHead )
      else
        -- Not halted → run original δ, wrapping state in Sum.inl
        let (q', wW, oW, iD, wD, oD) := tm.δ q iHead wHeads oHead
        ( Sum.inl q', wW, oW, iD, wD, oD )
    -- ══════════════════════════════════════════════════════════════════
    -- Rewind phase: move output head left to ▷, then right to cell 1
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inr .rewind =>
      if oHead = Γ.start then
        -- At cell 0 (▷) → move right to cell 1, enter flip state
        ( Sum.inr .flip,
          fun _ => .blank,
          .blank,
          idleDir iHead,
          fun i => idleDir (wHeads i),
          Dir3.right )
      else
        -- Not at cell 0 → keep moving left, preserve output cell contents
        ( Sum.inr .rewind,
          fun _ => .blank,
          readBackWrite oHead,
          idleDir iHead,
          fun i => idleDir (wHeads i),
          Dir3.left )
    -- ══════════════════════════════════════════════════════════════════
    -- Flip phase: at cell 1, flip the output bit and halt
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inr .flip =>
      ( Sum.inr .done,
        fun _ => .blank,
        flipBit oHead,
        idleDir iHead,
        fun i => idleDir (wHeads i),
        idleDir oHead )
    -- ══════════════════════════════════════════════════════════════════
    -- Done (= qhalt): unreachable by step, but δ is total
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inr .done =>
      allIdle (Sum.inr .done) iHead wHeads oHead,
    δ_right_of_start := by
      intro state iHead wHeads oHead
      match state with
      | Sum.inl q =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
        · exact tm.δ_right_of_start q iHead wHeads oHead
      | Sum.inr .rewind =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, fun _ => rfl⟩
        · refine ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, ?_⟩
          intro h; next hn => exact absurd h hn
      | Sum.inr .flip =>
        exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      | Sum.inr .done =>
        exact rightOfStart_allIdle iHead wHeads oHead }

-- ════════════════════════════════════════════════════════════════════════
-- Conditional Branching
-- ════════════════════════════════════════════════════════════════════════

/-- Intermediate states for the conditional branching machine. -/
inductive IfPhase where
  | rewindOut  -- rewind output head left to ▷ (cell 0)
  | check      -- at cell 0, move right to cell 1, read result, branch
  | done       -- halt state (reached when either branch halts)
  deriving DecidableEq

instance : Fintype IfPhase where
  elems := {.rewindOut, .check, .done}
  complete := fun x => by cases x <;> simp

/-- The state type for the conditional branching TM. -/
abbrev IfQ (QT QThen QElse : Type) := QT ⊕ IfPhase ⊕ QThen ⊕ QElse

/-- Conditional branching: run `tmTest` to completion, read its output at
    cell 1, then run `tmThen` (if output = `Γ.one`) or `tmElse` (otherwise).

    All three machines share the same `n` work tapes, input tape, and output
    tape. Work tape contents are preserved across all transitions via
    `readBackWrite`, maintaining shared state for the branch machines.

    ## Phases

    1. **Test**: Simulate `tmTest`. When it halts, enter rewind.
    2. **Rewind output**: Move output head left to `▷` (cell 0).
    3. **Check**: Move output head right to cell 1, read the test result.
       If `Γ.one`, enter `tmThen.qstart`. Otherwise, enter `tmElse.qstart`.
    4. **Branch**: Simulate `tmThen` or `tmElse`. When the branch machine
       halts, transition to the `done` halt state.

    ## Time

    `t_test + (output_head_pos + 2) + 1 + t_branch + 1` where
    `output_head_pos ≤ t_test`. Total: at most `2·t_test + t_branch + 4`. -/
def ifTM (tmTest : TM n) (tmThen : TM n) (tmElse : TM n) : TM n :=
  haveI : Fintype tmTest.Q := tmTest.finQ
  haveI : DecidableEq tmTest.Q := tmTest.decEq
  haveI : Fintype tmThen.Q := tmThen.finQ
  haveI : DecidableEq tmThen.Q := tmThen.decEq
  haveI : Fintype tmElse.Q := tmElse.finQ
  haveI : DecidableEq tmElse.Q := tmElse.decEq
  { Q := IfQ tmTest.Q tmThen.Q tmElse.Q,
    qstart := Sum.inl tmTest.qstart,
    qhalt := Sum.inr (Sum.inl .done),
    δ := fun state iHead wHeads oHead =>
    match state with
    -- ══════════════════════════════════════════════════════════════════
    -- Test phase: simulate tmTest
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inl q =>
      if q = tmTest.qhalt then
        -- tmTest halted → begin rewinding output, preserve all tapes
        ( Sum.inr (Sum.inl .rewindOut),
          fun i => readBackWrite (wHeads i),
          readBackWrite oHead,
          idleDir iHead,
          fun i => idleDir (wHeads i),
          idleDir oHead )
      else
        let (q', wW, oW, iD, wD, oD) := tmTest.δ q iHead wHeads oHead
        ( Sum.inl q', wW, oW, iD, wD, oD )
    -- ══════════════════════════════════════════════════════════════════
    -- Transition: rewind output and check result
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inr (Sum.inl phase) =>
      match phase with
      | .rewindOut =>
        if oHead = Γ.start then
          -- At ▷ (cell 0) → move right to cell 1, enter check
          ( Sum.inr (Sum.inl .check),
            fun i => readBackWrite (wHeads i),
            .blank,
            idleDir iHead,
            fun i => idleDir (wHeads i),
            Dir3.right )
        else
          -- Not at cell 0 → keep moving left, preserve output
          ( Sum.inr (Sum.inl .rewindOut),
            fun i => readBackWrite (wHeads i),
            readBackWrite oHead,
            idleDir iHead,
            fun i => idleDir (wHeads i),
            Dir3.left )
      | .check =>
        -- At cell 1: read output and branch
        if oHead = Γ.one then
          ( Sum.inr (Sum.inr (Sum.inl tmThen.qstart)),
            fun i => readBackWrite (wHeads i),
            readBackWrite oHead,
            idleDir iHead,
            fun i => idleDir (wHeads i),
            idleDir oHead )
        else
          ( Sum.inr (Sum.inr (Sum.inr tmElse.qstart)),
            fun i => readBackWrite (wHeads i),
            readBackWrite oHead,
            idleDir iHead,
            fun i => idleDir (wHeads i),
            idleDir oHead )
      | .done =>
        allIdle (Sum.inr (Sum.inl .done)) iHead wHeads oHead
    -- ══════════════════════════════════════════════════════════════════
    -- Then branch: simulate tmThen
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inr (Sum.inr (Sum.inl q)) =>
      if q = tmThen.qhalt then
        -- tmThen halted → transition to done, preserve tapes
        ( Sum.inr (Sum.inl .done),
          fun i => readBackWrite (wHeads i),
          readBackWrite oHead,
          idleDir iHead,
          fun i => idleDir (wHeads i),
          idleDir oHead )
      else
        let (q', wW, oW, iD, wD, oD) := tmThen.δ q iHead wHeads oHead
        ( Sum.inr (Sum.inr (Sum.inl q')), wW, oW, iD, wD, oD )
    -- ══════════════════════════════════════════════════════════════════
    -- Else branch: simulate tmElse
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inr (Sum.inr (Sum.inr q)) =>
      if q = tmElse.qhalt then
        -- tmElse halted → transition to done, preserve tapes
        ( Sum.inr (Sum.inl .done),
          fun i => readBackWrite (wHeads i),
          readBackWrite oHead,
          idleDir iHead,
          fun i => idleDir (wHeads i),
          idleDir oHead )
      else
        let (q', wW, oW, iD, wD, oD) := tmElse.δ q iHead wHeads oHead
        ( Sum.inr (Sum.inr (Sum.inr q')), wW, oW, iD, wD, oD ),
    δ_right_of_start := by
      intro state iHead wHeads oHead
      match state with
      | Sum.inl q =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
        · exact tmTest.δ_right_of_start q iHead wHeads oHead
      | Sum.inr (Sum.inl phase) =>
        match phase with
        | .rewindOut =>
          dsimp only []
          split
          · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                   fun _ => rfl⟩
          · refine ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, ?_⟩
            intro h; next hn => exact absurd h hn
        | .check =>
          dsimp only []
          split <;> exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                           idleDir_right_of_start⟩
        | .done =>
          exact rightOfStart_allIdle iHead wHeads oHead
      | Sum.inr (Sum.inr (Sum.inl q)) =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
        · exact tmThen.δ_right_of_start q iHead wHeads oHead
      | Sum.inr (Sum.inr (Sum.inr q)) =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
        · exact tmElse.δ_right_of_start q iHead wHeads oHead }

-- ════════════════════════════════════════════════════════════════════════
-- Sequential Composition
-- ════════════════════════════════════════════════════════════════════════

/-- The state type for the sequential composition TM. -/
abbrev SeqQ (Q₁ Q₂ : Type) := Q₁ ⊕ Q₂

/-- Sequential composition: run tm₁ to completion, then tm₂ on the same tapes.

    Both machines share the same `n` work tapes, input tape, and output tape.
    When tm₁ halts, there is one transition step that:
    - Changes state from `Q₁` to `Q₂` (entering `tm₂.qstart`)
    - Preserves all tape cell contents (via `readBackWrite`)
    - Moves any tape head at position 0 to position 1 (forced by `δ_right_of_start`)
    - Leaves all other tape head positions unchanged

    After the transition, tm₂ runs from the resulting tape state.
    Total time: `t₁ + 1 + t₂` where `t₁` and `t₂` are the run times of
    `tm₁` and `tm₂` respectively. -/
def seqTM (tm₁ tm₂ : TM n) : TM n :=
  haveI : Fintype tm₁.Q := tm₁.finQ
  haveI : DecidableEq tm₁.Q := tm₁.decEq
  haveI : Fintype tm₂.Q := tm₂.finQ
  haveI : DecidableEq tm₂.Q := tm₂.decEq
  { Q := SeqQ tm₁.Q tm₂.Q,
    qstart := Sum.inl tm₁.qstart,
    qhalt := Sum.inr tm₂.qhalt,
    δ := fun state iHead wHeads oHead =>
    match state with
    -- ══════════════════════════════════════════════════════════════════
    -- Phase 1: simulate tm₁
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inl q =>
      if q = tm₁.qhalt then
        -- tm₁ halted → transition to tm₂.qstart, preserve tape contents
        ( Sum.inr tm₂.qstart,
          fun i => readBackWrite (wHeads i),
          readBackWrite oHead,
          idleDir iHead,
          fun i => idleDir (wHeads i),
          idleDir oHead )
      else
        -- Not halted → run tm₁.δ, wrapping state in Sum.inl
        let (q', wW, oW, iD, wD, oD) := tm₁.δ q iHead wHeads oHead
        ( Sum.inl q', wW, oW, iD, wD, oD )
    -- ══════════════════════════════════════════════════════════════════
    -- Phase 2: simulate tm₂
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inr q =>
      if q = tm₂.qhalt then
        -- Unreachable by step, but δ is total
        allIdle (Sum.inr tm₂.qhalt) iHead wHeads oHead
      else
        -- Not halted → run tm₂.δ, wrapping state in Sum.inr
        let (q', wW, oW, iD, wD, oD) := tm₂.δ q iHead wHeads oHead
        ( Sum.inr q', wW, oW, iD, wD, oD ),
    δ_right_of_start := by
      intro state iHead wHeads oHead
      match state with
      | Sum.inl q =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
        · exact tm₁.δ_right_of_start q iHead wHeads oHead
      | Sum.inr q =>
        dsimp only []
        split
        · exact rightOfStart_allIdle iHead wHeads oHead
        · exact tm₂.δ_right_of_start q iHead wHeads oHead }

-- ════════════════════════════════════════════════════════════════════════
-- Loop Combinator
-- ════════════════════════════════════════════════════════════════════════

/-- Intermediate states for the loop machine's output-checking phase. -/
inductive LoopPhase where
  | rewindOut  -- rewind output head left to ▷ (cell 0)
  | check      -- at cell 1: read output, decide continue/halt
  | done       -- halt state
  deriving DecidableEq

instance : Fintype LoopPhase where
  elems := {.rewindOut, .check, .done}
  complete := fun x => by cases x <;> simp

/-- The state type for the loop TM. -/
abbrev LoopQ (QBody QTest : Type) := QBody ⊕ LoopPhase ⊕ QTest

/-- Loop combinator: repeatedly run `tmBody` then `tmTest`, halting when
    the test's output at cell 1 is `Γ.one`.

    Both machines share the same `n` work tapes, input tape, and output tape.
    Work tape contents are preserved across transitions (via `readBackWrite`),
    allowing the body to accumulate state across iterations.

    ## Phases

    1. **Body**: Simulate `tmBody`. When it halts, transition to test.
    2. **Test**: Simulate `tmTest`. When it halts, enter rewind.
    3. **Rewind output**: Move output head left to `▷` (cell 0).
    4. **Check**: Move right to cell 1, read the test result.
       If `Γ.one`, enter `done` (halt). Otherwise, transition back to body.

    ## Use case

    The UTM's main loop: `loopTM simStepTM checkHaltTM` runs one simulation
    step, then checks if the simulated machine has halted. -/
def loopTM (tmBody : TM n) (tmTest : TM n) : TM n :=
  haveI : Fintype tmBody.Q := tmBody.finQ
  haveI : DecidableEq tmBody.Q := tmBody.decEq
  haveI : Fintype tmTest.Q := tmTest.finQ
  haveI : DecidableEq tmTest.Q := tmTest.decEq
  { Q := LoopQ tmBody.Q tmTest.Q,
    qstart := Sum.inl tmBody.qstart,
    qhalt := Sum.inr (Sum.inl .done),
    δ := fun state iHead wHeads oHead =>
    match state with
    -- ══════════════════════════════════════════════════════════════════
    -- Body phase: simulate tmBody
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inl q =>
      if q = tmBody.qhalt then
        -- Body halted → transition to test, preserve tape contents
        ( Sum.inr (Sum.inr tmTest.qstart),
          fun i => readBackWrite (wHeads i),
          readBackWrite oHead,
          idleDir iHead,
          fun i => idleDir (wHeads i),
          idleDir oHead )
      else
        let (q', wW, oW, iD, wD, oD) := tmBody.δ q iHead wHeads oHead
        ( Sum.inl q', wW, oW, iD, wD, oD )
    -- ══════════════════════════════════════════════════════════════════
    -- Transition phases: rewind and check output
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inr (Sum.inl phase) =>
      match phase with
      | .rewindOut =>
        if oHead = Γ.start then
          -- At ▷ (cell 0) → move right to cell 1, enter check
          ( Sum.inr (Sum.inl .check),
            fun i => readBackWrite (wHeads i),
            .blank,
            idleDir iHead,
            fun i => idleDir (wHeads i),
            Dir3.right )
        else
          -- Not at cell 0 → keep moving left, preserve output
          ( Sum.inr (Sum.inl .rewindOut),
            fun i => readBackWrite (wHeads i),
            readBackWrite oHead,
            idleDir iHead,
            fun i => idleDir (wHeads i),
            Dir3.left )
      | .check =>
        if oHead = Γ.one then
          -- Test output = 1: halt the loop
          ( Sum.inr (Sum.inl .done),
            fun i => readBackWrite (wHeads i),
            readBackWrite oHead,
            idleDir iHead,
            fun i => idleDir (wHeads i),
            idleDir oHead )
        else
          -- Test output ≠ 1: loop back to body
          ( Sum.inl tmBody.qstart,
            fun i => readBackWrite (wHeads i),
            readBackWrite oHead,
            idleDir iHead,
            fun i => idleDir (wHeads i),
            idleDir oHead )
      | .done =>
        allIdle (Sum.inr (Sum.inl .done)) iHead wHeads oHead
    -- ══════════════════════════════════════════════════════════════════
    -- Test phase: simulate tmTest
    -- ══════════════════════════════════════════════════════════════════
    | Sum.inr (Sum.inr q) =>
      if q = tmTest.qhalt then
        -- Test halted → begin rewinding output, preserve tapes
        ( Sum.inr (Sum.inl .rewindOut),
          fun i => readBackWrite (wHeads i),
          readBackWrite oHead,
          idleDir iHead,
          fun i => idleDir (wHeads i),
          idleDir oHead )
      else
        let (q', wW, oW, iD, wD, oD) := tmTest.δ q iHead wHeads oHead
        ( Sum.inr (Sum.inr q'), wW, oW, iD, wD, oD ),
    δ_right_of_start := by
      intro state iHead wHeads oHead
      match state with
      | Sum.inl q =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
        · exact tmBody.δ_right_of_start q iHead wHeads oHead
      | Sum.inr (Sum.inl phase) =>
        match phase with
        | .rewindOut =>
          dsimp only []
          split
          · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                   fun _ => rfl⟩
          · refine ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, ?_⟩
            intro h; next hn => exact absurd h hn
        | .check =>
          dsimp only []
          split <;> exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                           idleDir_right_of_start⟩
        | .done =>
          exact rightOfStart_allIdle iHead wHeads oHead
      | Sum.inr (Sum.inr q) =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
        · exact tmTest.δ_right_of_start q iHead wHeads oHead }

-- ════════════════════════════════════════════════════════════════════════
-- Finite-state scanner
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of a generic finite-state scanner parameterized by a
    user-supplied scan-state type `S`. The machine has a one-time `start`
    step that advances off cell 0, then a stream of `scan s` states holding
    the current scan state, and finally a `done` halt state. -/
inductive ScannerPhase (S : Type) where
  | start
  | scan (s : S)
  | done

instance {S : Type} [DecidableEq S] : DecidableEq (ScannerPhase S)
  | .start, .start => isTrue rfl
  | .start, .scan _ => isFalse (fun h => by cases h)
  | .start, .done => isFalse (fun h => by cases h)
  | .scan _, .start => isFalse (fun h => by cases h)
  | .scan _, .done => isFalse (fun h => by cases h)
  | .done, .start => isFalse (fun h => by cases h)
  | .done, .scan _ => isFalse (fun h => by cases h)
  | .done, .done => isTrue rfl
  | .scan s₁, .scan s₂ =>
    if h : s₁ = s₂ then isTrue (by rw [h])
    else isFalse (fun heq => h (by cases heq; rfl))

instance {S : Type} [DecidableEq S] [Fintype S] : Fintype (ScannerPhase S) where
  elems := insert ScannerPhase.start
           (insert (ScannerPhase.done : ScannerPhase S)
             (Finset.univ.image ScannerPhase.scan))
  complete := fun x => by
    cases x with
    | start => exact Finset.mem_insert_self _ _
    | done => exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    | scan s =>
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩

/-- **Generic finite-state scanner.**

    A 0-work-tape TM parameterized by a scan-state type `S`, an initial
    state `s₀`, a transition function `scanStep : S → Bool → S` (called on
    each input bit), and a finalizer `finalOutput : S → Γw` (the symbol to
    emit when end-of-input is reached).

    Semantics: runs left-to-right through the input, folding `scanStep` over
    the bits starting from `s₀`; when a blank is reached, writes
    `finalOutput (finalState)` to output cell 1 and halts.

    This captures the common "read once, fold into a fixed-size state"
    pattern used by `evenLength`, `allZeros`/`allOnes`, `containsZero`/`containsOne`,
    `lengthDivBy k`, `lastBit`, and similar regular-language scanners.

    Halts in `|x| + 2` steps on every input (1 start + `|x|` scans + 1 halt). -/
def scannerTM {S : Type} [DecidableEq S] [Fintype S]
    (s₀ : S) (scanStep : S → Bool → S) (finalOutput : S → Γw) : TM 0 where
  Q := ScannerPhase S
  qstart := .start
  qhalt := .done
  δ := fun state iHead _wHeads oHead =>
    match state with
    | .start =>
      -- Advance input and output from cell 0 (▷) to cell 1. Writes at cell 0
      -- are no-ops. Enter the initial scan state.
      (.scan s₀, fun i => i.elim0, .blank,
       .right, fun i => i.elim0, .right)
    | .scan s =>
      if iHead = Γ.blank then
        -- End of input. Emit `finalOutput s` and halt.
        (.done, fun i => i.elim0, finalOutput s,
         idleDir iHead, fun i => i.elim0, idleDir oHead)
      else
        -- Read a bit: `Γ.one ↦ true`, anything else (including the
        -- structurally-unreachable `Γ.start`) ↦ `false`.
        let b : Bool := decide (iHead = Γ.one)
        (.scan (scanStep s b), fun i => i.elim0, readBackWrite oHead,
         .right, fun i => i.elim0, idleDir oHead)
    | .done =>
      allIdle .done iHead _wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .start =>
      refine ⟨fun _ => rfl, fun i => i.elim0, fun _ => rfl⟩
    | .scan _ =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun i => i.elim0, idleDir_right_of_start⟩
      · exact ⟨fun _ => rfl, fun i => i.elim0, idleDir_right_of_start⟩
    | .done =>
      exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- retargetInput: read virtual input from work tape k instead of input tape
-- ════════════════════════════════════════════════════════════════════════

/-- Given a DTM `M : TM k`, construct a DTM `retargetInput M : TM (k + 1)`
    that behaves like `M` but reads its "input" from work tape `k` (the last
    work tape) instead of the real input tape.

    Tape layout:
    - Real input tape: ignored (moved idly each step, never read).
    - Work tapes `0..k-1`: mirror `M`'s work tapes.
    - Work tape `k`: plays the role of `M`'s input tape (read-only, no
      writes except a no-op `readBackWrite` that preserves cells).

    When work tape `k` is initialized with `Tape.init (z.map Γ.ofBool)`, the
    machine simulates `M` on input `z`.

    Used in `witnessLang` NTM constructions where the verifier DTM's
    "input" (e.g. `pair(x, y)`) is built on a work tape rather than
    supplied on the real input tape. -/
def retargetInput {k : ℕ} (M : TM k) : TM (k + 1) where
  Q := M.Q
  qstart := M.qstart
  qhalt := M.qhalt
  δ := fun q _iHead wHeads oHead =>
    let virtualInput : Γ := wHeads ⟨k, by omega⟩
    let innerWork : Fin k → Γ := fun i => wHeads ⟨i.val, by omega⟩
    let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
      M.δ q virtualInput innerWork oHead
    ( q',
      fun i =>
        if h : i.val < k then workWrites ⟨i.val, h⟩
        else readBackWrite virtualInput,
      outWrite,
      idleDir _iHead,
      fun i =>
        if h : i.val < k then workDirs ⟨i.val, h⟩
        else inDir,
      outDir )
  δ_right_of_start := by
    intro q iHead wHeads oHead
    have hδ := M.δ_right_of_start q (wHeads ⟨k, by omega⟩)
      (fun i => wHeads ⟨i.val, by omega⟩) oHead
    obtain ⟨hinp, hwork, hout⟩ := hδ
    refine ⟨idleDir_right_of_start, ?_, hout⟩
    intro i hwi
    dsimp only []
    split
    · next hi =>
      -- i.val < k: use M's work condition
      exact hwork ⟨i.val, hi⟩ (by
        change wHeads ⟨i.val, _⟩ = _
        rwa [show wHeads ⟨i.val, by omega⟩ = wHeads i from by congr 1])
    · next hi =>
      -- i.val = k: use M's input condition
      have hik : i.val = k := by
        have := i.isLt
        omega
      have : wHeads ⟨k, by omega⟩ = Γ.start := by
        rw [show (⟨k, by omega⟩ : Fin (k + 1)) = i from by ext; simp [hik]]
        exact hwi
      exact hinp this

end TM

end Complexity
