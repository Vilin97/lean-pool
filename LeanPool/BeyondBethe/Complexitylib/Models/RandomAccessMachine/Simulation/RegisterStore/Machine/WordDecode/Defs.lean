/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.ForWorkOnes.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Defs

/-!
# RAM snapshot word-width decoder — definitions

`RAM.RegisterStore.Machine.wordWidthTM` is the first concrete Turing-machine
phase of the reverse RAM simulation. It scans the unary-width prefix of one
self-delimiting snapshot word and increments a canonical binary counter once
per `1`. The source head stops on the zero separator, ready for the payload
copy phase.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Scan the unary prefix on work tape `sourceIdx` and store its length in
canonical little-endian binary on work tape `widthIdx`. The two indices must
be distinct for the semantic theorem. -/
def wordWidthTM {n : ℕ} (sourceIdx widthIdx : Fin n) : TM n :=
  TM.forWorkOnesTM sourceIdx (TM.binarySuccTM widthIdx)

/-- Exact transition count for decoding a unary prefix of length `width`. -/
def wordWidthTime (width : ℕ) : ℕ :=
  TM.forWorkOnesLoopTime TM.binarySuccTime 0 width

/-- Control states for copying one fixed-width payload bit. -/
inductive PayloadBitPhase where
  | copy
  | done
  deriving DecidableEq

/-- `PayloadBitPhase` has exactly two states. -/
instance instFintypePayloadBitPhase : Fintype PayloadBitPhase where
  elems := {.copy, .done}
  complete := fun phase => by cases phase <;> simp

/-- Copy the bit under `sourceIdx` to the append position on `targetIdx`,
advancing both heads once. The semantic theorem assumes distinct indices and
that the source reads a bit. -/
def payloadBitTM {n : ℕ} (sourceIdx targetIdx : Fin n) : TM n where
  Q := PayloadBitPhase
  qstart := .copy
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .copy =>
        match wHeads sourceIdx with
        | .zero | .one =>
            (.done,
              fun i =>
                if i = targetIdx then Γw.ofBool (wHeads sourceIdx = Γ.one)
                else TM.readBackWrite (wHeads i),
              TM.readBackWrite oHead,
              TM.idleDir iHead,
              fun i =>
                if i = sourceIdx then Dir3.right
                else if i = targetIdx then Dir3.right
                else TM.idleDir (wHeads i),
              TM.idleDir oHead)
        | .blank => TM.allReadBack .done iHead wHeads oHead
        | .start => TM.allIdle .copy iHead wHeads oHead
    | .done => TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    cases state with
    | copy =>
        cases hsource : wHeads sourceIdx with
        | zero | one =>
            refine ⟨TM.idleDir_right_of_start, ?_, TM.idleDir_right_of_start⟩
            intro i hi
            by_cases his : i = sourceIdx
            · simp [his]
            · by_cases hit : i = targetIdx
              · simp [hit]
              · simp [his, hit, TM.idleDir_right_of_start hi]
        | blank => exact TM.rightOfStart_allReadBack iHead wHeads oHead
        | start => exact TM.rightOfStart_allIdle iHead wHeads oHead
    | done => exact TM.rightOfStart_allIdle iHead wHeads oHead

/-- Pairwise distinct work tapes used by the bounded payload decoder. -/
structure PayloadLoopDistinct {n : ℕ}
    (sourceIdx targetIdx counterIdx widthIdx : Fin n) : Prop where
  /-- Source and target tapes are distinct. -/
  source_target : sourceIdx ≠ targetIdx
  /-- Source and loop-counter tapes are distinct. -/
  source_counter : sourceIdx ≠ counterIdx
  /-- Source and width-limit tapes are distinct. -/
  source_width : sourceIdx ≠ widthIdx
  /-- Target and loop-counter tapes are distinct. -/
  target_counter : targetIdx ≠ counterIdx
  /-- Target and width-limit tapes are distinct. -/
  target_width : targetIdx ≠ widthIdx
  /-- Counter and width-limit tapes are distinct. -/
  counter_width : counterIdx ≠ widthIdx

/-- Copy exactly the number of payload bits recorded on `widthIdx`.
`counterIdx` is the canonical binary loop counter and `targetIdx` is an
appendable binary prefix. -/
def wordPayloadTM {n : ℕ}
    (sourceIdx targetIdx counterIdx widthIdx : Fin n) : TM n :=
  TM.binaryForTM (payloadBitTM sourceIdx targetIdx) counterIdx widthIdx

/-- Exact transition count for a complete fixed-width payload copy. -/
def wordPayloadTime (width : ℕ) : ℕ :=
  TM.binaryForLoopTime (fun _ => 1) width 0 width

/-- Control states for consuming the zero separator between a word's unary
width and fixed-width payload. -/
inductive WordSeparatorPhase where
  | skip
  | done
  deriving DecidableEq

/-- `WordSeparatorPhase` has exactly two states. -/
instance instFintypeWordSeparatorPhase : Fintype WordSeparatorPhase where
  elems := {.skip, .done}
  complete := fun phase => by cases phase <;> simp

/-- Consume exactly one zero separator on the selected source work tape. -/
def wordSeparatorTM {n : ℕ} (sourceIdx : Fin n) : TM n where
  Q := WordSeparatorPhase
  qstart := .skip
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .skip =>
        if wHeads sourceIdx = Γ.zero then
          (.done, fun i => TM.readBackWrite (wHeads i), TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i => if i = sourceIdx then Dir3.right else TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else if wHeads sourceIdx = Γ.start then
          TM.allIdle .skip iHead wHeads oHead
        else
          TM.allReadBack .done iHead wHeads oHead
    | .done => TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    cases state with
    | skip =>
        dsimp only
        split
        · refine ⟨TM.idleDir_right_of_start, ?_, TM.idleDir_right_of_start⟩
          intro i hi
          by_cases his : i = sourceIdx
          · simp [his]
          · simp [his, TM.idleDir_right_of_start hi]
        · split
          · exact TM.rightOfStart_allIdle iHead wHeads oHead
          · exact TM.rightOfStart_allReadBack iHead wHeads oHead
    | done => exact TM.rightOfStart_allIdle iHead wHeads oHead

/-- Decode one complete self-delimiting word by scanning its unary width,
consuming the separator, and copying exactly that many payload bits. -/
def wordDecodeTM {n : ℕ}
    (sourceIdx targetIdx counterIdx widthIdx : Fin n) : TM n :=
  TM.seqTM (wordWidthTM sourceIdx widthIdx)
    (TM.seqTM (wordSeparatorTM sourceIdx)
      (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx))

/-- Exact transition count for complete word decoding, including both
sequential-composition seams. -/
def wordDecodeTime (width : ℕ) : ℕ :=
  wordWidthTime width + 1 + (1 + 1 + wordPayloadTime width)

/-! ## Linear unary-marker decoder -/

/-- Pairwise-distinct source, target, and unary-marker tapes for the optimized
word decoder. -/
structure LinearWordDistinct {n : ℕ}
    (sourceIdx targetIdx markerIdx : Fin n) : Prop where
  /-- Source and target tapes are distinct. -/
  source_target : sourceIdx ≠ targetIdx
  /-- Source and marker tapes are distinct. -/
  source_marker : sourceIdx ≠ markerIdx
  /-- Target and marker tapes are distinct. -/
  target_marker : targetIdx ≠ markerIdx

/-- Control phases of the optimized self-delimiting word decoder. -/
inductive LinearWordPhase where
  /-- Copy the unary width prefix to the marker tape. -/
  | mark
  /-- Rewind the copied unary marker while parking the payload cursor. -/
  | rewind
  /-- Consume one marker and copy one payload bit per transition. -/
  | copy
  /-- Halt after the marker is exhausted. -/
  | done
  deriving DecidableEq

/-- `LinearWordPhase` has exactly four states. -/
instance instFintypeLinearWordPhase : Fintype LinearWordPhase where
  elems := {.mark, .rewind, .copy, .done}
  complete := fun phase => by cases phase <;> simp

/-- Decode one unary-width/fixed-payload word in a single linear pass.

The prefix pass copies one unary marker per width bit. After rewinding that
marker tape, the payload pass advances source, target, and marker together.
This removes the old payload loop's repeated full binary-counter comparison.
The marker tape starts as an empty appendable prefix and finishes containing
`width` ones with its head on the following blank. -/
def wordDecodeLinearTM {n : ℕ}
    (sourceIdx targetIdx markerIdx : Fin n) : TM n where
  Q := LinearWordPhase
  qstart := .mark
  qhalt := .done
  δ := fun phase iHead wHeads oHead =>
    match phase with
    | .mark =>
        match wHeads sourceIdx with
        | .one =>
            (.mark,
              fun i =>
                if i = markerIdx then Γw.one else TM.readBackWrite (wHeads i),
              TM.readBackWrite oHead,
              TM.idleDir iHead,
              fun i =>
                if i = sourceIdx then Dir3.right
                else if i = markerIdx then Dir3.right
                else TM.idleDir (wHeads i),
              TM.idleDir oHead)
        | .zero =>
            (.rewind, fun i => TM.readBackWrite (wHeads i),
              TM.readBackWrite oHead, TM.idleDir iHead,
              fun i =>
                if i = sourceIdx then Dir3.right
                else if i = markerIdx then TM.moveLeftDir (wHeads i)
                else TM.idleDir (wHeads i),
              TM.idleDir oHead)
        | .blank => TM.allReadBack .done iHead wHeads oHead
        | .start => TM.allIdle .mark iHead wHeads oHead
    | .rewind =>
        if wHeads markerIdx = Γ.start then
          (.copy, fun i => TM.readBackWrite (wHeads i),
            TM.readBackWrite oHead, TM.idleDir iHead,
            fun i =>
              if i = markerIdx then Dir3.right else TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          (.rewind, fun i => TM.readBackWrite (wHeads i),
            TM.readBackWrite oHead, TM.idleDir iHead,
            fun i =>
              if i = markerIdx then TM.moveLeftDir (wHeads i)
              else TM.idleDir (wHeads i),
            TM.idleDir oHead)
    | .copy =>
        match wHeads markerIdx with
        | .one =>
            match wHeads sourceIdx with
            | .zero | .one =>
                (.copy,
                  fun i =>
                    if i = targetIdx then
                      Γw.ofBool (wHeads sourceIdx = Γ.one)
                    else TM.readBackWrite (wHeads i),
                  TM.readBackWrite oHead, TM.idleDir iHead,
                  fun i =>
                    if i = sourceIdx then Dir3.right
                    else if i = targetIdx then Dir3.right
                    else if i = markerIdx then Dir3.right
                    else TM.idleDir (wHeads i),
                  TM.idleDir oHead)
            | .blank | .start => TM.allReadBack .done iHead wHeads oHead
        | .start =>
            (.copy, fun i => TM.readBackWrite (wHeads i),
              TM.readBackWrite oHead, TM.idleDir iHead,
              fun i =>
                if i = markerIdx then Dir3.right else TM.idleDir (wHeads i),
              TM.idleDir oHead)
        | .zero | .blank => TM.allReadBack .done iHead wHeads oHead
    | .done => TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro phase iHead wHeads oHead
    cases phase with
    | mark =>
        cases hsource : wHeads sourceIdx with
        | one =>
            refine ⟨TM.idleDir_right_of_start, ?_,
              TM.idleDir_right_of_start⟩
            intro i hi
            by_cases his : i = sourceIdx
            · simp [his]
            · by_cases him : i = markerIdx
              · simp [him]
              · simp [his, him, TM.idleDir_right_of_start hi]
        | zero =>
            refine ⟨TM.idleDir_right_of_start, ?_,
              TM.idleDir_right_of_start⟩
            intro i hi
            by_cases his : i = sourceIdx
            · simp [his]
            · by_cases him : i = markerIdx
              · subst i
                simp [his, TM.moveLeftDir_right_of_start hi]
              · simp [his, him, TM.idleDir_right_of_start hi]
        | blank => exact TM.rightOfStart_allReadBack iHead wHeads oHead
        | start => exact TM.rightOfStart_allIdle iHead wHeads oHead
    | rewind =>
        dsimp only
        split
        · refine ⟨TM.idleDir_right_of_start, ?_,
            TM.idleDir_right_of_start⟩
          intro i hi
          by_cases him : i = markerIdx
          · simp [him]
          · simp [him, TM.idleDir_right_of_start hi]
        · refine ⟨TM.idleDir_right_of_start, ?_,
            TM.idleDir_right_of_start⟩
          intro i hi
          by_cases him : i = markerIdx
          · subst i
            simpa only [if_pos] using TM.moveLeftDir_right_of_start hi
          · simp [him, TM.idleDir_right_of_start hi]
    | copy =>
        cases hmarker : wHeads markerIdx with
        | one =>
            cases hsource : wHeads sourceIdx with
            | zero | one =>
                refine ⟨TM.idleDir_right_of_start, ?_,
                  TM.idleDir_right_of_start⟩
                intro i hi
                by_cases his : i = sourceIdx
                · simp [his]
                · by_cases hit : i = targetIdx
                  · simp [hit]
                  · by_cases him : i = markerIdx
                    · simp [him]
                    · simp [his, hit, him, TM.idleDir_right_of_start hi]
            | blank | start => exact TM.rightOfStart_allReadBack iHead wHeads oHead
        | start =>
            refine ⟨TM.idleDir_right_of_start, ?_,
              TM.idleDir_right_of_start⟩
            intro i hi
            by_cases him : i = markerIdx
            · simp [him]
            · simp [him, TM.idleDir_right_of_start hi]
        | zero | blank => exact TM.rightOfStart_allReadBack iHead wHeads oHead
    | done => exact TM.rightOfStart_allIdle iHead wHeads oHead

/-- Exact transition count of the optimized decoder on a well-formed width
`width` word. -/
def wordDecodeLinearTime (width : ℕ) : ℕ :=
  3 * width + 3

end Machine

end RegisterStore

end RAM

end Complexity
