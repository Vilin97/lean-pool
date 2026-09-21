/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineUnaryGridGenerator

/-!
# A reusable finite-word generator for square rational matrices

This is the nested-row counterpart of `machineUnaryGridGeneratorCode`.
Given a unary dimension, an accumulator bound, and an immutable payload, the
machine visits all matrix positions in row-major order.  It stores the current
row and the completed rows in reverse order, and reverses them at the two
row boundaries.  Thus its output is exactly the canonical nested-list matrix
code, not a flat list requiring an implicit decoder.

Both accumulators are explicitly clamped on malformed inputs.  The semantic
proof below shows that neither clamp is active on canonical inputs satisfying
the stated output-size bound.
-/

namespace BeyondBethe

open Complexity

def machineUnaryMatrixGeneratorDimension (word : List Bool) : List Bool :=
  machinePairFirst word

def machineUnaryMatrixGeneratorRest (word : List Bool) : List Bool :=
  machinePairSecond word

def machineUnaryMatrixGeneratorInputBound (word : List Bool) : List Bool :=
  machinePairFirst (machineUnaryMatrixGeneratorRest word)

def machineUnaryMatrixGeneratorInputPayload (word : List Bool) : List Bool :=
  machinePairSecond (machineUnaryMatrixGeneratorRest word)

def machineUnaryMatrixGeneratorPack
    (row column current rows bound done payload : List Bool) : List Bool :=
  pair row (pair column (pair current
    (pair rows (pair bound (pair done payload)))))

def machineUnaryMatrixGeneratorRow (state : List Bool) : List Bool :=
  machinePairFirst state

def machineUnaryMatrixGeneratorColumn (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineUnaryMatrixGeneratorCurrent (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

def machineUnaryMatrixGeneratorRows (state : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

def machineUnaryMatrixGeneratorBound (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond
    (machinePairSecond (machinePairSecond (machinePairSecond state))))

def machineUnaryMatrixGeneratorDone (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond
    (machinePairSecond (machinePairSecond (machinePairSecond state)))))

def machineUnaryMatrixGeneratorPayload (state : List Bool) : List Bool :=
  machinePairSecond (machinePairSecond (machinePairSecond
    (machinePairSecond (machinePairSecond (machinePairSecond state)))))

@[simp] theorem machineUnaryMatrixGeneratorRow_pack
    (row column current rows bound done payload : List Bool) :
    machineUnaryMatrixGeneratorRow
        (machineUnaryMatrixGeneratorPack row column current rows bound done payload) = row := by
  simp [machineUnaryMatrixGeneratorRow, machineUnaryMatrixGeneratorPack]

@[simp] theorem machineUnaryMatrixGeneratorColumn_pack
    (row column current rows bound done payload : List Bool) :
    machineUnaryMatrixGeneratorColumn
        (machineUnaryMatrixGeneratorPack row column current rows bound done payload) = column := by
  simp [machineUnaryMatrixGeneratorColumn, machineUnaryMatrixGeneratorPack]

@[simp] theorem machineUnaryMatrixGeneratorCurrent_pack
    (row column current rows bound done payload : List Bool) :
    machineUnaryMatrixGeneratorCurrent
        (machineUnaryMatrixGeneratorPack row column current rows bound done payload) = current := by
  simp [machineUnaryMatrixGeneratorCurrent, machineUnaryMatrixGeneratorPack]

@[simp] theorem machineUnaryMatrixGeneratorRows_pack
    (row column current rows bound done payload : List Bool) :
    machineUnaryMatrixGeneratorRows
        (machineUnaryMatrixGeneratorPack row column current rows bound done payload) = rows := by
  simp [machineUnaryMatrixGeneratorRows, machineUnaryMatrixGeneratorPack]

@[simp] theorem machineUnaryMatrixGeneratorBound_pack
    (row column current rows bound done payload : List Bool) :
    machineUnaryMatrixGeneratorBound
        (machineUnaryMatrixGeneratorPack row column current rows bound done payload) = bound := by
  simp [machineUnaryMatrixGeneratorBound, machineUnaryMatrixGeneratorPack]

@[simp] theorem machineUnaryMatrixGeneratorDone_pack
    (row column current rows bound done payload : List Bool) :
    machineUnaryMatrixGeneratorDone
        (machineUnaryMatrixGeneratorPack row column current rows bound done payload) = done := by
  simp [machineUnaryMatrixGeneratorDone, machineUnaryMatrixGeneratorPack]

@[simp] theorem machineUnaryMatrixGeneratorPayload_pack
    (row column current rows bound done payload : List Bool) :
    machineUnaryMatrixGeneratorPayload
        (machineUnaryMatrixGeneratorPack row column current rows bound done payload) = payload := by
  simp [machineUnaryMatrixGeneratorPayload, machineUnaryMatrixGeneratorPack]

def machineUnaryMatrixGeneratorStateDimension (state : List Bool) : List Bool :=
  machineUnaryMatrixGeneratorDimension
    (machineUnaryMatrixGeneratorPayload state)

def machineUnaryMatrixGeneratorEntryInput (state : List Bool) : List Bool :=
  pair (machineUnaryMatrixGeneratorRow state)
    (pair (machineUnaryMatrixGeneratorColumn state)
      (machineUnaryMatrixGeneratorInputPayload
        (machineUnaryMatrixGeneratorPayload state)))

def machineUnaryMatrixGeneratorNextRow (state : List Bool) : List Bool :=
  (machineUnaryMatrixGeneratorRow state ++ [true]).take
    (machineUnaryMatrixGeneratorPayload state).length

def machineUnaryMatrixGeneratorNextColumn (state : List Bool) : List Bool :=
  (machineUnaryMatrixGeneratorColumn state ++ [true]).take
    (machineUnaryMatrixGeneratorPayload state).length

def machineUnaryMatrixGeneratorColumnCompletesBit
    (state : List Bool) : List Bool :=
  machineHeadBit (machineUnaryRulersEqualBit
    (machineUnaryMatrixGeneratorNextColumn state)
    (machineUnaryMatrixGeneratorStateDimension state))

def machineUnaryMatrixGeneratorRowCompletesBit
    (state : List Bool) : List Bool :=
  machineHeadBit (machineUnaryRulersEqualBit
    (machineUnaryMatrixGeneratorNextRow state)
    (machineUnaryMatrixGeneratorStateDimension state))

def machineUnaryMatrixGeneratorCurrentCandidate
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  pair (entry (machineUnaryMatrixGeneratorEntryInput state))
    (machineUnaryMatrixGeneratorCurrent state)

def machineUnaryMatrixGeneratorNextCurrent
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  (machineUnaryMatrixGeneratorCurrentCandidate entry state).take
    (machineUnaryMatrixGeneratorBound state).length

def machineUnaryMatrixGeneratorCompletedRow
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  machineListReverse (machineUnaryMatrixGeneratorNextCurrent entry state)

def machineUnaryMatrixGeneratorRowsCandidate
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  pair (machineUnaryMatrixGeneratorCompletedRow entry state)
    (machineUnaryMatrixGeneratorRows state)

def machineUnaryMatrixGeneratorNextRows
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  (machineUnaryMatrixGeneratorRowsCandidate entry state).take
    (machineUnaryMatrixGeneratorBound state).length

def machineUnaryMatrixGeneratorFinish
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  machineUnaryMatrixGeneratorPack
    (machineUnaryMatrixGeneratorRow state)
    (machineUnaryMatrixGeneratorColumn state) []
    (machineUnaryMatrixGeneratorNextRows entry state)
    (machineUnaryMatrixGeneratorBound state) [true]
    (machineUnaryMatrixGeneratorPayload state)

def machineUnaryMatrixGeneratorAdvanceRow
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  machineUnaryMatrixGeneratorPack
    (machineUnaryMatrixGeneratorNextRow state) [] []
    (machineUnaryMatrixGeneratorNextRows entry state)
    (machineUnaryMatrixGeneratorBound state)
    (machineUnaryMatrixGeneratorDone state)
    (machineUnaryMatrixGeneratorPayload state)

def machineUnaryMatrixGeneratorAdvanceColumn
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  machineUnaryMatrixGeneratorPack
    (machineUnaryMatrixGeneratorRow state)
    (machineUnaryMatrixGeneratorNextColumn state)
    (machineUnaryMatrixGeneratorNextCurrent entry state)
    (machineUnaryMatrixGeneratorRows state)
    (machineUnaryMatrixGeneratorBound state)
    (machineUnaryMatrixGeneratorDone state)
    (machineUnaryMatrixGeneratorPayload state)

def machineUnaryMatrixGeneratorProcess
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  machineIfHead (machineUnaryMatrixGeneratorColumnCompletesBit state)
    (machineIfHead (machineUnaryMatrixGeneratorRowCompletesBit state)
      (machineUnaryMatrixGeneratorFinish entry state)
      (machineUnaryMatrixGeneratorAdvanceRow entry state))
    (machineUnaryMatrixGeneratorAdvanceColumn entry state)

def machineUnaryMatrixGeneratorStep
    (entry : List Bool → List Bool) (state : List Bool) : List Bool :=
  machineIfHead (machineHeadBit (machineUnaryMatrixGeneratorDone state)) state
    (machineUnaryMatrixGeneratorProcess entry state)

def machineUnaryMatrixGeneratorInit (word : List Bool) : List Bool :=
  machineUnaryMatrixGeneratorPack [] [] [] []
    (machineUnaryMatrixGeneratorInputBound word) [false] word

def machineUnaryMatrixGeneratorDimensionBits (word : List Bool) : List Bool :=
  machineLengthBits (machineUnaryMatrixGeneratorDimension word)

def machineUnaryMatrixGeneratorWorkBits (word : List Bool) : List Bool :=
  machineBinaryMulBits (pair
    (machineUnaryMatrixGeneratorDimensionBits word)
    (machineUnaryMatrixGeneratorDimensionBits word))

def machineUnaryMatrixGeneratorGuard (word : List Bool) : List Bool :=
  machineBinaryMulWidth word

def machineUnaryMatrixGeneratorRuler (word : List Bool) : List Bool :=
  machineBoundedUnary (pair (machineUnaryMatrixGeneratorGuard word)
    (machineUnaryMatrixGeneratorWorkBits word))

def machineUnaryMatrixGeneratorEnvelope (word : List Bool) : List Bool :=
  machineIteratedBinaryWidth 2 (word ++ List.replicate 16 false)

def machineUnaryMatrixGeneratorWidth (word : List Bool) : List Bool :=
  let envelope := machineUnaryMatrixGeneratorEnvelope word
  machineUnaryMatrixGeneratorPack envelope envelope envelope envelope
    envelope envelope envelope

def machineUnaryMatrixGeneratorFinalState
    (entry : List Bool → List Bool) (word : List Bool) : List Bool :=
  (machineUnaryMatrixGeneratorStep entry)^[(machineUnaryMatrixGeneratorRuler word).length]
    (machineUnaryMatrixGeneratorInit word)

def machineUnaryMatrixGeneratorReversedRowsCode
    (entry : List Bool → List Bool) (word : List Bool) : List Bool :=
  machineUnaryMatrixGeneratorRows
    (machineUnaryMatrixGeneratorFinalState entry word)

def machineUnaryMatrixGeneratorRowsCode
    (entry : List Bool → List Bool) (word : List Bool) : List Bool :=
  machineListReverse (machineUnaryMatrixGeneratorReversedRowsCode entry word)

/-! ## Polynomial-time closure

The proof is deliberately structural: each accessor and transition is built
from already verified finite-word primitives, and the bounded iterator has an
explicit polynomial state envelope.
-/

theorem machineUnaryMatrixGeneratorDimension_mem_FP :
    machineUnaryMatrixGeneratorDimension ∈ FP := machinePairFirst_mem_FP

theorem machineUnaryMatrixGeneratorRest_mem_FP :
    machineUnaryMatrixGeneratorRest ∈ FP := machinePairSecond_mem_FP

theorem machineUnaryMatrixGeneratorInputBound_mem_FP :
    machineUnaryMatrixGeneratorInputBound ∈ FP := by
  simpa only [machineUnaryMatrixGeneratorInputBound] using
    machineCompose_mem_FP machineUnaryMatrixGeneratorRest_mem_FP
      machinePairFirst_mem_FP

theorem machineUnaryMatrixGeneratorInputPayload_mem_FP :
    machineUnaryMatrixGeneratorInputPayload ∈ FP := by
  simpa only [machineUnaryMatrixGeneratorInputPayload] using
    machineCompose_mem_FP machineUnaryMatrixGeneratorRest_mem_FP
      machinePairSecond_mem_FP

theorem machineUnaryMatrixGeneratorRow_mem_FP :
    machineUnaryMatrixGeneratorRow ∈ FP := machinePairFirst_mem_FP

theorem machineUnaryMatrixGeneratorColumn_mem_FP :
    machineUnaryMatrixGeneratorColumn ∈ FP := by
  simpa only [machineUnaryMatrixGeneratorColumn] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineUnaryMatrixGeneratorCurrent_mem_FP :
    machineUnaryMatrixGeneratorCurrent ∈ FP := by
  have h := machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP
  simpa only [machineUnaryMatrixGeneratorCurrent] using
    machineCompose_mem_FP h machinePairFirst_mem_FP

theorem machineUnaryMatrixGeneratorRows_mem_FP :
    machineUnaryMatrixGeneratorRows ∈ FP := by
  have h₂ := machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP
  have h₃ := machineCompose_mem_FP h₂ machinePairSecond_mem_FP
  simpa only [machineUnaryMatrixGeneratorRows] using
    machineCompose_mem_FP h₃ machinePairFirst_mem_FP

theorem machineUnaryMatrixGeneratorBound_mem_FP :
    machineUnaryMatrixGeneratorBound ∈ FP := by
  have h₂ := machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP
  have h₃ := machineCompose_mem_FP h₂ machinePairSecond_mem_FP
  have h₄ := machineCompose_mem_FP h₃ machinePairSecond_mem_FP
  simpa only [machineUnaryMatrixGeneratorBound] using
    machineCompose_mem_FP h₄ machinePairFirst_mem_FP

theorem machineUnaryMatrixGeneratorDone_mem_FP :
    machineUnaryMatrixGeneratorDone ∈ FP := by
  have h₂ := machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP
  have h₃ := machineCompose_mem_FP h₂ machinePairSecond_mem_FP
  have h₄ := machineCompose_mem_FP h₃ machinePairSecond_mem_FP
  have h₅ := machineCompose_mem_FP h₄ machinePairSecond_mem_FP
  simpa only [machineUnaryMatrixGeneratorDone] using
    machineCompose_mem_FP h₅ machinePairFirst_mem_FP

theorem machineUnaryMatrixGeneratorPayload_mem_FP :
    machineUnaryMatrixGeneratorPayload ∈ FP := by
  have h₂ := machineCompose_mem_FP machinePairSecond_mem_FP machinePairSecond_mem_FP
  have h₃ := machineCompose_mem_FP h₂ machinePairSecond_mem_FP
  have h₄ := machineCompose_mem_FP h₃ machinePairSecond_mem_FP
  have h₅ := machineCompose_mem_FP h₄ machinePairSecond_mem_FP
  simpa only [machineUnaryMatrixGeneratorPayload] using
    machineCompose_mem_FP h₅ machinePairSecond_mem_FP

theorem machineUnaryMatrixGeneratorStateDimension_mem_FP :
    machineUnaryMatrixGeneratorStateDimension ∈ FP := by
  simpa only [machineUnaryMatrixGeneratorStateDimension] using
    machineCompose_mem_FP machineUnaryMatrixGeneratorPayload_mem_FP
      machineUnaryMatrixGeneratorDimension_mem_FP

theorem machineUnaryMatrixGeneratorEntryInput_mem_FP :
    machineUnaryMatrixGeneratorEntryInput ∈ FP := by
  have hpayload := machineCompose_mem_FP
    machineUnaryMatrixGeneratorPayload_mem_FP
    machineUnaryMatrixGeneratorInputPayload_mem_FP
  exact machinePair_mem_FP machineUnaryMatrixGeneratorRow_mem_FP
    (machinePair_mem_FP machineUnaryMatrixGeneratorColumn_mem_FP hpayload)

theorem machineUnaryMatrixGeneratorNextRow_mem_FP :
    machineUnaryMatrixGeneratorNextRow ∈ FP := by
  have happend := machineAppend_mem_FP machineUnaryMatrixGeneratorRow_mem_FP
    (machineConst_mem_FP [true])
  simpa only [machineUnaryMatrixGeneratorNextRow] using
    machineTake_mem_FP machineUnaryMatrixGeneratorPayload_mem_FP happend

theorem machineUnaryMatrixGeneratorNextColumn_mem_FP :
    machineUnaryMatrixGeneratorNextColumn ∈ FP := by
  have happend := machineAppend_mem_FP machineUnaryMatrixGeneratorColumn_mem_FP
    (machineConst_mem_FP [true])
  simpa only [machineUnaryMatrixGeneratorNextColumn] using
    machineTake_mem_FP machineUnaryMatrixGeneratorPayload_mem_FP happend

theorem machineUnaryMatrixGeneratorColumnCompletesBit_mem_FP :
    machineUnaryMatrixGeneratorColumnCompletesBit ∈ FP := by
  have heq := machineUnaryRulersEqualBit_mem_FP
    machineUnaryMatrixGeneratorNextColumn_mem_FP
    machineUnaryMatrixGeneratorStateDimension_mem_FP
  simpa only [machineUnaryMatrixGeneratorColumnCompletesBit] using
    machineCompose_mem_FP heq machineHeadBit_mem_FP

theorem machineUnaryMatrixGeneratorRowCompletesBit_mem_FP :
    machineUnaryMatrixGeneratorRowCompletesBit ∈ FP := by
  have heq := machineUnaryRulersEqualBit_mem_FP
    machineUnaryMatrixGeneratorNextRow_mem_FP
    machineUnaryMatrixGeneratorStateDimension_mem_FP
  simpa only [machineUnaryMatrixGeneratorRowCompletesBit] using
    machineCompose_mem_FP heq machineHeadBit_mem_FP

theorem machineUnaryMatrixGeneratorCurrentCandidate_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryMatrixGeneratorCurrentCandidate entry ∈ FP := by
  have hcurrentEntry := machineCompose_mem_FP
    machineUnaryMatrixGeneratorEntryInput_mem_FP hentry
  exact machinePair_mem_FP hcurrentEntry
    machineUnaryMatrixGeneratorCurrent_mem_FP

theorem machineUnaryMatrixGeneratorNextCurrent_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryMatrixGeneratorNextCurrent entry ∈ FP := by
  simpa only [machineUnaryMatrixGeneratorNextCurrent] using
    machineTake_mem_FP machineUnaryMatrixGeneratorBound_mem_FP
      (machineUnaryMatrixGeneratorCurrentCandidate_mem_FP hentry)

theorem machineUnaryMatrixGeneratorCompletedRow_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryMatrixGeneratorCompletedRow entry ∈ FP := by
  simpa only [machineUnaryMatrixGeneratorCompletedRow] using
    machineCompose_mem_FP
      (machineUnaryMatrixGeneratorNextCurrent_mem_FP hentry)
      machineListReverse_mem_FP

theorem machineUnaryMatrixGeneratorRowsCandidate_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryMatrixGeneratorRowsCandidate entry ∈ FP :=
  machinePair_mem_FP (machineUnaryMatrixGeneratorCompletedRow_mem_FP hentry)
    machineUnaryMatrixGeneratorRows_mem_FP

theorem machineUnaryMatrixGeneratorNextRows_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryMatrixGeneratorNextRows entry ∈ FP := by
  simpa only [machineUnaryMatrixGeneratorNextRows] using
    machineTake_mem_FP machineUnaryMatrixGeneratorBound_mem_FP
      (machineUnaryMatrixGeneratorRowsCandidate_mem_FP hentry)

theorem machineUnaryMatrixGeneratorFinish_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryMatrixGeneratorFinish entry ∈ FP :=
  machinePair_mem_FP machineUnaryMatrixGeneratorRow_mem_FP
    (machinePair_mem_FP machineUnaryMatrixGeneratorColumn_mem_FP
      (machinePair_mem_FP (machineConst_mem_FP [])
        (machinePair_mem_FP (machineUnaryMatrixGeneratorNextRows_mem_FP hentry)
          (machinePair_mem_FP machineUnaryMatrixGeneratorBound_mem_FP
            (machinePair_mem_FP (machineConst_mem_FP [true])
              machineUnaryMatrixGeneratorPayload_mem_FP)))))

theorem machineUnaryMatrixGeneratorAdvanceRow_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryMatrixGeneratorAdvanceRow entry ∈ FP :=
  machinePair_mem_FP machineUnaryMatrixGeneratorNextRow_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP (machineConst_mem_FP [])
        (machinePair_mem_FP (machineUnaryMatrixGeneratorNextRows_mem_FP hentry)
          (machinePair_mem_FP machineUnaryMatrixGeneratorBound_mem_FP
            (machinePair_mem_FP machineUnaryMatrixGeneratorDone_mem_FP
              machineUnaryMatrixGeneratorPayload_mem_FP)))))

theorem machineUnaryMatrixGeneratorAdvanceColumn_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryMatrixGeneratorAdvanceColumn entry ∈ FP :=
  machinePair_mem_FP machineUnaryMatrixGeneratorRow_mem_FP
    (machinePair_mem_FP machineUnaryMatrixGeneratorNextColumn_mem_FP
      (machinePair_mem_FP (machineUnaryMatrixGeneratorNextCurrent_mem_FP hentry)
        (machinePair_mem_FP machineUnaryMatrixGeneratorRows_mem_FP
          (machinePair_mem_FP machineUnaryMatrixGeneratorBound_mem_FP
            (machinePair_mem_FP machineUnaryMatrixGeneratorDone_mem_FP
              machineUnaryMatrixGeneratorPayload_mem_FP)))))

theorem machineUnaryMatrixGeneratorProcess_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryMatrixGeneratorProcess entry ∈ FP := by
  have hrow := machineIfHead_mem_FP
    machineUnaryMatrixGeneratorRowCompletesBit_mem_FP
    (machineUnaryMatrixGeneratorFinish_mem_FP hentry)
    (machineUnaryMatrixGeneratorAdvanceRow_mem_FP hentry)
  exact machineIfHead_mem_FP
    machineUnaryMatrixGeneratorColumnCompletesBit_mem_FP hrow
    (machineUnaryMatrixGeneratorAdvanceColumn_mem_FP hentry)

theorem machineUnaryMatrixGeneratorStep_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryMatrixGeneratorStep entry ∈ FP := by
  have hdone := machineCompose_mem_FP machineUnaryMatrixGeneratorDone_mem_FP
    machineHeadBit_mem_FP
  exact machineIfHead_mem_FP hdone id_mem_FP
    (machineUnaryMatrixGeneratorProcess_mem_FP hentry)

theorem machineUnaryMatrixGeneratorInit_mem_FP :
    machineUnaryMatrixGeneratorInit ∈ FP :=
  machinePair_mem_FP (machineConst_mem_FP [])
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP (machineConst_mem_FP [])
        (machinePair_mem_FP (machineConst_mem_FP [])
          (machinePair_mem_FP machineUnaryMatrixGeneratorInputBound_mem_FP
            (machinePair_mem_FP (machineConst_mem_FP [false]) id_mem_FP)))))

theorem machineUnaryMatrixGeneratorDimensionBits_mem_FP :
    machineUnaryMatrixGeneratorDimensionBits ∈ FP := by
  simpa only [machineUnaryMatrixGeneratorDimensionBits] using
    machineCompose_mem_FP machineUnaryMatrixGeneratorDimension_mem_FP
      machineLengthBits_mem_FP

theorem machineUnaryMatrixGeneratorWorkBits_mem_FP :
    machineUnaryMatrixGeneratorWorkBits ∈ FP := by
  have hinput := machinePair_mem_FP
    machineUnaryMatrixGeneratorDimensionBits_mem_FP
    machineUnaryMatrixGeneratorDimensionBits_mem_FP
  simpa only [machineUnaryMatrixGeneratorWorkBits] using
    machineCompose_mem_FP hinput machineBinaryMulBits_mem_FP

theorem machineUnaryMatrixGeneratorGuard_mem_FP :
    machineUnaryMatrixGeneratorGuard ∈ FP := machineBinaryMulWidth_mem_FP

theorem machineUnaryMatrixGeneratorRuler_mem_FP :
    machineUnaryMatrixGeneratorRuler ∈ FP := by
  have hinput := machinePair_mem_FP machineUnaryMatrixGeneratorGuard_mem_FP
    machineUnaryMatrixGeneratorWorkBits_mem_FP
  simpa only [machineUnaryMatrixGeneratorRuler] using
    machineCompose_mem_FP hinput machineBoundedUnary_mem_FP

theorem machineUnaryMatrixGeneratorEnvelope_mem_FP :
    machineUnaryMatrixGeneratorEnvelope ∈ FP := by
  have hpadded := machineAppend_mem_FP id_mem_FP
    (machineConst_mem_FP (List.replicate 16 false))
  simpa only [machineUnaryMatrixGeneratorEnvelope] using
    machineCompose_mem_FP hpadded (machineIteratedBinaryWidth_mem_FP 2)

theorem machineUnaryMatrixGeneratorWidth_mem_FP :
    machineUnaryMatrixGeneratorWidth ∈ FP := by
  let h := machineUnaryMatrixGeneratorEnvelope_mem_FP
  exact machinePair_mem_FP h
    (machinePair_mem_FP h
      (machinePair_mem_FP h
        (machinePair_mem_FP h
          (machinePair_mem_FP h (machinePair_mem_FP h h)))))

def MachineUnaryMatrixGeneratorStateBound
    (word state : List Bool) : Prop :=
  state = machineUnaryMatrixGeneratorPack
      (machineUnaryMatrixGeneratorRow state)
      (machineUnaryMatrixGeneratorColumn state)
      (machineUnaryMatrixGeneratorCurrent state)
      (machineUnaryMatrixGeneratorRows state)
      (machineUnaryMatrixGeneratorBound state)
      (machineUnaryMatrixGeneratorDone state)
      (machineUnaryMatrixGeneratorPayload state) ∧
    (machineUnaryMatrixGeneratorRow state).length ≤ word.length ∧
    (machineUnaryMatrixGeneratorColumn state).length ≤ word.length ∧
    (machineUnaryMatrixGeneratorCurrent state).length ≤
      (machineUnaryMatrixGeneratorInputBound word).length ∧
    (machineUnaryMatrixGeneratorRows state).length ≤
      (machineUnaryMatrixGeneratorInputBound word).length ∧
    machineUnaryMatrixGeneratorBound state =
      machineUnaryMatrixGeneratorInputBound word ∧
    (machineUnaryMatrixGeneratorDone state).length ≤ 1 ∧
    machineUnaryMatrixGeneratorPayload state = word

theorem machineUnaryMatrixGeneratorInit_bound (word : List Bool) :
    MachineUnaryMatrixGeneratorStateBound word
      (machineUnaryMatrixGeneratorInit word) := by
  simp [MachineUnaryMatrixGeneratorStateBound,
    machineUnaryMatrixGeneratorInit]

theorem machineUnaryMatrixGeneratorStep_bound
    {entry : List Bool → List Bool} {word state : List Bool}
    (hs : MachineUnaryMatrixGeneratorStateBound word state) :
    MachineUnaryMatrixGeneratorStateBound word
      (machineUnaryMatrixGeneratorStep entry state) := by
  rcases hs with
    ⟨hdecomp, hrow, hcolumn, hcurrent, hrows, hbound, hdone, hpayload⟩
  have hnextCurrent :
      (machineUnaryMatrixGeneratorNextCurrent entry state).length ≤
        (machineUnaryMatrixGeneratorInputBound word).length := by
    rw [machineUnaryMatrixGeneratorNextCurrent, hbound]
    exact List.length_take_le _ _
  have hnextRows :
      (machineUnaryMatrixGeneratorNextRows entry state).length ≤
        (machineUnaryMatrixGeneratorInputBound word).length := by
    rw [machineUnaryMatrixGeneratorNextRows, hbound]
    exact List.length_take_le _ _
  have hnextRow : (machineUnaryMatrixGeneratorNextRow state).length ≤
      word.length := by
    rw [machineUnaryMatrixGeneratorNextRow, hpayload]
    exact List.length_take_le _ _
  have hnextColumn : (machineUnaryMatrixGeneratorNextColumn state).length ≤
      word.length := by
    rw [machineUnaryMatrixGeneratorNextColumn, hpayload]
    exact List.length_take_le _ _
  have hfinish : MachineUnaryMatrixGeneratorStateBound word
      (machineUnaryMatrixGeneratorFinish entry state) := by
    simp only [MachineUnaryMatrixGeneratorStateBound,
      machineUnaryMatrixGeneratorFinish,
      machineUnaryMatrixGeneratorRow_pack,
      machineUnaryMatrixGeneratorColumn_pack,
      machineUnaryMatrixGeneratorCurrent_pack,
      machineUnaryMatrixGeneratorRows_pack,
      machineUnaryMatrixGeneratorBound_pack,
      machineUnaryMatrixGeneratorDone_pack,
      machineUnaryMatrixGeneratorPayload_pack]
    exact ⟨trivial, hrow, hcolumn, by simp, hnextRows, hbound, by simp,
      hpayload⟩
  have hadvanceRow : MachineUnaryMatrixGeneratorStateBound word
      (machineUnaryMatrixGeneratorAdvanceRow entry state) := by
    simp only [MachineUnaryMatrixGeneratorStateBound,
      machineUnaryMatrixGeneratorAdvanceRow,
      machineUnaryMatrixGeneratorRow_pack,
      machineUnaryMatrixGeneratorColumn_pack,
      machineUnaryMatrixGeneratorCurrent_pack,
      machineUnaryMatrixGeneratorRows_pack,
      machineUnaryMatrixGeneratorBound_pack,
      machineUnaryMatrixGeneratorDone_pack,
      machineUnaryMatrixGeneratorPayload_pack]
    exact ⟨trivial, hnextRow, by simp, by simp, hnextRows, hbound, hdone,
      hpayload⟩
  have hadvanceColumn : MachineUnaryMatrixGeneratorStateBound word
      (machineUnaryMatrixGeneratorAdvanceColumn entry state) := by
    simp only [MachineUnaryMatrixGeneratorStateBound,
      machineUnaryMatrixGeneratorAdvanceColumn,
      machineUnaryMatrixGeneratorRow_pack,
      machineUnaryMatrixGeneratorColumn_pack,
      machineUnaryMatrixGeneratorCurrent_pack,
      machineUnaryMatrixGeneratorRows_pack,
      machineUnaryMatrixGeneratorBound_pack,
      machineUnaryMatrixGeneratorDone_pack,
      machineUnaryMatrixGeneratorPayload_pack]
    exact ⟨trivial, hrow, hnextColumn, hnextCurrent, hrows, hbound, hdone,
      hpayload⟩
  rw [machineUnaryMatrixGeneratorStep]
  cases hdoneCode : machineUnaryMatrixGeneratorDone state with
  | nil =>
      rw [machineHeadBit_nil, machineIfHead_false,
        machineUnaryMatrixGeneratorProcess]
      cases hcolumnCode : machineUnaryMatrixGeneratorColumnCompletesBit state with
      | nil =>
          have hlen :
              (machineUnaryMatrixGeneratorColumnCompletesBit state).length = 1 := by
            simp [machineUnaryMatrixGeneratorColumnCompletesBit]
          rw [hcolumnCode] at hlen
          simp at hlen
      | cons columnBit columnTail =>
          cases columnBit with
          | false => rw [machineIfHead_false]; exact hadvanceColumn
          | true =>
              rw [machineIfHead_true]
              cases hrowCode : machineUnaryMatrixGeneratorRowCompletesBit state with
              | nil =>
                  have hlen :
                      (machineUnaryMatrixGeneratorRowCompletesBit state).length = 1 := by
                    simp [machineUnaryMatrixGeneratorRowCompletesBit]
                  rw [hrowCode] at hlen
                  simp at hlen
              | cons rowBit rowTail =>
                  cases rowBit with
                  | false => rw [machineIfHead_false]; exact hadvanceRow
                  | true => rw [machineIfHead_true]; exact hfinish
  | cons doneBit doneTail =>
      cases doneBit with
      | false =>
          rw [machineHeadBit_cons, machineIfHead_false,
            machineUnaryMatrixGeneratorProcess]
          cases hcolumnCode : machineUnaryMatrixGeneratorColumnCompletesBit state with
          | nil =>
              have hlen :
                  (machineUnaryMatrixGeneratorColumnCompletesBit state).length = 1 := by
                simp [machineUnaryMatrixGeneratorColumnCompletesBit]
              rw [hcolumnCode] at hlen
              simp at hlen
          | cons columnBit columnTail =>
              cases columnBit with
              | false => rw [machineIfHead_false]; exact hadvanceColumn
              | true =>
                  rw [machineIfHead_true]
                  cases hrowCode : machineUnaryMatrixGeneratorRowCompletesBit state with
                  | nil =>
                      have hlen :
                          (machineUnaryMatrixGeneratorRowCompletesBit state).length = 1 := by
                        simp [machineUnaryMatrixGeneratorRowCompletesBit]
                      rw [hrowCode] at hlen
                      simp at hlen
                  | cons rowBit rowTail =>
                      cases rowBit with
                      | false => rw [machineIfHead_false]; exact hadvanceRow
                      | true => rw [machineIfHead_true]; exact hfinish
      | true =>
          rw [machineHeadBit_cons, machineIfHead_true]
          exact ⟨hdecomp, hrow, hcolumn, hcurrent, hrows, hbound, hdone,
            hpayload⟩

theorem machineUnaryMatrixGeneratorIterate_bound
    (entry : List Bool → List Bool) (word : List Bool) : ∀ k,
    MachineUnaryMatrixGeneratorStateBound word
      ((machineUnaryMatrixGeneratorStep entry)^[k]
        (machineUnaryMatrixGeneratorInit word)) := by
  intro k
  induction k with
  | zero => exact machineUnaryMatrixGeneratorInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineUnaryMatrixGeneratorStep_bound ih

theorem machineUnaryMatrixGeneratorEnvelope_word_le (word : List Bool) :
    word.length ≤ (machineUnaryMatrixGeneratorEnvelope word).length := by
  rw [machineUnaryMatrixGeneratorEnvelope,
    machineIteratedBinaryWidth_length]
  have hpadded : word.length ≤ (word ++ List.replicate 16 false).length := by
    simp
  exact hpadded.trans (certificateExpGuardWidth_self_le 2 _)

theorem machineUnaryMatrixGeneratorEnvelope_pos (word : List Bool) :
    1 ≤ (machineUnaryMatrixGeneratorEnvelope word).length := by
  have hword := machineUnaryMatrixGeneratorEnvelope_word_le word
  by_cases hnil : word = []
  · subst word
    norm_num [machineUnaryMatrixGeneratorEnvelope,
      machineIteratedBinaryWidth_length, certificateExpGuardWidth]
  · have hpos : 0 < word.length := List.length_pos_of_ne_nil hnil
    have : 1 ≤ word.length := by omega
    omega

theorem machineUnaryMatrixGeneratorInputBound_le_envelope (word : List Bool) :
    (machineUnaryMatrixGeneratorInputBound word).length ≤
      (machineUnaryMatrixGeneratorEnvelope word).length :=
  (machinePairFirst_length_le (machineUnaryMatrixGeneratorRest word)).trans
    ((machinePairSecond_length_le word).trans
      (machineUnaryMatrixGeneratorEnvelope_word_le word))

theorem machineUnaryMatrixGeneratorIterate_length_le_width
    (entry : List Bool → List Bool) (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineUnaryMatrixGeneratorRuler word).length) :
    ((machineUnaryMatrixGeneratorStep entry)^[iterations]
      (machineUnaryMatrixGeneratorInit word)).length ≤
        (machineUnaryMatrixGeneratorWidth word).length := by
  rcases machineUnaryMatrixGeneratorIterate_bound entry word iterations with
    ⟨hdecomp, hrow, hcolumn, hcurrent, hrows, hbound, hdone, hpayload⟩
  have hwe := machineUnaryMatrixGeneratorEnvelope_word_le word
  have hbe := machineUnaryMatrixGeneratorInputBound_le_envelope word
  have hepos := machineUnaryMatrixGeneratorEnvelope_pos word
  rw [hdecomp, hbound, hpayload]
  simp only [machineUnaryMatrixGeneratorPack,
    machineUnaryMatrixGeneratorWidth, pair_length]
  omega

theorem machineUnaryMatrixGeneratorFinalState_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryMatrixGeneratorFinalState entry ∈ FP :=
  Cobham.iterate_mem_FP
    (machineUnaryMatrixGeneratorStep_mem_FP hentry)
    machineUnaryMatrixGeneratorInit_mem_FP
    machineUnaryMatrixGeneratorRuler_mem_FP
    machineUnaryMatrixGeneratorWidth_mem_FP
    (machineUnaryMatrixGeneratorIterate_length_le_width entry)

theorem machineUnaryMatrixGeneratorReversedRowsCode_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryMatrixGeneratorReversedRowsCode entry ∈ FP := by
  simpa only [machineUnaryMatrixGeneratorReversedRowsCode] using
    machineCompose_mem_FP
      (machineUnaryMatrixGeneratorFinalState_mem_FP hentry)
      machineUnaryMatrixGeneratorRows_mem_FP

theorem machineUnaryMatrixGeneratorRowsCode_mem_FP
    {entry : List Bool → List Bool} (hentry : entry ∈ FP) :
    machineUnaryMatrixGeneratorRowsCode entry ∈ FP := by
  simpa only [machineUnaryMatrixGeneratorRowsCode] using
    machineCompose_mem_FP
      (machineUnaryMatrixGeneratorReversedRowsCode_mem_FP hentry)
      machineListReverse_mem_FP

/-! ## Canonical inputs and exact traversal -/

def machineUnaryMatrixGeneratorCanonicalWord
    (m : ℕ) (bound payload : List Bool) : List Bool :=
  pair (List.replicate m true) (pair bound payload)

@[simp] theorem machineUnaryMatrixGeneratorDimension_encode
    (m : ℕ) (bound payload : List Bool) :
    machineUnaryMatrixGeneratorDimension
        (machineUnaryMatrixGeneratorCanonicalWord m bound payload) =
      List.replicate m true := by
  simp [machineUnaryMatrixGeneratorDimension,
    machineUnaryMatrixGeneratorCanonicalWord]

@[simp] theorem machineUnaryMatrixGeneratorInputBound_encode
    (m : ℕ) (bound payload : List Bool) :
    machineUnaryMatrixGeneratorInputBound
        (machineUnaryMatrixGeneratorCanonicalWord m bound payload) = bound := by
  simp [machineUnaryMatrixGeneratorInputBound,
    machineUnaryMatrixGeneratorRest,
    machineUnaryMatrixGeneratorCanonicalWord]

@[simp] theorem machineUnaryMatrixGeneratorInputPayload_encode
    (m : ℕ) (bound payload : List Bool) :
    machineUnaryMatrixGeneratorInputPayload
        (machineUnaryMatrixGeneratorCanonicalWord m bound payload) = payload := by
  simp [machineUnaryMatrixGeneratorInputPayload,
    machineUnaryMatrixGeneratorRest,
    machineUnaryMatrixGeneratorCanonicalWord]

@[simp] theorem machineUnaryMatrixGeneratorWorkBits_encode
    (m : ℕ) (bound payload : List Bool) :
    machineUnaryMatrixGeneratorWorkBits
        (machineUnaryMatrixGeneratorCanonicalWord m bound payload) =
      (m * m).bits := by
  rw [machineUnaryMatrixGeneratorWorkBits,
    machineUnaryMatrixGeneratorDimensionBits,
    machineUnaryMatrixGeneratorDimension_encode,
    machineLengthBits_encode, List.length_replicate,
    machineBinaryMulBits_pair_natBits]

theorem machineUnaryMatrixGeneratorWork_le_guard
    (m : ℕ) (bound payload : List Bool) :
    m * m ≤
      (machineUnaryMatrixGeneratorGuard
        (machineUnaryMatrixGeneratorCanonicalWord m bound payload)).length := by
  have hm : m ≤
      (machineUnaryMatrixGeneratorCanonicalWord m bound payload).length := by
    simp only [machineUnaryMatrixGeneratorCanonicalWord, pair_length,
      List.length_replicate]
    omega
  simp only [machineUnaryMatrixGeneratorGuard, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith

@[simp] theorem machineUnaryMatrixGeneratorRuler_encode
    (m : ℕ) (bound payload : List Bool) :
    machineUnaryMatrixGeneratorRuler
        (machineUnaryMatrixGeneratorCanonicalWord m bound payload) =
      List.replicate (m * m) true := by
  rw [machineUnaryMatrixGeneratorRuler,
    machineUnaryMatrixGeneratorWorkBits_encode,
    machineBoundedUnary_encode_of_le]
  exact machineUnaryMatrixGeneratorWork_le_guard m bound payload

/-! ## Typed row-major semantics -/

def unaryMatrixRows {m : ℕ}
    (f : Fin m → Fin m → ℚ) : List (List ℚ) :=
  List.ofFn fun i ↦ List.ofFn fun j ↦ f i j

@[simp] theorem unaryMatrixRows_length {m : ℕ}
    (f : Fin m → Fin m → ℚ) : (unaryMatrixRows f).length = m := by
  simp [unaryMatrixRows]

@[simp] theorem unaryMatrixRows_getElem {m : ℕ}
    (f : Fin m → Fin m → ℚ) (i : ℕ) (hi : i < (unaryMatrixRows f).length) :
    (unaryMatrixRows f)[i] =
      List.ofFn (f ⟨i, by simpa using hi⟩) := by
  simp [unaryMatrixRows]

def unaryMatrixCurrent {m : ℕ}
    (f : Fin m → Fin m → ℚ) (state : UnaryGridSemanticState m) : List ℚ :=
  if state.done then []
  else (List.ofFn (f state.row)).take state.column.1 |>.reverse

def unaryMatrixCompletedRows {m : ℕ}
    (f : Fin m → Fin m → ℚ) (state : UnaryGridSemanticState m) :
    List (List ℚ) :=
  if state.done then (unaryMatrixRows f).reverse
  else ((unaryMatrixRows f).take state.row.1).reverse

def machineUnaryMatrixGeneratorSemanticCode {m : ℕ}
    (f : Fin m → Fin m → ℚ) (bound payload : List Bool)
    (state : UnaryGridSemanticState m) : List Bool :=
  machineUnaryMatrixGeneratorPack
    (List.replicate state.row.1 true)
    (List.replicate state.column.1 true)
    (binaryListCode rationalEntryBinaryCode (unaryMatrixCurrent f state))
    (binaryListCode (binaryListCode rationalEntryBinaryCode)
      (unaryMatrixCompletedRows f state))
    bound [state.done]
    (machineUnaryMatrixGeneratorCanonicalWord m bound payload)

@[simp] theorem machineUnaryMatrixGeneratorEntryInput_semanticCode {m : ℕ}
    (f : Fin m → Fin m → ℚ) (bound payload : List Bool)
    (state : UnaryGridSemanticState m) :
    machineUnaryMatrixGeneratorEntryInput
        (machineUnaryMatrixGeneratorSemanticCode f bound payload state) =
      pair (List.replicate state.row.1 true)
        (pair (List.replicate state.column.1 true) payload) := by
  simp [machineUnaryMatrixGeneratorEntryInput,
    machineUnaryMatrixGeneratorSemanticCode]

@[simp] theorem machineUnaryMatrixGeneratorNextRow_semanticCode {m : ℕ}
    (f : Fin m → Fin m → ℚ) (bound payload : List Bool)
    (state : UnaryGridSemanticState m) :
    machineUnaryMatrixGeneratorNextRow
        (machineUnaryMatrixGeneratorSemanticCode f bound payload state) =
      List.replicate (state.row.1 + 1) true := by
  have hlength : state.row.1 + 1 ≤
      (machineUnaryMatrixGeneratorCanonicalWord m bound payload).length := by
    have hrow : state.row.1 + 1 ≤ m := by omega
    have hm : m ≤
        (machineUnaryMatrixGeneratorCanonicalWord m bound payload).length := by
      simp only [machineUnaryMatrixGeneratorCanonicalWord, pair_length,
        List.length_replicate]
      omega
    omega
  rw [machineUnaryMatrixGeneratorNextRow]
  simp only [machineUnaryMatrixGeneratorSemanticCode,
    machineUnaryMatrixGeneratorRow_pack,
    machineUnaryMatrixGeneratorPayload_pack]
  have happend : List.replicate state.row.1 true ++ [true] =
      List.replicate (state.row.1 + 1) true := by
    rw [show ([true] : List Bool) = List.replicate 1 true by rfl,
      List.replicate_append_replicate]
  rw [happend, List.take_of_length_le (by simpa using hlength)]

@[simp] theorem machineUnaryMatrixGeneratorNextColumn_semanticCode {m : ℕ}
    (f : Fin m → Fin m → ℚ) (bound payload : List Bool)
    (state : UnaryGridSemanticState m) :
    machineUnaryMatrixGeneratorNextColumn
        (machineUnaryMatrixGeneratorSemanticCode f bound payload state) =
      List.replicate (state.column.1 + 1) true := by
  have hlength : state.column.1 + 1 ≤
      (machineUnaryMatrixGeneratorCanonicalWord m bound payload).length := by
    have hcolumn : state.column.1 + 1 ≤ m := by omega
    have hm : m ≤
        (machineUnaryMatrixGeneratorCanonicalWord m bound payload).length := by
      simp only [machineUnaryMatrixGeneratorCanonicalWord, pair_length,
        List.length_replicate]
      omega
    omega
  rw [machineUnaryMatrixGeneratorNextColumn]
  simp only [machineUnaryMatrixGeneratorSemanticCode,
    machineUnaryMatrixGeneratorColumn_pack,
    machineUnaryMatrixGeneratorPayload_pack]
  have happend : List.replicate state.column.1 true ++ [true] =
      List.replicate (state.column.1 + 1) true := by
    rw [show ([true] : List Bool) = List.replicate 1 true by rfl,
      List.replicate_append_replicate]
  rw [happend, List.take_of_length_le (by simpa using hlength)]

@[simp] theorem machineUnaryMatrixGeneratorColumnCompletesBit_semanticCode
    {m : ℕ} (f : Fin m → Fin m → ℚ) (bound payload : List Bool)
    (state : UnaryGridSemanticState m) :
    machineUnaryMatrixGeneratorColumnCompletesBit
        (machineUnaryMatrixGeneratorSemanticCode f bound payload state) =
      [decide (state.column.1 + 1 = m)] := by
  rw [machineUnaryMatrixGeneratorColumnCompletesBit,
    machineUnaryMatrixGeneratorNextColumn_semanticCode,
    machineUnaryMatrixGeneratorStateDimension]
  simp only [machineUnaryMatrixGeneratorSemanticCode,
    machineUnaryMatrixGeneratorPayload_pack,
    machineUnaryMatrixGeneratorDimension_encode,
    machineUnaryRulersEqualBit_replicate, machineHeadBit_cons]

@[simp] theorem machineUnaryMatrixGeneratorRowCompletesBit_semanticCode
    {m : ℕ} (f : Fin m → Fin m → ℚ) (bound payload : List Bool)
    (state : UnaryGridSemanticState m) :
    machineUnaryMatrixGeneratorRowCompletesBit
        (machineUnaryMatrixGeneratorSemanticCode f bound payload state) =
      [decide (state.row.1 + 1 = m)] := by
  rw [machineUnaryMatrixGeneratorRowCompletesBit,
    machineUnaryMatrixGeneratorNextRow_semanticCode,
    machineUnaryMatrixGeneratorStateDimension]
  simp only [machineUnaryMatrixGeneratorSemanticCode,
    machineUnaryMatrixGeneratorPayload_pack,
    machineUnaryMatrixGeneratorDimension_encode,
    machineUnaryRulersEqualBit_replicate, machineHeadBit_cons]

theorem unaryMatrixCurrent_active {m : ℕ}
    (f : Fin m → Fin m → ℚ) (state : UnaryGridSemanticState m)
    (hdone : state.done = false) :
    unaryMatrixCurrent f state =
      ((List.ofFn (f state.row)).take state.column.1).reverse := by
  simp [unaryMatrixCurrent, hdone]

theorem unaryMatrixCompletedRows_active {m : ℕ}
    (f : Fin m → Fin m → ℚ) (state : UnaryGridSemanticState m)
    (hdone : state.done = false) :
    unaryMatrixCompletedRows f state =
      ((unaryMatrixRows f).take state.row.1).reverse := by
  simp [unaryMatrixCompletedRows, hdone]

theorem unaryMatrixCurrentCandidate_eq {m : ℕ}
    (f : Fin m → Fin m → ℚ) (state : UnaryGridSemanticState m)
    (hdone : state.done = false) :
    f state.row state.column :: unaryMatrixCurrent f state =
      ((List.ofFn (f state.row)).take (state.column.1 + 1)).reverse := by
  rw [unaryMatrixCurrent_active f state hdone]
  have hcolumn : state.column.1 < (List.ofFn (f state.row)).length := by
    simp
  have htake := List.take_concat_get hcolumn
  have hget : (List.ofFn (f state.row))[state.column.1] =
      f state.row state.column := by simp
  rw [hget] at htake
  rw [← htake]
  simpa only [List.concat_eq_append] using
    (List.reverse_concat
      (l := (List.ofFn (f state.row)).take state.column.1)
      (a := f state.row state.column)).symm

theorem unaryMatrixRowsCandidate_eq {m : ℕ}
    (f : Fin m → Fin m → ℚ) (state : UnaryGridSemanticState m)
    (hdone : state.done = false)
    (hcolumn : state.column.1 + 1 = m) :
    (f state.row state.column :: unaryMatrixCurrent f state).reverse ::
        unaryMatrixCompletedRows f state =
      ((unaryMatrixRows f).take (state.row.1 + 1)).reverse := by
  rw [unaryMatrixCurrentCandidate_eq f state hdone,
    unaryMatrixCompletedRows_active f state hdone,
    List.reverse_reverse]
  have hfull :
      (List.ofFn (f state.row)).take (state.column.1 + 1) =
        List.ofFn (f state.row) := by
    rw [hcolumn]
    exact List.take_of_length_le (by simp)
  rw [hfull]
  have hrow : state.row.1 < (unaryMatrixRows f).length := by simp
  have htake := List.take_concat_get hrow
  have hget : (unaryMatrixRows f)[state.row.1] =
      List.ofFn (f state.row) := by
    simp [unaryMatrixRows]
  rw [← hget, ← htake]
  simpa only [List.concat_eq_append] using
    (List.reverse_concat
      (l := (unaryMatrixRows f).take state.row.1)
      (a := (unaryMatrixRows f)[state.row.1])).symm

theorem unaryMatrixCurrentCandidate_code_length_le {m : ℕ}
    (f : Fin m → Fin m → ℚ) (state : UnaryGridSemanticState m)
    (hdone : state.done = false) :
    (binaryListCode rationalEntryBinaryCode
      (f state.row state.column :: unaryMatrixCurrent f state)).length ≤
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (unaryMatrixRows f)).length := by
  rw [unaryMatrixCurrentCandidate_eq f state hdone]
  have hprefix := binaryListCode_take_reverse_length_le
    rationalEntryBinaryCode (List.ofFn (f state.row))
      (state.column.1 + 1)
  have hmem : List.ofFn (f state.row) ∈ unaryMatrixRows f := by
    rw [unaryMatrixRows]
    exact List.mem_ofFn.mpr ⟨state.row, rfl⟩
  exact hprefix.trans (binaryListCode_element_length_le
    (binaryListCode rationalEntryBinaryCode) hmem)

theorem unaryMatrixRowsCandidate_code_length_le {m : ℕ}
    (f : Fin m → Fin m → ℚ) (state : UnaryGridSemanticState m)
    (hdone : state.done = false)
    (hcolumn : state.column.1 + 1 = m) :
    (binaryListCode (binaryListCode rationalEntryBinaryCode)
      ((f state.row state.column :: unaryMatrixCurrent f state).reverse ::
        unaryMatrixCompletedRows f state)).length ≤
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (unaryMatrixRows f)).length := by
  rw [unaryMatrixRowsCandidate_eq f state hdone hcolumn]
  exact binaryListCode_take_reverse_length_le
    (binaryListCode rationalEntryBinaryCode) (unaryMatrixRows f)
      (state.row.1 + 1)

theorem machineUnaryMatrixGeneratorStep_semanticCode {m : ℕ}
    (entry : List Bool → List Bool) (f : Fin m → Fin m → ℚ)
    (bound payload : List Bool) (state : UnaryGridSemanticState m)
    (hentry : ∀ i j,
      entry (pair (List.replicate i.1 true)
        (pair (List.replicate j.1 true) payload)) =
        rationalEntryBinaryCode (f i j))
    (hbound :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (unaryMatrixRows f)).length ≤ bound.length) :
    machineUnaryMatrixGeneratorStep entry
        (machineUnaryMatrixGeneratorSemanticCode f bound payload state) =
      machineUnaryMatrixGeneratorSemanticCode f bound payload
        (unaryGridSemanticStep f state) := by
  rcases state with ⟨row, column, accumulator, done⟩
  cases done
  · have hcurrentCandidate :
        machineUnaryMatrixGeneratorCurrentCandidate entry
            (machineUnaryMatrixGeneratorSemanticCode f bound payload
              ⟨row, column, accumulator, false⟩) =
          binaryListCode rationalEntryBinaryCode
            (f row column ::
              unaryMatrixCurrent f ⟨row, column, accumulator, false⟩) := by
      rw [machineUnaryMatrixGeneratorCurrentCandidate,
        machineUnaryMatrixGeneratorEntryInput_semanticCode, hentry]
      simp [machineUnaryMatrixGeneratorSemanticCode, binaryListCode]
    have hcurrentLarge :
        (binaryListCode rationalEntryBinaryCode
          (f row column ::
            unaryMatrixCurrent f ⟨row, column, accumulator, false⟩)).length ≤
          bound.length :=
      (unaryMatrixCurrentCandidate_code_length_le f
        ⟨row, column, accumulator, false⟩ rfl).trans hbound
    have hnextCurrent :
        machineUnaryMatrixGeneratorNextCurrent entry
            (machineUnaryMatrixGeneratorSemanticCode f bound payload
              ⟨row, column, accumulator, false⟩) =
          binaryListCode rationalEntryBinaryCode
            (f row column ::
              unaryMatrixCurrent f ⟨row, column, accumulator, false⟩) := by
      rw [machineUnaryMatrixGeneratorNextCurrent, hcurrentCandidate]
      simp only [machineUnaryMatrixGeneratorSemanticCode,
        machineUnaryMatrixGeneratorBound_pack]
      exact List.take_of_length_le hcurrentLarge
    have hcompletedRow :
        machineUnaryMatrixGeneratorCompletedRow entry
            (machineUnaryMatrixGeneratorSemanticCode f bound payload
              ⟨row, column, accumulator, false⟩) =
          binaryListCode rationalEntryBinaryCode
            (f row column ::
              unaryMatrixCurrent f
                ⟨row, column, accumulator, false⟩).reverse := by
      rw [machineUnaryMatrixGeneratorCompletedRow, hnextCurrent,
        machineListReverse_encode]
    have hcurrentEq := unaryMatrixCurrentCandidate_eq f
      ⟨row, column, accumulator, false⟩ rfl
    rw [hcurrentEq] at hnextCurrent
    by_cases hcolumn : column.1 + 1 = m
    · have hrowsCandidate :
          machineUnaryMatrixGeneratorRowsCandidate entry
              (machineUnaryMatrixGeneratorSemanticCode f bound payload
                ⟨row, column, accumulator, false⟩) =
            binaryListCode (binaryListCode rationalEntryBinaryCode)
              ((f row column ::
                  unaryMatrixCurrent f
                    ⟨row, column, accumulator, false⟩).reverse ::
                unaryMatrixCompletedRows f
                  ⟨row, column, accumulator, false⟩) := by
        rw [machineUnaryMatrixGeneratorRowsCandidate, hcompletedRow]
        simp [machineUnaryMatrixGeneratorSemanticCode, binaryListCode]
      have hrowsLarge :
          (binaryListCode (binaryListCode rationalEntryBinaryCode)
            ((f row column ::
                unaryMatrixCurrent f
                  ⟨row, column, accumulator, false⟩).reverse ::
              unaryMatrixCompletedRows f
                ⟨row, column, accumulator, false⟩)).length ≤ bound.length :=
        (unaryMatrixRowsCandidate_code_length_le f
          ⟨row, column, accumulator, false⟩ rfl hcolumn).trans hbound
      have hnextRows :
          machineUnaryMatrixGeneratorNextRows entry
              (machineUnaryMatrixGeneratorSemanticCode f bound payload
                ⟨row, column, accumulator, false⟩) =
            binaryListCode (binaryListCode rationalEntryBinaryCode)
              ((f row column ::
                  unaryMatrixCurrent f
                    ⟨row, column, accumulator, false⟩).reverse ::
                unaryMatrixCompletedRows f
                  ⟨row, column, accumulator, false⟩) := by
        rw [machineUnaryMatrixGeneratorNextRows, hrowsCandidate]
        simp only [machineUnaryMatrixGeneratorSemanticCode,
          machineUnaryMatrixGeneratorBound_pack]
        exact List.take_of_length_le hrowsLarge
      have hrowsEq := unaryMatrixRowsCandidate_eq f
        ⟨row, column, accumulator, false⟩ rfl hcolumn
      rw [hrowsEq] at hnextRows
      by_cases hrow : row.1 + 1 = m
      · have htakeAll : (unaryMatrixRows f).take m = unaryMatrixRows f := by
          exact List.take_of_length_le (by simp)
        have hdoneFalse :
            machineHeadBit (machineUnaryMatrixGeneratorDone
              (machineUnaryMatrixGeneratorSemanticCode f bound payload
                ⟨row, column, accumulator, false⟩)) = [false] := by
            simp [machineUnaryMatrixGeneratorSemanticCode]
        rw [machineUnaryMatrixGeneratorStep, hdoneFalse,
          machineIfHead_false, machineUnaryMatrixGeneratorProcess,
          machineUnaryMatrixGeneratorColumnCompletesBit_semanticCode]
        simp only [hcolumn, decide_true, machineIfHead_true]
        rw [machineUnaryMatrixGeneratorRowCompletesBit_semanticCode]
        simp only [hrow, decide_true, machineIfHead_true]
        rw [machineUnaryMatrixGeneratorFinish, hnextRows]
        simp [unaryGridSemanticStep, hcolumn, hrow,
          machineUnaryMatrixGeneratorSemanticCode,
          unaryMatrixCurrent, unaryMatrixCompletedRows,
          htakeAll, binaryListCode]
      · have hdoneFalse :
            machineHeadBit (machineUnaryMatrixGeneratorDone
              (machineUnaryMatrixGeneratorSemanticCode f bound payload
                ⟨row, column, accumulator, false⟩)) = [false] := by
            simp [machineUnaryMatrixGeneratorSemanticCode]
        rw [machineUnaryMatrixGeneratorStep, hdoneFalse,
          machineIfHead_false, machineUnaryMatrixGeneratorProcess,
          machineUnaryMatrixGeneratorColumnCompletesBit_semanticCode]
        simp only [hcolumn, decide_true, machineIfHead_true]
        rw [machineUnaryMatrixGeneratorRowCompletesBit_semanticCode]
        simp only [hrow, decide_false, machineIfHead_false]
        rw [machineUnaryMatrixGeneratorAdvanceRow,
          machineUnaryMatrixGeneratorNextRow_semanticCode, hnextRows]
        simp [unaryGridSemanticStep, hcolumn, hrow,
          machineUnaryMatrixGeneratorSemanticCode,
          unaryMatrixCurrent, unaryMatrixCompletedRows, binaryListCode]
    · have hdoneFalse :
          machineHeadBit (machineUnaryMatrixGeneratorDone
            (machineUnaryMatrixGeneratorSemanticCode f bound payload
              ⟨row, column, accumulator, false⟩)) = [false] := by
          simp [machineUnaryMatrixGeneratorSemanticCode]
      rw [machineUnaryMatrixGeneratorStep, hdoneFalse,
        machineIfHead_false, machineUnaryMatrixGeneratorProcess,
        machineUnaryMatrixGeneratorColumnCompletesBit_semanticCode]
      simp only [hcolumn, decide_false, machineIfHead_false]
      rw [machineUnaryMatrixGeneratorAdvanceColumn,
        machineUnaryMatrixGeneratorNextColumn_semanticCode, hnextCurrent]
      simp [unaryGridSemanticStep, hcolumn,
        machineUnaryMatrixGeneratorSemanticCode,
        unaryMatrixCurrent, unaryMatrixCompletedRows]
  · simp [machineUnaryMatrixGeneratorStep, unaryGridSemanticStep,
      machineUnaryMatrixGeneratorSemanticCode]

theorem machineUnaryMatrixGeneratorInit_semanticCode {m : ℕ}
    (hm : 0 < m) (f : Fin m → Fin m → ℚ)
    (bound payload : List Bool) :
    machineUnaryMatrixGeneratorInit
        (machineUnaryMatrixGeneratorCanonicalWord m bound payload) =
      machineUnaryMatrixGeneratorSemanticCode f bound payload
        (unaryGridSemanticInit hm) := by
  rw [machineUnaryMatrixGeneratorInit,
    machineUnaryMatrixGeneratorInputBound_encode]
  simp [machineUnaryMatrixGeneratorSemanticCode, unaryGridSemanticInit,
    machineUnaryMatrixGeneratorCanonicalWord, unaryMatrixCurrent,
    unaryMatrixCompletedRows, binaryListCode]

theorem machineUnaryMatrixGeneratorIterate_semanticCode {m : ℕ}
    (hm : 0 < m) (entry : List Bool → List Bool)
    (f : Fin m → Fin m → ℚ) (bound payload : List Bool)
    (hentry : ∀ i j,
      entry (pair (List.replicate i.1 true)
        (pair (List.replicate j.1 true) payload)) =
        rationalEntryBinaryCode (f i j))
    (hbound :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (unaryMatrixRows f)).length ≤ bound.length) : ∀ k,
    (machineUnaryMatrixGeneratorStep entry)^[k]
        (machineUnaryMatrixGeneratorInit
          (machineUnaryMatrixGeneratorCanonicalWord m bound payload)) =
      machineUnaryMatrixGeneratorSemanticCode f bound payload
        (unaryGridSemanticStateAt hm f k) := by
  intro k
  induction k with
  | zero => exact machineUnaryMatrixGeneratorInit_semanticCode hm f bound payload
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simpa only [unaryGridSemanticStateAt,
        Function.iterate_succ_apply'] using
        machineUnaryMatrixGeneratorStep_semanticCode
          entry f bound payload (unaryGridSemanticStateAt hm f k)
            hentry hbound

theorem unaryGridSemanticStateAt_full_done {m : ℕ}
    (hm : 0 < m) (f : Fin m → Fin m → ℚ) :
    (unaryGridSemanticStateAt hm f (m * m)).done = true := by
  have hinvariant := unaryGridSemanticStateAt_valueInvariant hm f (m * m)
  rcases hinvariant with hdone | hactive
  · exact hdone.1
  · have hord := hactive.2.1
    have hlt := unaryGridOrdinal_lt_square
      (unaryGridSemanticStateAt hm f (m * m)).row
      (unaryGridSemanticStateAt hm f (m * m)).column
    omega

theorem machineUnaryMatrixGeneratorReversedRowsCode_encode_of_bound {m : ℕ}
    (entry : List Bool → List Bool) (f : Fin m → Fin m → ℚ)
    (bound payload : List Bool)
    (hentry : ∀ i j,
      entry (pair (List.replicate i.1 true)
        (pair (List.replicate j.1 true) payload)) =
        rationalEntryBinaryCode (f i j))
    (hbound :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (unaryMatrixRows f)).length ≤ bound.length) :
    machineUnaryMatrixGeneratorReversedRowsCode entry
        (machineUnaryMatrixGeneratorCanonicalWord m bound payload) =
      binaryListCode (binaryListCode rationalEntryBinaryCode)
        (unaryMatrixRows f).reverse := by
  cases m with
  | zero =>
      rw [machineUnaryMatrixGeneratorReversedRowsCode,
        machineUnaryMatrixGeneratorFinalState,
        machineUnaryMatrixGeneratorRuler_encode]
      simp [machineUnaryMatrixGeneratorInit,
        machineUnaryMatrixGeneratorCanonicalWord,
        unaryMatrixRows, binaryListCode]
  | succ m =>
      have hm : 0 < m + 1 := by omega
      rw [machineUnaryMatrixGeneratorReversedRowsCode,
        machineUnaryMatrixGeneratorFinalState,
        machineUnaryMatrixGeneratorRuler_encode, List.length_replicate,
        machineUnaryMatrixGeneratorIterate_semanticCode hm entry f
          bound payload hentry hbound ((m + 1) * (m + 1))]
      simp only [machineUnaryMatrixGeneratorSemanticCode,
        machineUnaryMatrixGeneratorRows_pack]
      rw [unaryMatrixCompletedRows,
        unaryGridSemanticStateAt_full_done hm f]
      simp

theorem machineUnaryMatrixGeneratorRowsCode_encode_of_bound {m : ℕ}
    (entry : List Bool → List Bool) (f : Fin m → Fin m → ℚ)
    (bound payload : List Bool)
    (hentry : ∀ i j,
      entry (pair (List.replicate i.1 true)
        (pair (List.replicate j.1 true) payload)) =
        rationalEntryBinaryCode (f i j))
    (hbound :
      (binaryListCode (binaryListCode rationalEntryBinaryCode)
        (unaryMatrixRows f)).length ≤ bound.length) :
    machineUnaryMatrixGeneratorRowsCode entry
        (machineUnaryMatrixGeneratorCanonicalWord m bound payload) =
      binaryListCode (binaryListCode rationalEntryBinaryCode)
        (unaryMatrixRows f) := by
  rw [machineUnaryMatrixGeneratorRowsCode,
    machineUnaryMatrixGeneratorReversedRowsCode_encode_of_bound
      entry f bound payload hentry hbound,
    machineListReverse_encode, List.reverse_reverse]

end BeyondBethe
