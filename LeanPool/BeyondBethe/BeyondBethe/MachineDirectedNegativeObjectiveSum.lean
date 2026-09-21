/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineDirectedNegativeObjectiveCoordinate
import LeanPool.BeyondBethe.BeyondBethe.MachineBetheFloorScan
import LeanPool.BeyondBethe.BeyondBethe.MachineListIndex
import LeanPool.BeyondBethe.BeyondBethe.MachineScheduledLogWidth
import LeanPool.BeyondBethe.BeyondBethe.MachineCertificateExpGuard

/-!
# Finite-word evaluation of the complete directed Bethe objective

This module scans all `(m+1)^2` recovered Birkhoff entries in row-major
order.  At each entry it reads the corresponding input-matrix coordinate,
recovers and normalizes the affine Birkhoff coordinate, invokes the directed
coordinate evaluator, and adds its rational lower endpoint to an unreduced
accumulator.

The concrete state machine is total on arbitrary bitstrings.  Its counters
and accumulator are clamped by an explicit polynomial word.  The semantic
proof below is kept separate from this global finite-word bound; on canonical
inputs the clamp is proved inactive.
-/

namespace BeyondBethe

open Complexity

/-! ## Public input layout -/

/-- Input layout:
`pair mUnary (pair precisionUnary (pair tauRaw (pair matrixCode yCode)))`. -/
def machineDirectedObjectiveSumDimension (word : List Bool) : List Bool :=
  machinePairFirst word

def machineDirectedObjectiveSumRest (word : List Bool) : List Bool :=
  machinePairSecond word

def machineDirectedObjectiveSumPrecision (word : List Bool) : List Bool :=
  machinePairFirst (machineDirectedObjectiveSumRest word)

def machineDirectedObjectiveSumAfterPrecision (word : List Bool) : List Bool :=
  machinePairSecond (machineDirectedObjectiveSumRest word)

def machineDirectedObjectiveSumTau (word : List Bool) : List Bool :=
  machinePairFirst (machineDirectedObjectiveSumAfterPrecision word)

def machineDirectedObjectiveSumAfterTau (word : List Bool) : List Bool :=
  machinePairSecond (machineDirectedObjectiveSumAfterPrecision word)

def machineDirectedObjectiveSumMatrix (word : List Bool) : List Bool :=
  machinePairFirst (machineDirectedObjectiveSumAfterTau word)

def machineDirectedObjectiveSumVector (word : List Bool) : List Bool :=
  machinePairSecond (machineDirectedObjectiveSumAfterTau word)

/-! ## Row-major state and one coordinate evaluation -/

def machineDirectedObjectiveSumPack
    (row column acc bound done payload : List Bool) : List Bool :=
  pair row (pair column (pair acc (pair bound (pair done payload))))

def machineDirectedObjectiveSumRow (state : List Bool) : List Bool :=
  machinePairFirst state

def machineDirectedObjectiveSumColumn (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

def machineDirectedObjectiveSumAcc (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

def machineDirectedObjectiveSumBound (state : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

def machineDirectedObjectiveSumDone (state : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond
      (machinePairSecond (machinePairSecond (machinePairSecond state))))

def machineDirectedObjectiveSumPayload (state : List Bool) : List Bool :=
  machinePairSecond
    (machinePairSecond
      (machinePairSecond (machinePairSecond (machinePairSecond state))))

def machineDirectedObjectiveSumStateDimension
    (state : List Bool) : List Bool :=
  machineDirectedObjectiveSumDimension
    (machineDirectedObjectiveSumPayload state)

def machineDirectedObjectiveSumStatePrecision
    (state : List Bool) : List Bool :=
  machineDirectedObjectiveSumPrecision
    (machineDirectedObjectiveSumPayload state)

def machineDirectedObjectiveSumStateTau
    (state : List Bool) : List Bool :=
  machineDirectedObjectiveSumTau
    (machineDirectedObjectiveSumPayload state)

def machineDirectedObjectiveSumStateMatrix
    (state : List Bool) : List Bool :=
  machineDirectedObjectiveSumMatrix
    (machineDirectedObjectiveSumPayload state)

def machineDirectedObjectiveSumStateVector
    (state : List Bool) : List Bool :=
  machineDirectedObjectiveSumVector
    (machineDirectedObjectiveSumPayload state)

def machineDirectedObjectiveSumLastRowBit (state : List Bool) : List Bool :=
  machineUnaryRulersEqualBit (machineDirectedObjectiveSumRow state)
    (machineDirectedObjectiveSumStateDimension state)

def machineDirectedObjectiveSumLastColumnBit
    (state : List Bool) : List Bool :=
  machineUnaryRulersEqualBit (machineDirectedObjectiveSumColumn state)
    (machineDirectedObjectiveSumStateDimension state)

def machineDirectedObjectiveSumMatrixEntryInput
    (state : List Bool) : List Bool :=
  pair (machineDirectedObjectiveSumRow state)
    (pair (machineDirectedObjectiveSumColumn state)
      (machineDirectedObjectiveSumStateMatrix state))

def machineDirectedObjectiveSumMatrixEntryRaw
    (state : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineMatrixEntryAtUnary
      (machineDirectedObjectiveSumMatrixEntryInput state))

def machineDirectedObjectiveSumAffineEntryInput
    (state : List Bool) : List Bool :=
  pair (machineDirectedObjectiveSumStateDimension state)
    (pair (machineDirectedObjectiveSumRow state)
      (pair (machineDirectedObjectiveSumColumn state)
        (machineDirectedObjectiveSumStateVector state)))

def machineDirectedObjectiveSumAffineEntryRaw
    (state : List Bool) : List Bool :=
  machineNormalizeRawRatEntryCode
    (machineBetheAffineEntryRawCode
      (machineDirectedObjectiveSumAffineEntryInput state))

def machineDirectedObjectiveSumCoordinateInput
    (state : List Bool) : List Bool :=
  pair (machineDirectedObjectiveSumStatePrecision state)
    (pair (machineDirectedObjectiveSumStateTau state)
      (pair (machineDirectedObjectiveSumMatrixEntryRaw state)
        (machineDirectedObjectiveSumAffineEntryRaw state)))

def machineDirectedObjectiveSumCoordinateRawCode
    (state : List Bool) : List Bool :=
  machineDirectedNegativeObjectiveCoordinateLowerRawCode
    (machineDirectedObjectiveSumCoordinateInput state)

def machineDirectedObjectiveSumCandidate (state : List Bool) : List Bool :=
  machineRawRatAddCode
    (pair (machineDirectedObjectiveSumAcc state)
      (machineDirectedObjectiveSumCoordinateRawCode state))

def machineDirectedObjectiveSumNextAcc (state : List Bool) : List Bool :=
  (machineDirectedObjectiveSumCandidate state).take
    (machineDirectedObjectiveSumBound state).length

def machineDirectedObjectiveSumNextRow (state : List Bool) : List Bool :=
  (machineDirectedObjectiveSumRow state ++ [true]).take
    (machineDirectedObjectiveSumBound state).length

def machineDirectedObjectiveSumNextColumn (state : List Bool) : List Bool :=
  (machineDirectedObjectiveSumColumn state ++ [true]).take
    (machineDirectedObjectiveSumBound state).length

def machineDirectedObjectiveSumFinish (state : List Bool) : List Bool :=
  machineDirectedObjectiveSumPack
    (machineDirectedObjectiveSumRow state)
    (machineDirectedObjectiveSumColumn state)
    (machineDirectedObjectiveSumNextAcc state)
    (machineDirectedObjectiveSumBound state) [true]
    (machineDirectedObjectiveSumPayload state)

def machineDirectedObjectiveSumAdvanceRow (state : List Bool) : List Bool :=
  machineDirectedObjectiveSumPack
    (machineDirectedObjectiveSumNextRow state) []
    (machineDirectedObjectiveSumNextAcc state)
    (machineDirectedObjectiveSumBound state)
    (machineDirectedObjectiveSumDone state)
    (machineDirectedObjectiveSumPayload state)

def machineDirectedObjectiveSumAdvanceColumn
    (state : List Bool) : List Bool :=
  machineDirectedObjectiveSumPack
    (machineDirectedObjectiveSumRow state)
    (machineDirectedObjectiveSumNextColumn state)
    (machineDirectedObjectiveSumNextAcc state)
    (machineDirectedObjectiveSumBound state)
    (machineDirectedObjectiveSumDone state)
    (machineDirectedObjectiveSumPayload state)

def machineDirectedObjectiveSumProcess (state : List Bool) : List Bool :=
  machineIfHead (machineHeadBit
      (machineDirectedObjectiveSumLastColumnBit state))
    (machineIfHead (machineHeadBit
        (machineDirectedObjectiveSumLastRowBit state))
      (machineDirectedObjectiveSumFinish state)
      (machineDirectedObjectiveSumAdvanceRow state))
    (machineDirectedObjectiveSumAdvanceColumn state)

def machineDirectedObjectiveSumStep (state : List Bool) : List Bool :=
  machineIfHead (machineHeadBit (machineDirectedObjectiveSumDone state))
    state (machineDirectedObjectiveSumProcess state)

/-! ## Explicit iteration and state bounds -/

def machineDirectedObjectiveSumAccumulatorBound
    (word : List Bool) : List Bool :=
  machineIteratedBinaryWidth 6 word

def machineDirectedObjectiveSumStateEnvelope
    (word : List Bool) : List Bool :=
  machineIteratedBinaryWidth 7 word

def machineDirectedObjectiveSumInit (word : List Bool) : List Bool :=
  machineDirectedObjectiveSumPack [] []
    (rawRatBinaryCode RawRat.zero)
    (machineDirectedObjectiveSumAccumulatorBound word) [false] word

/-- The floor scanner already provides the exact bounded-unary construction
for `(m+1)^2`; it depends only on the first component of the word. -/
def machineDirectedObjectiveSumRuler (word : List Bool) : List Bool :=
  machineBetheFloorScanRuler word

def machineDirectedObjectiveSumWidth (word : List Bool) : List Bool :=
  let envelope := machineDirectedObjectiveSumStateEnvelope word
  machineDirectedObjectiveSumPack envelope envelope envelope envelope
    envelope envelope

def machineDirectedObjectiveSumFinalState (word : List Bool) : List Bool :=
  (machineDirectedObjectiveSumStep)^[(machineDirectedObjectiveSumRuler word).length]
    (machineDirectedObjectiveSumInit word)

def machineDirectedNegativeObjectiveSumRawCode
    (word : List Bool) : List Bool :=
  machineDirectedObjectiveSumAcc
    (machineDirectedObjectiveSumFinalState word)

/-! ## Polynomial-time closure -/

theorem machineDirectedObjectiveSumDimension_mem_FP :
    machineDirectedObjectiveSumDimension ∈ FP := machinePairFirst_mem_FP

theorem machineDirectedObjectiveSumRest_mem_FP :
    machineDirectedObjectiveSumRest ∈ FP := machinePairSecond_mem_FP

theorem machineDirectedObjectiveSumPrecision_mem_FP :
    machineDirectedObjectiveSumPrecision ∈ FP := by
  simpa only [machineDirectedObjectiveSumPrecision] using
    machineCompose_mem_FP machineDirectedObjectiveSumRest_mem_FP
      machinePairFirst_mem_FP

theorem machineDirectedObjectiveSumAfterPrecision_mem_FP :
    machineDirectedObjectiveSumAfterPrecision ∈ FP := by
  simpa only [machineDirectedObjectiveSumAfterPrecision] using
    machineCompose_mem_FP machineDirectedObjectiveSumRest_mem_FP
      machinePairSecond_mem_FP

theorem machineDirectedObjectiveSumTau_mem_FP :
    machineDirectedObjectiveSumTau ∈ FP := by
  simpa only [machineDirectedObjectiveSumTau] using
    machineCompose_mem_FP machineDirectedObjectiveSumAfterPrecision_mem_FP
      machinePairFirst_mem_FP

theorem machineDirectedObjectiveSumAfterTau_mem_FP :
    machineDirectedObjectiveSumAfterTau ∈ FP := by
  simpa only [machineDirectedObjectiveSumAfterTau] using
    machineCompose_mem_FP machineDirectedObjectiveSumAfterPrecision_mem_FP
      machinePairSecond_mem_FP

theorem machineDirectedObjectiveSumMatrix_mem_FP :
    machineDirectedObjectiveSumMatrix ∈ FP := by
  simpa only [machineDirectedObjectiveSumMatrix] using
    machineCompose_mem_FP machineDirectedObjectiveSumAfterTau_mem_FP
      machinePairFirst_mem_FP

theorem machineDirectedObjectiveSumVector_mem_FP :
    machineDirectedObjectiveSumVector ∈ FP := by
  simpa only [machineDirectedObjectiveSumVector] using
    machineCompose_mem_FP machineDirectedObjectiveSumAfterTau_mem_FP
      machinePairSecond_mem_FP

theorem machineDirectedObjectiveSumRow_mem_FP :
    machineDirectedObjectiveSumRow ∈ FP := machinePairFirst_mem_FP

theorem machineDirectedObjectiveSumColumn_mem_FP :
    machineDirectedObjectiveSumColumn ∈ FP := by
  simpa only [machineDirectedObjectiveSumColumn] using
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineDirectedObjectiveSumAcc_mem_FP :
    machineDirectedObjectiveSumAcc ∈ FP := by
  have htail := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineDirectedObjectiveSumAcc] using
    machineCompose_mem_FP htail machinePairFirst_mem_FP

theorem machineDirectedObjectiveSumBound_mem_FP :
    machineDirectedObjectiveSumBound ∈ FP := by
  have htailTwo := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have htailThree := machineCompose_mem_FP htailTwo machinePairSecond_mem_FP
  simpa only [machineDirectedObjectiveSumBound] using
    machineCompose_mem_FP htailThree machinePairFirst_mem_FP

theorem machineDirectedObjectiveSumDone_mem_FP :
    machineDirectedObjectiveSumDone ∈ FP := by
  have htailTwo := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have htailThree := machineCompose_mem_FP htailTwo machinePairSecond_mem_FP
  have htailFour := machineCompose_mem_FP htailThree machinePairSecond_mem_FP
  simpa only [machineDirectedObjectiveSumDone] using
    machineCompose_mem_FP htailFour machinePairFirst_mem_FP

theorem machineDirectedObjectiveSumPayload_mem_FP :
    machineDirectedObjectiveSumPayload ∈ FP := by
  have htailTwo := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have htailThree := machineCompose_mem_FP htailTwo machinePairSecond_mem_FP
  have htailFour := machineCompose_mem_FP htailThree machinePairSecond_mem_FP
  simpa only [machineDirectedObjectiveSumPayload] using
    machineCompose_mem_FP htailFour machinePairSecond_mem_FP

theorem machineDirectedObjectiveSumStateDimension_mem_FP :
    machineDirectedObjectiveSumStateDimension ∈ FP := by
  simpa only [machineDirectedObjectiveSumStateDimension] using
    machineCompose_mem_FP machineDirectedObjectiveSumPayload_mem_FP
      machineDirectedObjectiveSumDimension_mem_FP

theorem machineDirectedObjectiveSumStatePrecision_mem_FP :
    machineDirectedObjectiveSumStatePrecision ∈ FP := by
  simpa only [machineDirectedObjectiveSumStatePrecision] using
    machineCompose_mem_FP machineDirectedObjectiveSumPayload_mem_FP
      machineDirectedObjectiveSumPrecision_mem_FP

theorem machineDirectedObjectiveSumStateTau_mem_FP :
    machineDirectedObjectiveSumStateTau ∈ FP := by
  simpa only [machineDirectedObjectiveSumStateTau] using
    machineCompose_mem_FP machineDirectedObjectiveSumPayload_mem_FP
      machineDirectedObjectiveSumTau_mem_FP

theorem machineDirectedObjectiveSumStateMatrix_mem_FP :
    machineDirectedObjectiveSumStateMatrix ∈ FP := by
  simpa only [machineDirectedObjectiveSumStateMatrix] using
    machineCompose_mem_FP machineDirectedObjectiveSumPayload_mem_FP
      machineDirectedObjectiveSumMatrix_mem_FP

theorem machineDirectedObjectiveSumStateVector_mem_FP :
    machineDirectedObjectiveSumStateVector ∈ FP := by
  simpa only [machineDirectedObjectiveSumStateVector] using
    machineCompose_mem_FP machineDirectedObjectiveSumPayload_mem_FP
      machineDirectedObjectiveSumVector_mem_FP

theorem machineDirectedObjectiveSumLastRowBit_mem_FP :
    machineDirectedObjectiveSumLastRowBit ∈ FP :=
  machineUnaryRulersEqualBit_mem_FP machineDirectedObjectiveSumRow_mem_FP
    machineDirectedObjectiveSumStateDimension_mem_FP

theorem machineDirectedObjectiveSumLastColumnBit_mem_FP :
    machineDirectedObjectiveSumLastColumnBit ∈ FP :=
  machineUnaryRulersEqualBit_mem_FP machineDirectedObjectiveSumColumn_mem_FP
    machineDirectedObjectiveSumStateDimension_mem_FP

theorem machineDirectedObjectiveSumMatrixEntryInput_mem_FP :
    machineDirectedObjectiveSumMatrixEntryInput ∈ FP :=
  machinePair_mem_FP machineDirectedObjectiveSumRow_mem_FP
    (machinePair_mem_FP machineDirectedObjectiveSumColumn_mem_FP
      machineDirectedObjectiveSumStateMatrix_mem_FP)

theorem machineDirectedObjectiveSumMatrixEntryRaw_mem_FP :
    machineDirectedObjectiveSumMatrixEntryRaw ∈ FP := by
  have hentry := machineCompose_mem_FP
    machineDirectedObjectiveSumMatrixEntryInput_mem_FP
    machineMatrixEntryAtUnary_mem_FP
  simpa only [machineDirectedObjectiveSumMatrixEntryRaw] using
    machineCompose_mem_FP hentry machineNormalizeRawRatEntryCode_mem_FP

theorem machineDirectedObjectiveSumAffineEntryInput_mem_FP :
    machineDirectedObjectiveSumAffineEntryInput ∈ FP :=
  machinePair_mem_FP machineDirectedObjectiveSumStateDimension_mem_FP
    (machinePair_mem_FP machineDirectedObjectiveSumRow_mem_FP
      (machinePair_mem_FP machineDirectedObjectiveSumColumn_mem_FP
        machineDirectedObjectiveSumStateVector_mem_FP))

theorem machineDirectedObjectiveSumAffineEntryRaw_mem_FP :
    machineDirectedObjectiveSumAffineEntryRaw ∈ FP := by
  have hentry := machineCompose_mem_FP
    machineDirectedObjectiveSumAffineEntryInput_mem_FP
    machineBetheAffineEntryRawCode_mem_FP
  simpa only [machineDirectedObjectiveSumAffineEntryRaw] using
    machineCompose_mem_FP hentry machineNormalizeRawRatEntryCode_mem_FP

theorem machineDirectedObjectiveSumCoordinateInput_mem_FP :
    machineDirectedObjectiveSumCoordinateInput ∈ FP :=
  machinePair_mem_FP machineDirectedObjectiveSumStatePrecision_mem_FP
    (machinePair_mem_FP machineDirectedObjectiveSumStateTau_mem_FP
      (machinePair_mem_FP machineDirectedObjectiveSumMatrixEntryRaw_mem_FP
        machineDirectedObjectiveSumAffineEntryRaw_mem_FP))

theorem machineDirectedObjectiveSumCoordinateRawCode_mem_FP :
    machineDirectedObjectiveSumCoordinateRawCode ∈ FP := by
  simpa only [machineDirectedObjectiveSumCoordinateRawCode] using
    machineCompose_mem_FP machineDirectedObjectiveSumCoordinateInput_mem_FP
      machineDirectedNegativeObjectiveCoordinateLowerRawCode_mem_FP

theorem machineDirectedObjectiveSumCandidate_mem_FP :
    machineDirectedObjectiveSumCandidate ∈ FP := by
  have hinput := machinePair_mem_FP machineDirectedObjectiveSumAcc_mem_FP
    machineDirectedObjectiveSumCoordinateRawCode_mem_FP
  simpa only [machineDirectedObjectiveSumCandidate] using
    machineCompose_mem_FP hinput machineRawRatAddCode_mem_FP

theorem machineDirectedObjectiveSumNextAcc_mem_FP :
    machineDirectedObjectiveSumNextAcc ∈ FP := by
  simpa only [machineDirectedObjectiveSumNextAcc] using
    machineTake_mem_FP machineDirectedObjectiveSumBound_mem_FP
      machineDirectedObjectiveSumCandidate_mem_FP

theorem machineDirectedObjectiveSumNextRow_mem_FP :
    machineDirectedObjectiveSumNextRow ∈ FP := by
  have happend := machineAppend_mem_FP machineDirectedObjectiveSumRow_mem_FP
    (machineConst_mem_FP [true])
  simpa only [machineDirectedObjectiveSumNextRow] using
    machineTake_mem_FP machineDirectedObjectiveSumBound_mem_FP happend

theorem machineDirectedObjectiveSumNextColumn_mem_FP :
    machineDirectedObjectiveSumNextColumn ∈ FP := by
  have happend := machineAppend_mem_FP
    machineDirectedObjectiveSumColumn_mem_FP
    (machineConst_mem_FP [true])
  simpa only [machineDirectedObjectiveSumNextColumn] using
    machineTake_mem_FP machineDirectedObjectiveSumBound_mem_FP happend

theorem machineDirectedObjectiveSumFinish_mem_FP :
    machineDirectedObjectiveSumFinish ∈ FP :=
  machinePair_mem_FP machineDirectedObjectiveSumRow_mem_FP
    (machinePair_mem_FP machineDirectedObjectiveSumColumn_mem_FP
      (machinePair_mem_FP machineDirectedObjectiveSumNextAcc_mem_FP
        (machinePair_mem_FP machineDirectedObjectiveSumBound_mem_FP
          (machinePair_mem_FP (machineConst_mem_FP [true])
            machineDirectedObjectiveSumPayload_mem_FP))))

theorem machineDirectedObjectiveSumAdvanceRow_mem_FP :
    machineDirectedObjectiveSumAdvanceRow ∈ FP :=
  machinePair_mem_FP machineDirectedObjectiveSumNextRow_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP machineDirectedObjectiveSumNextAcc_mem_FP
        (machinePair_mem_FP machineDirectedObjectiveSumBound_mem_FP
          (machinePair_mem_FP machineDirectedObjectiveSumDone_mem_FP
            machineDirectedObjectiveSumPayload_mem_FP))))

theorem machineDirectedObjectiveSumAdvanceColumn_mem_FP :
    machineDirectedObjectiveSumAdvanceColumn ∈ FP :=
  machinePair_mem_FP machineDirectedObjectiveSumRow_mem_FP
    (machinePair_mem_FP machineDirectedObjectiveSumNextColumn_mem_FP
      (machinePair_mem_FP machineDirectedObjectiveSumNextAcc_mem_FP
        (machinePair_mem_FP machineDirectedObjectiveSumBound_mem_FP
          (machinePair_mem_FP machineDirectedObjectiveSumDone_mem_FP
            machineDirectedObjectiveSumPayload_mem_FP))))

theorem machineDirectedObjectiveSumProcess_mem_FP :
    machineDirectedObjectiveSumProcess ∈ FP := by
  have hlastColumn := machineCompose_mem_FP
    machineDirectedObjectiveSumLastColumnBit_mem_FP machineHeadBit_mem_FP
  have hlastRow := machineCompose_mem_FP
    machineDirectedObjectiveSumLastRowBit_mem_FP machineHeadBit_mem_FP
  have hlast := machineIfHead_mem_FP hlastRow
    machineDirectedObjectiveSumFinish_mem_FP
    machineDirectedObjectiveSumAdvanceRow_mem_FP
  exact machineIfHead_mem_FP hlastColumn hlast
    machineDirectedObjectiveSumAdvanceColumn_mem_FP

theorem machineDirectedObjectiveSumStep_mem_FP :
    machineDirectedObjectiveSumStep ∈ FP := by
  have hdone := machineCompose_mem_FP machineDirectedObjectiveSumDone_mem_FP
    machineHeadBit_mem_FP
  exact machineIfHead_mem_FP hdone id_mem_FP
    machineDirectedObjectiveSumProcess_mem_FP

theorem machineDirectedObjectiveSumAccumulatorBound_mem_FP :
    machineDirectedObjectiveSumAccumulatorBound ∈ FP := by
  simpa only [machineDirectedObjectiveSumAccumulatorBound] using
    machineIteratedBinaryWidth_mem_FP 6

theorem machineDirectedObjectiveSumStateEnvelope_mem_FP :
    machineDirectedObjectiveSumStateEnvelope ∈ FP := by
  simpa only [machineDirectedObjectiveSumStateEnvelope] using
    machineIteratedBinaryWidth_mem_FP 7

theorem machineDirectedObjectiveSumInit_mem_FP :
    machineDirectedObjectiveSumInit ∈ FP :=
  machinePair_mem_FP (machineConst_mem_FP [])
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP
        (machineConst_mem_FP (rawRatBinaryCode RawRat.zero))
        (machinePair_mem_FP
          machineDirectedObjectiveSumAccumulatorBound_mem_FP
          (machinePair_mem_FP (machineConst_mem_FP [false]) id_mem_FP))))

theorem machineDirectedObjectiveSumRuler_mem_FP :
    machineDirectedObjectiveSumRuler ∈ FP := by
  simpa only [machineDirectedObjectiveSumRuler] using
    machineBetheFloorScanRuler_mem_FP

theorem machineDirectedObjectiveSumWidth_mem_FP :
    machineDirectedObjectiveSumWidth ∈ FP := by
  have h := machineDirectedObjectiveSumStateEnvelope_mem_FP
  exact machinePair_mem_FP h
    (machinePair_mem_FP h
      (machinePair_mem_FP h
        (machinePair_mem_FP h (machinePair_mem_FP h h))))

/-! ## A global state envelope for the bounded iteration -/

@[simp] theorem machineDirectedObjectiveSumRow_pack
    (row column acc bound done payload) :
    machineDirectedObjectiveSumRow
        (machineDirectedObjectiveSumPack row column acc bound done payload) =
      row := by
  simp [machineDirectedObjectiveSumRow, machineDirectedObjectiveSumPack]

@[simp] theorem machineDirectedObjectiveSumColumn_pack
    (row column acc bound done payload) :
    machineDirectedObjectiveSumColumn
        (machineDirectedObjectiveSumPack row column acc bound done payload) =
      column := by
  simp [machineDirectedObjectiveSumColumn, machineDirectedObjectiveSumPack]

@[simp] theorem machineDirectedObjectiveSumAcc_pack
    (row column acc bound done payload) :
    machineDirectedObjectiveSumAcc
        (machineDirectedObjectiveSumPack row column acc bound done payload) =
      acc := by
  simp [machineDirectedObjectiveSumAcc, machineDirectedObjectiveSumPack]

@[simp] theorem machineDirectedObjectiveSumBound_pack
    (row column acc bound done payload) :
    machineDirectedObjectiveSumBound
        (machineDirectedObjectiveSumPack row column acc bound done payload) =
      bound := by
  simp [machineDirectedObjectiveSumBound, machineDirectedObjectiveSumPack]

@[simp] theorem machineDirectedObjectiveSumDone_pack
    (row column acc bound done payload) :
    machineDirectedObjectiveSumDone
        (machineDirectedObjectiveSumPack row column acc bound done payload) =
      done := by
  simp [machineDirectedObjectiveSumDone, machineDirectedObjectiveSumPack]

@[simp] theorem machineDirectedObjectiveSumPayload_pack
    (row column acc bound done payload) :
    machineDirectedObjectiveSumPayload
        (machineDirectedObjectiveSumPack row column acc bound done payload) =
      payload := by
  simp [machineDirectedObjectiveSumPayload, machineDirectedObjectiveSumPack]

def MachineDirectedObjectiveSumStateBound
    (word state : List Bool) : Prop :=
  state = machineDirectedObjectiveSumPack
      (machineDirectedObjectiveSumRow state)
      (machineDirectedObjectiveSumColumn state)
      (machineDirectedObjectiveSumAcc state)
      (machineDirectedObjectiveSumBound state)
      (machineDirectedObjectiveSumDone state)
      (machineDirectedObjectiveSumPayload state) ∧
    (machineDirectedObjectiveSumRow state).length ≤
      (machineDirectedObjectiveSumAccumulatorBound word).length ∧
    (machineDirectedObjectiveSumColumn state).length ≤
      (machineDirectedObjectiveSumAccumulatorBound word).length ∧
    (machineDirectedObjectiveSumAcc state).length ≤
      (machineDirectedObjectiveSumAccumulatorBound word).length ∧
    machineDirectedObjectiveSumBound state =
      machineDirectedObjectiveSumAccumulatorBound word ∧
    (machineDirectedObjectiveSumDone state).length ≤ 1 ∧
    machineDirectedObjectiveSumPayload state = word

theorem machineDirectedObjectiveSumInit_bound (word : List Bool) :
    MachineDirectedObjectiveSumStateBound word
      (machineDirectedObjectiveSumInit word) := by
  simp only [MachineDirectedObjectiveSumStateBound,
    machineDirectedObjectiveSumInit,
    machineDirectedObjectiveSumRow_pack,
    machineDirectedObjectiveSumColumn_pack,
    machineDirectedObjectiveSumAcc_pack,
    machineDirectedObjectiveSumBound_pack,
    machineDirectedObjectiveSumDone_pack,
    machineDirectedObjectiveSumPayload_pack]
  refine ⟨trivial, by simp, by simp, ?_, trivial, by simp, trivial⟩
  have hzero : (rawRatBinaryCode RawRat.zero).length = 5 := by decide
  rw [hzero]
  rw [machineDirectedObjectiveSumAccumulatorBound,
    machineIteratedBinaryWidth_length]
  have hbase : 16 ≤ word.length + 16 := by omega
  have hpow : 16 ^ (2 ^ (5 + 1)) ≤
      (word.length + 16) ^ (2 ^ (5 + 1)) :=
    Nat.pow_le_pow_left hbase _
  exact (by norm_num : 5 ≤ 16 ^ (2 ^ (5 + 1))).trans
    (hpow.trans (certificateExpGuardWidth_pow_lower 5 word.length))

theorem machineDirectedObjectiveSumStep_bound {word state : List Bool}
    (hstate : MachineDirectedObjectiveSumStateBound word state) :
    MachineDirectedObjectiveSumStateBound word
      (machineDirectedObjectiveSumStep state) := by
  rcases hstate with
    ⟨hdecomp, hrow, hcolumn, hacc, hbound, hdone, hpayload⟩
  have hfinish : MachineDirectedObjectiveSumStateBound word
      (machineDirectedObjectiveSumFinish state) := by
    rw [machineDirectedObjectiveSumFinish]
    simp only [MachineDirectedObjectiveSumStateBound,
      machineDirectedObjectiveSumRow_pack,
      machineDirectedObjectiveSumColumn_pack,
      machineDirectedObjectiveSumAcc_pack,
      machineDirectedObjectiveSumBound_pack,
      machineDirectedObjectiveSumDone_pack,
      machineDirectedObjectiveSumPayload_pack]
    refine ⟨trivial, hrow, hcolumn, ?_, hbound, by simp, hpayload⟩
    rw [machineDirectedObjectiveSumNextAcc, hbound]
    exact List.length_take_le _ _
  have hadvanceRow : MachineDirectedObjectiveSumStateBound word
      (machineDirectedObjectiveSumAdvanceRow state) := by
    rw [machineDirectedObjectiveSumAdvanceRow]
    simp only [MachineDirectedObjectiveSumStateBound,
      machineDirectedObjectiveSumRow_pack,
      machineDirectedObjectiveSumColumn_pack,
      machineDirectedObjectiveSumAcc_pack,
      machineDirectedObjectiveSumBound_pack,
      machineDirectedObjectiveSumDone_pack,
      machineDirectedObjectiveSumPayload_pack]
    refine ⟨trivial, ?_, by simp, ?_, hbound, hdone, hpayload⟩
    · rw [machineDirectedObjectiveSumNextRow, hbound]
      exact List.length_take_le _ _
    · rw [machineDirectedObjectiveSumNextAcc, hbound]
      exact List.length_take_le _ _
  have hadvanceColumn : MachineDirectedObjectiveSumStateBound word
      (machineDirectedObjectiveSumAdvanceColumn state) := by
    rw [machineDirectedObjectiveSumAdvanceColumn]
    simp only [MachineDirectedObjectiveSumStateBound,
      machineDirectedObjectiveSumRow_pack,
      machineDirectedObjectiveSumColumn_pack,
      machineDirectedObjectiveSumAcc_pack,
      machineDirectedObjectiveSumBound_pack,
      machineDirectedObjectiveSumDone_pack,
      machineDirectedObjectiveSumPayload_pack]
    refine ⟨trivial, hrow, ?_, ?_, hbound, hdone, hpayload⟩
    · rw [machineDirectedObjectiveSumNextColumn, hbound]
      exact List.length_take_le _ _
    · rw [machineDirectedObjectiveSumNextAcc, hbound]
      exact List.length_take_le _ _
  have hprocess : MachineDirectedObjectiveSumStateBound word
      (machineDirectedObjectiveSumProcess state) := by
    cases hcolumnCode : machineDirectedObjectiveSumLastColumnBit state with
    | nil =>
        rw [machineDirectedObjectiveSumProcess, hcolumnCode,
          machineHeadBit_nil, machineIfHead_false]
        exact hadvanceColumn
    | cons columnBit columnTail =>
        cases columnBit with
        | false =>
            rw [machineDirectedObjectiveSumProcess, hcolumnCode,
              machineHeadBit_cons, machineIfHead_false]
            exact hadvanceColumn
        | true =>
            cases hrowCode : machineDirectedObjectiveSumLastRowBit state with
            | nil =>
                rw [machineDirectedObjectiveSumProcess, hcolumnCode,
                  machineHeadBit_cons, machineIfHead_true, hrowCode,
                  machineHeadBit_nil, machineIfHead_false]
                exact hadvanceRow
            | cons rowBit rowTail =>
                cases rowBit with
                | false =>
                    rw [machineDirectedObjectiveSumProcess, hcolumnCode,
                      machineHeadBit_cons, machineIfHead_true, hrowCode,
                      machineHeadBit_cons, machineIfHead_false]
                    exact hadvanceRow
                | true =>
                    rw [machineDirectedObjectiveSumProcess, hcolumnCode,
                      machineHeadBit_cons, machineIfHead_true, hrowCode,
                      machineHeadBit_cons, machineIfHead_true]
                    exact hfinish
  cases hdoneCode : machineDirectedObjectiveSumDone state with
  | nil =>
      rw [machineDirectedObjectiveSumStep, hdoneCode,
        machineHeadBit_nil, machineIfHead_false]
      exact hprocess
  | cons doneBit doneTail =>
      cases doneBit with
      | false =>
          rw [machineDirectedObjectiveSumStep, hdoneCode,
            machineHeadBit_cons, machineIfHead_false]
          exact hprocess
      | true =>
          rw [machineDirectedObjectiveSumStep, hdoneCode,
            machineHeadBit_cons, machineIfHead_true]
          exact ⟨hdecomp, hrow, hcolumn, hacc, hbound, hdone, hpayload⟩

theorem machineDirectedObjectiveSumIterate_bound (word : List Bool) : ∀ k,
    MachineDirectedObjectiveSumStateBound word
      ((machineDirectedObjectiveSumStep)^[k]
        (machineDirectedObjectiveSumInit word)) := by
  intro k
  induction k with
  | zero => exact machineDirectedObjectiveSumInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineDirectedObjectiveSumStep_bound ih

theorem certificateExpGuardWidth_self_le (k L : ℕ) :
    L ≤ certificateExpGuardWidth k L := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [certificateExpGuardWidth]
      exact ih.trans (by
        nlinarith [sq_nonneg (certificateExpGuardWidth k L)])

theorem machineDirectedObjectiveSumAccumulatorBound_le_envelope
    (word : List Bool) :
    (machineDirectedObjectiveSumAccumulatorBound word).length ≤
      (machineDirectedObjectiveSumStateEnvelope word).length := by
  rw [machineDirectedObjectiveSumAccumulatorBound,
    machineDirectedObjectiveSumStateEnvelope,
    machineIteratedBinaryWidth_length,
    machineIteratedBinaryWidth_length]
  change certificateExpGuardWidth 6 word.length ≤
    (certificateExpGuardWidth 6 word.length + 16) ^ 2
  nlinarith [sq_nonneg (certificateExpGuardWidth 6 word.length)]

theorem machineDirectedObjectiveSumWord_le_envelope (word : List Bool) :
    word.length ≤
      (machineDirectedObjectiveSumStateEnvelope word).length := by
  rw [machineDirectedObjectiveSumStateEnvelope,
    machineIteratedBinaryWidth_length]
  exact certificateExpGuardWidth_self_le 7 word.length

theorem machineDirectedObjectiveSumEnvelope_pos (word : List Bool) :
    1 ≤ (machineDirectedObjectiveSumStateEnvelope word).length := by
  rw [machineDirectedObjectiveSumStateEnvelope,
    machineIteratedBinaryWidth_length]
  have hbase : 16 ≤ word.length + 16 := by omega
  have hpow : 16 ^ (2 ^ (6 + 1)) ≤
      (word.length + 16) ^ (2 ^ (6 + 1)) :=
    Nat.pow_le_pow_left hbase _
  exact (by norm_num : 1 ≤ 16 ^ (2 ^ (6 + 1))).trans
    (hpow.trans (certificateExpGuardWidth_pow_lower 6 word.length))

theorem machineDirectedObjectiveSumIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (_ : iterations ≤ (machineDirectedObjectiveSumRuler word).length) :
    ((machineDirectedObjectiveSumStep)^[iterations]
      (machineDirectedObjectiveSumInit word)).length ≤
        (machineDirectedObjectiveSumWidth word).length := by
  rcases machineDirectedObjectiveSumIterate_bound word iterations with
    ⟨hdecomp, hrow, hcolumn, hacc, hbound, hdone, hpayload⟩
  have hbe := machineDirectedObjectiveSumAccumulatorBound_le_envelope word
  have hwe := machineDirectedObjectiveSumWord_le_envelope word
  have hepos := machineDirectedObjectiveSumEnvelope_pos word
  rw [hdecomp, hbound, hpayload]
  simp only [machineDirectedObjectiveSumPack,
    machineDirectedObjectiveSumWidth, pair_length]
  omega

theorem machineDirectedObjectiveSumFinalState_mem_FP :
    machineDirectedObjectiveSumFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineDirectedObjectiveSumStep_mem_FP
    machineDirectedObjectiveSumInit_mem_FP
    machineDirectedObjectiveSumRuler_mem_FP
    machineDirectedObjectiveSumWidth_mem_FP
    machineDirectedObjectiveSumIterate_length_le_width

theorem machineDirectedNegativeObjectiveSumRawCode_mem_FP :
    machineDirectedNegativeObjectiveSumRawCode ∈ FP := by
  simpa only [machineDirectedNegativeObjectiveSumRawCode] using
    machineCompose_mem_FP machineDirectedObjectiveSumFinalState_mem_FP
      machineDirectedObjectiveSumAcc_mem_FP

/-! ## Canonical inputs and exact coordinate semantics -/

def machineDirectedObjectiveSumCanonicalWord {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) : List Bool :=
  pair (List.replicate m true)
    (pair (List.replicate p true)
      (pair (rawRatBinaryCode (rawRatOfRat tau))
        (pair (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩)
          (rationalFiniteVectorCode y))))

@[simp] theorem machineDirectedObjectiveSumDimension_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    machineDirectedObjectiveSumDimension
        (machineDirectedObjectiveSumCanonicalWord tau A y p) =
      List.replicate m true := by
  simp [machineDirectedObjectiveSumDimension,
    machineDirectedObjectiveSumCanonicalWord]

@[simp] theorem machineDirectedObjectiveSumPrecision_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    machineDirectedObjectiveSumPrecision
        (machineDirectedObjectiveSumCanonicalWord tau A y p) =
      List.replicate p true := by
  simp [machineDirectedObjectiveSumPrecision,
    machineDirectedObjectiveSumRest,
    machineDirectedObjectiveSumCanonicalWord]

@[simp] theorem machineDirectedObjectiveSumTau_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    machineDirectedObjectiveSumTau
        (machineDirectedObjectiveSumCanonicalWord tau A y p) =
      rawRatBinaryCode (rawRatOfRat tau) := by
  simp [machineDirectedObjectiveSumTau,
    machineDirectedObjectiveSumAfterPrecision,
    machineDirectedObjectiveSumRest,
    machineDirectedObjectiveSumCanonicalWord]

@[simp] theorem machineDirectedObjectiveSumMatrix_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    machineDirectedObjectiveSumMatrix
        (machineDirectedObjectiveSumCanonicalWord tau A y p) =
      rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩ := by
  simp [machineDirectedObjectiveSumMatrix,
    machineDirectedObjectiveSumAfterTau,
    machineDirectedObjectiveSumAfterPrecision,
    machineDirectedObjectiveSumRest,
    machineDirectedObjectiveSumCanonicalWord]

@[simp] theorem machineDirectedObjectiveSumVector_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    machineDirectedObjectiveSumVector
        (machineDirectedObjectiveSumCanonicalWord tau A y p) =
      rationalFiniteVectorCode y := by
  simp [machineDirectedObjectiveSumVector,
    machineDirectedObjectiveSumAfterTau,
    machineDirectedObjectiveSumAfterPrecision,
    machineDirectedObjectiveSumRest,
    machineDirectedObjectiveSumCanonicalWord]

def machineDirectedObjectiveSumCanonicalState {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) : List Bool :=
  machineDirectedObjectiveSumPack
    (List.replicate i.1 true) (List.replicate j.1 true)
    (rawRatBinaryCode acc) bound [done]
    (machineDirectedObjectiveSumCanonicalWord tau A y p)

@[simp] theorem machineDirectedObjectiveSumRow_canonicalState {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumRow
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      List.replicate i.1 true := by
  simp [machineDirectedObjectiveSumCanonicalState]

@[simp] theorem machineDirectedObjectiveSumColumn_canonicalState {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumColumn
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      List.replicate j.1 true := by
  simp [machineDirectedObjectiveSumCanonicalState]

@[simp] theorem machineDirectedObjectiveSumAcc_canonicalState {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumAcc
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      rawRatBinaryCode acc := by
  simp [machineDirectedObjectiveSumCanonicalState]

@[simp] theorem machineDirectedObjectiveSumBound_canonicalState {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumBound
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) = bound := by
  simp [machineDirectedObjectiveSumCanonicalState]

@[simp] theorem machineDirectedObjectiveSumDone_canonicalState {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumDone
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) = [done] := by
  simp [machineDirectedObjectiveSumCanonicalState]

@[simp] theorem machineDirectedObjectiveSumPayload_canonicalState {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumPayload
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      machineDirectedObjectiveSumCanonicalWord tau A y p := by
  simp [machineDirectedObjectiveSumCanonicalState]

@[simp] theorem machineDirectedObjectiveSumStateDimension_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumStateDimension
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      List.replicate m true := by
  rw [machineDirectedObjectiveSumStateDimension,
    machineDirectedObjectiveSumPayload_canonicalState,
    machineDirectedObjectiveSumDimension_encode]

@[simp] theorem machineDirectedObjectiveSumStatePrecision_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumStatePrecision
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      List.replicate p true := by
  rw [machineDirectedObjectiveSumStatePrecision,
    machineDirectedObjectiveSumPayload_canonicalState,
    machineDirectedObjectiveSumPrecision_encode]

@[simp] theorem machineDirectedObjectiveSumStateTau_canonicalState {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumStateTau
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      rawRatBinaryCode (rawRatOfRat tau) := by
  rw [machineDirectedObjectiveSumStateTau,
    machineDirectedObjectiveSumPayload_canonicalState,
    machineDirectedObjectiveSumTau_encode]

@[simp] theorem machineDirectedObjectiveSumStateMatrix_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumStateMatrix
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩ := by
  rw [machineDirectedObjectiveSumStateMatrix,
    machineDirectedObjectiveSumPayload_canonicalState,
    machineDirectedObjectiveSumMatrix_encode]

@[simp] theorem machineDirectedObjectiveSumStateVector_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumStateVector
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      rationalFiniteVectorCode y := by
  rw [machineDirectedObjectiveSumStateVector,
    machineDirectedObjectiveSumPayload_canonicalState,
    machineDirectedObjectiveSumVector_encode]

@[simp] theorem machineDirectedObjectiveSumMatrixEntryInput_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumMatrixEntryInput
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      pair (List.replicate i.1 true)
        (pair (List.replicate j.1 true)
          (rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩)) := by
  simp [machineDirectedObjectiveSumMatrixEntryInput]

@[simp] theorem machineDirectedObjectiveSumMatrixEntryRaw_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumMatrixEntryRaw
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      rawRatBinaryCode (rawRatOfRat (A i j)) := by
  rw [machineDirectedObjectiveSumMatrixEntryRaw,
    machineDirectedObjectiveSumMatrixEntryInput_canonicalState,
    machineMatrixEntryAtUnary_encode]
  rw [← rawRatBinaryCode_rawRatOfRat,
    machineNormalizeRawRatEntryCode_encode,
    rawRatBinaryCode_rawRatOfRat]
  congr 1
  simp [binaryNormalizeRawRat_eq_value, rawRatOfRat_value]

@[simp] theorem machineDirectedObjectiveSumAffineEntryInput_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumAffineEntryInput
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      machineBetheAffineEntryCanonicalWord i j y := by
  simp [machineDirectedObjectiveSumAffineEntryInput,
    machineBetheAffineEntryCanonicalWord]

@[simp] theorem machineDirectedObjectiveSumAffineEntryRaw_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumAffineEntryRaw
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      rawRatBinaryCode (rawRatOfRat (betheAffineMatrixQ y i j)) := by
  rw [machineDirectedObjectiveSumAffineEntryRaw,
    machineDirectedObjectiveSumAffineEntryInput_canonicalState,
    machineBetheAffineEntryRawCode_encode,
    machineNormalizeRawRatEntryCode_encode,
    rawRatBinaryCode_rawRatOfRat]
  congr 1
  rw [binaryNormalizeRawRat_eq_value,
    rawBetheAffineEntry_value]

@[simp] theorem machineDirectedObjectiveSumCoordinateInput_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumCoordinateInput
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      machineDirectedObjectiveCoordinateCanonicalWord tau (A i j)
        (betheAffineMatrixQ y i j) p := by
  simp [machineDirectedObjectiveSumCoordinateInput,
    machineDirectedObjectiveCoordinateCanonicalWord]

@[simp] theorem machineDirectedObjectiveSumCoordinateRawCode_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumCoordinateRawCode
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      rawRatBinaryCode
        (rawDirectedNegativeObjectiveCoordinateLower tau (A i j)
          (betheAffineMatrixQ y i j) p) := by
  rw [machineDirectedObjectiveSumCoordinateRawCode,
    machineDirectedObjectiveSumCoordinateInput_canonicalState,
    machineDirectedNegativeObjectiveCoordinateLowerRawCode_encode]

/-! ## Exact `(m+1)^2` iteration ruler on canonical inputs -/

@[simp] theorem machineDirectedObjectiveSumWorkBits_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    machineBetheFloorScanWorkBits
        (machineDirectedObjectiveSumCanonicalWord tau A y p) =
      ((m + 1) * (m + 1)).bits := by
  rw [machineBetheFloorScanWorkBits, machineBetheFloorScanOrderBits,
    machineBetheFloorScanDimensionBits,
    machineBetheFloorScanDimension,
    machineDirectedObjectiveSumCanonicalWord, machinePairFirst_pair,
    machineLengthBits_encode, List.length_replicate]
  have hone : ([true] : List Bool) = (1 : ℕ).bits := rfl
  rw [hone, machineBinaryAddBits_pair_natBits,
    machineBinaryMulBits_pair_natBits]

theorem machineDirectedObjectiveSumWork_le_guard {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    (m + 1) * (m + 1) ≤
      (machineBetheFloorScanGuard
        (machineDirectedObjectiveSumCanonicalWord tau A y p)).length := by
  have hm : m ≤
      (machineDirectedObjectiveSumCanonicalWord tau A y p).length := by
    simp only [machineDirectedObjectiveSumCanonicalWord, pair_length,
      List.length_replicate]
    omega
  simp only [machineBetheFloorScanGuard, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith

@[simp] theorem machineDirectedObjectiveSumRuler_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    machineDirectedObjectiveSumRuler
        (machineDirectedObjectiveSumCanonicalWord tau A y p) =
      List.replicate ((m + 1) * (m + 1)) true := by
  rw [machineDirectedObjectiveSumRuler,
    machineBetheFloorScanRuler,
    machineDirectedObjectiveSumWorkBits_encode,
    machineBoundedUnary_encode_of_le]
  exact machineDirectedObjectiveSumWork_le_guard tau A y p

/-! ## Typed row-major semantics -/

def rawDirectedBetheObjectiveCoordinate {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) : RawRat :=
  rawDirectedNegativeObjectiveCoordinateLower tau (A i j)
    (betheAffineMatrixQ y i j) p

def rawDirectedNegativeObjectiveCoordinateWidthBudget
    (tau a x : ℚ) (p : ℕ) : ℕ :=
  2 * rawRatWidth (rawRatOfRat x) +
    rawRatWidth (rawRatOfRat tau) +
    rawRatWidth (rawRatOfRat (1 - x)) +
    rawRatWidth (rawScheduledLogUpper a p) +
    rawRatWidth (rawScheduledLogLower x p) +
    rawRatWidth (rawScheduledLogUpper (1 - x) p) + 4

theorem rawDirectedNegativeObjectiveCoordinateLower_width_le
    (tau a x : ℚ) (p : ℕ) :
    rawRatWidth
        (rawDirectedNegativeObjectiveCoordinateLower tau a x p) ≤
      rawDirectedNegativeObjectiveCoordinateWidthBudget tau a x p := by
  let rawTau := rawRatOfRat tau
  let rawX := rawRatOfRat x
  let rawComplement := rawRatOfRat (1 - x)
  let logA := rawScheduledLogUpper a p
  let logX := rawScheduledLogLower x p
  let logComplement := rawScheduledLogUpper (1 - x) p
  have hone : rawRatWidth RawRat.one = 1 := rawRatWidth_one
  have hfirst := rawRatWidth_mul_le rawX.neg logA
  rw [rawRatWidth_neg] at hfirst
  have honeTau := rawRatWidth_add_le RawRat.one rawTau
  rw [hone] at honeTau
  have hmiddleScale := rawRatWidth_mul_le
    (RawRat.one.add rawTau) rawX
  have hmiddle := rawRatWidth_mul_le
    ((RawRat.one.add rawTau).mul rawX) logX
  have hlastProduct := rawRatWidth_mul_le rawComplement logComplement
  have hfirstMiddle := rawRatWidth_add_le
    (rawX.neg.mul logA)
    (((RawRat.one.add rawTau).mul rawX).mul logX)
  have htotal := rawRatWidth_add_le
    ((rawX.neg.mul logA).add
      (((RawRat.one.add rawTau).mul rawX).mul logX))
    (rawComplement.mul logComplement).neg
  rw [rawRatWidth_neg] at htotal
  have honeTauBound :
      rawRatWidth (RawRat.one.add rawTau) ≤
        rawRatWidth rawTau + 2 := by omega
  have hmiddleScaleBound :
      rawRatWidth ((RawRat.one.add rawTau).mul rawX) ≤
        rawRatWidth rawTau + rawRatWidth rawX + 2 := by omega
  have hmiddleBound :
      rawRatWidth (((RawRat.one.add rawTau).mul rawX).mul logX) ≤
        rawRatWidth rawTau + rawRatWidth rawX +
          rawRatWidth logX + 2 := by omega
  have hfirstMiddleBound :
      rawRatWidth
          ((rawX.neg.mul logA).add
            (((RawRat.one.add rawTau).mul rawX).mul logX)) ≤
        2 * rawRatWidth rawX + rawRatWidth rawTau +
          rawRatWidth logA + rawRatWidth logX + 3 := by omega
  have htotalBound :
      rawRatWidth
          (((rawX.neg.mul logA).add
              (((RawRat.one.add rawTau).mul rawX).mul logX)).add
            (rawComplement.mul logComplement).neg) ≤
        2 * rawRatWidth rawX + rawRatWidth rawTau +
          rawRatWidth rawComplement + rawRatWidth logA +
          rawRatWidth logX + rawRatWidth logComplement + 4 := by omega
  simpa [rawDirectedNegativeObjectiveCoordinateLower,
    rawDirectedNegativeObjectiveCoordinateWidthBudget,
    rawTau, rawX, rawComplement, logA, logX, logComplement] using
    htotalBound

theorem rawRatListCost_le_uniform_width {W : ℕ} : ∀ xs : List ℚ,
    (∀ q ∈ xs, rawRatWidth (rawRatOfRat q) ≤ W) →
      rawRatListCost xs ≤ xs.length * (W + 1) := by
  intro xs hwidth
  induction xs with
  | nil => simp [rawRatListCost]
  | cons q qs ih =>
      have hq := hwidth q (by simp)
      have hqs : ∀ r ∈ qs, rawRatWidth (rawRatOfRat r) ≤ W := by
        intro r hr
        exact hwidth r (by simp [hr])
      have ih' := ih hqs
      simp only [rawRatListCost] at ih'
      simp only [rawRatListCost, List.map_cons, List.sum_cons,
        List.length_cons]
      rw [Nat.succ_mul]
      omega

theorem rawDirectedObjectiveSum_y_width_le_word {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (k : Fin (m * m)) :
    rawRatWidth (rawRatOfRat (y k)) ≤
      (machineDirectedObjectiveSumCanonicalWord tau A y p).length := by
  let word := machineDirectedObjectiveSumCanonicalWord tau A y p
  have hk : y k ∈ List.ofFn y := by
    rw [List.mem_ofFn']
    exact ⟨k, rfl⟩
  have hentry := binaryListCode_element_length_le
    rationalEntryBinaryCode hk
  have hvector : (rationalFiniteVectorCode y).length ≤ word.length := by
    simp only [word, machineDirectedObjectiveSumCanonicalWord,
      rationalFiniteVectorCode, pair_length, List.length_replicate]
    omega
  have hcode : (rawRatBinaryCode (rawRatOfRat (y k))).length ≤
      word.length := by
    rw [rawRatBinaryCode_rawRatOfRat]
    exact hentry.trans hvector
  exact (rawRatWidth_le_binaryCode_length _).trans hcode

theorem rawDirectedObjectiveSum_A_width_le_word {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) :
    rawRatWidth (rawRatOfRat (A i j)) ≤
      (machineDirectedObjectiveSumCanonicalWord tau A y p).length := by
  let rows := rationalMatrixRows A
  let matrixWord := rationalMatrixBinaryEncoding.encode ⟨m + 1, A⟩
  let word := machineDirectedObjectiveSumCanonicalWord tau A y p
  have hrow : List.ofFn (A i) ∈ rows := by
    change List.ofFn (A i) ∈ rationalMatrixRows A
    rw [rationalMatrixRows, List.mem_ofFn']
    exact ⟨i, rfl⟩
  have hentryMem : A i j ∈ List.ofFn (A i) := by
    rw [List.mem_ofFn']
    exact ⟨j, rfl⟩
  have hentry := binaryListCode_element_length_le
    rationalEntryBinaryCode hentryMem
  have hrowCode := binaryListCode_element_length_le
    (binaryListCode rationalEntryBinaryCode) hrow
  have hrowsMatrix :
      (binaryListCode (binaryListCode rationalEntryBinaryCode) rows).length ≤
        matrixWord.length := by
    calc
      _ = (machineMatrixRowsWord matrixWord).length := by
        simpa only [rows, matrixWord] using congrArg List.length
          (machineMatrixRowsWord_encode A).symm
      _ ≤ matrixWord.length := by
        simpa only [machineMatrixRowsWord] using
          machinePairSecond_length_le matrixWord
  have hmatrixWord : matrixWord.length ≤ word.length := by
    simp only [matrixWord, word, machineDirectedObjectiveSumCanonicalWord,
      pair_length, List.length_replicate]
    omega
  have hcode : (rawRatBinaryCode (rawRatOfRat (A i j))).length ≤
      word.length := by
    rw [rawRatBinaryCode_rawRatOfRat]
    exact hentry.trans (hrowCode.trans (hrowsMatrix.trans hmatrixWord))
  exact (rawRatWidth_le_binaryCode_length _).trans hcode

theorem rawDirectedObjectiveSum_tau_width_le_word {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    rawRatWidth (rawRatOfRat tau) ≤
      (machineDirectedObjectiveSumCanonicalWord tau A y p).length := by
  have hcode : (rawRatBinaryCode (rawRatOfRat tau)).length ≤
      (machineDirectedObjectiveSumCanonicalWord tau A y p).length := by
    simp only [machineDirectedObjectiveSumCanonicalWord, pair_length,
      List.length_replicate]
    omega
  exact (rawRatWidth_le_binaryCode_length _).trans hcode

theorem rawBetheDimensionMinusOne_width_le (m : ℕ) :
    rawRatWidth (rawBetheDimensionMinusOne m) ≤ m + 2 := by
  rw [rawBetheDimensionMinusOne, rawRatWidth]
  cases m with
  | zero => norm_num
  | succ k =>
      norm_num only [Int.natCast_add, Int.natCast_one,
        add_sub_cancel_right, Nat.size_one]
      have hsize : k.size ≤ k + 1 := by
        rw [Nat.size_le]
        exact (Nat.lt_two_pow_self (n := k)).trans_le
          (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
      exact max_le (hsize.trans (by omega)) (by omega)

theorem rawBetheAffineLineSum_width_le_word {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (rowMode : Bool) (fixed : Fin m) :
    rawRatWidth (rawBetheAffineLineSum rowMode fixed y) ≤
      1 + m *
        ((machineDirectedObjectiveSumCanonicalWord tau A y p).length + 1) := by
  let values := betheAffineLineValues rowMode fixed y
  let L := (machineDirectedObjectiveSumCanonicalWord tau A y p).length
  have hvalueWidth : ∀ q ∈ values,
      rawRatWidth (rawRatOfRat q) ≤ L := by
    intro q hq
    simp only [values, betheAffineLineValues, List.mem_ofFn'] at hq
    rcases hq with ⟨k, rfl⟩
    split
    · exact rawDirectedObjectiveSum_y_width_le_word tau A y p _
    · exact rawDirectedObjectiveSum_y_width_le_word tau A y p _
  have hcost := rawRatListCost_le_uniform_width values hvalueWidth
  have hsum := rawRatWidth_listSum_le RawRat.zero values
  have hzero : rawRatWidth RawRat.zero = 1 := rawRatWidth_zero
  rw [hzero] at hsum
  have hlen : values.length = m := by
    simp [values]
  rw [hlen] at hcost
  have hfinal : rawRatWidth (rawRatListSum RawRat.zero values) ≤
      1 + m * (L + 1) := hsum.trans (by omega)
  simpa only [rawBetheAffineLineSum, values, L] using hfinal

theorem rawBetheAffineTotal_width_le_word {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    rawRatWidth (rawRatListSum RawRat.zero (List.ofFn y)) ≤
      1 + m * m *
        ((machineDirectedObjectiveSumCanonicalWord tau A y p).length + 1) := by
  let values := List.ofFn y
  let L := (machineDirectedObjectiveSumCanonicalWord tau A y p).length
  have hvalueWidth : ∀ q ∈ values,
      rawRatWidth (rawRatOfRat q) ≤ L := by
    intro q hq
    simp only [values, List.mem_ofFn'] at hq
    rcases hq with ⟨k, rfl⟩
    exact rawDirectedObjectiveSum_y_width_le_word tau A y p k
  have hcost := rawRatListCost_le_uniform_width values hvalueWidth
  have hsum := rawRatWidth_listSum_le RawRat.zero values
  have hzero : rawRatWidth RawRat.zero = 1 := rawRatWidth_zero
  rw [hzero] at hsum
  have hlen : values.length = m * m := by simp [values]
  rw [hlen] at hcost
  have hfinal : rawRatWidth (rawRatListSum RawRat.zero values) ≤
      1 + m * m * (L + 1) := hsum.trans (by omega)
  simpa only [values, L] using hfinal

def rawBetheAffineEntryWidthBudget (m L : ℕ) : ℕ :=
  m * m * (L + 1) + m + L + 8

theorem rawBetheAffineEntry_width_le_word {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) :
    rawRatWidth (rawBetheAffineEntry y i j) ≤
      rawBetheAffineEntryWidthBudget m
        (machineDirectedObjectiveSumCanonicalWord tau A y p).length := by
  let L := (machineDirectedObjectiveSumCanonicalWord tau A y p).length
  have hlineRow := fun fixed : Fin m ↦
    rawBetheAffineLineSum_width_le_word tau A y p true fixed
  have hlineColumn := fun fixed : Fin m ↦
    rawBetheAffineLineSum_width_le_word tau A y p false fixed
  have htotal := rawBetheAffineTotal_width_le_word tau A y p
  have hdimension := rawBetheDimensionMinusOne_width_le m
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp only [rawBetheAffineEntry, Fin.lastCases_last]
    have hsub := rawRatWidth_sub_le
      (rawRatListSum RawRat.zero (List.ofFn y))
      (rawBetheDimensionMinusOne m)
    simp only [rawBetheAffineEntryWidthBudget]
    change m * m *
      ((machineDirectedObjectiveSumCanonicalWord tau A y p).length + 1) +
      m + (machineDirectedObjectiveSumCanonicalWord tau A y p).length + 8 ≥
        rawRatWidth
          ((rawRatListSum RawRat.zero (List.ofFn y)).sub
            (rawBetheDimensionMinusOne m))
    omega
  · simp only [rawBetheAffineEntry, Fin.lastCases_last,
      Fin.lastCases_castSucc]
    have hsub := rawRatWidth_sub_le RawRat.one
      (rawBetheAffineLineSum false j y)
    rw [rawRatWidth_one] at hsub
    have hline := hlineColumn j
    have hmpos : 0 < m := Nat.zero_lt_of_lt j.isLt
    have hmm : m ≤ m * m := Nat.le_mul_of_pos_left m hmpos
    have hquad := Nat.mul_le_mul_right
      ((machineDirectedObjectiveSumCanonicalWord tau A y p).length + 1) hmm
    simp only [rawBetheAffineEntryWidthBudget]
    omega
  · simp only [rawBetheAffineEntry, Fin.lastCases_last,
      Fin.lastCases_castSucc]
    have hsub := rawRatWidth_sub_le RawRat.one
      (rawBetheAffineLineSum true i y)
    rw [rawRatWidth_one] at hsub
    have hline := hlineRow i
    have hmpos : 0 < m := Nat.zero_lt_of_lt i.isLt
    have hmm : m ≤ m * m := Nat.le_mul_of_pos_left m hmpos
    have hquad := Nat.mul_le_mul_right
      ((machineDirectedObjectiveSumCanonicalWord tau A y p).length + 1) hmm
    simp only [rawBetheAffineEntryWidthBudget]
    omega
  · simp only [rawBetheAffineEntry, Fin.lastCases_castSucc]
    have hy := rawDirectedObjectiveSum_y_width_le_word tau A y p
      (finProdFinEquiv (i, j))
    simp only [rawBetheAffineEntryWidthBudget]
    omega

theorem rawBetheAffineMatrixQ_width_le_word {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) :
    rawRatWidth (rawRatOfRat (betheAffineMatrixQ y i j)) ≤
      20 + 12 * rawBetheAffineEntryWidthBudget m
        (machineDirectedObjectiveSumCanonicalWord tau A y p).length := by
  let raw := rawBetheAffineEntry y i j
  have hvalue : binaryNormalizeRawRat raw = betheAffineMatrixQ y i j := by
    rw [binaryNormalizeRawRat_eq_value, rawBetheAffineEntry_value]
  have hcanonical := rawRatOfRat_width_le_encodedBitLength
    (binaryNormalizeRawRat raw)
  have hnormalize := binaryNormalizeRawRat_encodedBitLength_le raw
  have hraw := rawBetheAffineEntry_width_le_word tau A y p i j
  have hraw' : rawRatWidth raw ≤ rawBetheAffineEntryWidthBudget m
      (machineDirectedObjectiveSumCanonicalWord tau A y p).length := by
    simpa only [raw] using hraw
  have hscaled := Nat.mul_le_mul_left 12 hraw'
  calc
    rawRatWidth (rawRatOfRat (betheAffineMatrixQ y i j)) =
        rawRatWidth (rawRatOfRat (binaryNormalizeRawRat raw)) := by rw [hvalue]
    _ ≤ encodedBitLength ℚ (binaryNormalizeRawRat raw) := hcanonical
    _ ≤ 20 + 12 * rawRatWidth raw := hnormalize
    _ ≤ 20 + 12 * rawBetheAffineEntryWidthBudget m
        (machineDirectedObjectiveSumCanonicalWord tau A y p).length := by
      omega

def rawDirectedObjectiveCoordinateWordXBudget (m L : ℕ) : ℕ :=
  20 + 12 * rawBetheAffineEntryWidthBudget m L

def rawDirectedObjectiveCoordinateWordComplementBudget
    (m L : ℕ) : ℕ :=
  44 + 12 * rawDirectedObjectiveCoordinateWordXBudget m L

def rawScheduledLogWordBudget (L W : ℕ) : ℕ :=
  64 * (L + 2 * W + 4) ^ 2 * (W + 2)

def rawDirectedObjectiveCoordinateWordBudget (m L : ℕ) : ℕ :=
  let WX := rawDirectedObjectiveCoordinateWordXBudget m L
  let WC := rawDirectedObjectiveCoordinateWordComplementBudget m L
  2 * WX + L + WC +
    rawScheduledLogWordBudget L L +
    rawScheduledLogWordBudget L WX +
    rawScheduledLogWordBudget L WC + 4

theorem directedObjectiveSum_precision_le_word {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    p ≤ (machineDirectedObjectiveSumCanonicalWord tau A y p).length := by
  simp only [machineDirectedObjectiveSumCanonicalWord, pair_length,
    List.length_replicate]
  omega

theorem rawDirectedBetheObjectiveCoordinate_width_le_word_budget {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) :
    rawRatWidth (rawDirectedBetheObjectiveCoordinate tau A y p i j) ≤
      rawDirectedObjectiveCoordinateWordBudget m
        (machineDirectedObjectiveSumCanonicalWord tau A y p).length := by
  let L := (machineDirectedObjectiveSumCanonicalWord tau A y p).length
  let x := betheAffineMatrixQ y i j
  let WX := rawDirectedObjectiveCoordinateWordXBudget m L
  let WC := rawDirectedObjectiveCoordinateWordComplementBudget m L
  have hp : p ≤ L := directedObjectiveSum_precision_le_word tau A y p
  have htau : rawRatWidth (rawRatOfRat tau) ≤ L :=
    rawDirectedObjectiveSum_tau_width_le_word tau A y p
  have ha : rawRatWidth (rawRatOfRat (A i j)) ≤ L :=
    rawDirectedObjectiveSum_A_width_le_word tau A y p i j
  have hx : rawRatWidth (rawRatOfRat x) ≤ WX := by
    simpa only [x, WX, L,
      rawDirectedObjectiveCoordinateWordXBudget] using
      rawBetheAffineMatrixQ_width_le_word tau A y p i j
  have hc0 := rawRatWidth_complement_le x
  have hc : rawRatWidth (rawRatOfRat (1 - x)) ≤ WC := by
    simp only [WC, rawDirectedObjectiveCoordinateWordComplementBudget]
    omega
  have hlogA := rawRatWidth_scheduledLogUpper_of_bounds_le
    (A i j) hp ha
  have hlogX := rawRatWidth_scheduledLogLower_of_bounds_le x hp hx
  have hlogC := rawRatWidth_scheduledLogUpper_of_bounds_le (1 - x) hp hc
  have hraw := rawDirectedNegativeObjectiveCoordinateLower_width_le
    tau (A i j) x p
  have hfinal :
      rawRatWidth
          (rawDirectedNegativeObjectiveCoordinateLower tau (A i j) x p) ≤
        2 * WX + L + WC +
          64 * (L + 2 * L + 4) ^ 2 * (L + 2) +
          64 * (L + 2 * WX + 4) ^ 2 * (WX + 2) +
          64 * (L + 2 * WC + 4) ^ 2 * (WC + 2) + 4 := by
    simp only [rawDirectedNegativeObjectiveCoordinateWidthBudget] at hraw
    omega
  simpa only [rawDirectedBetheObjectiveCoordinate,
    rawDirectedObjectiveCoordinateWordBudget, rawScheduledLogWordBudget,
    WX, WC, L, x] using hfinal

structure DirectedObjectiveSumSemanticState (m : ℕ) where
  row : Fin (m + 1)
  column : Fin (m + 1)
  acc : RawRat
  done : Bool

def directedObjectiveSumSemanticInit (m : ℕ) :
    DirectedObjectiveSumSemanticState m where
  row := ⟨0, by omega⟩
  column := ⟨0, by omega⟩
  acc := RawRat.zero
  done := false

def directedObjectiveSumSemanticStep {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (state : DirectedObjectiveSumSemanticState m) :
    DirectedObjectiveSumSemanticState m :=
  if state.done then state
  else
    let nextAcc := state.acc.add
      (rawDirectedBetheObjectiveCoordinate tau A y p
        state.row state.column)
    if hcolumn : state.column = Fin.last m then
      if hrow : state.row = Fin.last m then
        { state with acc := nextAcc, done := true }
      else
        { state with
            row := betheFloorScanNextFin state.row
            column := ⟨0, by omega⟩
            acc := nextAcc }
    else
      { state with
          column := betheFloorScanNextFin state.column
          acc := nextAcc }

theorem directedObjectiveSumSemanticStep_acc_width {m B C : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (state : DirectedObjectiveSumSemanticState m)
    (hacc : rawRatWidth state.acc ≤ C)
    (hcoordinate : rawRatWidth
      (rawDirectedBetheObjectiveCoordinate tau A y p
        state.row state.column) ≤ B) :
    rawRatWidth (directedObjectiveSumSemanticStep tau A y p state).acc ≤
      C + B + 1 := by
  rcases state with ⟨i, j, acc, done⟩
  dsimp only [DirectedObjectiveSumSemanticState.acc,
    DirectedObjectiveSumSemanticState.row,
    DirectedObjectiveSumSemanticState.column] at hacc hcoordinate ⊢
  cases done
  · have hadd := rawRatWidth_add_le acc
      (rawDirectedBetheObjectiveCoordinate tau A y p i j)
    by_cases hcolumn : j = Fin.last m
    · by_cases hrow : i = Fin.last m
      · simpa [directedObjectiveSumSemanticStep, hcolumn, hrow] using
          hadd.trans (by omega)
      · simpa [directedObjectiveSumSemanticStep, hcolumn, hrow] using
          hadd.trans (by omega)
    · simpa [directedObjectiveSumSemanticStep, hcolumn] using
        hadd.trans (by omega)
  · simpa [directedObjectiveSumSemanticStep] using
      hacc.trans (by omega)

def machineDirectedObjectiveSumSemanticCode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (bound : List Bool)
    (state : DirectedObjectiveSumSemanticState m) : List Bool :=
  machineDirectedObjectiveSumCanonicalState tau A y p
    state.row state.column state.acc state.done bound

@[simp] theorem machineDirectedObjectiveSumLastRowBit_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumLastRowBit
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      [decide (i = Fin.last m)] := by
  rw [machineDirectedObjectiveSumLastRowBit,
    machineDirectedObjectiveSumRow_canonicalState,
    machineDirectedObjectiveSumStateDimension_canonicalState,
    machineUnaryRulersEqualBit_replicate]
  by_cases hi : i = Fin.last m
  · simp [hi]
  · have hval : i.1 ≠ m := by
      intro h
      apply hi
      apply Fin.ext
      simpa using h
    simp [hi, hval]

@[simp] theorem machineDirectedObjectiveSumLastColumnBit_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumLastColumnBit
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      [decide (j = Fin.last m)] := by
  rw [machineDirectedObjectiveSumLastColumnBit,
    machineDirectedObjectiveSumColumn_canonicalState,
    machineDirectedObjectiveSumStateDimension_canonicalState,
    machineUnaryRulersEqualBit_replicate]
  by_cases hj : j = Fin.last m
  · simp [hj]
  · have hval : j.1 ≠ m := by
      intro h
      apply hj
      apply Fin.ext
      simpa using h
    simp [hj, hval]

@[simp] theorem machineDirectedObjectiveSumCandidate_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) :
    machineDirectedObjectiveSumCandidate
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      rawRatBinaryCode
        (acc.add (rawDirectedBetheObjectiveCoordinate tau A y p i j)) := by
  rw [machineDirectedObjectiveSumCandidate,
    machineDirectedObjectiveSumAcc_canonicalState,
    machineDirectedObjectiveSumCoordinateRawCode_canonicalState,
    machineRawRatAddCode_encode]
  rfl

theorem machineDirectedObjectiveSumNextAcc_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool)
    (hlarge :
      (rawRatBinaryCode
        (acc.add (rawDirectedBetheObjectiveCoordinate tau A y p i j))).length
          ≤ bound.length) :
    machineDirectedObjectiveSumNextAcc
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      rawRatBinaryCode
        (acc.add (rawDirectedBetheObjectiveCoordinate tau A y p i j)) := by
  rw [machineDirectedObjectiveSumNextAcc,
    machineDirectedObjectiveSumCandidate_canonicalState,
    machineDirectedObjectiveSumBound_canonicalState]
  exact (List.take_eq_self_iff _).mpr hlarge

theorem machineDirectedObjectiveSumNextRow_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) (hi : i ≠ Fin.last m)
    (hbound : m ≤ bound.length) :
    machineDirectedObjectiveSumNextRow
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      List.replicate (betheFloorScanNextFin i).1 true := by
  rw [machineDirectedObjectiveSumNextRow,
    machineDirectedObjectiveSumRow_canonicalState,
    machineDirectedObjectiveSumBound_canonicalState,
    betheFloorScanNextFin_val i hi,
    List.replicate_succ']
  apply (List.take_eq_self_iff _).mpr
  simp only [List.length_append, List.length_replicate,
    List.length_singleton]
  have hval : i.1 ≠ m := by
    intro h
    apply hi
    apply Fin.ext
    simpa using h
  have : i.1 + 1 ≤ m := by omega
  omega

theorem machineDirectedObjectiveSumNextColumn_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) (hj : j ≠ Fin.last m)
    (hbound : m ≤ bound.length) :
    machineDirectedObjectiveSumNextColumn
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      List.replicate (betheFloorScanNextFin j).1 true := by
  rw [machineDirectedObjectiveSumNextColumn,
    machineDirectedObjectiveSumColumn_canonicalState,
    machineDirectedObjectiveSumBound_canonicalState,
    betheFloorScanNextFin_val j hj,
    List.replicate_succ']
  apply (List.take_eq_self_iff _).mpr
  simp only [List.length_append, List.length_replicate,
    List.length_singleton]
  have hval : j.1 ≠ m := by
    intro h
    apply hj
    apply Fin.ext
    simpa using h
  have : j.1 + 1 ≤ m := by omega
  omega

theorem machineDirectedObjectiveSumFinish_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool)
    (hlarge :
      (rawRatBinaryCode
        (acc.add (rawDirectedBetheObjectiveCoordinate tau A y p i j))).length
          ≤ bound.length) :
    machineDirectedObjectiveSumFinish
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      machineDirectedObjectiveSumCanonicalState tau A y p i j
        (acc.add (rawDirectedBetheObjectiveCoordinate tau A y p i j))
        true bound := by
  rw [machineDirectedObjectiveSumFinish]
  simp only [machineDirectedObjectiveSumRow_canonicalState,
    machineDirectedObjectiveSumColumn_canonicalState,
    machineDirectedObjectiveSumNextAcc_canonicalState
      tau A y p i j acc done bound hlarge,
    machineDirectedObjectiveSumBound_canonicalState,
    machineDirectedObjectiveSumPayload_canonicalState]
  rfl

theorem machineDirectedObjectiveSumAdvanceRow_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) (hi : i ≠ Fin.last m)
    (hbound : m ≤ bound.length)
    (hlarge :
      (rawRatBinaryCode
        (acc.add (rawDirectedBetheObjectiveCoordinate tau A y p i j))).length
          ≤ bound.length) :
    machineDirectedObjectiveSumAdvanceRow
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      machineDirectedObjectiveSumCanonicalState tau A y p
        (betheFloorScanNextFin i) ⟨0, by omega⟩
        (acc.add (rawDirectedBetheObjectiveCoordinate tau A y p i j))
        done bound := by
  rw [machineDirectedObjectiveSumAdvanceRow]
  simp only [machineDirectedObjectiveSumNextRow_canonicalState
      tau A y p i j acc done bound hi hbound,
    machineDirectedObjectiveSumNextAcc_canonicalState
      tau A y p i j acc done bound hlarge,
    machineDirectedObjectiveSumBound_canonicalState,
    machineDirectedObjectiveSumDone_canonicalState,
    machineDirectedObjectiveSumPayload_canonicalState]
  rfl

theorem machineDirectedObjectiveSumAdvanceColumn_canonicalState
    {m : ℕ} (tau : ℚ)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (i j : Fin (m + 1)) (acc : RawRat) (done : Bool)
    (bound : List Bool) (hj : j ≠ Fin.last m)
    (hbound : m ≤ bound.length)
    (hlarge :
      (rawRatBinaryCode
        (acc.add (rawDirectedBetheObjectiveCoordinate tau A y p i j))).length
          ≤ bound.length) :
    machineDirectedObjectiveSumAdvanceColumn
        (machineDirectedObjectiveSumCanonicalState
          tau A y p i j acc done bound) =
      machineDirectedObjectiveSumCanonicalState tau A y p i
        (betheFloorScanNextFin j)
        (acc.add (rawDirectedBetheObjectiveCoordinate tau A y p i j))
        done bound := by
  rw [machineDirectedObjectiveSumAdvanceColumn]
  simp only [machineDirectedObjectiveSumRow_canonicalState,
    machineDirectedObjectiveSumNextColumn_canonicalState
      tau A y p i j acc done bound hj hbound,
    machineDirectedObjectiveSumNextAcc_canonicalState
      tau A y p i j acc done bound hlarge,
    machineDirectedObjectiveSumBound_canonicalState,
    machineDirectedObjectiveSumDone_canonicalState,
    machineDirectedObjectiveSumPayload_canonicalState]
  rfl

theorem machineDirectedObjectiveSumStep_semanticCode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (bound : List Bool)
    (state : DirectedObjectiveSumSemanticState m)
    (hbound : m ≤ bound.length)
    (hlarge :
      (rawRatBinaryCode
        (state.acc.add (rawDirectedBetheObjectiveCoordinate tau A y p
          state.row state.column))).length ≤ bound.length) :
    machineDirectedObjectiveSumStep
        (machineDirectedObjectiveSumSemanticCode tau A y p bound state) =
      machineDirectedObjectiveSumSemanticCode tau A y p bound
        (directedObjectiveSumSemanticStep tau A y p state) := by
  rcases state with ⟨i, j, acc, done⟩
  cases done
  · dsimp only [DirectedObjectiveSumSemanticState.row,
      DirectedObjectiveSumSemanticState.column,
      DirectedObjectiveSumSemanticState.acc,
      DirectedObjectiveSumSemanticState.done] at hlarge ⊢
    by_cases hcolumn : j = Fin.last m
    · by_cases hrow : i = Fin.last m
      · rw [machineDirectedObjectiveSumStep,
          machineDirectedObjectiveSumSemanticCode,
          machineDirectedObjectiveSumDone_canonicalState,
          machineHeadBit_cons, machineIfHead_false,
          machineDirectedObjectiveSumProcess,
          machineDirectedObjectiveSumLastColumnBit_canonicalState,
          machineHeadBit_cons]
        have hc : decide (j = Fin.last m) = true := by simp [hcolumn]
        have hr : decide (i = Fin.last m) = true := by simp [hrow]
        rw [hc, machineIfHead_true,
          machineDirectedObjectiveSumLastRowBit_canonicalState,
          machineHeadBit_cons, hr, machineIfHead_true,
          machineDirectedObjectiveSumFinish_canonicalState
            tau A y p i j acc false bound hlarge]
        simp [machineDirectedObjectiveSumSemanticCode,
          directedObjectiveSumSemanticStep, hcolumn, hrow]
      · rw [machineDirectedObjectiveSumStep,
          machineDirectedObjectiveSumSemanticCode,
          machineDirectedObjectiveSumDone_canonicalState,
          machineHeadBit_cons, machineIfHead_false,
          machineDirectedObjectiveSumProcess,
          machineDirectedObjectiveSumLastColumnBit_canonicalState,
          machineHeadBit_cons]
        have hc : decide (j = Fin.last m) = true := by simp [hcolumn]
        have hr : decide (i = Fin.last m) = false := by simp [hrow]
        rw [hc, machineIfHead_true,
          machineDirectedObjectiveSumLastRowBit_canonicalState,
          machineHeadBit_cons, hr, machineIfHead_false,
          machineDirectedObjectiveSumAdvanceRow_canonicalState
            tau A y p i j acc false bound hrow hbound hlarge]
        simp [machineDirectedObjectiveSumSemanticCode,
          directedObjectiveSumSemanticStep, hcolumn, hrow]
    · rw [machineDirectedObjectiveSumStep,
        machineDirectedObjectiveSumSemanticCode,
        machineDirectedObjectiveSumDone_canonicalState,
        machineHeadBit_cons, machineIfHead_false,
        machineDirectedObjectiveSumProcess,
        machineDirectedObjectiveSumLastColumnBit_canonicalState,
        machineHeadBit_cons]
      have hc : decide (j = Fin.last m) = false := by simp [hcolumn]
      rw [hc, machineIfHead_false,
        machineDirectedObjectiveSumAdvanceColumn_canonicalState
          tau A y p i j acc false bound hcolumn hbound hlarge]
      simp [machineDirectedObjectiveSumSemanticCode,
        directedObjectiveSumSemanticStep, hcolumn]
  · dsimp only [DirectedObjectiveSumSemanticState.row,
      DirectedObjectiveSumSemanticState.column,
      DirectedObjectiveSumSemanticState.acc,
      DirectedObjectiveSumSemanticState.done] at hlarge ⊢
    rw [machineDirectedObjectiveSumStep,
      machineDirectedObjectiveSumSemanticCode,
      machineDirectedObjectiveSumDone_canonicalState,
      machineHeadBit_cons, machineIfHead_true]
    simp [machineDirectedObjectiveSumSemanticCode,
      directedObjectiveSumSemanticStep]

@[simp] theorem machineDirectedObjectiveSumInit_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    machineDirectedObjectiveSumInit
        (machineDirectedObjectiveSumCanonicalWord tau A y p) =
      machineDirectedObjectiveSumSemanticCode tau A y p
        (machineDirectedObjectiveSumAccumulatorBound
          (machineDirectedObjectiveSumCanonicalWord tau A y p))
        (directedObjectiveSumSemanticInit m) := by
  simp [machineDirectedObjectiveSumInit,
    machineDirectedObjectiveSumSemanticCode,
    machineDirectedObjectiveSumCanonicalState,
    directedObjectiveSumSemanticInit]

def finalDirectedObjectiveSumSemanticState {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    DirectedObjectiveSumSemanticState m :=
  (directedObjectiveSumSemanticStep tau A y p)^[(m + 1) * (m + 1)]
    (directedObjectiveSumSemanticInit m)

def directedObjectiveSumSemanticStateAt {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p k : ℕ) :
    DirectedObjectiveSumSemanticState m :=
  (directedObjectiveSumSemanticStep tau A y p)^[k]
    (directedObjectiveSumSemanticInit m)

@[simp] theorem directedObjectiveSumSemanticStateAt_zero {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    directedObjectiveSumSemanticStateAt tau A y p 0 =
      directedObjectiveSumSemanticInit m := rfl

theorem directedObjectiveSumSemanticStateAt_succ {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p k : ℕ) :
    directedObjectiveSumSemanticStateAt tau A y p (k + 1) =
      directedObjectiveSumSemanticStep tau A y p
        (directedObjectiveSumSemanticStateAt tau A y p k) := by
  simp only [directedObjectiveSumSemanticStateAt,
    Function.iterate_succ_apply']

theorem directedObjectiveSumSemanticStateAt_acc_width {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p k : ℕ) :
    let B := rawDirectedObjectiveCoordinateWordBudget m
      (machineDirectedObjectiveSumCanonicalWord tau A y p).length
    rawRatWidth
        (directedObjectiveSumSemanticStateAt tau A y p k).acc ≤
      1 + k * (B + 1) := by
  let B := rawDirectedObjectiveCoordinateWordBudget m
    (machineDirectedObjectiveSumCanonicalWord tau A y p).length
  induction k with
  | zero =>
      simp [directedObjectiveSumSemanticStateAt,
        directedObjectiveSumSemanticInit, rawRatWidth_zero]
  | succ k ih =>
      let state := directedObjectiveSumSemanticStateAt tau A y p k
      have ih' : rawRatWidth state.acc ≤ 1 + k * (B + 1) := by
        simpa only [state, B] using ih
      have hcoordinate : rawRatWidth
          (rawDirectedBetheObjectiveCoordinate tau A y p
            state.row state.column) ≤ B := by
        simpa only [B] using
          rawDirectedBetheObjectiveCoordinate_width_le_word_budget
            tau A y p state.row state.column
      have hstep := directedObjectiveSumSemanticStep_acc_width
        (B := B) (C := 1 + k * (B + 1)) tau A y p state ih' hcoordinate
      rw [directedObjectiveSumSemanticStateAt_succ]
      change rawRatWidth
          (directedObjectiveSumSemanticStep tau A y p state).acc ≤
        1 + (k + 1) * (B + 1)
      simpa only [Nat.succ_eq_add_one] using hstep.trans (by
        ring_nf
        omega)

theorem rawDirectedObjectiveCoordinateWordBudget_le_pow
    {m L : ℕ} (hm : m ≤ L) :
    rawDirectedObjectiveCoordinateWordBudget m L ≤ (L + 16) ^ 20 := by
  let T := L + 16
  have hT16 : 16 ≤ T := by simp [T]
  have hTpos : 0 < T := by omega
  have hmT : m ≤ T := hm.trans (by simp [T])
  have hLT : L ≤ T := by simp [T]
  have hL1T : L + 1 ≤ T := by simp [T]
  have hmm := Nat.mul_le_mul hmT hmT
  have hcube0 := Nat.mul_le_mul hmm hL1T
  have hcube : m * m * (L + 1) ≤ T ^ 3 := by
    simpa [pow_succ, mul_assoc] using hcube0
  have haff : rawBetheAffineEntryWidthBudget m L ≤ 2 * T ^ 3 := by
    simp only [rawBetheAffineEntryWidthBudget]
    nlinarith [sq_nonneg T]
  have hX : rawDirectedObjectiveCoordinateWordXBudget m L ≤
      26 * T ^ 3 := by
    simp only [rawDirectedObjectiveCoordinateWordXBudget]
    nlinarith [sq_nonneg T]
  have hC : rawDirectedObjectiveCoordinateWordComplementBudget m L ≤
      315 * T ^ 3 := by
    simp only [rawDirectedObjectiveCoordinateWordComplementBudget]
    nlinarith [sq_nonneg T]
  have hlogA : rawScheduledLogWordBudget L L ≤ 2048 * T ^ 3 := by
    have hinner : L + 2 * L + 4 ≤ 4 * T := by omega
    have hsquare := Nat.pow_le_pow_left hinner 2
    have hlast : L + 2 ≤ 2 * T := by omega
    have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left 64 hsquare) hlast
    calc
      rawScheduledLogWordBudget L L =
          64 * (L + 2 * L + 4) ^ 2 * (L + 2) := rfl
      _ ≤ 64 * (4 * T) ^ 2 * (2 * T) := hmul
      _ = 2048 * T ^ 3 := by ring
  have hinnerX : L +
      2 * rawDirectedObjectiveCoordinateWordXBudget m L + 4 ≤
        54 * T ^ 3 := by
    nlinarith [sq_nonneg T]
  have hlastX : rawDirectedObjectiveCoordinateWordXBudget m L + 2 ≤
      28 * T ^ 3 := by
    nlinarith [sq_nonneg T]
  have hlogX : rawScheduledLogWordBudget L
      (rawDirectedObjectiveCoordinateWordXBudget m L) ≤
        5225472 * T ^ 9 := by
    have hsquare := Nat.pow_le_pow_left hinnerX 2
    have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left 64 hsquare) hlastX
    calc
      rawScheduledLogWordBudget L
          (rawDirectedObjectiveCoordinateWordXBudget m L) =
          64 * (L +
            2 * rawDirectedObjectiveCoordinateWordXBudget m L + 4) ^ 2 *
              (rawDirectedObjectiveCoordinateWordXBudget m L + 2) := rfl
      _ ≤ 64 * (54 * T ^ 3) ^ 2 * (28 * T ^ 3) := hmul
      _ = 5225472 * T ^ 9 := by ring
  have hinnerC : L +
      2 * rawDirectedObjectiveCoordinateWordComplementBudget m L + 4 ≤
        632 * T ^ 3 := by
    nlinarith [sq_nonneg T]
  have hlastC : rawDirectedObjectiveCoordinateWordComplementBudget m L + 2 ≤
      317 * T ^ 3 := by
    nlinarith [sq_nonneg T]
  have hlogC : rawScheduledLogWordBudget L
      (rawDirectedObjectiveCoordinateWordComplementBudget m L) ≤
        8103514112 * T ^ 9 := by
    have hsquare := Nat.pow_le_pow_left hinnerC 2
    have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left 64 hsquare) hlastC
    calc
      rawScheduledLogWordBudget L
          (rawDirectedObjectiveCoordinateWordComplementBudget m L) =
          64 * (L +
            2 * rawDirectedObjectiveCoordinateWordComplementBudget m L + 4) ^ 2 *
              (rawDirectedObjectiveCoordinateWordComplementBudget m L + 2) := rfl
      _ ≤ 64 * (632 * T ^ 3) ^ 2 * (317 * T ^ 3) := hmul
      _ = 8103514112 * T ^ 9 := by ring
  have hpow39 : T ^ 3 ≤ T ^ 9 :=
    Nat.pow_le_pow_right hTpos (by omega)
  have hbudget : rawDirectedObjectiveCoordinateWordBudget m L ≤
      8200000000 * T ^ 9 := by
    simp only [rawDirectedObjectiveCoordinateWordBudget]
    nlinarith
  have hconstant : 8200000000 ≤ 16 ^ 11 := by norm_num
  have hbasePow : 16 ^ 11 ≤ T ^ 11 := Nat.pow_le_pow_left hT16 11
  have hcoeff : 8200000000 ≤ T ^ 11 := hconstant.trans hbasePow
  have hmul := Nat.mul_le_mul_right (T ^ 9) hcoeff
  calc
    rawDirectedObjectiveCoordinateWordBudget m L ≤
        8200000000 * T ^ 9 := hbudget
    _ ≤ T ^ 11 * T ^ 9 := hmul
    _ = (L + 16) ^ 20 := by simp only [T]; ring

theorem machineDirectedObjectiveSumDimension_le_accumulatorBound {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    m ≤ (machineDirectedObjectiveSumAccumulatorBound
      (machineDirectedObjectiveSumCanonicalWord tau A y p)).length := by
  have hm : m ≤
      (machineDirectedObjectiveSumCanonicalWord tau A y p).length := by
    simp only [machineDirectedObjectiveSumCanonicalWord, pair_length,
      List.length_replicate]
    omega
  rw [machineDirectedObjectiveSumAccumulatorBound,
    machineIteratedBinaryWidth_length]
  exact hm.trans (certificateExpGuardWidth_self_le 6 _)

theorem machineDirectedObjectiveSumAccumulatorBound_dominates_next {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p k : ℕ)
    (hk : k < (m + 1) * (m + 1)) :
    let state := directedObjectiveSumSemanticStateAt tau A y p k
    (rawRatBinaryCode
      (state.acc.add (rawDirectedBetheObjectiveCoordinate tau A y p
        state.row state.column))).length ≤
      (machineDirectedObjectiveSumAccumulatorBound
        (machineDirectedObjectiveSumCanonicalWord tau A y p)).length := by
  let word := machineDirectedObjectiveSumCanonicalWord tau A y p
  let L := word.length
  let T := L + 16
  let B := rawDirectedObjectiveCoordinateWordBudget m L
  let state := directedObjectiveSumSemanticStateAt tau A y p k
  have hmL : m ≤ L := by
    simp only [L, word, machineDirectedObjectiveSumCanonicalWord,
      pair_length, List.length_replicate]
    omega
  have hT16 : 16 ≤ T := by simp [T]
  have hTpos : 0 < T := by omega
  have hm1T : m + 1 ≤ T := by
    dsimp only [T]
    omega
  have hworkSquare := Nat.mul_le_mul hm1T hm1T
  have hkT : k + 1 ≤ T ^ 2 := by
    have hk' : k + 1 ≤ (m + 1) * (m + 1) := by omega
    exact hk'.trans (by simpa only [pow_two] using hworkSquare)
  have hB : B ≤ T ^ 20 := by
    simpa only [B, T] using
      rawDirectedObjectiveCoordinateWordBudget_le_pow hmL
  have hacc : rawRatWidth state.acc ≤ 1 + k * (B + 1) := by
    simpa only [state, B, L, word] using
      directedObjectiveSumSemanticStateAt_acc_width tau A y p k
  have hcoordinate : rawRatWidth
      (rawDirectedBetheObjectiveCoordinate tau A y p
        state.row state.column) ≤ B := by
    simpa only [state, B, L, word] using
      rawDirectedBetheObjectiveCoordinate_width_le_word_budget
        tau A y p state.row state.column
  have hadd := rawRatWidth_add_le state.acc
    (rawDirectedBetheObjectiveCoordinate tau A y p
      state.row state.column)
  have hnext : rawRatWidth
      (state.acc.add (rawDirectedBetheObjectiveCoordinate tau A y p
        state.row state.column)) ≤ 1 + (k + 1) * (B + 1) := by
    calc
      _ ≤ rawRatWidth state.acc +
          rawRatWidth (rawDirectedBetheObjectiveCoordinate tau A y p
            state.row state.column) + 1 := hadd
      _ ≤ (1 + k * (B + 1)) + B + 1 :=
        Nat.add_le_add_right (Nat.add_le_add hacc hcoordinate) 1
      _ = 1 + (k + 1) * (B + 1) := by ring
  have hpow20pos : 1 ≤ T ^ 20 := by
    have hbase : 1 ≤ T := by omega
    exact one_le_pow₀ hbase
  have hB1 : B + 1 ≤ 2 * T ^ 20 := by omega
  have hproduct := Nat.mul_le_mul hkT hB1
  have hproductEq : T ^ 2 * (2 * T ^ 20) = 2 * T ^ 22 := by ring
  have hwidthMajor : rawRatWidth
      (state.acc.add (rawDirectedBetheObjectiveCoordinate tau A y p
        state.row state.column)) ≤ 3 * T ^ 22 := by
    calc
      _ ≤ 1 + (k + 1) * (B + 1) := hnext
      _ ≤ 1 + T ^ 2 * (2 * T ^ 20) :=
        Nat.add_le_add_left hproduct 1
      _ = 1 + 2 * T ^ 22 := by rw [hproductEq]
      _ ≤ 3 * T ^ 22 := by
        have hpow22 : 1 ≤ T ^ 22 := one_le_pow₀ (by omega)
        omega
  have hcode := rawRatBinaryCode_length_le_width
    (state.acc.add (rawDirectedBetheObjectiveCoordinate tau A y p
      state.row state.column))
  have hcodeMajor :
      (rawRatBinaryCode
        (state.acc.add (rawDirectedBetheObjectiveCoordinate tau A y p
          state.row state.column))).length ≤ 10 * T ^ 22 := by
    have hpow22 : 4 ≤ T ^ 22 := by
      have hbasePow := Nat.pow_le_pow_left hT16 22
      exact (by norm_num : 4 ≤ 16 ^ 22).trans hbasePow
    omega
  have hten : 10 ≤ T ^ 42 := by
    have hbasePow := Nat.pow_le_pow_left hT16 42
    exact (by norm_num : 10 ≤ 16 ^ 42).trans hbasePow
  have hmul := Nat.mul_le_mul_right (T ^ 22) hten
  have hcodePower :
      (rawRatBinaryCode
        (state.acc.add (rawDirectedBetheObjectiveCoordinate tau A y p
          state.row state.column))).length ≤ T ^ 64 := by
    calc
      _ ≤ 10 * T ^ 22 := hcodeMajor
      _ ≤ T ^ 42 * T ^ 22 := hmul
      _ = T ^ 64 := by ring
  rw [machineDirectedObjectiveSumAccumulatorBound,
    machineIteratedBinaryWidth_length]
  exact hcodePower.trans (by
    simpa only [T, L, word] using
      certificateExpGuardWidth_pow_lower 5
        (machineDirectedObjectiveSumCanonicalWord tau A y p).length)

theorem machineDirectedObjectiveSumIterate_semanticCode_of_large {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) (bound : List Bool)
    (hbound : m ≤ bound.length)
    (hlarge : ∀ k, k < (m + 1) * (m + 1) →
      let state := directedObjectiveSumSemanticStateAt tau A y p k
      (rawRatBinaryCode
        (state.acc.add (rawDirectedBetheObjectiveCoordinate tau A y p
          state.row state.column))).length ≤ bound.length) :
    ∀ k, k ≤ (m + 1) * (m + 1) →
      (machineDirectedObjectiveSumStep)^[k]
          (machineDirectedObjectiveSumSemanticCode tau A y p bound
            (directedObjectiveSumSemanticInit m)) =
        machineDirectedObjectiveSumSemanticCode tau A y p bound
          (directedObjectiveSumSemanticStateAt tau A y p k) := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
      have hklt : k < (m + 1) * (m + 1) := by omega
      rw [Function.iterate_succ_apply', ih (by omega)]
      have hstep := machineDirectedObjectiveSumStep_semanticCode tau A y p bound
        (directedObjectiveSumSemanticStateAt tau A y p k) hbound
        (hlarge k hklt)
      simpa only [directedObjectiveSumSemanticStateAt,
        Function.iterate_succ_apply'] using hstep

theorem machineDirectedObjectiveSumFinalState_encode_of_large {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (hlarge : ∀ k, k < (m + 1) * (m + 1) →
      let state := directedObjectiveSumSemanticStateAt tau A y p k
      (rawRatBinaryCode
        (state.acc.add (rawDirectedBetheObjectiveCoordinate tau A y p
          state.row state.column))).length ≤
        (machineDirectedObjectiveSumAccumulatorBound
          (machineDirectedObjectiveSumCanonicalWord tau A y p)).length) :
    machineDirectedObjectiveSumFinalState
        (machineDirectedObjectiveSumCanonicalWord tau A y p) =
      machineDirectedObjectiveSumSemanticCode tau A y p
        (machineDirectedObjectiveSumAccumulatorBound
          (machineDirectedObjectiveSumCanonicalWord tau A y p))
        (finalDirectedObjectiveSumSemanticState tau A y p) := by
  rw [machineDirectedObjectiveSumFinalState,
    machineDirectedObjectiveSumRuler_encode, List.length_replicate,
    machineDirectedObjectiveSumInit_encode]
  have hiterate := machineDirectedObjectiveSumIterate_semanticCode_of_large
    tau A y p
    (machineDirectedObjectiveSumAccumulatorBound
      (machineDirectedObjectiveSumCanonicalWord tau A y p))
    (machineDirectedObjectiveSumDimension_le_accumulatorBound tau A y p)
    hlarge ((m + 1) * (m + 1)) (by omega)
  simpa only [directedObjectiveSumSemanticStateAt,
    finalDirectedObjectiveSumSemanticState] using hiterate

def rawDirectedNegativeObjectiveSum {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) : RawRat :=
  (finalDirectedObjectiveSumSemanticState tau A y p).acc

theorem machineDirectedNegativeObjectiveSumRawCode_encode_of_large {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (hlarge : ∀ k, k < (m + 1) * (m + 1) →
      let state := directedObjectiveSumSemanticStateAt tau A y p k
      (rawRatBinaryCode
        (state.acc.add (rawDirectedBetheObjectiveCoordinate tau A y p
          state.row state.column))).length ≤
        (machineDirectedObjectiveSumAccumulatorBound
          (machineDirectedObjectiveSumCanonicalWord tau A y p)).length) :
    machineDirectedNegativeObjectiveSumRawCode
        (machineDirectedObjectiveSumCanonicalWord tau A y p) =
      rawRatBinaryCode (rawDirectedNegativeObjectiveSum tau A y p) := by
  rw [machineDirectedNegativeObjectiveSumRawCode,
    machineDirectedObjectiveSumFinalState_encode_of_large tau A y p hlarge]
  simp [machineDirectedObjectiveSumSemanticCode,
    rawDirectedNegativeObjectiveSum]

@[simp] theorem machineDirectedNegativeObjectiveSumRawCode_encode {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    machineDirectedNegativeObjectiveSumRawCode
        (machineDirectedObjectiveSumCanonicalWord tau A y p) =
      rawRatBinaryCode (rawDirectedNegativeObjectiveSum tau A y p) := by
  apply machineDirectedNegativeObjectiveSumRawCode_encode_of_large
  intro k hk
  exact machineDirectedObjectiveSumAccumulatorBound_dominates_next
    tau A y p k hk

/-! ## Mathematical value of the row-major sum -/

def directedNegativeObjectivePairValue {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (ij : Fin (m + 1) × Fin (m + 1)) : ℚ :=
  directedNegativeObjectiveCoordinateLower tau (A ij.1 ij.2)
    (betheAffineMatrixQ y ij.1 ij.2) p

def directedNegativeObjectivePrefix {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p k : ℕ) : ℚ :=
  ∑ ij ∈ Finset.univ.filter
      (fun ij : Fin (m + 1) × Fin (m + 1) =>
        betheFloorScanOrdinal ij.1 ij.2 < k),
    directedNegativeObjectivePairValue tau A y p ij

theorem directedNegativeObjectivePrefix_succ_of_ordinal {m k : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (row column : Fin (m + 1))
    (hordinal : betheFloorScanOrdinal row column = k) :
    directedNegativeObjectivePrefix tau A y p (k + 1) =
      directedNegativeObjectivePrefix tau A y p k +
        directedNegativeObjectiveCoordinateLower tau (A row column)
          (betheAffineMatrixQ y row column) p := by
  classical
  let current : Fin (m + 1) × Fin (m + 1) := (row, column)
  let prior := Finset.univ.filter
    (fun ij : Fin (m + 1) × Fin (m + 1) =>
      betheFloorScanOrdinal ij.1 ij.2 < k)
  have hcurrentNotMem : current ∉ prior := by
    simp only [current, prior, Finset.mem_filter, Finset.mem_univ,
      true_and, not_lt]
    omega
  have hfilter :
      Finset.univ.filter
          (fun ij : Fin (m + 1) × Fin (m + 1) =>
            betheFloorScanOrdinal ij.1 ij.2 < k + 1) =
        insert current prior := by
    ext ij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, current, prior]
    constructor
    · intro hlt
      by_cases hprior : betheFloorScanOrdinal ij.1 ij.2 < k
      · exact Or.inr hprior
      · left
        apply betheFloorScanOrdinal_injective m
        have heq : betheFloorScanOrdinal ij.1 ij.2 = k := by omega
        exact heq.trans hordinal.symm
    · intro hmem
      rcases hmem with hij | hprior
      · subst ij
        simpa only [Prod.fst, Prod.snd, hordinal] using Nat.lt_succ_self k
      · omega
  rw [directedNegativeObjectivePrefix, hfilter,
    Finset.sum_insert hcurrentNotMem]
  simp only [directedNegativeObjectivePrefix, prior,
    directedNegativeObjectivePairValue]
  ring

theorem directedNegativeObjectivePrefix_zero {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    directedNegativeObjectivePrefix tau A y p 0 = 0 := by
  simp [directedNegativeObjectivePrefix]

theorem directedNegativeObjectivePrefix_full {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    directedNegativeObjectivePrefix tau A y p
        ((m + 1) * (m + 1)) =
      directedNegativeObjectiveLower tau A (betheAffineMatrixQ y) p := by
  classical
  have hfilter :
      Finset.univ.filter
          (fun ij : Fin (m + 1) × Fin (m + 1) =>
            betheFloorScanOrdinal ij.1 ij.2 < (m + 1) * (m + 1)) =
        Finset.univ := by
    ext ij
    simp [betheFloorScanOrdinal_lt_square]
  rw [directedNegativeObjectivePrefix, hfilter,
    Fintype.sum_prod_type]
  rfl

def DirectedObjectiveSumValueInvariant {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p k : ℕ)
    (state : DirectedObjectiveSumSemanticState m) : Prop :=
  (state.done = true ∧ (m + 1) * (m + 1) ≤ k ∧
      state.acc.value =
        directedNegativeObjectiveLower tau A (betheAffineMatrixQ y) p) ∨
  (state.done = false ∧
      betheFloorScanOrdinal state.row state.column = k ∧
      state.acc.value = directedNegativeObjectivePrefix tau A y p k)

theorem directedObjectiveSumSemanticInit_valueInvariant {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    DirectedObjectiveSumValueInvariant tau A y p 0
      (directedObjectiveSumSemanticInit m) := by
  right
  refine ⟨rfl, ?_, ?_⟩
  · simp [directedObjectiveSumSemanticInit, betheFloorScanOrdinal]
  · rw [directedNegativeObjectivePrefix_zero]
    simp [directedObjectiveSumSemanticInit]

theorem directedObjectiveSumSemanticStep_valueInvariant {m k : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (state : DirectedObjectiveSumSemanticState m)
    (hinvariant : DirectedObjectiveSumValueInvariant tau A y p k state) :
    DirectedObjectiveSumValueInvariant tau A y p (k + 1)
      (directedObjectiveSumSemanticStep tau A y p state) := by
  rcases hinvariant with hdone | hactive
  · rcases hdone with ⟨hdone, hwork, hvalue⟩
    have hstep : directedObjectiveSumSemanticStep tau A y p state = state := by
      simp [directedObjectiveSumSemanticStep, hdone]
    rw [hstep]
    left
    exact ⟨hdone, hwork.trans (by omega), hvalue⟩
  · rcases hactive with ⟨hdone, hordinal, hvalue⟩
    have hnextValue :
        (state.acc.add (rawDirectedBetheObjectiveCoordinate tau A y p
          state.row state.column)).value =
          directedNegativeObjectivePrefix tau A y p (k + 1) := by
      rw [RawRat.value_add, hvalue,
        rawDirectedBetheObjectiveCoordinate,
        rawDirectedNegativeObjectiveCoordinateLower_value]
      exact (directedNegativeObjectivePrefix_succ_of_ordinal
        tau A y p state.row state.column hordinal).symm
    by_cases hcolumn : state.column = Fin.last m
    · by_cases hrow : state.row = Fin.last m
      · have hstep : directedObjectiveSumSemanticStep tau A y p state =
            { state with
              acc := state.acc.add
                (rawDirectedBetheObjectiveCoordinate tau A y p
                  state.row state.column)
              done := true } := by
          simp [directedObjectiveSumSemanticStep, hdone, hcolumn, hrow]
        rw [hstep]
        left
        refine ⟨rfl, ?_, ?_⟩
        · rw [hrow, hcolumn] at hordinal
          rw [← hordinal, betheFloorScanOrdinal_last_last]
        · change
            (state.acc.add (rawDirectedBetheObjectiveCoordinate tau A y p
              state.row state.column)).value = _
          rw [hnextValue]
          have htotal : k + 1 = (m + 1) * (m + 1) := by
            rw [← hordinal, hrow, hcolumn,
              betheFloorScanOrdinal_last_last]
          rw [htotal, directedNegativeObjectivePrefix_full]
      · have hstep : directedObjectiveSumSemanticStep tau A y p state =
            { state with
              row := betheFloorScanNextFin state.row
              column := ⟨0, by omega⟩
              acc := state.acc.add
                (rawDirectedBetheObjectiveCoordinate tau A y p
                  state.row state.column) } := by
          simp [directedObjectiveSumSemanticStep, hdone, hcolumn, hrow]
        rw [hstep]
        right
        refine ⟨hdone, ?_, hnextValue⟩
        rw [betheFloorScanOrdinal_nextRow state.row hrow,
          ← hcolumn, hordinal]
    · have hstep : directedObjectiveSumSemanticStep tau A y p state =
          { state with
            column := betheFloorScanNextFin state.column
            acc := state.acc.add
              (rawDirectedBetheObjectiveCoordinate tau A y p
                state.row state.column) } := by
        simp [directedObjectiveSumSemanticStep, hdone, hcolumn]
      rw [hstep]
      right
      refine ⟨hdone, ?_, hnextValue⟩
      rw [betheFloorScanOrdinal_nextColumn state.row state.column hcolumn,
        hordinal]

theorem directedObjectiveSumSemanticStateAt_valueInvariant {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) : ∀ k,
    DirectedObjectiveSumValueInvariant tau A y p k
      (directedObjectiveSumSemanticStateAt tau A y p k) := by
  intro k
  induction k with
  | zero => exact directedObjectiveSumSemanticInit_valueInvariant tau A y p
  | succ k ih =>
      rw [directedObjectiveSumSemanticStateAt,
        Function.iterate_succ_apply']
      exact directedObjectiveSumSemanticStep_valueInvariant tau A y p _ ih

theorem rawDirectedNegativeObjectiveSum_value {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ) :
    (rawDirectedNegativeObjectiveSum tau A y p).value =
      directedNegativeObjectiveLower tau A (betheAffineMatrixQ y) p := by
  have hinvariant := directedObjectiveSumSemanticStateAt_valueInvariant
    tau A y p ((m + 1) * (m + 1))
  rcases hinvariant with hdone | hactive
  · exact hdone.2.2
  · have hord := hactive.2.1
    have hlt := betheFloorScanOrdinal_lt_square
      (directedObjectiveSumSemanticStateAt tau A y p
        ((m + 1) * (m + 1))).row
      (directedObjectiveSumSemanticStateAt tau A y p
        ((m + 1) * (m + 1))).column
    omega

end BeyondBethe
