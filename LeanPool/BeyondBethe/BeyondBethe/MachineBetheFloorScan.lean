/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineBetheFloorTest
public import LeanPool.BeyondBethe.BeyondBethe.MachineBoundedUnary

/-!
# Finite-word row-major scan of all Bethe floor constraints

The scan keeps unary row and column counters, a one-bit found flag, a one-bit
done flag, and the immutable input payload.  It examines the recovered
`(m+1)`-by-`(m+1)` matrix in row-major order and freezes at the first strict
floor violation.  Its iteration ruler is constructed, in polynomial time,
as exactly `(m+1)^2` unary bits on canonical inputs.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-! ## Input and state layout -/

/-- Extracts the unary dimension parameter from the floor-scan input. -/
def machineBetheFloorScanDimension (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Extracts the paired threshold and coordinate vector from the floor-scan input. -/
def machineBetheFloorScanRest (word : List Bool) : List Bool :=
  machinePairSecond word

/-- Extracts the encoded rational floor threshold from the scan input. -/
def machineBetheFloorScanThreshold (word : List Bool) : List Bool :=
  machinePairFirst (machineBetheFloorScanRest word)

/-- Extracts the encoded rational coordinate vector from the scan input. -/
def machineBetheFloorScanVector (word : List Bool) : List Bool :=
  machinePairSecond (machineBetheFloorScanRest word)

/-- Encodes a floor-scan state as row, column, found flag, done flag, and input payload. -/
def machineBetheFloorScanPack (row column found done payload : List Bool) :
    List Bool :=
  pair row (pair column (pair found (pair done payload)))

/-- Extracts the current unary row index from the floor-scan state. -/
def machineBetheFloorScanRow (state : List Bool) : List Bool :=
  machinePairFirst state

/-- Extracts the current unary column index from the floor-scan state. -/
def machineBetheFloorScanColumn (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond state)

/-- Extracts the flag recording discovery of an entry below the floor threshold. -/
def machineBetheFloorScanFound (state : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machinePairSecond state))

/-- Extracts the flag recording completion of the floor scan. -/
def machineBetheFloorScanDone (state : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

/-- Extracts the original scan input stored in the state. -/
def machineBetheFloorScanPayload (state : List Bool) : List Bool :=
  machinePairSecond
    (machinePairSecond (machinePairSecond (machinePairSecond state)))

/-- Reads the unary dimension parameter from the state's stored input. -/
def machineBetheFloorScanStateDimension (state : List Bool) : List Bool :=
  machineBetheFloorScanDimension (machineBetheFloorScanPayload state)

/-- Reads the rational floor threshold from the state's stored input. -/
def machineBetheFloorScanStateThreshold (state : List Bool) : List Bool :=
  machineBetheFloorScanThreshold (machineBetheFloorScanPayload state)

/-- Reads the rational coordinate vector from the state's stored input. -/
def machineBetheFloorScanStateVector (state : List Bool) : List Bool :=
  machineBetheFloorScanVector (machineBetheFloorScanPayload state)

/-- Tests whether the current row ruler equals the dimension ruler, marking the last row. -/
def machineBetheFloorScanLastRowBit (state : List Bool) : List Bool :=
  machineUnaryRulersEqualBit (machineBetheFloorScanRow state)
    (machineBetheFloorScanStateDimension state)

/-- Tests whether the current column ruler equals the dimension ruler, marking the last column. -/
def machineBetheFloorScanLastColumnBit (state : List Bool) : List Bool :=
  machineUnaryRulersEqualBit (machineBetheFloorScanColumn state)
    (machineBetheFloorScanStateDimension state)

/-- Assembles the dimension, current indices, and coordinate vector for an affine-entry query. -/
def machineBetheFloorScanEntryWord (state : List Bool) : List Bool :=
  pair (machineBetheFloorScanStateDimension state)
    (pair (machineBetheFloorScanRow state)
      (pair (machineBetheFloorScanColumn state)
        (machineBetheFloorScanStateVector state)))

/-- Pairs the floor threshold with the current affine-entry query. -/
def machineBetheFloorScanTestWord (state : List Bool) : List Bool :=
  pair (machineBetheFloorScanStateThreshold state)
    (machineBetheFloorScanEntryWord state)

/-- Tests whether the current affine matrix entry violates the floor constraint. -/
def machineBetheFloorScanViolationBit (state : List Bool) : List Bool :=
  machineBetheFloorViolationBit (machineBetheFloorScanTestWord state)

/-- Increments the current unary row index by appending one bit. -/
def machineBetheFloorScanNextRow (state : List Bool) : List Bool :=
  machineBetheFloorScanRow state ++ [true]

/-- Increments the current unary column index by appending one bit. -/
def machineBetheFloorScanNextColumn (state : List Bool) : List Bool :=
  machineBetheFloorScanColumn state ++ [true]

/-- Sets the found flag while retaining the current indices and input payload. -/
def machineBetheFloorScanMarkFound (state : List Bool) : List Bool :=
  machineBetheFloorScanPack (machineBetheFloorScanRow state)
    (machineBetheFloorScanColumn state) [true]
    (machineBetheFloorScanDone state)
    (machineBetheFloorScanPayload state)

/-- Sets the done flag while retaining the current indices and input payload. -/
def machineBetheFloorScanFinish (state : List Bool) : List Bool :=
  machineBetheFloorScanPack (machineBetheFloorScanRow state)
    (machineBetheFloorScanColumn state)
    (machineBetheFloorScanFound state) [true]
    (machineBetheFloorScanPayload state)

/-- Advances to the next row and resets the column index to zero. -/
def machineBetheFloorScanAdvanceRow (state : List Bool) : List Bool :=
  machineBetheFloorScanPack (machineBetheFloorScanNextRow state) []
    (machineBetheFloorScanFound state) (machineBetheFloorScanDone state)
    (machineBetheFloorScanPayload state)

/-- Advances the column index while retaining the current row and flags. -/
def machineBetheFloorScanAdvanceColumn (state : List Bool) : List Bool :=
  machineBetheFloorScanPack (machineBetheFloorScanRow state)
    (machineBetheFloorScanNextColumn state)
    (machineBetheFloorScanFound state) (machineBetheFloorScanDone state)
    (machineBetheFloorScanPayload state)

/-- Advances in row-major order, marking completion after the final matrix entry. -/
def machineBetheFloorScanAdvance (state : List Bool) : List Bool :=
  machineIfHead (machineHeadBit (machineBetheFloorScanLastColumnBit state))
    (machineIfHead (machineHeadBit (machineBetheFloorScanLastRowBit state))
      (machineBetheFloorScanFinish state)
      (machineBetheFloorScanAdvanceRow state))
    (machineBetheFloorScanAdvanceColumn state)

/-- Marks a floor violation at the current entry or advances to the next entry. -/
def machineBetheFloorScanProcess (state : List Bool) : List Bool :=
  machineIfHead (machineHeadBit (machineBetheFloorScanViolationBit state))
    (machineBetheFloorScanMarkFound state)
    (machineBetheFloorScanAdvance state)

/-- Performs one floor-scan step, leaving found or completed states fixed. -/
def machineBetheFloorScanStep (state : List Bool) : List Bool :=
  machineIfHead (machineHeadBit (machineBetheFloorScanFound state)) state
    (machineIfHead (machineHeadBit (machineBetheFloorScanDone state)) state
      (machineBetheFloorScanProcess state))

/-- Initializes the floor scan at row and column zero with both flags false. -/
def machineBetheFloorScanInit (word : List Bool) : List Bool :=
  machineBetheFloorScanPack [] [] [false] [false] word

/-! ## Exact polynomial iteration ruler -/

/-- Computes binary bits for the length of the input's dimension ruler. -/
def machineBetheFloorScanDimensionBits (word : List Bool) : List Bool :=
  machineLengthBits (machineBetheFloorScanDimension word)

/-- Computes binary bits for one plus the dimension-ruler length. -/
def machineBetheFloorScanOrderBits (word : List Bool) : List Bool :=
  machineBinaryAddBits
    (pair (machineBetheFloorScanDimensionBits word) [true])

/-- Computes the square of one plus the dimension-ruler length as binary bits. -/
def machineBetheFloorScanWorkBits (word : List Bool) : List Bool :=
  machineBinaryMulBits
    (pair (machineBetheFloorScanOrderBits word)
      (machineBetheFloorScanOrderBits word))

/-- Supplies the binary-multiplication width bound used to construct the scan ruler. -/
def machineBetheFloorScanGuard (word : List Bool) : List Bool :=
  machineBinaryMulWidth word

/-- Converts the square of the matrix order to a unary iteration ruler within the guard bound. -/
def machineBetheFloorScanRuler (word : List Bool) : List Bool :=
  machineBoundedUnary
    (pair (machineBetheFloorScanGuard word)
      (machineBetheFloorScanWorkBits word))

/-- Applies the binary-multiplication width bound twice to bound encoded scan components. -/
def machineBetheFloorScanStateEnvelope (word : List Bool) : List Bool :=
  machineBinaryMulWidth (machineBinaryMulWidth word)

/-- Packs five copies of the state envelope to provide an encoded-state width bound. -/
def machineBetheFloorScanWidth (word : List Bool) : List Bool :=
  let bound := machineBetheFloorScanStateEnvelope word
  machineBetheFloorScanPack bound bound bound bound bound

/-- Runs the floor-scan step for the number of iterations specified by its unary ruler. -/
def machineBetheFloorScanFinalState (word : List Bool) : List Bool :=
  (machineBetheFloorScanStep)^[(machineBetheFloorScanRuler word).length]
    (machineBetheFloorScanInit word)

/-- The public result is a found bit followed by the unary row and column of
the first violation.  When the bit is false the two counters are ignored. -/
def machineBetheFloorScanResultCode (word : List Bool) : List Bool :=
  pair (machineBetheFloorScanFound (machineBetheFloorScanFinalState word))
    (pair (machineBetheFloorScanRow (machineBetheFloorScanFinalState word))
      (machineBetheFloorScanColumn
        (machineBetheFloorScanFinalState word)))

/-! ## Polynomial-time closure -/

theorem machineBetheFloorScanDimension_mem_FP :
    machineBetheFloorScanDimension ∈ FP := machinePairFirst_mem_FP

theorem machineBetheFloorScanRest_mem_FP :
    machineBetheFloorScanRest ∈ FP := machinePairSecond_mem_FP

theorem machineBetheFloorScanThreshold_mem_FP :
    machineBetheFloorScanThreshold ∈ FP := by
  simpa only [machineBetheFloorScanThreshold] using!
    machineCompose_mem_FP machineBetheFloorScanRest_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheFloorScanVector_mem_FP :
    machineBetheFloorScanVector ∈ FP := by
  simpa only [machineBetheFloorScanVector] using!
    machineCompose_mem_FP machineBetheFloorScanRest_mem_FP
      machinePairSecond_mem_FP

theorem machineBetheFloorScanRow_mem_FP :
    machineBetheFloorScanRow ∈ FP := machinePairFirst_mem_FP

theorem machineBetheFloorScanColumn_mem_FP :
    machineBetheFloorScanColumn ∈ FP := by
  simpa only [machineBetheFloorScanColumn] using!
    machineCompose_mem_FP machinePairSecond_mem_FP machinePairFirst_mem_FP

theorem machineBetheFloorScanFound_mem_FP :
    machineBetheFloorScanFound ∈ FP := by
  have htail := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineBetheFloorScanFound] using!
    machineCompose_mem_FP htail machinePairFirst_mem_FP

theorem machineBetheFloorScanDone_mem_FP :
    machineBetheFloorScanDone ∈ FP := by
  have htailTwo := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have htailThree := machineCompose_mem_FP htailTwo machinePairSecond_mem_FP
  simpa only [machineBetheFloorScanDone] using!
    machineCompose_mem_FP htailThree machinePairFirst_mem_FP

theorem machineBetheFloorScanPayload_mem_FP :
    machineBetheFloorScanPayload ∈ FP := by
  have htailTwo := machineCompose_mem_FP machinePairSecond_mem_FP
    machinePairSecond_mem_FP
  have htailThree := machineCompose_mem_FP htailTwo machinePairSecond_mem_FP
  simpa only [machineBetheFloorScanPayload] using!
    machineCompose_mem_FP htailThree machinePairSecond_mem_FP

theorem machineBetheFloorScanStateDimension_mem_FP :
    machineBetheFloorScanStateDimension ∈ FP := by
  simpa only [machineBetheFloorScanStateDimension] using!
    machineCompose_mem_FP machineBetheFloorScanPayload_mem_FP
      machineBetheFloorScanDimension_mem_FP

theorem machineBetheFloorScanStateThreshold_mem_FP :
    machineBetheFloorScanStateThreshold ∈ FP := by
  simpa only [machineBetheFloorScanStateThreshold] using!
    machineCompose_mem_FP machineBetheFloorScanPayload_mem_FP
      machineBetheFloorScanThreshold_mem_FP

theorem machineBetheFloorScanStateVector_mem_FP :
    machineBetheFloorScanStateVector ∈ FP := by
  simpa only [machineBetheFloorScanStateVector] using!
    machineCompose_mem_FP machineBetheFloorScanPayload_mem_FP
      machineBetheFloorScanVector_mem_FP

theorem machineBetheFloorScanLastRowBit_mem_FP :
    machineBetheFloorScanLastRowBit ∈ FP :=
  machineUnaryRulersEqualBit_mem_FP machineBetheFloorScanRow_mem_FP
    machineBetheFloorScanStateDimension_mem_FP

theorem machineBetheFloorScanLastColumnBit_mem_FP :
    machineBetheFloorScanLastColumnBit ∈ FP :=
  machineUnaryRulersEqualBit_mem_FP machineBetheFloorScanColumn_mem_FP
    machineBetheFloorScanStateDimension_mem_FP

theorem machineBetheFloorScanEntryWord_mem_FP :
    machineBetheFloorScanEntryWord ∈ FP :=
  machinePair_mem_FP machineBetheFloorScanStateDimension_mem_FP
    (machinePair_mem_FP machineBetheFloorScanRow_mem_FP
      (machinePair_mem_FP machineBetheFloorScanColumn_mem_FP
        machineBetheFloorScanStateVector_mem_FP))

theorem machineBetheFloorScanTestWord_mem_FP :
    machineBetheFloorScanTestWord ∈ FP :=
  machinePair_mem_FP machineBetheFloorScanStateThreshold_mem_FP
    machineBetheFloorScanEntryWord_mem_FP

theorem machineBetheFloorScanViolationBit_mem_FP :
    machineBetheFloorScanViolationBit ∈ FP := by
  simpa only [machineBetheFloorScanViolationBit] using!
    machineCompose_mem_FP machineBetheFloorScanTestWord_mem_FP
      machineBetheFloorViolationBit_mem_FP

theorem machineBetheFloorScanNextRow_mem_FP :
    machineBetheFloorScanNextRow ∈ FP :=
  machineAppend_mem_FP machineBetheFloorScanRow_mem_FP
    (machineConst_mem_FP [true])

theorem machineBetheFloorScanNextColumn_mem_FP :
    machineBetheFloorScanNextColumn ∈ FP :=
  machineAppend_mem_FP machineBetheFloorScanColumn_mem_FP
    (machineConst_mem_FP [true])

theorem machineBetheFloorScanMarkFound_mem_FP :
    machineBetheFloorScanMarkFound ∈ FP :=
  machinePair_mem_FP machineBetheFloorScanRow_mem_FP
    (machinePair_mem_FP machineBetheFloorScanColumn_mem_FP
      (machinePair_mem_FP (machineConst_mem_FP [true])
        (machinePair_mem_FP machineBetheFloorScanDone_mem_FP
          machineBetheFloorScanPayload_mem_FP)))

theorem machineBetheFloorScanFinish_mem_FP :
    machineBetheFloorScanFinish ∈ FP :=
  machinePair_mem_FP machineBetheFloorScanRow_mem_FP
    (machinePair_mem_FP machineBetheFloorScanColumn_mem_FP
      (machinePair_mem_FP machineBetheFloorScanFound_mem_FP
        (machinePair_mem_FP (machineConst_mem_FP [true])
          machineBetheFloorScanPayload_mem_FP)))

theorem machineBetheFloorScanAdvanceRow_mem_FP :
    machineBetheFloorScanAdvanceRow ∈ FP :=
  machinePair_mem_FP machineBetheFloorScanNextRow_mem_FP
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP machineBetheFloorScanFound_mem_FP
        (machinePair_mem_FP machineBetheFloorScanDone_mem_FP
          machineBetheFloorScanPayload_mem_FP)))

theorem machineBetheFloorScanAdvanceColumn_mem_FP :
    machineBetheFloorScanAdvanceColumn ∈ FP :=
  machinePair_mem_FP machineBetheFloorScanRow_mem_FP
    (machinePair_mem_FP machineBetheFloorScanNextColumn_mem_FP
      (machinePair_mem_FP machineBetheFloorScanFound_mem_FP
        (machinePair_mem_FP machineBetheFloorScanDone_mem_FP
          machineBetheFloorScanPayload_mem_FP)))

theorem machineBetheFloorScanAdvance_mem_FP :
    machineBetheFloorScanAdvance ∈ FP := by
  have hlastRowHead := machineCompose_mem_FP
    machineBetheFloorScanLastRowBit_mem_FP machineHeadBit_mem_FP
  have hlastColumnHead := machineCompose_mem_FP
    machineBetheFloorScanLastColumnBit_mem_FP machineHeadBit_mem_FP
  have hlast := machineIfHead_mem_FP
    hlastRowHead
    machineBetheFloorScanFinish_mem_FP
    machineBetheFloorScanAdvanceRow_mem_FP
  exact machineIfHead_mem_FP hlastColumnHead
    hlast machineBetheFloorScanAdvanceColumn_mem_FP

theorem machineBetheFloorScanProcess_mem_FP :
    machineBetheFloorScanProcess ∈ FP := by
  have hhead := machineCompose_mem_FP
    machineBetheFloorScanViolationBit_mem_FP machineHeadBit_mem_FP
  exact machineIfHead_mem_FP hhead machineBetheFloorScanMarkFound_mem_FP
    machineBetheFloorScanAdvance_mem_FP

theorem machineBetheFloorScanStep_mem_FP :
    machineBetheFloorScanStep ∈ FP := by
  have hfoundHead := machineCompose_mem_FP
    machineBetheFloorScanFound_mem_FP machineHeadBit_mem_FP
  have hdoneHead := machineCompose_mem_FP
    machineBetheFloorScanDone_mem_FP machineHeadBit_mem_FP
  have hnotFound := machineIfHead_mem_FP
    hdoneHead id_mem_FP
    machineBetheFloorScanProcess_mem_FP
  exact machineIfHead_mem_FP hfoundHead id_mem_FP
    hnotFound

theorem machineBetheFloorScanInit_mem_FP :
    machineBetheFloorScanInit ∈ FP :=
  machinePair_mem_FP (machineConst_mem_FP [])
    (machinePair_mem_FP (machineConst_mem_FP [])
      (machinePair_mem_FP (machineConst_mem_FP [false])
        (machinePair_mem_FP (machineConst_mem_FP [false]) id_mem_FP)))

theorem machineBetheFloorScanDimensionBits_mem_FP :
    machineBetheFloorScanDimensionBits ∈ FP := by
  simpa only [machineBetheFloorScanDimensionBits] using!
    machineCompose_mem_FP machineBetheFloorScanDimension_mem_FP
      machineLengthBits_mem_FP

theorem machineBetheFloorScanOrderBits_mem_FP :
    machineBetheFloorScanOrderBits ∈ FP := by
  have hinput := machinePair_mem_FP
    machineBetheFloorScanDimensionBits_mem_FP
    (machineConst_mem_FP [true])
  simpa only [machineBetheFloorScanOrderBits] using!
    machineCompose_mem_FP hinput machineBinaryAddBits_mem_FP

theorem machineBetheFloorScanWorkBits_mem_FP :
    machineBetheFloorScanWorkBits ∈ FP := by
  have hinput := machinePair_mem_FP machineBetheFloorScanOrderBits_mem_FP
    machineBetheFloorScanOrderBits_mem_FP
  simpa only [machineBetheFloorScanWorkBits] using!
    machineCompose_mem_FP hinput machineBinaryMulBits_mem_FP

theorem machineBetheFloorScanGuard_mem_FP :
    machineBetheFloorScanGuard ∈ FP := machineBinaryMulWidth_mem_FP

theorem machineBetheFloorScanRuler_mem_FP :
    machineBetheFloorScanRuler ∈ FP := by
  have hinput := machinePair_mem_FP machineBetheFloorScanGuard_mem_FP
    machineBetheFloorScanWorkBits_mem_FP
  simpa only [machineBetheFloorScanRuler] using!
    machineCompose_mem_FP hinput machineBoundedUnary_mem_FP

theorem machineBetheFloorScanStateEnvelope_mem_FP :
    machineBetheFloorScanStateEnvelope ∈ FP := by
  simpa only [machineBetheFloorScanStateEnvelope] using!
    machineCompose_mem_FP machineBinaryMulWidth_mem_FP
      machineBinaryMulWidth_mem_FP

theorem machineBetheFloorScanWidth_mem_FP :
    machineBetheFloorScanWidth ∈ FP := by
  have hbound := machineBetheFloorScanStateEnvelope_mem_FP
  exact machinePair_mem_FP hbound
    (machinePair_mem_FP hbound
      (machinePair_mem_FP hbound (machinePair_mem_FP hbound hbound)))

/-! ## A global state envelope for the Cobham iteration -/

@[simp] theorem machineBetheFloorScanRow_pack
    (row column found done payload) :
    machineBetheFloorScanRow
        (machineBetheFloorScanPack row column found done payload) = row := by
  simp [machineBetheFloorScanRow, machineBetheFloorScanPack]

@[simp] theorem machineBetheFloorScanColumn_pack
    (row column found done payload) :
    machineBetheFloorScanColumn
        (machineBetheFloorScanPack row column found done payload) = column := by
  simp [machineBetheFloorScanColumn, machineBetheFloorScanPack]

@[simp] theorem machineBetheFloorScanFound_pack
    (row column found done payload) :
    machineBetheFloorScanFound
        (machineBetheFloorScanPack row column found done payload) = found := by
  simp [machineBetheFloorScanFound, machineBetheFloorScanPack]

@[simp] theorem machineBetheFloorScanDone_pack
    (row column found done payload) :
    machineBetheFloorScanDone
        (machineBetheFloorScanPack row column found done payload) = done := by
  simp [machineBetheFloorScanDone, machineBetheFloorScanPack]

@[simp] theorem machineBetheFloorScanPayload_pack
    (row column found done payload) :
    machineBetheFloorScanPayload
        (machineBetheFloorScanPack row column found done payload) = payload := by
  simp [machineBetheFloorScanPayload, machineBetheFloorScanPack]

/-- Bounds a canonically packed scan state's index lengths, single-bit flags, and payload
length. -/
def MachineBetheFloorScanStateBound
    (word : List Bool) (iterations : ℕ) (state : List Bool) : Prop :=
  state = machineBetheFloorScanPack
      (machineBetheFloorScanRow state)
      (machineBetheFloorScanColumn state)
      (machineBetheFloorScanFound state)
      (machineBetheFloorScanDone state)
      (machineBetheFloorScanPayload state) ∧
    (machineBetheFloorScanRow state).length ≤ word.length + iterations ∧
    (machineBetheFloorScanColumn state).length ≤ word.length + iterations ∧
    (machineBetheFloorScanFound state).length ≤ 1 ∧
    (machineBetheFloorScanDone state).length ≤ 1 ∧
    (machineBetheFloorScanPayload state).length ≤ word.length

theorem machineBetheFloorScanInit_bound (word : List Bool) :
    MachineBetheFloorScanStateBound word 0
      (machineBetheFloorScanInit word) := by
  simp [MachineBetheFloorScanStateBound, machineBetheFloorScanInit]

@[simp] theorem machineIfHead_nil_floorScan
    (whenTrue whenFalse : List Bool) :
    machineIfHead [] whenTrue whenFalse = [] := by
  simp [machineIfHead, Cobham.selectHead]

theorem machineBetheFloorScanMarkFound_bound {word state : List Bool}
    {iterations : ℕ}
    (hs : MachineBetheFloorScanStateBound word iterations state) :
    MachineBetheFloorScanStateBound word (iterations + 1)
      (machineBetheFloorScanMarkFound state) := by
  rcases hs with ⟨hdecomp, hrow, hcolumn, hfound, hdone, hpayload⟩
  simp only [machineBetheFloorScanMarkFound,
    MachineBetheFloorScanStateBound,
    machineBetheFloorScanRow_pack, machineBetheFloorScanColumn_pack,
    machineBetheFloorScanFound_pack, machineBetheFloorScanDone_pack,
    machineBetheFloorScanPayload_pack, List.length_singleton]
  exact ⟨trivial, hrow.trans (by omega), hcolumn.trans (by omega),
    by simp, hdone, hpayload⟩

theorem machineBetheFloorScanFinish_bound {word state : List Bool}
    {iterations : ℕ}
    (hs : MachineBetheFloorScanStateBound word iterations state) :
    MachineBetheFloorScanStateBound word (iterations + 1)
      (machineBetheFloorScanFinish state) := by
  rcases hs with ⟨hdecomp, hrow, hcolumn, hfound, hdone, hpayload⟩
  simp only [machineBetheFloorScanFinish,
    MachineBetheFloorScanStateBound,
    machineBetheFloorScanRow_pack, machineBetheFloorScanColumn_pack,
    machineBetheFloorScanFound_pack, machineBetheFloorScanDone_pack,
    machineBetheFloorScanPayload_pack, List.length_singleton]
  exact ⟨trivial, hrow.trans (by omega), hcolumn.trans (by omega),
    hfound, by simp, hpayload⟩

theorem machineBetheFloorScanAdvanceRow_bound {word state : List Bool}
    {iterations : ℕ}
    (hs : MachineBetheFloorScanStateBound word iterations state) :
    MachineBetheFloorScanStateBound word (iterations + 1)
      (machineBetheFloorScanAdvanceRow state) := by
  rcases hs with ⟨hdecomp, hrow, hcolumn, hfound, hdone, hpayload⟩
  simp only [machineBetheFloorScanAdvanceRow,
    MachineBetheFloorScanStateBound,
    machineBetheFloorScanRow_pack, machineBetheFloorScanColumn_pack,
    machineBetheFloorScanFound_pack, machineBetheFloorScanDone_pack,
    machineBetheFloorScanPayload_pack, machineBetheFloorScanNextRow,
    List.length_append, List.length_singleton, List.length_nil]
  exact ⟨trivial, by omega, by omega, hfound, hdone, hpayload⟩

theorem machineBetheFloorScanAdvanceColumn_bound {word state : List Bool}
    {iterations : ℕ}
    (hs : MachineBetheFloorScanStateBound word iterations state) :
    MachineBetheFloorScanStateBound word (iterations + 1)
      (machineBetheFloorScanAdvanceColumn state) := by
  rcases hs with ⟨hdecomp, hrow, hcolumn, hfound, hdone, hpayload⟩
  simp only [machineBetheFloorScanAdvanceColumn,
    MachineBetheFloorScanStateBound,
    machineBetheFloorScanRow_pack, machineBetheFloorScanColumn_pack,
    machineBetheFloorScanFound_pack, machineBetheFloorScanDone_pack,
    machineBetheFloorScanPayload_pack, machineBetheFloorScanNextColumn,
    List.length_append, List.length_singleton]
  exact ⟨trivial, hrow.trans (by omega), by omega, hfound, hdone, hpayload⟩

theorem machineBetheFloorScanAdvance_bound {word state : List Bool}
    {iterations : ℕ}
    (hs : MachineBetheFloorScanStateBound word iterations state) :
    MachineBetheFloorScanStateBound word (iterations + 1)
      (machineBetheFloorScanAdvance state) := by
  rw [machineBetheFloorScanAdvance]
  cases hc : machineBetheFloorScanLastColumnBit state with
  | nil =>
      rw [machineHeadBit_nil, machineIfHead_false]
      exact machineBetheFloorScanAdvanceColumn_bound hs
  | cons columnBit columnTail =>
      rw [machineHeadBit_cons]
      cases columnBit
      · rw [machineIfHead_false]
        exact machineBetheFloorScanAdvanceColumn_bound hs
      · rw [machineIfHead_true]
        cases hr : machineBetheFloorScanLastRowBit state with
        | nil =>
            rw [machineHeadBit_nil, machineIfHead_false]
            exact machineBetheFloorScanAdvanceRow_bound hs
        | cons rowBit rowTail =>
            rw [machineHeadBit_cons]
            cases rowBit
            · rw [machineIfHead_false]
              exact machineBetheFloorScanAdvanceRow_bound hs
            · rw [machineIfHead_true]
              exact machineBetheFloorScanFinish_bound hs

theorem machineBetheFloorScanProcess_bound {word state : List Bool}
    {iterations : ℕ}
    (hs : MachineBetheFloorScanStateBound word iterations state) :
    MachineBetheFloorScanStateBound word (iterations + 1)
      (machineBetheFloorScanProcess state) := by
  rw [machineBetheFloorScanProcess]
  cases hv : machineBetheFloorScanViolationBit state with
  | nil =>
      rw [machineHeadBit_nil, machineIfHead_false]
      exact machineBetheFloorScanAdvance_bound hs
  | cons violationBit violationTail =>
      rw [machineHeadBit_cons]
      cases violationBit
      · rw [machineIfHead_false]
        exact machineBetheFloorScanAdvance_bound hs
      · rw [machineIfHead_true]
        exact machineBetheFloorScanMarkFound_bound hs

theorem machineBetheFloorScanStep_bound {word state : List Bool}
    {iterations : ℕ}
    (hs : MachineBetheFloorScanStateBound word iterations state) :
    MachineBetheFloorScanStateBound word (iterations + 1)
      (machineBetheFloorScanStep state) := by
  rw [machineBetheFloorScanStep]
  cases hf : machineBetheFloorScanFound state with
  | nil =>
      rw [machineHeadBit_nil, machineIfHead_false]
      cases hd : machineBetheFloorScanDone state with
      | nil =>
          rw [machineHeadBit_nil, machineIfHead_false]
          exact machineBetheFloorScanProcess_bound hs
      | cons doneBit doneTail =>
          rw [machineHeadBit_cons]
          cases doneBit
          · rw [machineIfHead_false]
            exact machineBetheFloorScanProcess_bound hs
          · rw [machineIfHead_true]
            rcases hs with ⟨hdecomp, hrow, hcolumn, hfound, hdone, hpayload⟩
            exact ⟨hdecomp, hrow.trans (by omega),
              hcolumn.trans (by omega), hfound, hdone, hpayload⟩
  | cons foundBit foundTail =>
      rw [machineHeadBit_cons]
      cases foundBit
      · rw [machineIfHead_false]
        cases hd : machineBetheFloorScanDone state with
        | nil =>
            rw [machineHeadBit_nil, machineIfHead_false]
            exact machineBetheFloorScanProcess_bound hs
        | cons doneBit doneTail =>
            rw [machineHeadBit_cons]
            cases doneBit
            · rw [machineIfHead_false]
              exact machineBetheFloorScanProcess_bound hs
            · rw [machineIfHead_true]
              rcases hs with
                ⟨hdecomp, hrow, hcolumn, hfound, hdone, hpayload⟩
              exact ⟨hdecomp, hrow.trans (by omega),
                hcolumn.trans (by omega), hfound, hdone, hpayload⟩
      · rw [machineIfHead_true]
        rcases hs with ⟨hdecomp, hrow, hcolumn, hfound, hdone, hpayload⟩
        exact ⟨hdecomp, hrow.trans (by omega),
          hcolumn.trans (by omega), hfound, hdone, hpayload⟩

theorem machineBetheFloorScanIterate_bound (word : List Bool) : ∀ k,
    MachineBetheFloorScanStateBound word k
      ((machineBetheFloorScanStep)^[k]
        (machineBetheFloorScanInit word)) := by
  intro k
  induction k with
  | zero => exact machineBetheFloorScanInit_bound word
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact machineBetheFloorScanStep_bound ih

theorem machineBetheFloorScanRuler_length_le_envelope (word : List Bool) :
    (machineBetheFloorScanRuler word).length ≤
      (machineBinaryMulWidth word).length := by
  let input := pair (machineBetheFloorScanGuard word)
    (machineBetheFloorScanWorkBits word)
  have hbound := machineBoundedUnaryIterate_bound input
    (machineBetheFloorScanGuard word).length
  have hacc := hbound.2.2
  simpa only [machineBetheFloorScanRuler, machineBoundedUnary,
    machineBoundedUnaryFinalState, machineBoundedUnaryRuler,
    input, machinePairFirst_pair, machineBetheFloorScanGuard] using! hacc

theorem machineBetheFloorScanIterate_length_le_width
    (word : List Bool) (iterations : ℕ)
    (hiterations : iterations ≤ (machineBetheFloorScanRuler word).length) :
    ((machineBetheFloorScanStep)^[iterations]
      (machineBetheFloorScanInit word)).length ≤
        (machineBetheFloorScanWidth word).length := by
  rcases machineBetheFloorScanIterate_bound word iterations with
    ⟨hdecomp, hrow, hcolumn, hfound, hdone, hpayload⟩
  have hk : iterations ≤ (machineBinaryMulWidth word).length :=
    hiterations.trans (machineBetheFloorScanRuler_length_le_envelope word)
  rw [hdecomp]
  simp only [machineBetheFloorScanPack, machineBetheFloorScanWidth,
    machineBetheFloorScanStateEnvelope, pair_length,
    machineBinaryMulWidth, List.length_replicate, List.length_append]
  simp only [machineBinaryMulWidth, List.length_replicate,
    List.length_append] at hk
  nlinarith [sq_nonneg word.length]

theorem machineBetheFloorScanFinalState_mem_FP :
    machineBetheFloorScanFinalState ∈ FP := by
  exact Cobham.iterate_mem_FP machineBetheFloorScanStep_mem_FP
    machineBetheFloorScanInit_mem_FP machineBetheFloorScanRuler_mem_FP
    machineBetheFloorScanWidth_mem_FP
    machineBetheFloorScanIterate_length_le_width

theorem machineBetheFloorScanResultCode_mem_FP :
    machineBetheFloorScanResultCode ∈ FP := by
  have hfound := machineCompose_mem_FP
    machineBetheFloorScanFinalState_mem_FP machineBetheFloorScanFound_mem_FP
  have hrow := machineCompose_mem_FP
    machineBetheFloorScanFinalState_mem_FP machineBetheFloorScanRow_mem_FP
  have hcolumn := machineCompose_mem_FP
    machineBetheFloorScanFinalState_mem_FP machineBetheFloorScanColumn_mem_FP
  exact machinePair_mem_FP hfound (machinePair_mem_FP hrow hcolumn)

/-! ## Canonical ruler semantics -/

/-- Encodes a dimension, rational threshold, and coordinate vector as a canonical floor-scan
input. -/
def machineBetheFloorScanCanonicalWord {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ) : List Bool :=
  pair (List.replicate m true)
    (pair (rawRatBinaryCode delta) (rationalFiniteVectorCode y))

@[simp] theorem machineBetheFloorScanDimension_encode {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ) :
    machineBetheFloorScanDimension
        (machineBetheFloorScanCanonicalWord delta y) =
      List.replicate m true := by
  simp [machineBetheFloorScanDimension,
    machineBetheFloorScanCanonicalWord]

@[simp] theorem machineBetheFloorScanThreshold_encode {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ) :
    machineBetheFloorScanThreshold
        (machineBetheFloorScanCanonicalWord delta y) =
      rawRatBinaryCode delta := by
  simp [machineBetheFloorScanThreshold, machineBetheFloorScanRest,
    machineBetheFloorScanCanonicalWord]

@[simp] theorem machineBetheFloorScanVector_encode {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ) :
    machineBetheFloorScanVector
        (machineBetheFloorScanCanonicalWord delta y) =
      rationalFiniteVectorCode y := by
  simp [machineBetheFloorScanVector, machineBetheFloorScanRest,
    machineBetheFloorScanCanonicalWord]

@[simp] theorem machineBetheFloorScanWorkBits_encode {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ) :
    machineBetheFloorScanWorkBits
        (machineBetheFloorScanCanonicalWord delta y) =
      ((m + 1) * (m + 1)).bits := by
  rw [machineBetheFloorScanWorkBits, machineBetheFloorScanOrderBits,
    machineBetheFloorScanDimensionBits,
    machineBetheFloorScanDimension_encode, machineLengthBits_encode,
    List.length_replicate]
  have hone : ([true] : List Bool) = (1 : ℕ).bits := rfl
  rw [hone, machineBinaryAddBits_pair_natBits,
    machineBinaryMulBits_pair_natBits]

theorem machineBetheFloorScanWork_le_guard {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ) :
    (m + 1) * (m + 1) ≤
      (machineBetheFloorScanGuard
        (machineBetheFloorScanCanonicalWord delta y)).length := by
  have hm : m ≤ (machineBetheFloorScanCanonicalWord delta y).length := by
    simp only [machineBetheFloorScanCanonicalWord, pair_length,
      List.length_replicate]
    omega
  simp only [machineBetheFloorScanGuard, machineBinaryMulWidth,
    List.length_replicate, List.length_append]
  nlinarith

@[simp] theorem machineBetheFloorScanRuler_encode {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ) :
    machineBetheFloorScanRuler
        (machineBetheFloorScanCanonicalWord delta y) =
      List.replicate ((m + 1) * (m + 1)) true := by
  rw [machineBetheFloorScanRuler,
    machineBetheFloorScanWorkBits_encode,
    machineBoundedUnary_encode_of_le]
  exact machineBetheFloorScanWork_le_guard delta y

/-! ## Exact state semantics on canonical inputs -/

/-- Successor inside `Fin (m+1)`, fixing the last element.  The scan invokes
this operation only away from the last element. -/
def betheFloorScanNextFin {m : ℕ} (i : Fin (m + 1)) : Fin (m + 1) :=
  if h : i.1 < m then ⟨i.1 + 1, by omega⟩ else i

@[simp] theorem betheFloorScanNextFin_val {m : ℕ}
    (i : Fin (m + 1)) (hi : i ≠ Fin.last m) :
    (betheFloorScanNextFin i).1 = i.1 + 1 := by
  have hlt : i.1 < m := by
    have hle : i.1 ≤ m := by omega
    have hne : i.1 ≠ m := by
      intro h
      apply hi
      apply Fin.ext
      simpa using! h
    omega
  simp [betheFloorScanNextFin, hlt]

/-- Typed semantic state mirrored by the finite-word scan. -/
structure BetheFloorScanSemanticState (m : ℕ) where
  /-- Current row of the affine matrix, whose indices range from zero through `m`. -/
  row : Fin (m + 1)
  /-- Current column of the affine matrix, whose indices range from zero through `m`. -/
  column : Fin (m + 1)
  /-- Records whether the scan has found an entry below the floor threshold. -/
  found : Bool
  /-- Records whether the scan has examined all matrix entries without stopping at a violation. -/
  done : Bool

/-- Initializes the semantic floor scan at the first matrix entry with both flags false. -/
def betheFloorScanSemanticInit (m : ℕ) :
    BetheFloorScanSemanticState m where
  row := ⟨0, by omega⟩
  column := ⟨0, by omega⟩
  found := false
  done := false

/-- Scans one affine matrix entry in row-major order, stopping at a floor violation or
completion. -/
def betheFloorScanSemanticStep {m : ℕ} (delta : RawRat)
    (y : Fin (m * m) → ℚ) (state : BetheFloorScanSemanticState m) :
    BetheFloorScanSemanticState m :=
  if state.found then state
  else if state.done then state
  else if betheAffineMatrixQ y state.row state.column < delta.value then
    { state with found := true }
  else if hcolumn : state.column = Fin.last m then
    if hrow : state.row = Fin.last m then
      { state with done := true }
    else
      { state with
          row := betheFloorScanNextFin state.row
          column := ⟨0, by omega⟩ }
  else
    { state with column := betheFloorScanNextFin state.column }

/-- Encodes a semantic scan state with unary indices, Boolean flags, and its canonical input. -/
def machineBetheFloorScanCanonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) : List Bool :=
  machineBetheFloorScanPack
    (List.replicate state.row.1 true)
    (List.replicate state.column.1 true)
    [state.found] [state.done]
    (machineBetheFloorScanCanonicalWord delta y)

@[simp] theorem machineBetheFloorScanRow_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) :
    machineBetheFloorScanRow
        (machineBetheFloorScanCanonicalState delta y state) =
      List.replicate state.row.1 true := by
  simp [machineBetheFloorScanCanonicalState]

@[simp] theorem machineBetheFloorScanColumn_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) :
    machineBetheFloorScanColumn
        (machineBetheFloorScanCanonicalState delta y state) =
      List.replicate state.column.1 true := by
  simp [machineBetheFloorScanCanonicalState]

@[simp] theorem machineBetheFloorScanFound_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) :
    machineBetheFloorScanFound
        (machineBetheFloorScanCanonicalState delta y state) =
      [state.found] := by
  simp [machineBetheFloorScanCanonicalState]

@[simp] theorem machineBetheFloorScanDone_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) :
    machineBetheFloorScanDone
        (machineBetheFloorScanCanonicalState delta y state) =
      [state.done] := by
  simp [machineBetheFloorScanCanonicalState]

@[simp] theorem machineBetheFloorScanPayload_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) :
    machineBetheFloorScanPayload
        (machineBetheFloorScanCanonicalState delta y state) =
      machineBetheFloorScanCanonicalWord delta y := by
  simp [machineBetheFloorScanCanonicalState]

@[simp] theorem machineBetheFloorScanStateDimension_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) :
    machineBetheFloorScanStateDimension
        (machineBetheFloorScanCanonicalState delta y state) =
      List.replicate m true := by
  rw [machineBetheFloorScanStateDimension,
    machineBetheFloorScanPayload_canonicalState,
    machineBetheFloorScanDimension_encode]

@[simp] theorem machineBetheFloorScanStateThreshold_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) :
    machineBetheFloorScanStateThreshold
        (machineBetheFloorScanCanonicalState delta y state) =
      rawRatBinaryCode delta := by
  rw [machineBetheFloorScanStateThreshold,
    machineBetheFloorScanPayload_canonicalState,
    machineBetheFloorScanThreshold_encode]

@[simp] theorem machineBetheFloorScanStateVector_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) :
    machineBetheFloorScanStateVector
        (machineBetheFloorScanCanonicalState delta y state) =
      rationalFiniteVectorCode y := by
  rw [machineBetheFloorScanStateVector,
    machineBetheFloorScanPayload_canonicalState,
    machineBetheFloorScanVector_encode]

@[simp] theorem machineBetheFloorScanLastRowBit_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) :
    machineBetheFloorScanLastRowBit
        (machineBetheFloorScanCanonicalState delta y state) =
      [decide (state.row = Fin.last m)] := by
  rw [machineBetheFloorScanLastRowBit,
    machineBetheFloorScanRow_canonicalState,
    machineBetheFloorScanStateDimension_canonicalState,
    machineUnaryRulersEqualBit_replicate]
  by_cases hi : state.row = Fin.last m
  · simp [hi]
  · have hval : state.row.1 ≠ m := by
      intro h
      apply hi
      apply Fin.ext
      simpa using! h
    simp [hi, hval]

@[simp] theorem machineBetheFloorScanLastColumnBit_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) :
    machineBetheFloorScanLastColumnBit
        (machineBetheFloorScanCanonicalState delta y state) =
      [decide (state.column = Fin.last m)] := by
  rw [machineBetheFloorScanLastColumnBit,
    machineBetheFloorScanColumn_canonicalState,
    machineBetheFloorScanStateDimension_canonicalState,
    machineUnaryRulersEqualBit_replicate]
  by_cases hj : state.column = Fin.last m
  · simp [hj]
  · have hval : state.column.1 ≠ m := by
      intro h
      apply hj
      apply Fin.ext
      simpa using! h
    simp [hj, hval]

@[simp] theorem machineBetheFloorScanEntryWord_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) :
    machineBetheFloorScanEntryWord
        (machineBetheFloorScanCanonicalState delta y state) =
      machineBetheAffineEntryCanonicalWord state.row state.column y := by
  simp [machineBetheFloorScanEntryWord,
    machineBetheAffineEntryCanonicalWord]

@[simp] theorem machineBetheFloorScanTestWord_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) :
    machineBetheFloorScanTestWord
        (machineBetheFloorScanCanonicalState delta y state) =
      machineBetheFloorTestCanonicalWord delta state.row state.column y := by
  simp [machineBetheFloorScanTestWord,
    machineBetheFloorTestCanonicalWord]

@[simp] theorem machineBetheFloorScanViolationBit_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) :
    machineBetheFloorScanViolationBit
        (machineBetheFloorScanCanonicalState delta y state) =
      [decide (betheAffineMatrixQ y state.row state.column < delta.value)] := by
  rw [machineBetheFloorScanViolationBit,
    machineBetheFloorScanTestWord_canonicalState,
    machineBetheFloorViolationBit_encode]

@[simp] theorem machineBetheFloorScanNextRow_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m)
    (hrow : state.row ≠ Fin.last m) :
    machineBetheFloorScanNextRow
        (machineBetheFloorScanCanonicalState delta y state) =
      List.replicate (betheFloorScanNextFin state.row).1 true := by
  rw [machineBetheFloorScanNextRow,
    machineBetheFloorScanRow_canonicalState,
    betheFloorScanNextFin_val state.row hrow,
    List.replicate_succ']

@[simp] theorem machineBetheFloorScanNextColumn_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m)
    (hcolumn : state.column ≠ Fin.last m) :
    machineBetheFloorScanNextColumn
        (machineBetheFloorScanCanonicalState delta y state) =
      List.replicate (betheFloorScanNextFin state.column).1 true := by
  rw [machineBetheFloorScanNextColumn,
    machineBetheFloorScanColumn_canonicalState,
    betheFloorScanNextFin_val state.column hcolumn,
    List.replicate_succ']

@[simp] theorem machineBetheFloorScanMarkFound_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) :
    machineBetheFloorScanMarkFound
        (machineBetheFloorScanCanonicalState delta y state) =
      machineBetheFloorScanCanonicalState delta y
        { state with found := true } := by
  simp [machineBetheFloorScanMarkFound,
    machineBetheFloorScanCanonicalState]

@[simp] theorem machineBetheFloorScanFinish_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) :
    machineBetheFloorScanFinish
        (machineBetheFloorScanCanonicalState delta y state) =
      machineBetheFloorScanCanonicalState delta y
        { state with done := true } := by
  simp [machineBetheFloorScanFinish,
    machineBetheFloorScanCanonicalState]

@[simp] theorem machineBetheFloorScanAdvanceRow_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m)
    (hrow : state.row ≠ Fin.last m) :
    machineBetheFloorScanAdvanceRow
        (machineBetheFloorScanCanonicalState delta y state) =
      machineBetheFloorScanCanonicalState delta y
        { state with
            row := betheFloorScanNextFin state.row
            column := ⟨0, by omega⟩ } := by
  rw [machineBetheFloorScanAdvanceRow]
  simp only [machineBetheFloorScanNextRow_canonicalState delta y state hrow,
    machineBetheFloorScanFound_canonicalState,
    machineBetheFloorScanDone_canonicalState,
    machineBetheFloorScanPayload_canonicalState]
  rfl

@[simp] theorem machineBetheFloorScanAdvanceColumn_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m)
    (hcolumn : state.column ≠ Fin.last m) :
    machineBetheFloorScanAdvanceColumn
        (machineBetheFloorScanCanonicalState delta y state) =
      machineBetheFloorScanCanonicalState delta y
        { state with column := betheFloorScanNextFin state.column } := by
  rw [machineBetheFloorScanAdvanceColumn]
  simp only [machineBetheFloorScanRow_canonicalState,
    machineBetheFloorScanNextColumn_canonicalState delta y state hcolumn,
    machineBetheFloorScanFound_canonicalState,
    machineBetheFloorScanDone_canonicalState,
    machineBetheFloorScanPayload_canonicalState]
  rfl

@[simp] theorem machineBetheFloorScanStep_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) :
    machineBetheFloorScanStep
        (machineBetheFloorScanCanonicalState delta y state) =
      machineBetheFloorScanCanonicalState delta y
        (betheFloorScanSemanticStep delta y state) := by
  cases hfound : state.found
  · cases hdone : state.done
    · by_cases hbelow :
          betheAffineMatrixQ y state.row state.column < delta.value
      · rw [machineBetheFloorScanStep,
          machineBetheFloorScanFound_canonicalState,
          machineHeadBit_cons, hfound, machineIfHead_false,
          machineBetheFloorScanDone_canonicalState,
          machineHeadBit_cons, hdone, machineIfHead_false,
          machineBetheFloorScanProcess,
          machineBetheFloorScanViolationBit_canonicalState,
          machineHeadBit_cons]
        have hdecBelow : decide
            (betheAffineMatrixQ y state.row state.column < delta.value) =
              true := by simp [hbelow]
        rw [hdecBelow, machineIfHead_true,
          machineBetheFloorScanMarkFound_canonicalState]
        simp [betheFloorScanSemanticStep, hfound, hdone, hbelow]
      · by_cases hcolumn : state.column = Fin.last m
        · by_cases hrow : state.row = Fin.last m
          · rw [machineBetheFloorScanStep,
              machineBetheFloorScanFound_canonicalState,
              machineHeadBit_cons, hfound, machineIfHead_false,
              machineBetheFloorScanDone_canonicalState,
              machineHeadBit_cons, hdone, machineIfHead_false,
              machineBetheFloorScanProcess,
              machineBetheFloorScanViolationBit_canonicalState,
              machineHeadBit_cons]
            have hdecBelow : decide
                (betheAffineMatrixQ y state.row state.column < delta.value) =
                  false := by simp [hbelow]
            have hdecColumn : decide
                (state.column = Fin.last m) = true := by simp [hcolumn]
            have hdecRow : decide
                (state.row = Fin.last m) = true := by simp [hrow]
            have hbelowLast : ¬betheAffineMatrixQ y
                (Fin.last m) (Fin.last m) < delta.value := by
              simpa [hrow, hcolumn] using! hbelow
            rw [hdecBelow, machineIfHead_false,
              machineBetheFloorScanAdvance,
              machineBetheFloorScanLastColumnBit_canonicalState,
              machineHeadBit_cons, hdecColumn, machineIfHead_true,
              machineBetheFloorScanLastRowBit_canonicalState,
              machineHeadBit_cons, hdecRow, machineIfHead_true,
              machineBetheFloorScanFinish_canonicalState]
            simp [betheFloorScanSemanticStep, hfound, hdone, hbelowLast,
              hcolumn, hrow]
          · rw [machineBetheFloorScanStep,
              machineBetheFloorScanFound_canonicalState,
              machineHeadBit_cons, hfound, machineIfHead_false,
              machineBetheFloorScanDone_canonicalState,
              machineHeadBit_cons, hdone, machineIfHead_false,
              machineBetheFloorScanProcess,
              machineBetheFloorScanViolationBit_canonicalState,
              machineHeadBit_cons]
            have hdecBelow : decide
                (betheAffineMatrixQ y state.row state.column < delta.value) =
                  false := by simp [hbelow]
            have hdecColumn : decide
                (state.column = Fin.last m) = true := by simp [hcolumn]
            have hdecRow : decide
                (state.row = Fin.last m) = false := by simp [hrow]
            have hbelowLastColumn : ¬betheAffineMatrixQ y
                state.row (Fin.last m) < delta.value := by
              simpa [hcolumn] using! hbelow
            rw [hdecBelow, machineIfHead_false,
              machineBetheFloorScanAdvance,
              machineBetheFloorScanLastColumnBit_canonicalState,
              machineHeadBit_cons, hdecColumn, machineIfHead_true,
              machineBetheFloorScanLastRowBit_canonicalState,
              machineHeadBit_cons, hdecRow, machineIfHead_false,
              machineBetheFloorScanAdvanceRow_canonicalState delta y state hrow]
            simp [betheFloorScanSemanticStep, hfound, hdone,
              hbelowLastColumn, hcolumn, hrow]
        · rw [machineBetheFloorScanStep,
            machineBetheFloorScanFound_canonicalState,
            machineHeadBit_cons, hfound, machineIfHead_false,
            machineBetheFloorScanDone_canonicalState,
            machineHeadBit_cons, hdone, machineIfHead_false,
            machineBetheFloorScanProcess,
            machineBetheFloorScanViolationBit_canonicalState,
            machineHeadBit_cons]
          have hdecBelow : decide
              (betheAffineMatrixQ y state.row state.column < delta.value) =
                false := by simp [hbelow]
          have hdecColumn : decide
              (state.column = Fin.last m) = false := by simp [hcolumn]
          rw [hdecBelow, machineIfHead_false,
            machineBetheFloorScanAdvance,
            machineBetheFloorScanLastColumnBit_canonicalState,
            machineHeadBit_cons, hdecColumn, machineIfHead_false,
            machineBetheFloorScanAdvanceColumn_canonicalState
              delta y state hcolumn]
          simp [betheFloorScanSemanticStep, hfound, hdone, hbelow,
            hcolumn]
    · rw [machineBetheFloorScanStep,
        machineBetheFloorScanFound_canonicalState,
        machineHeadBit_cons, hfound, machineIfHead_false,
        machineBetheFloorScanDone_canonicalState,
        machineHeadBit_cons, hdone, machineIfHead_true]
      simp [betheFloorScanSemanticStep, hfound, hdone]
  · rw [machineBetheFloorScanStep,
      machineBetheFloorScanFound_canonicalState,
      machineHeadBit_cons, hfound, machineIfHead_true]
    simp [betheFloorScanSemanticStep, hfound]

theorem machineBetheFloorScanIterate_canonicalState {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m) : ∀ k,
    (machineBetheFloorScanStep)^[k]
        (machineBetheFloorScanCanonicalState delta y state) =
      machineBetheFloorScanCanonicalState delta y
        ((betheFloorScanSemanticStep delta y)^[k] state) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        machineBetheFloorScanStep_canonicalState]

@[simp] theorem machineBetheFloorScanInit_encode {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ) :
    machineBetheFloorScanInit
        (machineBetheFloorScanCanonicalWord delta y) =
      machineBetheFloorScanCanonicalState delta y
        (betheFloorScanSemanticInit m) := by
  simp [machineBetheFloorScanInit, machineBetheFloorScanCanonicalState,
    betheFloorScanSemanticInit]

/-- Runs the semantic scan for `(m + 1)^2` steps, enough to examine every matrix entry. -/
def finalBetheFloorScanSemanticState {m : ℕ} (delta : RawRat)
    (y : Fin (m * m) → ℚ) : BetheFloorScanSemanticState m :=
  (betheFloorScanSemanticStep delta y)^[(m + 1) * (m + 1)]
    (betheFloorScanSemanticInit m)

@[simp] theorem machineBetheFloorScanFinalState_encode {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ) :
    machineBetheFloorScanFinalState
        (machineBetheFloorScanCanonicalWord delta y) =
      machineBetheFloorScanCanonicalState delta y
        (finalBetheFloorScanSemanticState delta y) := by
  rw [machineBetheFloorScanFinalState, machineBetheFloorScanRuler_encode,
    List.length_replicate, machineBetheFloorScanInit_encode,
    machineBetheFloorScanIterate_canonicalState]
  rfl

/-- Encodes the found flag and the row and column at which the semantic scan stopped. -/
def betheFloorScanSemanticResultCode {m : ℕ}
    (state : BetheFloorScanSemanticState m) : List Bool :=
  pair [state.found]
    (pair (List.replicate state.row.1 true)
      (List.replicate state.column.1 true))

@[simp] theorem machineBetheFloorScanResultCode_encode {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ) :
    machineBetheFloorScanResultCode
        (machineBetheFloorScanCanonicalWord delta y) =
      betheFloorScanSemanticResultCode
        (finalBetheFloorScanSemanticState delta y) := by
  rw [machineBetheFloorScanResultCode,
    machineBetheFloorScanFinalState_encode]
  simp [betheFloorScanSemanticResultCode]

/-! ## Mathematical correctness of the row-major semantic scan -/

/-- Numbers matrix entries in row-major order by `i * (m + 1) + j`. -/
def betheFloorScanOrdinal {m : ℕ}
    (i j : Fin (m + 1)) : ℕ := i.1 * (m + 1) + j.1

theorem betheFloorScanOrdinal_lt_square {m : ℕ}
    (i j : Fin (m + 1)) :
    betheFloorScanOrdinal i j < (m + 1) * (m + 1) := by
  rw [betheFloorScanOrdinal]
  calc
    i.1 * (m + 1) + j.1 < i.1 * (m + 1) + (m + 1) :=
      Nat.add_lt_add_left j.isLt _
    _ = (i.1 + 1) * (m + 1) := by ring
    _ ≤ (m + 1) * (m + 1) :=
      Nat.mul_le_mul_right (m + 1) (by omega)

theorem betheFloorScanOrdinal_injective (m : ℕ) :
    Function.Injective
      (fun ij : Fin (m + 1) × Fin (m + 1) ↦
        betheFloorScanOrdinal ij.1 ij.2) := by
  intro a b hab
  have hmod := congrArg (fun q : ℕ ↦ q % (m + 1)) hab
  have hmodA : betheFloorScanOrdinal a.1 a.2 % (m + 1) = a.2.1 := by
    simp [betheFloorScanOrdinal, Nat.add_mod,
      Nat.mod_eq_of_lt a.2.isLt]
  have hmodB : betheFloorScanOrdinal b.1 b.2 % (m + 1) = b.2.1 := by
    simp [betheFloorScanOrdinal, Nat.add_mod,
      Nat.mod_eq_of_lt b.2.isLt]
  have hcolumn : a.2.1 = b.2.1 := by
    calc
      a.2.1 = betheFloorScanOrdinal a.1 a.2 % (m + 1) := hmodA.symm
      _ = betheFloorScanOrdinal b.1 b.2 % (m + 1) := hmod
      _ = b.2.1 := hmodB
  have hrowMul : a.1.1 * (m + 1) = b.1.1 * (m + 1) := by
    have hab' := hab
    simp only [betheFloorScanOrdinal] at hab'
    rw [hcolumn] at hab'
    exact Nat.add_right_cancel hab'
  have hrow : a.1.1 = b.1.1 :=
    Nat.mul_right_cancel (by omega : 0 < m + 1) hrowMul
  exact Prod.ext (Fin.ext hrow) (Fin.ext hcolumn)

theorem betheFloorScanOrdinal_nextColumn {m : ℕ}
    (i j : Fin (m + 1)) (hj : j ≠ Fin.last m) :
    betheFloorScanOrdinal i (betheFloorScanNextFin j) =
      betheFloorScanOrdinal i j + 1 := by
  simp [betheFloorScanOrdinal, betheFloorScanNextFin_val j hj]
  omega

theorem betheFloorScanOrdinal_nextRow {m : ℕ}
    (i : Fin (m + 1)) (hi : i ≠ Fin.last m) :
    betheFloorScanOrdinal (betheFloorScanNextFin i) ⟨0, by omega⟩ =
      betheFloorScanOrdinal i (Fin.last m) + 1 := by
  rw [betheFloorScanOrdinal, betheFloorScanOrdinal,
    betheFloorScanNextFin_val i hi]
  simp
  ring

@[simp] theorem betheFloorScanOrdinal_last_last (m : ℕ) :
    betheFloorScanOrdinal (Fin.last m) (Fin.last m) + 1 =
      (m + 1) * (m + 1) := by
  simp [betheFloorScanOrdinal]
  ring

theorem betheFloorScanOrdinal_lt_last_of_ne {m : ℕ}
    (i j : Fin (m + 1))
    (hij : (i, j) ≠ (Fin.last m, Fin.last m)) :
    betheFloorScanOrdinal i j <
      betheFloorScanOrdinal (Fin.last m) (Fin.last m) := by
  by_cases hi : i = Fin.last m
  · have hj : j ≠ Fin.last m := by
      intro hj
      exact hij (by simp [hi, hj])
    have hjlt : j.1 < m := by
      have hjle : j.1 ≤ m := by omega
      have hjne : j.1 ≠ m := by
        intro h
        apply hj
        apply Fin.ext
        simpa using! h
      omega
    subst i
    simp only [betheFloorScanOrdinal, Fin.val_last]
    omega
  · have hilt : i.1 < m := by
      have hile : i.1 ≤ m := by omega
      have hine : i.1 ≠ m := by
        intro h
        apply hi
        apply Fin.ext
        simpa using! h
      omega
    calc
      betheFloorScanOrdinal i j <
          (i.1 + 1) * (m + 1) := by
        rw [betheFloorScanOrdinal]
        calc
          i.1 * (m + 1) + j.1 <
              i.1 * (m + 1) + (m + 1) :=
            Nat.add_lt_add_left j.isLt _
          _ = (i.1 + 1) * (m + 1) := by ring
      _ ≤ m * (m + 1) :=
        Nat.mul_le_mul_right (m + 1) (by omega)
      _ ≤ betheFloorScanOrdinal (Fin.last m) (Fin.last m) := by
        simp [betheFloorScanOrdinal]

/-- Records either the first violating entry, successful completion, or the next unchecked
ordinal. -/
def BetheFloorScanInvariant {m : ℕ} (delta : RawRat)
    (y : Fin (m * m) → ℚ) (k : ℕ)
    (state : BetheFloorScanSemanticState m) : Prop :=
  (state.found = true ∧
      betheAffineMatrixQ y state.row state.column < delta.value ∧
      betheFloorScanOrdinal state.row state.column < k ∧
      ∀ i j,
        betheFloorScanOrdinal i j <
            betheFloorScanOrdinal state.row state.column →
          delta.value ≤ betheAffineMatrixQ y i j) ∨
  (state.found = false ∧ state.done = true ∧
      (m + 1) * (m + 1) ≤ k ∧
      ∀ i j, delta.value ≤ betheAffineMatrixQ y i j) ∨
  (state.found = false ∧ state.done = false ∧
      betheFloorScanOrdinal state.row state.column = k ∧
      ∀ i j, betheFloorScanOrdinal i j < k →
        delta.value ≤ betheAffineMatrixQ y i j)

theorem betheFloorScanExtendPrior {m k : ℕ} {delta : RawRat}
    {y : Fin (m * m) → ℚ}
    {row column : Fin (m + 1)}
    (hordinal : betheFloorScanOrdinal row column = k)
    (hprior : ∀ i j, betheFloorScanOrdinal i j < k →
      delta.value ≤ betheAffineMatrixQ y i j)
    (hcurrent : delta.value ≤ betheAffineMatrixQ y row column) :
    ∀ i j, betheFloorScanOrdinal i j < k + 1 →
      delta.value ≤ betheAffineMatrixQ y i j := by
  intro i j hij
  by_cases hlt : betheFloorScanOrdinal i j < k
  · exact hprior i j hlt
  · have heqOrdinal : betheFloorScanOrdinal i j =
        betheFloorScanOrdinal row column := by omega
    have hpairs : (i, j) = (row, column) :=
      betheFloorScanOrdinal_injective m heqOrdinal
    cases hpairs
    exact hcurrent

theorem betheFloorScanSemanticInit_invariant {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ) :
    BetheFloorScanInvariant delta y 0
      (betheFloorScanSemanticInit m) := by
  right
  right
  simp [betheFloorScanSemanticInit, betheFloorScanOrdinal]

theorem betheFloorScanSemanticStep_invariant {m k : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (state : BetheFloorScanSemanticState m)
    (hinvariant : BetheFloorScanInvariant delta y k state) :
    BetheFloorScanInvariant delta y (k + 1)
      (betheFloorScanSemanticStep delta y state) := by
  rcases hinvariant with hfound | hrest
  · rcases hfound with ⟨hfound, hbelow, hord, hprior⟩
    have hstep : betheFloorScanSemanticStep delta y state = state := by
      simp [betheFloorScanSemanticStep, hfound]
    rw [hstep]
    left
    exact ⟨hfound, hbelow, by omega, hprior⟩
  · rcases hrest with hdone | hactive
    · rcases hdone with ⟨hfound, hdone, hwork, hall⟩
      have hstep : betheFloorScanSemanticStep delta y state = state := by
        simp [betheFloorScanSemanticStep, hfound, hdone]
      rw [hstep]
      right
      left
      exact ⟨hfound, hdone, hwork.trans (by omega), hall⟩
    · rcases hactive with ⟨hfound, hdone, hord, hprior⟩
      by_cases hbelow :
          betheAffineMatrixQ y state.row state.column < delta.value
      · have hstep : betheFloorScanSemanticStep delta y state =
            { state with found := true } := by
          simp [betheFloorScanSemanticStep, hfound, hdone, hbelow]
        rw [hstep]
        left
        refine ⟨rfl, hbelow, ?_, ?_⟩
        · change betheFloorScanOrdinal state.row state.column < k + 1
          omega
        intro i j hij
        apply hprior i j
        rwa [hord] at hij
      · have hcurrent : delta.value ≤
            betheAffineMatrixQ y state.row state.column := not_lt.mp hbelow
        have hextend := betheFloorScanExtendPrior hord hprior hcurrent
        by_cases hcolumn : state.column = Fin.last m
        · by_cases hrow : state.row = Fin.last m
          · have hbelowLast : ¬betheAffineMatrixQ y
                (Fin.last m) (Fin.last m) < delta.value := by
              simpa [hrow, hcolumn] using! hbelow
            have hcurrentLast : delta.value ≤ betheAffineMatrixQ y
                (Fin.last m) (Fin.last m) := not_lt.mp hbelowLast
            have hstep : betheFloorScanSemanticStep delta y state =
                { state with done := true } := by
              simp [betheFloorScanSemanticStep, hfound, hdone, hbelowLast,
                hcolumn, hrow]
            rw [hstep]
            right
            left
            refine ⟨hfound, rfl, ?_, ?_⟩
            · calc
                (m + 1) * (m + 1) =
                    betheFloorScanOrdinal (Fin.last m) (Fin.last m) + 1 :=
                  (betheFloorScanOrdinal_last_last m).symm
                _ = betheFloorScanOrdinal state.row state.column + 1 := by
                  rw [hrow, hcolumn]
                _ = k + 1 := congrArg (· + 1) hord
                _ ≤ k + 1 := le_rfl
            · intro i j
              by_cases hij : (i, j) = (Fin.last m, Fin.last m)
              · cases hij
                exact hcurrentLast
              · apply hprior i j
                rw [← hord, hrow, hcolumn]
                exact betheFloorScanOrdinal_lt_last_of_ne i j hij
          · have hbelowLastColumn : ¬betheAffineMatrixQ y
                state.row (Fin.last m) < delta.value := by
              simpa [hcolumn] using! hbelow
            have hstep : betheFloorScanSemanticStep delta y state =
                { state with
                    row := betheFloorScanNextFin state.row
                    column := ⟨0, by omega⟩ } := by
              simp [betheFloorScanSemanticStep, hfound, hdone,
                hbelowLastColumn, hcolumn, hrow]
            rw [hstep]
            right
            right
            refine ⟨hfound, hdone, ?_, hextend⟩
            rw [betheFloorScanOrdinal_nextRow state.row hrow,
              ← hcolumn, hord]
        · have hstep : betheFloorScanSemanticStep delta y state =
              { state with
                  column := betheFloorScanNextFin state.column } := by
            simp [betheFloorScanSemanticStep, hfound, hdone, hbelow,
              hcolumn]
          rw [hstep]
          right
          right
          refine ⟨hfound, hdone, ?_, hextend⟩
          rw [betheFloorScanOrdinal_nextColumn state.row state.column hcolumn,
            hord]

theorem betheFloorScanSemanticIterate_invariant {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ) : ∀ k,
    BetheFloorScanInvariant delta y k
      ((betheFloorScanSemanticStep delta y)^[k]
        (betheFloorScanSemanticInit m)) := by
  intro k
  induction k with
  | zero => exact betheFloorScanSemanticInit_invariant delta y
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact betheFloorScanSemanticStep_invariant delta y _ ih

theorem finalBetheFloorScanSemanticState_invariant {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ) :
    BetheFloorScanInvariant delta y ((m + 1) * (m + 1))
      (finalBetheFloorScanSemanticState delta y) := by
  simpa only [finalBetheFloorScanSemanticState] using!
    betheFloorScanSemanticIterate_invariant delta y
      ((m + 1) * (m + 1))

theorem finalBetheFloorScanSemanticState_found_is_below {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (hfound : (finalBetheFloorScanSemanticState delta y).found = true) :
    betheAffineMatrixQ y
        (finalBetheFloorScanSemanticState delta y).row
        (finalBetheFloorScanSemanticState delta y).column < delta.value := by
  rcases finalBetheFloorScanSemanticState_invariant delta y with
    hfoundCase | hrest
  · exact hfoundCase.2.1
  · rcases hrest with hdoneCase | hactiveCase
    · rw [hfound] at hdoneCase
      simp at hdoneCase
    · rw [hfound] at hactiveCase
      simp at hactiveCase

theorem finalBetheFloorScanSemanticState_notFound_all_above {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ)
    (hnotFound :
      (finalBetheFloorScanSemanticState delta y).found = false) :
    ∀ i j, delta.value ≤ betheAffineMatrixQ y i j := by
  rcases finalBetheFloorScanSemanticState_invariant delta y with
    hfoundCase | hrest
  · rw [hnotFound] at hfoundCase
    simp at hfoundCase
  · rcases hrest with hdoneCase | hactiveCase
    · exact hdoneCase.2.2.2
    · exfalso
      have heq := hactiveCase.2.2.1
      have hlt := betheFloorScanOrdinal_lt_square
        (finalBetheFloorScanSemanticState delta y).row
        (finalBetheFloorScanSemanticState delta y).column
      omega

theorem finalBetheFloorScanSemanticState_found_iff_exists_below {m : ℕ}
    (delta : RawRat) (y : Fin (m * m) → ℚ) :
    (finalBetheFloorScanSemanticState delta y).found = true ↔
      ∃ i j, betheAffineMatrixQ y i j < delta.value := by
  constructor
  · intro hfound
    exact ⟨(finalBetheFloorScanSemanticState delta y).row,
      (finalBetheFloorScanSemanticState delta y).column,
      finalBetheFloorScanSemanticState_found_is_below delta y hfound⟩
  · rintro ⟨i, j, hij⟩
    cases hfound : (finalBetheFloorScanSemanticState delta y).found
    · have hall := finalBetheFloorScanSemanticState_notFound_all_above
        delta y hfound i j
      exact (not_lt_of_ge hall hij).elim
    · rfl

end BeyondBethe
