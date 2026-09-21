/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.BetheFloorCutFormula
import LeanPool.BeyondBethe.BeyondBethe.MachineBetheHeightCap

/-!
# Finite-word coefficients of Bethe floor cuts

For a queried recovered entry and a current base coordinate, this machine
returns the canonical rational code of the corresponding cut coefficient.
The four cases are a negative unit vector, a positive row, a positive column,
and the fixedValue negative-one vector.  A supplied height-coordinate bit
overrides all four cases with zero.
-/

namespace BeyondBethe

open Complexity

def machineBetheFloorCutEntryDimension (word : List Bool) : List Bool :=
  machinePairFirst word

def machineBetheFloorCutEntryRest (word : List Bool) : List Bool :=
  machinePairSecond word

def machineBetheFloorCutEntryQueryRow (word : List Bool) : List Bool :=
  machinePairFirst (machineBetheFloorCutEntryRest word)

def machineBetheFloorCutEntryQueryColumn (word : List Bool) : List Bool :=
  machinePairFirst (machinePairSecond (machineBetheFloorCutEntryRest word))

def machineBetheFloorCutEntryBaseRow (word : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond
      (machineBetheFloorCutEntryRest word)))

def machineBetheFloorCutEntryBaseColumn (word : List Bool) : List Bool :=
  machinePairFirst
    (machinePairSecond (machinePairSecond (machinePairSecond
      (machineBetheFloorCutEntryRest word))))

def machineBetheFloorCutEntryHeightBit (word : List Bool) : List Bool :=
  machinePairSecond
    (machinePairSecond (machinePairSecond (machinePairSecond
      (machineBetheFloorCutEntryRest word))))

def machineBetheFloorCutEntryQueryLastRowBit
    (word : List Bool) : List Bool :=
  machineHeadBit (machineUnaryRulersEqualBit
    (machineBetheFloorCutEntryQueryRow word)
    (machineBetheFloorCutEntryDimension word))

def machineBetheFloorCutEntryQueryLastColumnBit
    (word : List Bool) : List Bool :=
  machineHeadBit (machineUnaryRulersEqualBit
    (machineBetheFloorCutEntryQueryColumn word)
    (machineBetheFloorCutEntryDimension word))

def machineBetheFloorCutEntryBaseRowEqBit
    (word : List Bool) : List Bool :=
  machineHeadBit (machineUnaryRulersEqualBit
    (machineBetheFloorCutEntryBaseRow word)
    (machineBetheFloorCutEntryQueryRow word))

def machineBetheFloorCutEntryBaseColumnEqBit
    (word : List Bool) : List Bool :=
  machineHeadBit (machineUnaryRulersEqualBit
    (machineBetheFloorCutEntryBaseColumn word)
    (machineBetheFloorCutEntryQueryColumn word))

def machineBetheFloorCutEntryBothBaseEqBit
    (word : List Bool) : List Bool :=
  machineAndBit (machineBetheFloorCutEntryBaseRowEqBit word)
    (machineBetheFloorCutEntryBaseColumnEqBit word)

def machineBetheFloorCutEntryZeroCode : List Bool :=
  rationalEntryBinaryCode 0

def machineBetheFloorCutEntryOneCode : List Bool :=
  rationalEntryBinaryCode 1

def machineBetheFloorCutEntryNegOneCode : List Bool :=
  rationalEntryBinaryCode (-1)

def machineBetheFloorCutEntryBaseCode (word : List Bool) : List Bool :=
  machineIfHead (machineBetheFloorCutEntryQueryLastRowBit word)
    (machineIfHead (machineBetheFloorCutEntryQueryLastColumnBit word)
      machineBetheFloorCutEntryNegOneCode
      (machineIfHead (machineBetheFloorCutEntryBaseColumnEqBit word)
        machineBetheFloorCutEntryOneCode machineBetheFloorCutEntryZeroCode))
    (machineIfHead (machineBetheFloorCutEntryQueryLastColumnBit word)
      (machineIfHead (machineBetheFloorCutEntryBaseRowEqBit word)
        machineBetheFloorCutEntryOneCode machineBetheFloorCutEntryZeroCode)
      (machineIfHead (machineBetheFloorCutEntryBothBaseEqBit word)
        machineBetheFloorCutEntryNegOneCode machineBetheFloorCutEntryZeroCode))

def machineBetheFloorCutEntryCode (word : List Bool) : List Bool :=
  machineIfHead (machineHeadBit (machineBetheFloorCutEntryHeightBit word))
    machineBetheFloorCutEntryZeroCode
    (machineBetheFloorCutEntryBaseCode word)

theorem machineBetheFloorCutEntryDimension_mem_FP :
    machineBetheFloorCutEntryDimension ∈ FP := machinePairFirst_mem_FP

theorem machineBetheFloorCutEntryRest_mem_FP :
    machineBetheFloorCutEntryRest ∈ FP := machinePairSecond_mem_FP

theorem machineBetheFloorCutEntryQueryRow_mem_FP :
    machineBetheFloorCutEntryQueryRow ∈ FP := by
  simpa only [machineBetheFloorCutEntryQueryRow] using
    machineCompose_mem_FP machineBetheFloorCutEntryRest_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheFloorCutEntryQueryColumn_mem_FP :
    machineBetheFloorCutEntryQueryColumn ∈ FP := by
  have htail := machineCompose_mem_FP machineBetheFloorCutEntryRest_mem_FP
    machinePairSecond_mem_FP
  simpa only [machineBetheFloorCutEntryQueryColumn] using
    machineCompose_mem_FP htail machinePairFirst_mem_FP

theorem machineBetheFloorCutEntryBaseRow_mem_FP :
    machineBetheFloorCutEntryBaseRow ∈ FP := by
  have htailOne := machineCompose_mem_FP
    machineBetheFloorCutEntryRest_mem_FP machinePairSecond_mem_FP
  have htailTwo := machineCompose_mem_FP htailOne machinePairSecond_mem_FP
  simpa only [machineBetheFloorCutEntryBaseRow] using
    machineCompose_mem_FP htailTwo machinePairFirst_mem_FP

theorem machineBetheFloorCutEntryBaseColumn_mem_FP :
    machineBetheFloorCutEntryBaseColumn ∈ FP := by
  have htailOne := machineCompose_mem_FP
    machineBetheFloorCutEntryRest_mem_FP machinePairSecond_mem_FP
  have htailTwo := machineCompose_mem_FP htailOne machinePairSecond_mem_FP
  have htailThree := machineCompose_mem_FP htailTwo machinePairSecond_mem_FP
  simpa only [machineBetheFloorCutEntryBaseColumn] using
    machineCompose_mem_FP htailThree machinePairFirst_mem_FP

theorem machineBetheFloorCutEntryHeightBit_mem_FP :
    machineBetheFloorCutEntryHeightBit ∈ FP := by
  have htailOne := machineCompose_mem_FP
    machineBetheFloorCutEntryRest_mem_FP machinePairSecond_mem_FP
  have htailTwo := machineCompose_mem_FP htailOne machinePairSecond_mem_FP
  have htailThree := machineCompose_mem_FP htailTwo machinePairSecond_mem_FP
  simpa only [machineBetheFloorCutEntryHeightBit] using
    machineCompose_mem_FP htailThree machinePairSecond_mem_FP

theorem machineBetheFloorCutEntryQueryLastRowBit_mem_FP :
    machineBetheFloorCutEntryQueryLastRowBit ∈ FP := by
  have heq := machineUnaryRulersEqualBit_mem_FP
    machineBetheFloorCutEntryQueryRow_mem_FP
    machineBetheFloorCutEntryDimension_mem_FP
  simpa only [machineBetheFloorCutEntryQueryLastRowBit] using
    machineCompose_mem_FP heq machineHeadBit_mem_FP

theorem machineBetheFloorCutEntryQueryLastColumnBit_mem_FP :
    machineBetheFloorCutEntryQueryLastColumnBit ∈ FP := by
  have heq := machineUnaryRulersEqualBit_mem_FP
    machineBetheFloorCutEntryQueryColumn_mem_FP
    machineBetheFloorCutEntryDimension_mem_FP
  simpa only [machineBetheFloorCutEntryQueryLastColumnBit] using
    machineCompose_mem_FP heq machineHeadBit_mem_FP

theorem machineBetheFloorCutEntryBaseRowEqBit_mem_FP :
    machineBetheFloorCutEntryBaseRowEqBit ∈ FP := by
  have heq := machineUnaryRulersEqualBit_mem_FP
    machineBetheFloorCutEntryBaseRow_mem_FP
    machineBetheFloorCutEntryQueryRow_mem_FP
  simpa only [machineBetheFloorCutEntryBaseRowEqBit] using
    machineCompose_mem_FP heq machineHeadBit_mem_FP

theorem machineBetheFloorCutEntryBaseColumnEqBit_mem_FP :
    machineBetheFloorCutEntryBaseColumnEqBit ∈ FP := by
  have heq := machineUnaryRulersEqualBit_mem_FP
    machineBetheFloorCutEntryBaseColumn_mem_FP
    machineBetheFloorCutEntryQueryColumn_mem_FP
  simpa only [machineBetheFloorCutEntryBaseColumnEqBit] using
    machineCompose_mem_FP heq machineHeadBit_mem_FP

theorem machineBetheFloorCutEntryBothBaseEqBit_mem_FP :
    machineBetheFloorCutEntryBothBaseEqBit ∈ FP :=
  machineAndBit_mem_FP machineBetheFloorCutEntryBaseRowEqBit_mem_FP
    machineBetheFloorCutEntryBaseColumnEqBit_mem_FP

theorem machineBetheFloorCutEntryBaseCode_mem_FP :
    machineBetheFloorCutEntryBaseCode ∈ FP := by
  let hzero : (fun _ : List Bool ↦ machineBetheFloorCutEntryZeroCode) ∈ FP :=
    machineConst_mem_FP _
  let hone : (fun _ : List Bool ↦ machineBetheFloorCutEntryOneCode) ∈ FP :=
    machineConst_mem_FP _
  let hnegOne : (fun _ : List Bool ↦ machineBetheFloorCutEntryNegOneCode) ∈ FP :=
    machineConst_mem_FP _
  have hcolumn := machineIfHead_mem_FP
    machineBetheFloorCutEntryBaseColumnEqBit_mem_FP hone hzero
  have hlastRow := machineIfHead_mem_FP
    machineBetheFloorCutEntryQueryLastColumnBit_mem_FP hnegOne hcolumn
  have hrow := machineIfHead_mem_FP
    machineBetheFloorCutEntryBaseRowEqBit_mem_FP hone hzero
  have hnotUpperLeft := machineIfHead_mem_FP
    machineBetheFloorCutEntryBothBaseEqBit_mem_FP hnegOne hzero
  have hnotLastRow := machineIfHead_mem_FP
    machineBetheFloorCutEntryQueryLastColumnBit_mem_FP hrow hnotUpperLeft
  exact machineIfHead_mem_FP machineBetheFloorCutEntryQueryLastRowBit_mem_FP
    hlastRow hnotLastRow

theorem machineBetheFloorCutEntryCode_mem_FP :
    machineBetheFloorCutEntryCode ∈ FP := by
  have hheight := machineCompose_mem_FP
    machineBetheFloorCutEntryHeightBit_mem_FP machineHeadBit_mem_FP
  exact machineIfHead_mem_FP hheight
    (machineConst_mem_FP machineBetheFloorCutEntryZeroCode)
    machineBetheFloorCutEntryBaseCode_mem_FP

def machineBetheFloorCutEntryCanonicalWord {m : ℕ}
    (i j : Fin (m + 1)) (a b : Fin m) (isHeight : Bool) : List Bool :=
  pair (List.replicate m true)
    (pair (List.replicate i.1 true)
      (pair (List.replicate j.1 true)
        (pair (List.replicate a.1 true)
          (pair (List.replicate b.1 true) [isHeight]))))

@[simp] theorem machineBetheFloorCutEntryQueryLastRowBit_encode {m : ℕ}
    (i j : Fin (m + 1)) (a b : Fin m) (isHeight : Bool) :
    machineBetheFloorCutEntryQueryLastRowBit
        (machineBetheFloorCutEntryCanonicalWord i j a b isHeight) =
      [decide (i = Fin.last m)] := by
  simp only [machineBetheFloorCutEntryQueryLastRowBit,
    machineBetheFloorCutEntryQueryRow, machineBetheFloorCutEntryRest,
    machineBetheFloorCutEntryDimension,
    machineBetheFloorCutEntryCanonicalWord, machinePairFirst_pair,
    machinePairSecond_pair, machineUnaryRulersEqualBit_replicate,
    machineHeadBit_cons]
  by_cases hi : i = Fin.last m
  · simp [hi]
  · have hval : i.1 ≠ m := by
      intro h
      apply hi
      apply Fin.ext
      simpa using h
    simp [hi, hval]

@[simp] theorem machineBetheFloorCutEntryQueryLastColumnBit_encode {m : ℕ}
    (i j : Fin (m + 1)) (a b : Fin m) (isHeight : Bool) :
    machineBetheFloorCutEntryQueryLastColumnBit
        (machineBetheFloorCutEntryCanonicalWord i j a b isHeight) =
      [decide (j = Fin.last m)] := by
  simp only [machineBetheFloorCutEntryQueryLastColumnBit,
    machineBetheFloorCutEntryQueryColumn, machineBetheFloorCutEntryRest,
    machineBetheFloorCutEntryDimension,
    machineBetheFloorCutEntryCanonicalWord, machinePairFirst_pair,
    machinePairSecond_pair, machineUnaryRulersEqualBit_replicate,
    machineHeadBit_cons]
  by_cases hj : j = Fin.last m
  · simp [hj]
  · have hval : j.1 ≠ m := by
      intro h
      apply hj
      apply Fin.ext
      simpa using h
    simp [hj, hval]

@[simp] theorem machineBetheFloorCutEntryBaseRowEqBit_encode {m : ℕ}
    (i j : Fin (m + 1)) (a b : Fin m) (isHeight : Bool) :
    machineBetheFloorCutEntryBaseRowEqBit
        (machineBetheFloorCutEntryCanonicalWord i j a b isHeight) =
      [decide (a.castSucc = i)] := by
  simp only [machineBetheFloorCutEntryBaseRowEqBit,
    machineBetheFloorCutEntryBaseRow,
    machineBetheFloorCutEntryQueryRow, machineBetheFloorCutEntryRest,
    machineBetheFloorCutEntryCanonicalWord, machinePairFirst_pair,
    machinePairSecond_pair, machineUnaryRulersEqualBit_replicate,
    machineHeadBit_cons]
  by_cases hai : a.castSucc = i
  · subst i
    simp
  · have hval : a.1 ≠ i.1 := by
      intro h
      apply hai
      apply Fin.ext
      simpa using h
    simp [hai, hval]

@[simp] theorem machineBetheFloorCutEntryBaseColumnEqBit_encode {m : ℕ}
    (i j : Fin (m + 1)) (a b : Fin m) (isHeight : Bool) :
    machineBetheFloorCutEntryBaseColumnEqBit
        (machineBetheFloorCutEntryCanonicalWord i j a b isHeight) =
      [decide (b.castSucc = j)] := by
  simp only [machineBetheFloorCutEntryBaseColumnEqBit,
    machineBetheFloorCutEntryBaseColumn,
    machineBetheFloorCutEntryQueryColumn, machineBetheFloorCutEntryRest,
    machineBetheFloorCutEntryCanonicalWord, machinePairFirst_pair,
    machinePairSecond_pair, machineUnaryRulersEqualBit_replicate,
    machineHeadBit_cons]
  by_cases hbj : b.castSucc = j
  · subst j
    simp
  · have hval : b.1 ≠ j.1 := by
      intro h
      apply hbj
      apply Fin.ext
      simpa using h
    simp [hbj, hval]

@[simp] theorem machineBetheFloorCutEntryHeightBit_encode {m : ℕ}
    (i j : Fin (m + 1)) (a b : Fin m) (isHeight : Bool) :
    machineBetheFloorCutEntryHeightBit
        (machineBetheFloorCutEntryCanonicalWord i j a b isHeight) =
      [isHeight] := by
  simp [machineBetheFloorCutEntryHeightBit,
    machineBetheFloorCutEntryRest,
    machineBetheFloorCutEntryCanonicalWord]

@[simp] theorem machineBetheFloorCutEntryBaseCode_encode {m : ℕ}
    (i j : Fin (m + 1)) (a b : Fin m) :
    machineBetheFloorCutEntryBaseCode
        (machineBetheFloorCutEntryCanonicalWord i j a b false) =
      rationalEntryBinaryCode (explicitBetheFloorCutBaseEntry i j a b) := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp [machineBetheFloorCutEntryBaseCode,
      machineBetheFloorCutEntryBothBaseEqBit,
      machineBetheFloorCutEntryNegOneCode,
      machineBetheFloorCutEntryZeroCode,
      machineBetheFloorCutEntryOneCode]
  · by_cases hbj : b = j
    · subst b
      simp [machineBetheFloorCutEntryBaseCode,
        machineBetheFloorCutEntryBothBaseEqBit,
        machineBetheFloorCutEntryNegOneCode,
        machineBetheFloorCutEntryZeroCode,
        machineBetheFloorCutEntryOneCode]
    · simp [machineBetheFloorCutEntryBaseCode,
        machineBetheFloorCutEntryBothBaseEqBit,
        machineBetheFloorCutEntryNegOneCode,
        machineBetheFloorCutEntryZeroCode,
        machineBetheFloorCutEntryOneCode, hbj]
  · by_cases hai : a = i
    · subst a
      simp [machineBetheFloorCutEntryBaseCode,
        machineBetheFloorCutEntryBothBaseEqBit,
        machineBetheFloorCutEntryNegOneCode,
        machineBetheFloorCutEntryZeroCode,
        machineBetheFloorCutEntryOneCode]
    · simp [machineBetheFloorCutEntryBaseCode,
        machineBetheFloorCutEntryBothBaseEqBit,
        machineBetheFloorCutEntryNegOneCode,
        machineBetheFloorCutEntryZeroCode,
        machineBetheFloorCutEntryOneCode, hai]
  · by_cases hai : a = i <;> by_cases hbj : b = j
    · subst a
      subst b
      simp [machineBetheFloorCutEntryBaseCode,
        machineBetheFloorCutEntryBothBaseEqBit,
        machineBetheFloorCutEntryNegOneCode,
        machineBetheFloorCutEntryZeroCode,
        machineBetheFloorCutEntryOneCode]
    · simp [machineBetheFloorCutEntryBaseCode,
        machineBetheFloorCutEntryBothBaseEqBit,
        machineBetheFloorCutEntryNegOneCode,
        machineBetheFloorCutEntryZeroCode,
        machineBetheFloorCutEntryOneCode, hai, hbj]
    · simp [machineBetheFloorCutEntryBaseCode,
        machineBetheFloorCutEntryBothBaseEqBit,
        machineBetheFloorCutEntryNegOneCode,
        machineBetheFloorCutEntryZeroCode,
        machineBetheFloorCutEntryOneCode, hai, hbj]
    · simp [machineBetheFloorCutEntryBaseCode,
        machineBetheFloorCutEntryBothBaseEqBit,
        machineBetheFloorCutEntryNegOneCode,
        machineBetheFloorCutEntryZeroCode,
        machineBetheFloorCutEntryOneCode, hai, hbj]

@[simp] theorem machineBetheFloorCutEntryCode_encode {m : ℕ}
    (i j : Fin (m + 1)) (a b : Fin m) (isHeight : Bool) :
    machineBetheFloorCutEntryCode
        (machineBetheFloorCutEntryCanonicalWord i j a b isHeight) =
      rationalEntryBinaryCode
        (if isHeight then 0 else explicitBetheFloorCutBaseEntry i j a b) := by
  cases isHeight
  · simp [machineBetheFloorCutEntryCode]
  · simp [machineBetheFloorCutEntryCode,
      machineBetheFloorCutEntryZeroCode]

end BeyondBethe
