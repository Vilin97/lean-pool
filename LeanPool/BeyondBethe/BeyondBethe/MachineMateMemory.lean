/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBooleanInit

/-!
# Column-mate memory for augmenting-path matching

One column stores either `[false]` for `none` or `true :: rowUnary` for a
matched row.  The enclosing right-nested list delimits these variable-length
elements.  This representation makes the old row immediately available to a
recursive augmenting-path search while retaining exact polynomial-time list
lookup and update.
-/

namespace BeyondBethe

open Complexity

def mateValueCode : Option ℕ → List Bool
  | none => [false]
  | some row => true :: List.replicate row true

def mateVectorCode (mate : List (Option ℕ)) : List Bool :=
  binaryListCode mateValueCode mate

def machineMateValueIsNoneBit (value : List Bool) : List Bool :=
  machineNotBit (machineHeadBit value)

def machineMateValueRowUnary (value : List Bool) : List Bool :=
  value.tail

def machineMateVectorGetAtUnary (word : List Bool) : List Bool :=
  machineListIndex word

/-- Input: `pair columnUnary (pair mateValue mateVectorCode)`. -/
def machineMateVectorUpdateAtUnary (word : List Bool) : List Bool :=
  machineListUpdate word

theorem machineMateValueIsNoneBit_mem_FP :
    machineMateValueIsNoneBit ∈ Complexity.FP := by
  simpa only [machineMateValueIsNoneBit] using
    machineNotBit_mem_FP machineHeadBit_mem_FP

theorem machineMateValueRowUnary_mem_FP :
    machineMateValueRowUnary ∈ Complexity.FP :=
  machineTail_mem_FP

theorem machineMateVectorGetAtUnary_mem_FP :
    machineMateVectorGetAtUnary ∈ Complexity.FP :=
  machineListIndex_mem_FP

theorem machineMateVectorUpdateAtUnary_mem_FP :
    machineMateVectorUpdateAtUnary ∈ Complexity.FP :=
  machineListUpdate_mem_FP

@[simp] theorem machineMateValueIsNoneBit_encode (value : Option ℕ) :
    machineMateValueIsNoneBit (mateValueCode value) =
      [decide value.isNone] := by
  cases value <;> simp [machineMateValueIsNoneBit, mateValueCode]

@[simp] theorem machineMateValueRowUnary_some (row : ℕ) :
    machineMateValueRowUnary (mateValueCode (some row)) =
      List.replicate row true := by
  simp [machineMateValueRowUnary, mateValueCode]

@[simp] theorem machineMateVectorGetAtUnary_encode
    (mate : List (Option ℕ)) (column : ℕ)
    (hcolumn : column < mate.length) :
    machineMateVectorGetAtUnary
        (pair (List.replicate column true) (mateVectorCode mate)) =
      mateValueCode mate[column] := by
  exact machineListIndex_binaryListCode mateValueCode mate column hcolumn

@[simp] theorem machineMateVectorUpdateAtUnary_encode
    (mate : List (Option ℕ)) (column : ℕ) (value : Option ℕ)
    (hcolumn : column < mate.length) :
    machineMateVectorUpdateAtUnary
        (pair (List.replicate column true)
          (pair (mateValueCode value) (mateVectorCode mate))) =
      mateVectorCode (mate.set column value) := by
  exact machineListUpdate_binaryListCode mateValueCode mate value column hcolumn

/-- The all-`none` mate vector is exactly the already verified false-vector
constructor. -/
def machineEmptyMateVectorCode (ruler : List Bool) : List Bool :=
  machineFalseVectorCode ruler

theorem machineEmptyMateVectorCode_mem_FP :
    machineEmptyMateVectorCode ∈ Complexity.FP :=
  machineFalseVectorCode_mem_FP

@[simp] theorem machineEmptyMateVectorCode_encode (n : ℕ) :
    machineEmptyMateVectorCode (List.replicate n true) =
      mateVectorCode (List.replicate n none) := by
  rw [machineEmptyMateVectorCode, machineFalseVectorCode_encode]
  change binaryListCode boolElementCode (List.replicate n false) =
    binaryListCode mateValueCode (List.replicate n none)
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, binaryListCode, boolElementCode,
        mateValueCode, ih]

end BeyondBethe
