/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.AlgorithmicSpec
import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal

/-!
# Machine access to the canonical binary encodings

The public theorem uses right-nested `Complexity.pair` codes.  This file
records both their exact behavior on well-formed inputs and the already
verified Complexitylib machines that split them in polynomial time.  No
semantic decoder or choice function occurs in these accessors.
-/

namespace BeyondBethe

open Complexity

/-- First component of a machine pair.  On a matrix code this is `n.bits`. -/
def machinePairFirst (word : List Bool) : List Bool := Cobham.fstBlock word

/-- Second component of a machine pair.  On a matrix code this is the encoded
row list. -/
def machinePairSecond (word : List Bool) : List Bool := Cobham.sndBlock word

theorem machinePairFirst_mem_FP : machinePairFirst ∈ Complexity.FP := by
  simpa only [machinePairFirst] using Cobham.fstBlock_mem_FP

theorem machinePairSecond_mem_FP : machinePairSecond ∈ Complexity.FP := by
  simpa only [machinePairSecond] using Cobham.sndBlock_mem_FP

@[simp] theorem machinePairFirst_pair (left right : List Bool) :
    machinePairFirst (pair left right) = left := by
  simp [machinePairFirst]

@[simp] theorem machinePairSecond_pair (left right : List Bool) :
    machinePairSecond (pair left right) = right := by
  simp [machinePairSecond]

/-- The dimension word extracted from a canonical matrix input. -/
def machineMatrixDimensionWord (word : List Bool) : List Bool :=
  machinePairFirst word

/-- The nested row-list word extracted from a canonical matrix input. -/
def machineMatrixRowsWord (word : List Bool) : List Bool :=
  machinePairSecond word

theorem machineMatrixDimensionWord_mem_FP :
    machineMatrixDimensionWord ∈ Complexity.FP := by
  simpa only [machineMatrixDimensionWord] using machinePairFirst_mem_FP

theorem machineMatrixRowsWord_mem_FP :
    machineMatrixRowsWord ∈ Complexity.FP := by
  simpa only [machineMatrixRowsWord] using machinePairSecond_mem_FP

@[simp] theorem machineMatrixDimensionWord_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixDimensionWord
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) = n.bits := by
  simp [rationalMatrixBinaryEncoding, rationalMatrixBinaryCode,
    machineMatrixDimensionWord]

@[simp] theorem machineMatrixRowsWord_encode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    machineMatrixRowsWord
        (rationalMatrixBinaryEncoding.encode ⟨n, A⟩) =
      binaryListCode (binaryListCode rationalEntryBinaryCode)
        (rationalMatrixRows A) := by
  simp [rationalMatrixBinaryEncoding, rationalMatrixBinaryCode,
    machineMatrixRowsWord]

/-- A nonempty right-nested list exposes its head through `fstBlock`. -/
def machineListHead (word : List Bool) : List Bool := machinePairFirst word

/-- A nonempty right-nested list exposes its tail through `sndBlock`. -/
def machineListTail (word : List Bool) : List Bool := machinePairSecond word

theorem machineListHead_mem_FP : machineListHead ∈ Complexity.FP := by
  simpa only [machineListHead] using machinePairFirst_mem_FP

theorem machineListTail_mem_FP : machineListTail ∈ Complexity.FP := by
  simpa only [machineListTail] using machinePairSecond_mem_FP

@[simp] theorem machineListHead_cons {α : Type*}
    (encode : α → List Bool) (x : α) (xs : List α) :
    machineListHead (binaryListCode encode (x :: xs)) = encode x := by
  simp [machineListHead, binaryListCode]

@[simp] theorem machineListTail_cons {α : Type*}
    (encode : α → List Bool) (x : α) (xs : List α) :
    machineListTail (binaryListCode encode (x :: xs)) =
      binaryListCode encode xs := by
  simp [machineListTail, binaryListCode]

/-- Signed numerator word of a canonical matrix-entry code. -/
def machineRationalEntryNumeratorWord (word : List Bool) : List Bool :=
  machinePairFirst word

/-- Positive denominator word of a canonical matrix-entry code. -/
def machineRationalEntryDenominatorWord (word : List Bool) : List Bool :=
  machinePairSecond word

theorem machineRationalEntryNumeratorWord_mem_FP :
    machineRationalEntryNumeratorWord ∈ Complexity.FP := by
  simpa only [machineRationalEntryNumeratorWord] using machinePairFirst_mem_FP

theorem machineRationalEntryDenominatorWord_mem_FP :
    machineRationalEntryDenominatorWord ∈ Complexity.FP := by
  simpa only [machineRationalEntryDenominatorWord] using machinePairSecond_mem_FP

@[simp] theorem machineRationalEntryNumeratorWord_encode (q : ℚ) :
    machineRationalEntryNumeratorWord (rationalEntryBinaryCode q) =
      integerBinaryCode q.num := by
  simp [rationalEntryBinaryCode, machineRationalEntryNumeratorWord]

@[simp] theorem machineRationalEntryDenominatorWord_encode (q : ℚ) :
    machineRationalEntryDenominatorWord (rationalEntryBinaryCode q) =
      q.den.bits := by
  simp [rationalEntryBinaryCode, machineRationalEntryDenominatorWord]

end BeyondBethe
