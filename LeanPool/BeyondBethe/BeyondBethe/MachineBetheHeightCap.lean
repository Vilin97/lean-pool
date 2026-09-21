/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBetheFloorScan
import LeanPool.BeyondBethe.BeyondBethe.MachineListIndex

/-!
# Exact finite-word test for the Bethe epigraph height cap

The last coordinate of a rational epigraph point is its height.  Given a
unary ruler for the number of base coordinates, this machine retrieves that
last entry and tests the strict violation `upper < height` by exact rational
cross multiplication.
-/

namespace BeyondBethe

open Complexity

def machineBetheHeightCapDimension (word : List Bool) : List Bool :=
  machinePairFirst word

def machineBetheHeightCapRest (word : List Bool) : List Bool :=
  machinePairSecond word

def machineBetheHeightCapUpper (word : List Bool) : List Bool :=
  machinePairFirst (machineBetheHeightCapRest word)

def machineBetheHeightCapVector (word : List Bool) : List Bool :=
  machinePairSecond (machineBetheHeightCapRest word)

def machineBetheHeightCapIndexInput (word : List Bool) : List Bool :=
  pair (machineBetheHeightCapDimension word)
    (machineBetheHeightCapVector word)

def machineBetheHeightCapEntryCode (word : List Bool) : List Bool :=
  machineListIndex (machineBetheHeightCapIndexInput word)

def machineBetheHeightLeUpperBit (word : List Bool) : List Bool :=
  machineRawRatLeBit
    (pair (machineBetheHeightCapEntryCode word)
      (machineBetheHeightCapUpper word))

/-- One-bit answer, true exactly when the height is strictly above the cap on
canonical inputs. -/
def machineBetheHeightCapViolationBit (word : List Bool) : List Bool :=
  machineNotBit (machineBetheHeightLeUpperBit word)

theorem machineBetheHeightCapDimension_mem_FP :
    machineBetheHeightCapDimension ∈ FP := machinePairFirst_mem_FP

theorem machineBetheHeightCapRest_mem_FP :
    machineBetheHeightCapRest ∈ FP := machinePairSecond_mem_FP

theorem machineBetheHeightCapUpper_mem_FP :
    machineBetheHeightCapUpper ∈ FP := by
  simpa only [machineBetheHeightCapUpper] using
    machineCompose_mem_FP machineBetheHeightCapRest_mem_FP
      machinePairFirst_mem_FP

theorem machineBetheHeightCapVector_mem_FP :
    machineBetheHeightCapVector ∈ FP := by
  simpa only [machineBetheHeightCapVector] using
    machineCompose_mem_FP machineBetheHeightCapRest_mem_FP
      machinePairSecond_mem_FP

theorem machineBetheHeightCapIndexInput_mem_FP :
    machineBetheHeightCapIndexInput ∈ FP :=
  machinePair_mem_FP machineBetheHeightCapDimension_mem_FP
    machineBetheHeightCapVector_mem_FP

theorem machineBetheHeightCapEntryCode_mem_FP :
    machineBetheHeightCapEntryCode ∈ FP := by
  simpa only [machineBetheHeightCapEntryCode] using
    machineCompose_mem_FP machineBetheHeightCapIndexInput_mem_FP
      machineListIndex_mem_FP

theorem machineBetheHeightLeUpperBit_mem_FP :
    machineBetheHeightLeUpperBit ∈ FP := by
  have hinput := machinePair_mem_FP machineBetheHeightCapEntryCode_mem_FP
    machineBetheHeightCapUpper_mem_FP
  simpa only [machineBetheHeightLeUpperBit] using
    machineCompose_mem_FP hinput machineRawRatLeBit_mem_FP

theorem machineBetheHeightCapViolationBit_mem_FP :
    machineBetheHeightCapViolationBit ∈ FP := by
  simpa only [machineBetheHeightCapViolationBit] using
    machineNotBit_mem_FP machineBetheHeightLeUpperBit_mem_FP

def machineBetheHeightCapCanonicalWord {d : ℕ}
    (upper : RawRat) (q : Fin (d + 1) → ℚ) : List Bool :=
  pair (List.replicate d true)
    (pair (rawRatBinaryCode upper) (rationalFiniteVectorCode q))

@[simp] theorem machineBetheHeightCapDimension_encode {d : ℕ}
    (upper : RawRat) (q : Fin (d + 1) → ℚ) :
    machineBetheHeightCapDimension
        (machineBetheHeightCapCanonicalWord upper q) =
      List.replicate d true := by
  simp [machineBetheHeightCapDimension,
    machineBetheHeightCapCanonicalWord]

@[simp] theorem machineBetheHeightCapUpper_encode {d : ℕ}
    (upper : RawRat) (q : Fin (d + 1) → ℚ) :
    machineBetheHeightCapUpper
        (machineBetheHeightCapCanonicalWord upper q) =
      rawRatBinaryCode upper := by
  simp [machineBetheHeightCapUpper, machineBetheHeightCapRest,
    machineBetheHeightCapCanonicalWord]

@[simp] theorem machineBetheHeightCapVector_encode {d : ℕ}
    (upper : RawRat) (q : Fin (d + 1) → ℚ) :
    machineBetheHeightCapVector
        (machineBetheHeightCapCanonicalWord upper q) =
      rationalFiniteVectorCode q := by
  simp [machineBetheHeightCapVector, machineBetheHeightCapRest,
    machineBetheHeightCapCanonicalWord]

@[simp] theorem machineBetheHeightCapEntryCode_encode {d : ℕ}
    (upper : RawRat) (q : Fin (d + 1) → ℚ) :
    machineBetheHeightCapEntryCode
        (machineBetheHeightCapCanonicalWord upper q) =
      rawRatBinaryCode (rawRatOfRat (q (Fin.last d))) := by
  rw [machineBetheHeightCapEntryCode,
    machineBetheHeightCapIndexInput,
    machineBetheHeightCapDimension_encode,
    machineBetheHeightCapVector_encode,
    rationalFiniteVectorCode,
    machineListIndex_binaryListCode rationalEntryBinaryCode
      (List.ofFn q) d]
  · rw [rawRatBinaryCode_rawRatOfRat]
    congr 1
    change (List.ofFn q)[d] = q (Fin.last d)
    simp only [List.getElem_ofFn]
    apply congrArg q
    apply Fin.ext
    rfl

@[simp] theorem machineBetheHeightLeUpperBit_encode {d : ℕ}
    (upper : RawRat) (q : Fin (d + 1) → ℚ) :
    machineBetheHeightLeUpperBit
        (machineBetheHeightCapCanonicalWord upper q) =
      [decide (q (Fin.last d) ≤ upper.value)] := by
  rw [machineBetheHeightLeUpperBit,
    machineBetheHeightCapEntryCode_encode,
    machineBetheHeightCapUpper_encode,
    machineRawRatLeBit_encode,
    rawRatOfRat_value]

@[simp] theorem machineBetheHeightCapViolationBit_encode {d : ℕ}
    (upper : RawRat) (q : Fin (d + 1) → ℚ) :
    machineBetheHeightCapViolationBit
        (machineBetheHeightCapCanonicalWord upper q) =
      [decide (upper.value < q (Fin.last d))] := by
  rw [machineBetheHeightCapViolationBit,
    machineBetheHeightLeUpperBit_encode,
    machineNotBit_one]
  by_cases h : q (Fin.last d) ≤ upper.value
  · have hnot : ¬upper.value < q (Fin.last d) := not_lt_of_ge h
    simp [h, hnot]
  · have hlt : upper.value < q (Fin.last d) := lt_of_not_ge h
    simp [h, hlt]

end BeyondBethe
