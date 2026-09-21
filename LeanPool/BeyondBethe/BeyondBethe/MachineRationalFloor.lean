/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineDyadicFloor
import LeanPool.BeyondBethe.BeyondBethe.MachineRationalUnary

/-!
# Polynomial-time rational floor and ceiling

This file specializes the verified dyadic-floor machine at precision zero.
Floor and ceiling are returned as canonical signed binary integers.  The
natural ceiling used by later schedules is returned in ordinary binary, not
unary: converting an unrestricted binary integer to a word of that length
would not be a polynomial-time operation.
-/

namespace BeyondBethe

open Complexity

/-- Canonical signed binary code of the floor of an unreduced rational. -/
def machineRationalFloorIntegerCode (word : List Bool) : List Bool :=
  machineDyadicFloorIntegerCode (pair [] word)

/-- Canonical signed binary code of the ceiling of an unreduced rational. -/
def machineRationalCeilIntegerCode (word : List Bool) : List Bool :=
  machineIntegerNegCode
    (machineRationalFloorIntegerCode (machineRawRatNegCode word))

/-- Convert the project's canonical signed-integer code to ordinary natural
bits using `Int.toNat` semantics. -/
def machineIntegerToNatBits (word : List Bool) : List Bool :=
  machineIfHead word [] word.tail

/-- Ordinary binary bits of the nonnegative natural ceiling. -/
def machineRationalCeilNatBits (word : List Bool) : List Bool :=
  machineIntegerToNatBits (machineRationalCeilIntegerCode word)

theorem machineRationalFloorIntegerCode_mem_FP :
    machineRationalFloorIntegerCode ∈ Complexity.FP := by
  have hpair := machinePair_mem_FP (machineConst_mem_FP []) id_mem_FP
  simpa only [machineRationalFloorIntegerCode] using
    machineCompose_mem_FP hpair machineDyadicFloorIntegerCode_mem_FP

theorem machineRationalCeilIntegerCode_mem_FP :
    machineRationalCeilIntegerCode ∈ Complexity.FP := by
  have hneg := machineCompose_mem_FP machineRawRatNegCode_mem_FP
    machineRationalFloorIntegerCode_mem_FP
  simpa only [machineRationalCeilIntegerCode] using
    machineCompose_mem_FP hneg machineIntegerNegCode_mem_FP

theorem machineIntegerToNatBits_mem_FP :
    machineIntegerToNatBits ∈ Complexity.FP := by
  simpa only [machineIntegerToNatBits] using
    machineIfHead_mem_FP id_mem_FP (machineConst_mem_FP [])
      machineTail_mem_FP

theorem machineRationalCeilNatBits_mem_FP :
    machineRationalCeilNatBits ∈ Complexity.FP := by
  simpa only [machineRationalCeilNatBits] using
    machineCompose_mem_FP machineRationalCeilIntegerCode_mem_FP
      machineIntegerToNatBits_mem_FP

theorem binaryRawFloorInt_eq_binaryRatFloor (q : RawRat) :
    binaryRawDyadicFloorInt 0 q = binaryRatFloor q.value := by
  rw [binaryRatFloor_eq_floor, binaryRawDyadicFloorInt_eq_floor]
  norm_num

theorem machineRationalFloorIntegerCode_encode (q : RawRat) :
    machineRationalFloorIntegerCode (rawRatBinaryCode q) =
      integerBinaryCode (binaryRatFloor q.value) := by
  rw [machineRationalFloorIntegerCode]
  simpa only [List.replicate_zero] using
    (machineDyadicFloorIntegerCode_encode 0 q).trans
      (congrArg integerBinaryCode (binaryRawFloorInt_eq_binaryRatFloor q))

theorem machineRationalCeilIntegerCode_encode (q : RawRat) :
    machineRationalCeilIntegerCode (rawRatBinaryCode q) =
      integerBinaryCode (binaryRatCeil q.value) := by
  rw [machineRationalCeilIntegerCode, machineRawRatNegCode_encode,
    machineRationalFloorIntegerCode_encode, machineIntegerNegCode_encode]
  congr 1
  simp [binaryRatCeil, binaryRatFloor_eq_floor]

@[simp] theorem machineIntegerToNatBits_encode (z : ℤ) :
    machineIntegerToNatBits (integerBinaryCode z) = z.toNat.bits := by
  cases z with
  | ofNat n => simp [machineIntegerToNatBits, integerBinaryCode]
  | negSucc n => simp [machineIntegerToNatBits, integerBinaryCode]

theorem machineRationalCeilNatBits_encode (q : RawRat) :
    machineRationalCeilNatBits (rawRatBinaryCode q) =
      (Int.toNat (binaryRatCeil q.value)).bits := by
  rw [machineRationalCeilNatBits, machineRationalCeilIntegerCode_encode,
    machineIntegerToNatBits_encode]

end BeyondBethe
