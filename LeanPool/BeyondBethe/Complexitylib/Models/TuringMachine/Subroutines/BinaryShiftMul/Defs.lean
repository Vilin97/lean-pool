/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.ForBinaryWork.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany.Defs
public import LeanPool.BeyondBethe.Complexitylib.Mathlib.NatBits

/-!
# Width-driven binary shift-and-add multiplication -- definitions

This module defines a six-work-tape multiplication ABI and a concrete
least-significant-bit-first shift-and-add machine. The multiplicands are
preserved, the accumulator receives their product, and three scratch tapes are
returned to canonical zero.
-/


@[expose] public section

namespace Complexity

namespace BinaryShiftMul

/-- One pure shift-and-add iteration. The first component is the partial
accumulator and the second is the current shifted multiplicand. -/
def step (bit : Bool) (acc shift : ℕ) : ℕ × ℕ :=
  (if bit then acc + shift else acc, 2 * shift)

/-- Fold little-endian multiplier bits through generalized initial accumulator
and shift values. -/
def fold : List Bool → ℕ → ℕ → ℕ × ℕ
  | [], acc, shift => (acc, shift)
  | bit :: bits, acc, shift =>
      let next := step bit acc shift
      fold bits next.1 next.2

/-- Accumulator value after the first `i` little-endian multiplier bits. -/
def partialAcc (lhs rhs i : ℕ) : ℕ :=
  lhs * Nat.fromBitsLE (rhs.bits.take i)

/-- Shifted multiplicand after `i` iterations. -/
def partialShift (lhs i : ℕ) : ℕ :=
  lhs * 2 ^ i

end BinaryShiftMul

namespace TM

/-- Compact injective assignment of the six multiplication roles to work
tapes. Injectivity makes every pair of roles structurally distinct. -/
structure BinaryShiftMulABI (n : ℕ) where
  /-- Injective map from semantic roles to physical work tapes. -/
  tape : Fin 6 ↪ Fin n

/-- Preserved multiplicand tape. -/
def BinaryShiftMulABI.lhs {n : ℕ} (abi : BinaryShiftMulABI n) : Fin n :=
  abi.tape 0

/-- Preserved multiplier and loop-driver tape. -/
def BinaryShiftMulABI.rhs {n : ℕ} (abi : BinaryShiftMulABI n) : Fin n :=
  abi.tape 1

/-- Initially-zero output accumulator tape. -/
def BinaryShiftMulABI.acc {n : ℕ} (abi : BinaryShiftMulABI n) : Fin n :=
  abi.tape 2

/-- Current shifted multiplicand tape. -/
def BinaryShiftMulABI.shift {n : ℕ} (abi : BinaryShiftMulABI n) : Fin n :=
  abi.tape 3

/-- First alternating zero scratch tape. -/
def BinaryShiftMulABI.tmp {n : ℕ} (abi : BinaryShiftMulABI n) : Fin n :=
  abi.tape 4

/-- Second alternating zero scratch tape. -/
def BinaryShiftMulABI.dbl {n : ℕ} (abi : BinaryShiftMulABI n) : Fin n :=
  abi.tape 5

/-- Distinct ABI slots map to distinct work tapes. -/
theorem BinaryShiftMulABI.tape_ne {n : ℕ} (abi : BinaryShiftMulABI n)
    {first second : Fin 6} (hne : first ≠ second) :
    abi.tape first ≠ abi.tape second := by
  exact fun heq => hne (abi.tape.injective heq)

@[simp] theorem BinaryShiftMulABI.lhs_ne_rhs {n : ℕ}
    (abi : BinaryShiftMulABI n) : abi.lhs ≠ abi.rhs :=
  abi.tape_ne (by decide)

@[simp] theorem BinaryShiftMulABI.lhs_ne_acc {n : ℕ}
    (abi : BinaryShiftMulABI n) : abi.lhs ≠ abi.acc :=
  abi.tape_ne (by decide)

@[simp] theorem BinaryShiftMulABI.lhs_ne_shift {n : ℕ}
    (abi : BinaryShiftMulABI n) : abi.lhs ≠ abi.shift :=
  abi.tape_ne (by decide)

@[simp] theorem BinaryShiftMulABI.lhs_ne_tmp {n : ℕ}
    (abi : BinaryShiftMulABI n) : abi.lhs ≠ abi.tmp :=
  abi.tape_ne (by decide)

@[simp] theorem BinaryShiftMulABI.lhs_ne_dbl {n : ℕ}
    (abi : BinaryShiftMulABI n) : abi.lhs ≠ abi.dbl :=
  abi.tape_ne (by decide)

@[simp] theorem BinaryShiftMulABI.rhs_ne_acc {n : ℕ}
    (abi : BinaryShiftMulABI n) : abi.rhs ≠ abi.acc :=
  abi.tape_ne (by decide)

@[simp] theorem BinaryShiftMulABI.rhs_ne_shift {n : ℕ}
    (abi : BinaryShiftMulABI n) : abi.rhs ≠ abi.shift :=
  abi.tape_ne (by decide)

@[simp] theorem BinaryShiftMulABI.rhs_ne_tmp {n : ℕ}
    (abi : BinaryShiftMulABI n) : abi.rhs ≠ abi.tmp :=
  abi.tape_ne (by decide)

@[simp] theorem BinaryShiftMulABI.rhs_ne_dbl {n : ℕ}
    (abi : BinaryShiftMulABI n) : abi.rhs ≠ abi.dbl :=
  abi.tape_ne (by decide)

@[simp] theorem BinaryShiftMulABI.acc_ne_shift {n : ℕ}
    (abi : BinaryShiftMulABI n) : abi.acc ≠ abi.shift :=
  abi.tape_ne (by decide)

@[simp] theorem BinaryShiftMulABI.acc_ne_tmp {n : ℕ}
    (abi : BinaryShiftMulABI n) : abi.acc ≠ abi.tmp :=
  abi.tape_ne (by decide)

@[simp] theorem BinaryShiftMulABI.acc_ne_dbl {n : ℕ}
    (abi : BinaryShiftMulABI n) : abi.acc ≠ abi.dbl :=
  abi.tape_ne (by decide)

@[simp] theorem BinaryShiftMulABI.shift_ne_tmp {n : ℕ}
    (abi : BinaryShiftMulABI n) : abi.shift ≠ abi.tmp :=
  abi.tape_ne (by decide)

@[simp] theorem BinaryShiftMulABI.shift_ne_dbl {n : ℕ}
    (abi : BinaryShiftMulABI n) : abi.shift ≠ abi.dbl :=
  abi.tape_ne (by decide)

@[simp] theorem BinaryShiftMulABI.tmp_ne_dbl {n : ℕ}
    (abi : BinaryShiftMulABI n) : abi.tmp ≠ abi.dbl :=
  abi.tape_ne (by decide)

/-- Initialize the shifted multiplicand from `lhs`, using the zero accumulator
as the copy routine's preserved zero scratch. -/
def binaryShiftMulInitTM {n : ℕ} (abi : BinaryShiftMulABI n) : TM n :=
  binaryCopyIntoTM abi.lhs abi.shift abi.acc

/-- Add the current shift into the accumulator. The sum is formed on `tmp`,
copied back through zero scratch `dbl`, and `tmp` is reset. -/
def binaryShiftMulUpdateTM {n : ℕ} (abi : BinaryShiftMulABI n) : TM n :=
  seqTM (binaryRippleAddTM abi.acc abi.shift abi.tmp)
    (seqTM (binaryCopyIntoTM abi.tmp abi.acc abi.dbl)
      (resetBinaryWorkTM abi.tmp))

/-- Double `shift`. A copy on `tmp` is added back into `dbl`; after alternating
copy-back and resets, `shift` contains twice its old value and both scratch
tapes are zero. -/
def binaryShiftMulDoubleTM {n : ℕ} (abi : BinaryShiftMulABI n) : TM n :=
  seqTM (binaryCopyIntoTM abi.shift abi.tmp abi.dbl)
    (seqTM (binaryRippleAddTM abi.shift abi.tmp abi.dbl)
      (seqTM (resetBinaryWorkTM abi.tmp)
        (seqTM (binaryCopyIntoTM abi.dbl abi.shift abi.tmp)
          (resetBinaryWorkTM abi.dbl))))

/-- Execute the conditional add and then the unconditional doubling step. -/
def binaryShiftMulOneTM {n : ℕ} (abi : BinaryShiftMulABI n) : TM n :=
  seqTM (binaryShiftMulUpdateTM abi) (binaryShiftMulDoubleTM abi)

/-- Branch on the current multiplier bit. A one performs update-and-double;
every other dispatched Boolean symbol performs only the doubling step. -/
def binaryShiftMulBitBodyTM {n : ℕ} (abi : BinaryShiftMulABI n) : TM n :=
  branchWorkSymbolTM abi.rhs Γ.one
    (binaryShiftMulOneTM abi) (binaryShiftMulDoubleTM abi)

/-- Iterate once per canonical bit on the preserved multiplier tape. -/
def binaryShiftMulLoopTM {n : ℕ} (abi : BinaryShiftMulABI n) : TM n :=
  forBinaryWorkTM abi.rhs (binaryShiftMulBitBodyTM abi)

/-- Restore the multiplier head and reset every non-output scratch tape. -/
def binaryShiftMulCleanupTM {n : ℕ} (abi : BinaryShiftMulABI n) : TM n :=
  seqTM (rewindWorkTM abi.rhs)
    (resetBinaryWorkManyTM [abi.shift, abi.tmp, abi.dbl])

/-- Initialize, scan the multiplier, and clean up the six-tape shift-and-add
implementation. -/
def binaryShiftMulTM {n : ℕ} (abi : BinaryShiftMulABI n) : TM n :=
  seqTM (binaryShiftMulInitTM abi)
    (seqTM (binaryShiftMulLoopTM abi) (binaryShiftMulCleanupTM abi))

/-- Combined input width used by the conservative multiplication budget. -/
def binaryShiftMulWidth (lhs rhs : ℕ) : ℕ :=
  lhs.size + rhs.size

/-- Audited conservative quadratic budget for initialization, all multiplier
iterations, cleanup, and composition seams. -/
def binaryShiftMulTime (lhs rhs : ℕ) : ℕ :=
  let width := binaryShiftMulWidth lhs rhs
  33 * width ^ 2 + 170 * width + 58

end TM

end Complexity
