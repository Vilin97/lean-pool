/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryShiftMul.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryShiftMul.Internal.Out
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryShiftMul.Internal.Pure
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryShiftMul.Internal.Sem

/-!
# Width-driven binary shift-and-add multiplication

This module exposes a concrete six-work-tape multiplier. It preserves two
canonical little-endian operands, writes their product to an initially-zero
accumulator, restores every owned head to cell one, clears three scratch tapes,
and preserves the complete external tape frame. Its running time is quadratic
in the combined operand width.
-/


@[expose] public section

namespace Complexity

namespace BinaryShiftMul

/-- The generalized shift-and-add fold has its closed arithmetic form. -/
theorem fold_eq (bits : List Bool) (acc shift : ℕ) :
    fold bits acc shift =
      (acc + shift * Nat.fromBitsLE bits, shift * 2 ^ bits.length) :=
  fold_eq_internal bits acc shift

/-- Folding all canonical multiplier bits computes multiplication. -/
theorem fold_natBits (lhs rhs : ℕ) :
    fold rhs.bits 0 lhs = (lhs * rhs, lhs * 2 ^ rhs.size) :=
  fold_natBits_internal lhs rhs

/-- Binary multiplication produces at most the sum of the operand widths. -/
theorem size_mul_le_add (lhs rhs : ℕ) :
    (lhs * rhs).size ≤ lhs.size + rhs.size :=
  size_mul_le_add_internal lhs rhs

end BinaryShiftMul

namespace TM

/-- The audited multiplier budget is quadratic in combined input width. -/
theorem binaryShiftMulTime_eq (lhs rhs : ℕ) :
    binaryShiftMulTime lhs rhs =
      33 * binaryShiftMulWidth lhs rhs ^ 2 +
        170 * binaryShiftMulWidth lhs rhs + 58 :=
  rfl

/-- Framed time contract for canonical binary multiplication. Both operands
are restored, the accumulator becomes their product, every scratch tape is
reset to zero, and all unrelated tapes are preserved exactly. -/
theorem binaryShiftMulTM_hoareTime_frame {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ abi.lhs).HasBinaryNat lhs)
    (hrhs : (work₀ abi.rhs).HasBinaryNat rhs)
    (hacc : (work₀ abi.acc).HasBinaryNat 0)
    (hshift : (work₀ abi.shift).HasBinaryNat 0)
    (htmp : (work₀ abi.tmp).HasBinaryNat 0)
    (hdbl : (work₀ abi.dbl).HasBinaryNat 0)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryShiftMulTM abi).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work abi.lhs).HasBinaryNat lhs ∧
        (work abi.rhs).HasBinaryNat rhs ∧
        (work abi.acc).HasBinaryNat (lhs * rhs) ∧
        (work abi.shift).HasBinaryNat 0 ∧
        (work abi.tmp).HasBinaryNat 0 ∧
        (work abi.dbl).HasBinaryNat 0 ∧
        (∀ i, i ≠ abi.lhs → i ≠ abi.rhs → i ≠ abi.acc →
          i ≠ abi.shift → i ≠ abi.tmp → i ≠ abi.dbl →
            work i = work₀ i) ∧
        out = out₀)
      (binaryShiftMulTime lhs rhs) :=
  binaryShiftMulTM_hoareTime_frame_internal abi lhs rhs inp₀ work₀ out₀
    hlhs hrhs hacc hshift htmp hdbl hinput hwork houtput

/-- Reachability form of the framed multiplication theorem. -/
theorem binaryShiftMulTM_reachesIn_frame {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ abi.lhs).HasBinaryNat lhs)
    (hrhs : (work₀ abi.rhs).HasBinaryNat rhs)
    (hacc : (work₀ abi.acc).HasBinaryNat 0)
    (hshift : (work₀ abi.shift).HasBinaryNat 0)
    (htmp : (work₀ abi.tmp).HasBinaryNat 0)
    (hdbl : (work₀ abi.dbl).HasBinaryNat 0)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    ∃ c' time,
      time ≤ binaryShiftMulTime lhs rhs ∧
      (binaryShiftMulTM abi).reachesIn time
        { state := (binaryShiftMulTM abi).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryShiftMulTM abi).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work abi.lhs).HasBinaryNat lhs ∧
      (c'.work abi.rhs).HasBinaryNat rhs ∧
      (c'.work abi.acc).HasBinaryNat (lhs * rhs) ∧
      (c'.work abi.shift).HasBinaryNat 0 ∧
      (c'.work abi.tmp).HasBinaryNat 0 ∧
      (c'.work abi.dbl).HasBinaryNat 0 ∧
      (∀ i, i ≠ abi.lhs → i ≠ abi.rhs → i ≠ abi.acc →
        i ≠ abi.shift → i ≠ abi.tmp → i ≠ abi.dbl →
          c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  exact binaryShiftMulTM_hoareTime_frame abi lhs rhs inp₀ work₀ out₀
    hlhs hrhs hacc hshift htmp hdbl hinput hwork houtput
    inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩

/-- All-prefix auxiliary-space contract obtained from the concrete quadratic
time envelope. -/
theorem binaryShiftMulTM_hoareTimeSpace_frame {n : ℕ}
    (abi : BinaryShiftMulABI n) (lhs rhs inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ abi.lhs).HasBinaryNat lhs)
    (hrhs : (work₀ abi.rhs).HasBinaryNat rhs)
    (hacc : (work₀ abi.acc).HasBinaryNat 0)
    (hshift : (work₀ abi.shift).HasBinaryNat 0)
    (htmp : (work₀ abi.tmp).HasBinaryNat 0)
    (hdbl : (work₀ abi.dbl).HasBinaryNat 0)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀)
    (hinitial :
      ({ state := (binaryShiftMulTM abi).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (binaryShiftMulTM abi).Q).WithinAuxSpace
          inputLength initialSpace) :
    (binaryShiftMulTM abi).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work abi.lhs).HasBinaryNat lhs ∧
        (work abi.rhs).HasBinaryNat rhs ∧
        (work abi.acc).HasBinaryNat (lhs * rhs) ∧
        (work abi.shift).HasBinaryNat 0 ∧
        (work abi.tmp).HasBinaryNat 0 ∧
        (work abi.dbl).HasBinaryNat 0 ∧
        (∀ i, i ≠ abi.lhs → i ≠ abi.rhs → i ≠ abi.acc →
          i ≠ abi.shift → i ≠ abi.tmp → i ≠ abi.dbl →
            work i = work₀ i) ∧
        out = out₀)
      (binaryShiftMulTime lhs rhs) inputLength
      (initialSpace + binaryShiftMulTime lhs rhs) :=
  binaryShiftMulTM_hoareTimeSpace_frame_internal abi lhs rhs inputLength
    initialSpace inp₀ work₀ out₀ hlhs hrhs hacc hshift htmp hdbl hinput
    hwork houtput hinitial

/-- Canonical shift-and-add multiplication never moves the public output head
left. -/
theorem binaryShiftMulTM_isTransducer {n : ℕ}
    (abi : BinaryShiftMulABI n) :
    (binaryShiftMulTM abi).IsTransducer :=
  binaryShiftMulTM_isTransducer_internal abi

end TM

end Complexity
