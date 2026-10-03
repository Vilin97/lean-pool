/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Internal

/-!
# Linear-time canonical binary addition

This module exposes a concrete three-tape ripple-carry adder. It preserves two
canonical little-endian operands, writes their canonical sum to a fresh zero
result tape, restores every owned head to cell one, and preserves the complete
external tape frame. Its running time is linear in the operand bit widths.

The older `TM.binaryAddIntoTM` remains useful as a value-iterating count-up
routine; complexity-sensitive RAM simulation should use this width-linear
machine instead.
-/


@[expose] public section

namespace Complexity

namespace BinaryRippleAdd

/-- Ripple carry over canonical little-endian encodings computes addition. -/
theorem ripple_natBits (lhs rhs : ℕ) :
    ripple false lhs.bits rhs.bits = (lhs + rhs).bits :=
  ripple_natBits_internal lhs rhs

end BinaryRippleAdd

namespace TM

/-- The scan bound is one more than the larger operand width. -/
theorem binaryRippleAddScanTime_natBits (lhs rhs : ℕ) :
    binaryRippleAddScanTime lhs.bits rhs.bits =
      max lhs.size rhs.size + 1 :=
  binaryRippleAddScanTime_natBits_internal lhs rhs

/-- Addition increases binary width by at most one over the larger operand. -/
theorem binaryRippleAdd_sum_size_le (lhs rhs : ℕ) :
    (lhs + rhs).size ≤ max lhs.size rhs.size + 1 :=
  size_add_le_max_add_one_internal lhs rhs

/-- The complete scan-and-rewind machine has a linear bit-width envelope. -/
theorem binaryRippleAddTime_le (lhs rhs : ℕ) :
    binaryRippleAddTime lhs rhs ≤
      3 * (lhs.size + rhs.size) + 14 :=
  binaryRippleAddTime_le_internal lhs rhs

/-- Framed time contract for canonical addition. Both operands are restored,
the initially-zero result becomes their sum, and every unrelated tape is
preserved exactly. -/
theorem binaryRippleAddTM_hoareTime_frame {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleAddDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryNat lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryNat rhs)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryRippleAddTM lhsIdx rhsIdx resultIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work lhsIdx).HasBinaryNat lhs ∧
        (work rhsIdx).HasBinaryNat rhs ∧
        (work resultIdx).HasBinaryNat (lhs + rhs) ∧
        (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
          work i = work₀ i) ∧
        out = out₀)
      (binaryRippleAddTime lhs rhs) :=
  binaryRippleAddTM_hoareTime_frame_internal lhsIdx rhsIdx resultIdx
    hdistinct lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult hinput hother
    houtput

/-- Reachability form of the framed addition theorem. -/
theorem binaryRippleAddTM_reachesIn_frame {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleAddDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryNat lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryNat rhs)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀) :
    ∃ c' time,
      time ≤ binaryRippleAddTime lhs rhs ∧
      (binaryRippleAddTM lhsIdx rhsIdx resultIdx).reachesIn time
        { state := (binaryRippleAddTM lhsIdx rhsIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryRippleAddTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work lhsIdx).HasBinaryNat lhs ∧
      (c'.work rhsIdx).HasBinaryNat rhs ∧
      (c'.work resultIdx).HasBinaryNat (lhs + rhs) ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  exact binaryRippleAddTM_hoareTime_frame lhsIdx rhsIdx resultIdx hdistinct
    lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult hinput hother houtput
    inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩

/-- All-prefix auxiliary-space contract obtained from the concrete linear
time bound. -/
theorem binaryRippleAddTM_hoareTimeSpace_frame {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleAddDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryNat lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryNat rhs)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀)
    (hinitial :
      ({ state := (binaryRippleAddTM lhsIdx rhsIdx resultIdx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (binaryRippleAddTM lhsIdx rhsIdx resultIdx).Q).WithinAuxSpace
          inputLength initialSpace) :
    (binaryRippleAddTM lhsIdx rhsIdx resultIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work lhsIdx).HasBinaryNat lhs ∧
        (work rhsIdx).HasBinaryNat rhs ∧
        (work resultIdx).HasBinaryNat (lhs + rhs) ∧
        (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
          work i = work₀ i) ∧
        out = out₀)
      (binaryRippleAddTime lhs rhs) inputLength
      (initialSpace + binaryRippleAddTime lhs rhs) :=
  binaryRippleAddTM_hoareTimeSpace_frame_internal lhsIdx rhsIdx resultIdx
    hdistinct lhs rhs inputLength initialSpace inp₀ work₀ out₀ hlhs hrhs
    hresult hinput hother houtput hinitial

/-- Canonical addition never moves the public output head left. -/
theorem binaryRippleAddTM_isTransducer {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) :
    (binaryRippleAddTM lhsIdx rhsIdx resultIdx).IsTransducer :=
  binaryRippleAddTM_isTransducer_internal lhsIdx rhsIdx resultIdx

end TM

end Complexity
