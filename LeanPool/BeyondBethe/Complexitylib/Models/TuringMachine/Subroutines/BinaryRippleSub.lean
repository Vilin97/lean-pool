/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Internal.Sem
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Internal.Out

/-!
# Linear-time canonical binary subtraction

This module exposes a concrete three-tape ripple-borrow subtractor. It preserves
two canonical little-endian operands, writes their truncated natural-number
difference to a fresh zero result tape, restores every owned head to cell one,
and preserves the complete external tape frame. Its running time is linear in
the operand bit widths.
-/


@[expose] public section

namespace Complexity

namespace BinaryRippleSub

/-- Canonical ripple-borrow subtraction agrees with natural-number monus. -/
theorem subtract_natBits (lhs rhs : ℕ) :
    subtract lhs.bits rhs.bits = (lhs - rhs).bits :=
  subtract_natBits_internal lhs rhs

end BinaryRippleSub

namespace TM

/-- The complete subtractor has a linear bit-width envelope. -/
theorem binaryRippleSubTime_le (lhs rhs : ℕ) :
    binaryRippleSubTime lhs rhs ≤ 3 * (lhs.size + rhs.size) + 10 :=
  binaryRippleSubTime_le_internal lhs rhs

/-- Framed time contract for truncated subtraction. Both operands are restored,
the initially-zero result becomes their natural-number difference, and every
unrelated tape is preserved exactly. -/
theorem binaryRippleSubTM_hoareTime_frame {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleSubDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryNat lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryNat rhs)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryRippleSubTM lhsIdx rhsIdx resultIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work lhsIdx).HasBinaryNat lhs ∧
        (work rhsIdx).HasBinaryNat rhs ∧
        (work resultIdx).HasBinaryNat (lhs - rhs) ∧
        (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
          work i = work₀ i) ∧
        out = out₀)
      (binaryRippleSubTime lhs rhs) :=
  binaryRippleSubTM_hoareTime_frame_internal lhsIdx rhsIdx resultIdx
    hdistinct lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult hinput hother
    houtput

/-- Reachability form of the framed subtraction theorem. -/
theorem binaryRippleSubTM_reachesIn_frame {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleSubDistinct lhsIdx rhsIdx resultIdx)
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
      time ≤ binaryRippleSubTime lhs rhs ∧
      (binaryRippleSubTM lhsIdx rhsIdx resultIdx).reachesIn time
        { state := (binaryRippleSubTM lhsIdx rhsIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryRippleSubTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work lhsIdx).HasBinaryNat lhs ∧
      (c'.work rhsIdx).HasBinaryNat rhs ∧
      (c'.work resultIdx).HasBinaryNat (lhs - rhs) ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  exact binaryRippleSubTM_hoareTime_frame lhsIdx rhsIdx resultIdx hdistinct
    lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult hinput hother houtput
    inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩

/-- All-prefix auxiliary-space contract obtained from the concrete linear
time bound. -/
theorem binaryRippleSubTM_hoareTimeSpace_frame {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleSubDistinct lhsIdx rhsIdx resultIdx)
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
      ({ state := (binaryRippleSubTM lhsIdx rhsIdx resultIdx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (binaryRippleSubTM lhsIdx rhsIdx resultIdx).Q).WithinAuxSpace
          inputLength initialSpace) :
    (binaryRippleSubTM lhsIdx rhsIdx resultIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work lhsIdx).HasBinaryNat lhs ∧
        (work rhsIdx).HasBinaryNat rhs ∧
        (work resultIdx).HasBinaryNat (lhs - rhs) ∧
        (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
          work i = work₀ i) ∧
        out = out₀)
      (binaryRippleSubTime lhs rhs) inputLength
      (initialSpace + binaryRippleSubTime lhs rhs) :=
  binaryRippleSubTM_hoareTimeSpace_frame_internal lhsIdx rhsIdx resultIdx
    hdistinct lhs rhs inputLength initialSpace inp₀ work₀ out₀ hlhs hrhs
    hresult hinput hother houtput hinitial

/-- Canonical subtraction never moves the public output head left. -/
theorem binaryRippleSubTM_isTransducer {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) :
    (binaryRippleSubTM lhsIdx rhsIdx resultIdx).IsTransducer :=
  binaryRippleSubTM_isTransducer_internal lhsIdx rhsIdx resultIdx

end TM

end Complexity
