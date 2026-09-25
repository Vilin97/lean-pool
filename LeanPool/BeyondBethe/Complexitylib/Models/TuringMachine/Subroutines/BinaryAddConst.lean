/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst.Internal

/-!
# Addition of a fixed natural to a canonical binary tape

This module exposes the literal-frame and resource contracts for a finite
sequence of binary successors compiled from a hardwired natural constant.

## Main results

- `binaryAddConstTM_reachesIn_frame` gives the exact runtime and endpoint.
- `binaryAddConstTM_hoareTime_frame` packages the exact literal frame.
- `binaryAddConstTM_hoareTimeSpace_frame` gives a width-based prefix bound.
- `binaryAddConstTM_isTransducer` proves append-only-output safety.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Adding a fixed constant to zero has a quadratic time bound. -/
theorem binaryAddConstTime_zero_le (fixedValue : ℕ) :
    binaryAddConstTime fixedValue 0 ≤ 4 * (fixedValue + 1) ^ 2 := by
  induction fixedValue with
  | zero => simp [binaryAddConstTime]
  | succ fixedValue ih =>
      rw [binaryAddConstTime]
      have hsucc := binarySuccTime_le fixedValue
      have hsize : fixedValue.size ≤ fixedValue := by
        rw [Nat.size_le]
        exact Nat.lt_pow_self (by decide)
      calc
        binaryAddConstTime fixedValue 0 + 1 +
            binarySuccTime (0 + fixedValue) ≤
            4 * (fixedValue + 1) ^ 2 + 1 + (2 * fixedValue + 2) := by
          simp only [Nat.zero_add]
          exact Nat.add_le_add (Nat.add_le_add ih le_rfl)
            (le_trans hsucc (by omega))
        _ ≤ 4 * (fixedValue + 1 + 1) ^ 2 := by nlinarith

/-- Fixed-constant addition has the advertised exact runtime and changes only
the destination tape. -/
theorem binaryAddConstTM_reachesIn_frame
    (idx : Fin n) (fixedValue dstValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hdst : (work₀ idx).HasBinaryNat dstValue)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryAddConstTM idx fixedValue).reachesIn
      (binaryAddConstTime fixedValue dstValue)
      { state := (binaryAddConstTM idx fixedValue).qstart
        input := inp₀
        work := work₀
        output := out₀ }
      { state := (binaryAddConstTM idx fixedValue).qhalt
        input := inp₀
        work := Function.update work₀ idx
          ((Tape.init ((dstValue + fixedValue).bits.map Γ.ofBool)).move
            Dir3.right)
        output := out₀ } :=
  binaryAddConstTM_reachesIn_frame_internal idx fixedValue dstValue inp₀ work₀
    out₀ hdst hinp hother hout

/-- Time-bounded literal-frame contract for fixed-constant addition. -/
theorem binaryAddConstTM_hoareTime_frame
    (idx : Fin n) (fixedValue dstValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hdst : (work₀ idx).HasBinaryNat dstValue)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryAddConstTM idx fixedValue).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx
          ((Tape.init ((dstValue + fixedValue).bits.map Γ.ofBool)).move
            Dir3.right) ∧
        out = out₀)
      (binaryAddConstTime fixedValue dstValue) :=
  binaryAddConstTM_hoareTime_frame_internal idx fixedValue dstValue inp₀ work₀
    out₀ hdst hinp hother hout

/-- Every prefix of fixed-constant addition respects a bound controlled by
the final destination width. -/
theorem binaryAddConstTM_hoareTimeSpace_frame
    (idx : Fin n) (fixedValue dstValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hdst : (work₀ idx).HasBinaryNat dstValue)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryAddConstTM idx fixedValue).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx
          ((Tape.init ((dstValue + fixedValue).bits.map Γ.ofBool)).move
            Dir3.right) ∧
        out = out₀)
      (binaryAddConstTime fixedValue dstValue) inputLength
      (binaryAddConstSpace initialSpace fixedValue dstValue) :=
  binaryAddConstTM_hoareTimeSpace_frame_internal idx fixedValue dstValue
    inputLength initialSpace inp₀ work₀ out₀ hdst hinp hother hout
    hworkSpace hinputSpace

/-- Fixed-constant addition never moves its output head left. -/
theorem binaryAddConstTM_isTransducer (idx : Fin n) (fixedValue : ℕ) :
    (binaryAddConstTM idx fixedValue).IsTransducer :=
  binaryAddConstTM_isTransducer_internal idx fixedValue

end TM

end Complexity
