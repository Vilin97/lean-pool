/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryPred.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryPred.Internal

/-!
# Little-endian binary predecessor

This module exposes the canonical semantics and compositional contracts for
`TM.binaryPredTM`. Natural numbers use little-endian `Nat.bits`. On positive
input `value + 1`, borrow propagates through initial zero bits, canonicalizes
the high bit when decrementing a power of two, and rewinds the target tape.

The machine is total on canonical zero and leaves its empty representation
unchanged, but the decrement theorems deliberately require the target to
represent `value + 1`; they make no underflow claim.

## Main results

- `BinaryPred.ripple_succ_natBits` — pure borrow computes predecessor.
- `TM.binaryPredTM_reachesIn_frame` — exact execution with a full tape frame.
- `TM.binaryPredTM_hoareTimeSpace_frame` — terminating and all-reachable
  width-based space contract.
- `TM.binaryPredTM_isTransducer` — the output head never moves left.
-/


public section

namespace Complexity

namespace BinaryPred

/-- Ripple borrow on the canonical bits of a positive natural computes its
predecessor, including high-bit erasure for powers of two. -/
theorem ripple_succ_natBits (value : ℕ) :
    ripple (value + 1).bits = value.bits :=
  ripple_succ_natBits_internal value

/-- The exact transition count is at most twice the represented positive
input width, plus two. -/
theorem steps_le (bits : List Bool) :
    steps bits ≤ 2 * bits.length + 2 :=
  steps_le_internal bits

end BinaryPred

namespace TM

/-- Exact predecessor time is bounded linearly in the binary width of the
positive input `value + 1`. -/
theorem binaryPredTime_le (value : ℕ) :
    binaryPredTime value ≤ 2 * (value + 1).size + 2 :=
  binaryPredTime_le_internal value

/-- Starting on canonical positive `value + 1`, `binaryPredTM` halts after
exactly `binaryPredTime value` transitions with canonical `value`. Input,
output, and every unrelated work tape are preserved exactly. The positive
precondition is the explicit no-underflow boundary of this contract. -/
theorem binaryPredTM_reachesIn_frame {n : ℕ}
    (idx : Fin n) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat (value + 1))
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∃ c',
      (binaryPredTM idx).reachesIn (binaryPredTime value)
        { state := (binaryPredTM idx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryPredTM idx).halted c' ∧
      c'.input = inp₀ ∧
      (∀ i, i ≠ idx → c'.work i = work₀ i) ∧
      (c'.work idx).HasBinaryNat value ∧
      c'.output = out₀ :=
  binaryPredTM_reachesIn_frame_internal idx value inp₀ work₀ out₀
    hvalue hinp hother hout

/-- Time-bounded compositional form of `binaryPredTM_reachesIn_frame`. -/
theorem binaryPredTM_hoareTime_frame {n : ℕ}
    (idx : Fin n) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat (value + 1))
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    (binaryPredTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        (work idx).HasBinaryNat value ∧
        out = out₀)
      (binaryPredTime value) :=
  binaryPredTM_hoareTime_frame_internal idx value inp₀ work₀ out₀
    hvalue hinp hother hout

/-- Time-and-space contract for positive canonical predecessor. Every
reachable configuration stays inside the explicit width-based budget
`binaryPredSpace initialSpace value`; this is independent of the represented
numeric magnitude except through its binary width. -/
theorem binaryPredTM_hoareTimeSpace_frame {n : ℕ}
    (idx : Fin n) (value inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat (value + 1))
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start)
    (hinitial :
      ({ state := (binaryPredTM idx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (binaryPredTM idx).Q).WithinAuxSpace inputLength initialSpace) :
    (binaryPredTM idx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        (work idx).HasBinaryNat value ∧
        out = out₀)
      (binaryPredTime value) inputLength
      (binaryPredSpace initialSpace value) :=
  binaryPredTM_hoareTimeSpace_frame_internal idx value inputLength initialSpace
    inp₀ work₀ out₀ hvalue hinp hother hout hinitial

/-- `binaryPredTM` never moves the output head left, so it is safe in
one-way-output, space-bounded compositions. -/
theorem binaryPredTM_isTransducer {n : ℕ} (idx : Fin n) :
    (binaryPredTM idx).IsTransducer :=
  binaryPredTM_isTransducer_internal idx

end TM

end Complexity
