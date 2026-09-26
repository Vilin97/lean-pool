/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Internal

/-!
# Little-endian binary successor

This module exposes the canonical semantics and compositional contracts for
`TM.binarySuccTM`. Natural numbers use `Nat.bits`, with the least significant
bit first and zero represented by the empty string. Successor propagates carry
through the initial one bits, appends on overflow, and rewinds the target work
tape to cell one.

## Main results

- `BinarySucc.ripple_natBits` — the pure ripple function computes successor.
- `TM.binarySuccTM_reachesIn_frame` — exact execution with a full tape frame.
- `TM.binarySuccTM_hoareTimeSpace_frame` — terminating and all-reachable space
  contract.
- `TM.binarySuccTM_isTransducer` — the output head never moves left.
-/


@[expose] public section

namespace Complexity

namespace BinarySucc

/-- Ripple carry on canonical little-endian bits computes natural-number
successor, including the empty representation of zero and overflow. -/
theorem ripple_natBits (value : ℕ) :
    ripple value.bits = (value + 1).bits :=
  ripple_natBits_internal value

/-- The exact transition count is at most twice the represented bit length,
plus two. -/
theorem steps_le (bits : List Bool) :
    steps bits ≤ 2 * bits.length + 2 :=
  steps_le_internal bits

end BinarySucc

namespace Tape

/-- `HasBinaryNat` determines the entire canonical initialized tape, including
its head position, left marker, digits, and blank tail. -/
theorem HasBinaryNat.eq_init_move_right {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) :
    t = (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right :=
  eq_init_move_right_of_hasBinaryString h.2 h.1

/-- The standard initialized natural-number tape satisfies `HasBinaryNat`. -/
theorem init_move_right_hasBinaryNat (value : ℕ) :
    ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right).HasBinaryNat value := by
  refine ⟨?_, init_move_right_hasBinaryString value.bits⟩
  simp [Tape.init, Tape.move]

end Tape

namespace TM

/-- The exact successor running time is at most twice the standard binary
size of the input value, plus two. -/
theorem binarySuccTime_le (value : ℕ) :
    binarySuccTime value ≤ 2 * value.size + 2 :=
  binarySuccTime_le_internal value

/-- Starting on a canonical rewound natural number, `binarySuccTM` halts after
exactly `binarySuccTime value` transitions with the canonical representation
of `value + 1`. Input, output, and every unrelated work tape are preserved
exactly. The off-marker hypotheses are precisely what makes the structurally
mandatory idle moves preserve those tape heads. -/
theorem binarySuccTM_reachesIn_frame {n : ℕ}
    (idx : Fin n) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat value)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∃ c',
      (binarySuccTM idx).reachesIn (binarySuccTime value)
        { state := (binarySuccTM idx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binarySuccTM idx).halted c' ∧
      c'.input = inp₀ ∧
      (∀ i, i ≠ idx → c'.work i = work₀ i) ∧
      (c'.work idx).HasBinaryNat (value + 1) ∧
      c'.output = out₀ :=
  binarySuccTM_reachesIn_frame_internal
    idx value inp₀ work₀ out₀ hvalue hinp hother hout

/-- Time-bounded compositional form of `binarySuccTM_reachesIn_frame`. -/
theorem binarySuccTM_hoareTime_frame {n : ℕ}
    (idx : Fin n) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat value)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    (binarySuccTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        (work idx).HasBinaryNat (value + 1) ∧
        out = out₀)
      (binarySuccTime value) :=
  binarySuccTM_hoareTime_frame_internal
    idx value inp₀ work₀ out₀ hvalue hinp hother hout

/-- Time-and-space contract for canonical successor. The space component
bounds every reachable configuration, not just the terminal one. Starting
from auxiliary-space budget `initialSpace`, one cell per possible transition
gives the explicit bound `initialSpace + binarySuccTime value`. -/
theorem binarySuccTM_hoareTimeSpace_frame {n : ℕ}
    (idx : Fin n) (value inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat value)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start)
    (hinitial :
      ({ state := (binarySuccTM idx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (binarySuccTM idx).Q).WithinAuxSpace inputLength initialSpace) :
    (binarySuccTM idx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        (work idx).HasBinaryNat (value + 1) ∧
        out = out₀)
      (binarySuccTime value) inputLength
      (initialSpace + binarySuccTime value) :=
  binarySuccTM_hoareTimeSpace_frame_internal idx value inputLength initialSpace
    inp₀ work₀ out₀ hvalue hinp hother hout hinitial

/-- `binarySuccTM` never moves the output head left, so it is safe to use in
one-way-output, space-bounded compositions. -/
theorem binarySuccTM_isTransducer {n : ℕ} (idx : Fin n) :
    (binarySuccTM idx).IsTransducer :=
  binarySuccTM_isTransducer_internal idx

end TM

end Complexity
