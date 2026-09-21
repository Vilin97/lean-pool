/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryEq.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryEq.Internal

/-!
# Binary work-tape equality

This module exposes a framed linear-time correctness theorem for the concrete
binary equality routine used by RAM register-store scans.
-/


public section

namespace Complexity

namespace TM

/-- Two canonical binary strings are compared in linear time. The Boolean
answer is appended to `resultIdx`; input, output, unrelated tapes, and all
binary contents are preserved. -/
theorem binaryEqTM_reachesIn_frame {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryEqDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryString lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryString rhs)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c' t,
      t ≤ binaryEqTime lhs rhs ∧
      (binaryEqTM lhsIdx rhsIdx resultIdx).reachesIn t
        { state := (binaryEqTM lhsIdx rhsIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryEqTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work resultIdx).HasBinaryPrefix [decide (lhs = rhs)] ∧
      (c'.work lhsIdx).HasBinaryContent lhs ∧
      1 ≤ (c'.work lhsIdx).head ∧
      (c'.work rhsIdx).HasBinaryContent rhs ∧
      1 ≤ (c'.work rhsIdx).head ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ :=
  binaryEqTM_reachesIn_frame_internal lhsIdx rhsIdx resultIdx hdistinct
    lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult hinput hother houtput

/-- Binary equality preserves one-way output safety. -/
theorem binaryEqTM_isTransducer {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) :
    (binaryEqTM lhsIdx rhsIdx resultIdx).IsTransducer :=
  binaryEqTM_isTransducer_internal lhsIdx rhsIdx resultIdx

end TM

end Complexity
