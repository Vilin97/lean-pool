/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Defs
public import Mathlib.Data.Nat.Size
public import Std.Tactic.BVDecide.Normalize.Bool

/-!
# Linear-time canonical binary addition -- pure proofs

This file proves that the finite full-adder recurrence computes addition on
canonical little-endian `Nat.bits`. The generalized theorem includes an
incoming carry so that its induction follows the recurrence exactly.
-/


public section

namespace Complexity

namespace BinaryRippleAdd

private theorem ripple_nil_cons (carry rhsBit : Bool)
    (rhs : List Bool) :
    ripple carry [] (rhsBit :: rhs) =
      sumBit carry false rhsBit ::
        ripple (carryBit carry false rhsBit) [] rhs := by
  cases carry <;> simp [ripple]

private theorem ripple_cons_nil (carry lhsBit : Bool)
    (lhs : List Bool) :
    ripple carry (lhsBit :: lhs) [] =
      sumBit carry lhsBit false ::
        ripple (carryBit carry lhsBit false) lhs [] := by
  cases carry <;> simp [ripple]

private theorem ripple_cons_cons (carry lhsBit rhsBit : Bool)
    (lhs rhs : List Bool) :
    ripple carry (lhsBit :: lhs) (rhsBit :: rhs) =
      sumBit carry lhsBit rhsBit ::
        ripple (carryBit carry lhsBit rhsBit) lhs rhs := by
  cases carry <;> simp [ripple]

private theorem fullAdder_value (carry lhsBit rhsBit : Bool) (lhs rhs : ℕ) :
    Nat.bit lhsBit lhs + Nat.bit rhsBit rhs + (if carry then 1 else 0) =
      Nat.bit (sumBit carry lhsBit rhsBit)
        (lhs + rhs + (if carryBit carry lhsBit rhsBit then 1 else 0)) := by
  cases carry <;> cases lhsBit <;> cases rhsBit <;>
    simp [sumBit, carryBit, Nat.bit] <;> omega

private theorem fullAdder_valid (carry lhsBit rhsBit : Bool) (lhs rhs : ℕ)
    (hvalue : Nat.bit lhsBit lhs + Nat.bit rhsBit rhs +
      (if carry then 1 else 0) ≠ 0) :
    lhs + rhs + (if carryBit carry lhsBit rhsBit then 1 else 0) = 0 →
      sumBit carry lhsBit rhsBit = true := by
  apply Nat.bit_ne_zero_iff.mp
  rw [← fullAdder_value]
  exact hvalue

/-- Ripple addition with an incoming carry computes the corresponding natural
sum. This is the induction-strengthened form of `ripple_natBits_internal`. -/
theorem ripple_natBits_carry_internal (carry : Bool) (lhs rhs : ℕ) :
    ripple carry lhs.bits rhs.bits =
      (lhs + rhs + (if carry then 1 else 0)).bits := by
  induction lhs using Nat.binaryRec' generalizing rhs carry with
  | zero =>
      simp only [Nat.zero_bits, Nat.zero_add]
      induction rhs using Nat.binaryRec' generalizing carry with
      | zero =>
          cases carry <;> simp [ripple]
      | bit rhsBit rhs hrhs ih =>
          have hrhsValue : Nat.bit rhsBit rhs ≠ 0 :=
            Nat.bit_ne_zero_iff.mpr hrhs
          have htotal : Nat.bit false 0 + Nat.bit rhsBit rhs +
              (if carry then 1 else 0) ≠ 0 := by
            omega
          have hvalid := fullAdder_valid carry false rhsBit 0 rhs htotal
          have hvalid' :
              rhs + (if carryBit carry false rhsBit then 1 else 0) = 0 →
                sumBit carry false rhsBit = true := by
            simpa using hvalid
          have hadd : Nat.bit rhsBit rhs + (if carry then 1 else 0) =
              Nat.bit (sumBit carry false rhsBit)
                (rhs + (if carryBit carry false rhsBit then 1 else 0)) := by
            simpa using fullAdder_value carry false rhsBit 0 rhs
          calc
            ripple carry [] (Nat.bit rhsBit rhs).bits =
                sumBit carry false rhsBit ::
                  ripple (carryBit carry false rhsBit) [] rhs.bits := by
              rw [Nat.bits_append_bit rhs rhsBit hrhs]
              exact ripple_nil_cons carry rhsBit rhs.bits
            _ = sumBit carry false rhsBit ::
                (rhs + (if carryBit carry false rhsBit then 1 else 0)).bits := by
              rw [ih]
            _ = (Nat.bit (sumBit carry false rhsBit)
                (rhs + (if carryBit carry false rhsBit then 1 else 0))).bits := by
              exact (Nat.bits_append_bit _ _ hvalid').symm
            _ = (Nat.bit rhsBit rhs + (if carry then 1 else 0)).bits := by
              rw [hadd]
  | bit lhsBit lhs hlhs ih =>
      induction rhs using Nat.binaryRec' generalizing carry with
      | zero =>
          have hlhsValue : Nat.bit lhsBit lhs ≠ 0 :=
            Nat.bit_ne_zero_iff.mpr hlhs
          have htotal : Nat.bit lhsBit lhs + Nat.bit false 0 +
              (if carry then 1 else 0) ≠ 0 := by
            omega
          have hvalid := fullAdder_valid carry lhsBit false lhs 0 htotal
          have hvalid' :
              lhs + (if carryBit carry lhsBit false then 1 else 0) = 0 →
                sumBit carry lhsBit false = true := by
            simpa using hvalid
          have hadd : Nat.bit lhsBit lhs + (if carry then 1 else 0) =
              Nat.bit (sumBit carry lhsBit false)
                (lhs + (if carryBit carry lhsBit false then 1 else 0)) := by
            simpa using fullAdder_value carry lhsBit false lhs 0
          calc
            ripple carry (Nat.bit lhsBit lhs).bits [] =
                sumBit carry lhsBit false ::
                  ripple (carryBit carry lhsBit false) lhs.bits [] := by
              rw [Nat.bits_append_bit lhs lhsBit hlhs]
              exact ripple_cons_nil carry lhsBit lhs.bits
            _ = sumBit carry lhsBit false ::
                (lhs + (if carryBit carry lhsBit false then 1 else 0)).bits := by
              simpa using congrArg (List.cons (sumBit carry lhsBit false))
                (ih (carryBit carry lhsBit false) 0)
            _ = (Nat.bit (sumBit carry lhsBit false)
                (lhs + (if carryBit carry lhsBit false then 1 else 0))).bits := by
              exact (Nat.bits_append_bit _ _ hvalid').symm
            _ = (Nat.bit lhsBit lhs + (if carry then 1 else 0)).bits := by
              rw [hadd]
      | bit rhsBit rhs hrhs _ =>
          have hlhsValue : Nat.bit lhsBit lhs ≠ 0 :=
            Nat.bit_ne_zero_iff.mpr hlhs
          have htotal : Nat.bit lhsBit lhs + Nat.bit rhsBit rhs +
              (if carry then 1 else 0) ≠ 0 := by
            omega
          have hvalid := fullAdder_valid carry lhsBit rhsBit lhs rhs htotal
          have hadd := fullAdder_value carry lhsBit rhsBit lhs rhs
          calc
            ripple carry (Nat.bit lhsBit lhs).bits (Nat.bit rhsBit rhs).bits =
                sumBit carry lhsBit rhsBit ::
                  ripple (carryBit carry lhsBit rhsBit) lhs.bits rhs.bits := by
              rw [Nat.bits_append_bit lhs lhsBit hlhs,
                Nat.bits_append_bit rhs rhsBit hrhs]
              exact ripple_cons_cons carry lhsBit rhsBit lhs.bits rhs.bits
            _ = sumBit carry lhsBit rhsBit ::
                (lhs + rhs +
                  (if carryBit carry lhsBit rhsBit then 1 else 0)).bits := by
              rw [ih]
            _ = (Nat.bit (sumBit carry lhsBit rhsBit)
                (lhs + rhs +
                  (if carryBit carry lhsBit rhsBit then 1 else 0))).bits := by
              exact (Nat.bits_append_bit _ _ hvalid).symm
            _ = (Nat.bit lhsBit lhs + Nat.bit rhsBit rhs +
                (if carry then 1 else 0)).bits := by
              rw [hadd]

/-- Ripple addition without an incoming carry computes canonical addition. -/
theorem ripple_natBits_internal (lhs rhs : ℕ) :
    ripple false lhs.bits rhs.bits = (lhs + rhs).bits := by
  simpa using ripple_natBits_carry_internal false lhs rhs

/-- The pure result has exactly the canonical width of the sum. -/
theorem length_ripple_natBits_internal (lhs rhs : ℕ) :
    (ripple false lhs.bits rhs.bits).length = (lhs + rhs).size := by
  rw [ripple_natBits_internal, Nat.size_eq_bits_len]

end BinaryRippleAdd

namespace TM

/-- Rewrite the list-level scan bound as a bound in natural-number widths. -/
theorem binaryRippleAddScanTime_natBits_internal (lhs rhs : ℕ) :
    binaryRippleAddScanTime lhs.bits rhs.bits = max lhs.size rhs.size + 1 := by
  simp [binaryRippleAddScanTime, Nat.size_eq_bits_len]

end TM

end Complexity
