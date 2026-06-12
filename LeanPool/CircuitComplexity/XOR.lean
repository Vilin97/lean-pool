/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.Basic

/-! # XOR (Parity) Function

This module defines the N-input XOR function and its key properties.

## Main definitions

* `Schnorr.xorBool` — the N-input XOR (parity) function

## Main results

* `Schnorr.xorBool_flip` — flipping any input bit flips XOR
* `Schnorr.xorBool_essential` — XOR depends on all inputs
-/

namespace CircuitComplexity


namespace Schnorr

/-- The N-input XOR (parity) function. -/
def xorBool : (N : Nat) → BitString N → Bool
  | 0, _ => false
  | _ + 1, x => (x 0).xor (xorBool _ (x ∘ Fin.succ))

/-- `a.xor (!b) = !(a.xor b)` — complement on the right side of XOR. -/
private theorem bxor_not_right (a b : Bool) : (a.xor (!b)) = !(a.xor b) := by
  rw [Bool.xor_comm, Bool.not_xor, Bool.xor_comm]

/-- Flipping any input bit flips the XOR output. -/
theorem xorBool_flip (N : Nat) (x : BitString N) (a : Fin N) :
    xorBool N (Function.update x a (!x a)) = !xorBool N x := by
  induction N with
  | zero => exact a.elim0
  | succ n ih =>
    change (Function.update x a (!x a) 0).xor
      (xorBool n (Function.update x a (!x a) ∘ Fin.succ)) =
      !((x 0).xor (xorBool n (x ∘ Fin.succ)))
    by_cases ha : a = 0
    · subst ha
      rw [Function.update_self]
      have htail : Function.update x 0 (!x 0) ∘ Fin.succ = x ∘ Fin.succ := by
        funext i; change Function.update x 0 (!x 0) (Fin.succ i) = x (Fin.succ i)
        exact Function.update_of_ne (Fin.succ_ne_zero i) (!x 0) x
      rw [htail, Bool.not_xor]
    · rw [Function.update_of_ne (Ne.symm ha)]
      have hpos : 0 < a.val := Nat.pos_of_ne_zero (fun h => ha (Fin.ext h))
      set a' : Fin n := ⟨a.val - 1, by omega⟩
      have ha_eq : a = Fin.succ a' := by ext; simp [Fin.succ, a']; omega
      have htail : Function.update x a (!x a) ∘ Fin.succ =
          Function.update (x ∘ Fin.succ) a' (!(x ∘ Fin.succ) a') := by
        conv_lhs => rw [ha_eq]
        exact Function.update_comp_eq_of_injective x (Fin.succ_injective n) a' (!x a'.succ)
      rw [htail, ih _ a', bxor_not_right]

/-- XOR depends on all inputs. -/
theorem xorBool_essential (N : Nat) (a : Fin N) (x : BitString N) :
    xorBool N x ≠ xorBool N (Function.update x a (!x a)) := by
  rw [xorBool_flip]; cases xorBool N x <;> simp

end Schnorr

end CircuitComplexity
