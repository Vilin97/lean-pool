/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.Sensitivity.Defs

/-!
# Elementary Properties of Sensitivity

Basic bounds and symmetries for the sensitivity of Boolean functions.

## Main results

* `LeanPoolSensitivity.BoolFun.localSensitivity_not` — taking the negation of
  a Boolean function preserves local sensitivity.
* `LeanPoolSensitivity.BoolFun.sensitivity_not` — and likewise sensitivity.
* `LeanPoolSensitivity.BoolFun.localSensitivity_le` — local sensitivity at
  any input is at most `n`.
* `LeanPoolSensitivity.BoolFun.sensitiveAt_flipBit` — the sensitivity
  predicate is invariant under flipping the same coordinate at the input.
-/

namespace LeanPoolSensitivity

variable {n : ℕ}

namespace BoolFun

/-- The local sensitivity of the negation of `f` equals the local sensitivity
of `f`. -/
theorem localSensitivity_not (f : BoolFun n) (x : Fin n → Bool) :
    BoolFun.localSensitivity (fun y => !f y) x = f.localSensitivity x := by
  simp [localSensitivity, sensitiveAt]

/-- The sensitivity of the negation of `f` equals the sensitivity of `f`. -/
theorem sensitivity_not (f : BoolFun n) :
    BoolFun.sensitivity (fun y => !f y) = f.sensitivity := by
  simp [sensitivity, f.localSensitivity_not]

/-- The local sensitivity of `f` at any input `x` is at most `n`. -/
theorem localSensitivity_le (f : BoolFun n) (x : Fin n → Bool) :
    f.localSensitivity x ≤ n := by
  unfold localSensitivity
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- Unfolding lemma: `f` is sensitive at `x` in coordinate `i` iff flipping
that coordinate changes the value of `f`. -/
theorem sensitiveAt_iff (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) :
    f.sensitiveAt x i ↔ f (flipBit x i) ≠ f x :=
  Iff.rfl

/-- Sensitivity at `x` is symmetric in the following sense: `f` is sensitive
at `x` in direction `i` iff `f` is sensitive at `flipBit x i` in direction
`i`. -/
theorem sensitiveAt_flipBit (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) :
    f.sensitiveAt (flipBit x i) i ↔ f.sensitiveAt x i := by
  simp [sensitiveAt, flipBit_flipBit_same, eq_comm]

end BoolFun

end LeanPoolSensitivity
