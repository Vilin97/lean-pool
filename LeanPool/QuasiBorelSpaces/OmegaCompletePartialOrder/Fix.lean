/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.Order.OmegaCompletePartialOrder
import LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Basic

/-!
# LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Fix

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Fix`.
-/


namespace OmegaCompletePartialOrder

variable {α : Type*} [OmegaCompletePartialOrder α]

lemma iterate_le_succ (f : α →𝒄 α) (x : α) (hx : x ≤ f x) (n : ℕ) :
    Nat.iterate f n x ≤ Nat.iterate f (n + 1) x := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ']
    rw [Function.iterate_succ']
    exact f.monotone ih

namespace Chain

/-- the sequence of iterates of a function -/
def iterate (f : α →𝒄 α) (x : α) (hx : x ≤ f x) : Chain α where
  toFun n := Nat.iterate f n x
  monotone' := by
    intro n m hnm
    induction hnm with
    | refl => exact le_rfl
    | step _ ih =>
      apply le_trans ih
      apply iterate_le_succ f x hx

@[simp]
lemma iterate_apply (f : α →𝒄 α) (x : α) (hx : x ≤ f x) (n : ℕ) :
    iterate f x hx n = Nat.iterate f n x := by
  rfl

end Chain

/-- the fixed point of a continuous function -/
def fix [OrderBot α] (f : α →𝒄 α) : α :=
  ωSup (Chain.iterate f ⊥ bot_le)

lemma fix_eq [OrderBot α] (f : α →𝒄 α) : fix f = f (fix f) := by
  rw [fix]
  conv_rhs =>
    change f.toFun (ωSup (Chain.iterate f ⊥ bot_le))
    rw [f.map_ωSup' (Chain.iterate f ⊥ bot_le)]
  apply le_antisymm
  · apply ωSup_le_ωSup_of_le
    intro n
    exists n
    simp only [Chain.iterate_apply, Chain.coe_map, Function.comp_apply]
    calc
      (⇑f)^[n] ⊥ ≤ (⇑f)^[n + 1] ⊥ := iterate_le_succ f ⊥ bot_le n
      _ = f ((⇑f)^[n] ⊥) := by
        change ((⇑f)^[n] ∘ ⇑f) ⊥ = (⇑f ∘ (⇑f)^[n]) ⊥
        rw [← Function.iterate_succ]
        rw [Function.iterate_succ']
  · apply ωSup_le_ωSup_of_le
    intro n
    exists n + 1
    simp only [Chain.iterate_apply, Chain.coe_map, Function.comp_apply]
    rw [Function.iterate_succ']
    exact le_rfl

end OmegaCompletePartialOrder
