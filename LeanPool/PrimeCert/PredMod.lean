/-
Copyright (c) 2026 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Bhavik Mehta
-/

/-! # Efficient computation of `(a - 1) % N`

`predModKR` computes `(a + (N - 1)) % N` using `Nat.rec` so the kernel can reduce it
via `eagerReduce`, avoiding the overhead of general modular arithmetic.
-/

/-- Kernel-reducible predecessor mod: computes `(a + (N - 1)) % N` for `a ≤ N`. -/
def predModKR (a N : Nat) : Nat :=
  a.rec N.pred fun a _ ↦ a

theorem predModKR_eq {a N : Nat} (hn : N ≠ 0) (ha : a ≤ N) :
    predModKR a N = (a + (N - 1)) % N := by
  delta predModKR
  cases a with
  | zero => rw [Nat.zero_add, Nat.mod_eq_of_lt (by grind)]; rfl
  | succ a =>
    rw [Nat.add_assoc, ← Nat.succ_eq_one_add, ← Nat.pred_eq_sub_one, Nat.succ_pred hn,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by grind), ← Nat.succ_eq_add_one]
