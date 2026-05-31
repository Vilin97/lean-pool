/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/

import Init.Data.Nat.Lemmas

namespace Nat

/-- The maximum of three natural numbers, `max (max a b) c`. -/
def max₃ (a b c : Nat) : Nat :=
  max (max a b) c

theorem max₃_mul_distrib_left (a b c d : Nat) : a * max₃ b c d = max₃ (a * b) (a * c) (a * d) := by
  rw [max₃, max₃, Nat.mul_max_mul_left, Nat.mul_max_mul_left]

theorem max₃_add_distrib_left (a b c d : Nat) : d + max₃ a b c = max₃ (d + a) (d + b) (d + c) := by
  rw [max₃, max₃, Nat.add_max_add_left, Nat.add_max_add_left]

theorem max₃_add_distrib_right (a b c d : Nat) : max₃ a b c + d = max₃ (a + d) (b + d) (c + d) := by
  rw [max₃, max₃, Nat.add_max_add_right, Nat.add_max_add_right]

theorem le_max₃_left (a b c : Nat) : a ≤ max₃ a b c :=
  Nat.le_trans (Nat.le_max_left a b) (Nat.le_max_left _ _)

theorem le_max₃_middle (a b c : Nat) : b ≤ max₃ a b c :=
  Nat.le_trans (Nat.le_max_right a b) (Nat.le_max_left _ _)

theorem le_max₃_right (a b c : Nat) : c ≤ max₃ a b c :=
  Nat.le_max_right _ c

theorem max₃_lt {a b c d : Nat} : max₃ a b c < d ↔ a < d ∧ b < d ∧ c < d := by
  rw [max₃, Nat.max_lt, Nat.max_lt, and_assoc]

theorem max₃_le {a b c d : Nat} : max₃ a b c ≤ d ↔ a ≤ d ∧ b ≤ d ∧ c ≤ d := by
  rw [max₃, Nat.max_le, Nat.max_le, and_assoc]

end Nat
