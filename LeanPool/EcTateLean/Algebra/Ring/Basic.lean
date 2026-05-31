/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Common
import Mathlib.Tactic.Contrapose



variable {R : Type _}

theorem add_self_eq_mul_two [Semiring R] (a : R) : a + a = 2 * a := by
  rw [←one_mul a, ←add_mul, one_mul]
  congr
  norm_num

section Ring
--theorem sub_eq_add_neg (a b : R) : a - b = a + -b := Ring.sub_eq_add_neg a b
variable [Ring R]

-- theorem mul_sub (a b c : R) : a * (b - c) = a * b - a * c := by
  -- rw [sub_eq_add_neg, mul_add, ←neg_mul_eq_mul_neg, ←sub_eq_add_neg]

-- theorem sub_mul (a b c : R) : (a - b) * c = a * c - b * c := by
  -- rw [sub_eq_add_neg, add_mul, ←neg_mul_eq_neg_mul, ←sub_eq_add_neg]

-- @[simp] theorem sub_zero (a : R) : a - 0 = a := by
--   rw [sub_eq_add_neg, ←add_zero (-0), add_left_neg (0: R)]
--   simp

-- theorem neg_add (a b : R) : - (a + b) = -a + -b := by
--   have h₁ : - (a + b) = -(a + b) + (a + b) + -a + -b := by
--     rw [add_assoc, add_comm (-a), add_assoc, add_assoc, ← add_assoc b]
--     rw [add_right_neg b, zero_add, add_right_neg a, add_zero]
--   rwa [add_left_neg (a + b), zero_add] at h₁

-- theorem sub_add (a b c : R) : a - (b + c) = a - b - c := by
--   rw [sub_eq_add_neg, neg_add, ←add_assoc, ←sub_eq_add_neg, ←sub_eq_add_neg]

-- theorem sub_add_comm (n m k : R) : n + m - k = n - k + m := by
--   rw [sub_eq_add_neg, add_assoc, add_comm m, ←add_assoc, ←sub_eq_add_neg]

end Ring


section CommRing
variable [CommRing R]


theorem evenpow_neg {n m : ℕ} (a : R) (h : n = 2 * m) : (-a) ^ n = a ^ n := by
  rw [h, pow_mul, pow_mul, neg_sq]

theorem oddpow_neg {n m : ℕ} (a : R) (h : n = 2 * m + 1) : (-a) ^ n = -(a ^ n) := by
  rw [h, pow_succ, evenpow_neg a (show 2 * m = 2 * m by rfl), pow_succ, mul_neg]

end CommRing


section IntegralDomain
variable [CommRing R] [IsDomain R]

-- TODO maybe delete
theorem nzero_mul_left_cancel (a b c : R) : a ≠ 0 → a * b = a * c → b = c := by
  intro a_ne_z ab_eq_ac
  rw [←add_left_inj (-(a * c)), add_neg_cancel (a * c), neg_mul_eq_mul_neg, ←mul_add] at ab_eq_ac
  cases (@mul_eq_zero _ _ _ a (b + -c)).1 ab_eq_ac with
  | inl h => exact False.elim (a_ne_z h)
  | inr h =>
    rw [←add_left_inj (-c), add_neg_cancel c]
    exact h


end IntegralDomain
