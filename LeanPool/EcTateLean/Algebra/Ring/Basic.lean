/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Common
import Mathlib.Tactic.Contrapose

/-!
# LeanPool.EcTateLean.Algebra.Ring.Basic

Imported Lean Pool material for `LeanPool.EcTateLean.Algebra.Ring.Basic`.
-/



variable {R : Type _}

theorem add_self_eq_mul_two [Semiring R] (a : R) : a + a = 2 * a := (two_mul a).symm

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
theorem nzero_mul_left_cancel (a b c : R) : a ≠ 0 → a * b = a * c → b = c :=
  fun h => mul_left_cancel₀ h


end IntegralDomain
