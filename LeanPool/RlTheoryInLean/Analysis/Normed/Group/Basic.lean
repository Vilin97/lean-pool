/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.Ring.Basic

/-!
# LeanPool.RlTheoryInLean.Analysis.Normed.Group.Basic
-/

variable {E : Type*} [SeminormedAddGroup E]

lemma norm_add_sq_le_norm_sq_add_norm_sq (x y : E) :
  ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have h2 : (‖x‖ + ‖y‖) ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := add_sq_le
  calc ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := sq_le_sq' (by linarith [norm_nonneg (x + y)]) h1
    _ ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := h2
    _ = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by ring
