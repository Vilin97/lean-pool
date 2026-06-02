/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Common

/-!
# LeanPool.EcTateLean.Init.Data.Int.Lemmas

Imported Lean Pool material for `LeanPool.EcTateLean.Init.Data.Int.Lemmas`.
-/

lemma mod_neg_right (m k : Int) : m % (-k) = m % k := by simp
-- lemma div_neg_left (m k : Int) : (-m) / k = -(m / k) := by simp
lemma div_neg_right (m k : Int) : m / (-k) = -(m / k) := by simp


namespace Int

@[simp] lemma ofNat_zero_eq_zero : ofNat Nat.zero = 0 :=
rfl

end Int
