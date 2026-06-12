/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib.Data.Int.Order.Basic

/-!
# Lemmas on `Int.natAbs`
-/


lemma Int.sub_le_add_natAbs {a b : ℤ} : a.natAbs - b.natAbs ≤ (a + b).natAbs := by lia

lemma Int.natAbs_add_of_mul_nonneg {a b : ℤ} (h : 0 ≤ a * b) :
    (a + b).natAbs = a.natAbs + b.natAbs := by
  obtain h | h := Int.mul_nonneg_iff.mp h
  · exact Int.natAbs_add_of_nonneg h.1 h.2
  · exact Int.natAbs_add_of_nonpos h.1 h.2
