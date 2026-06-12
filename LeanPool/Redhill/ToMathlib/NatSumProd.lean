/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Ring.Nat

/-!
# Lemmas on when sums of natural numbers are less than their products

These are used when proving the subsum condition in the odd case.
-/


namespace Nat

lemma sum_le_prod {ι : Type*} {s : Finset ι} {f : ι → ℕ} (hf : ∀ i ∈ s, 2 ≤ f i) :
    ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    simp_rw [Finset.mem_insert, forall_eq_or_imp] at hf
    refine (Nat.add_le_add_left (ih hf.2) _).trans (Nat.add_le_mul hf.1 ?_)
    obtain ⟨b, hb⟩ := hs
    refine (hf.2 _ hb).trans (Finset.single_le_prod' (fun j mj ↦ ?_) hb)
    exact one_le_two.trans (hf.2 _ mj)

/-- The sum of three natural numbers is strictly less than their product
if they are lower-bounded by 3, 3, 1 respectively. -/
lemma add3_lt_mul3 {a b c : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 1 ≤ c) : a + b + c < a * b * c := by
  induction a, ha using le_induction <;> induction b, hb using le_induction <;> lia

end Nat
