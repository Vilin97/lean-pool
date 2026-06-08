/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Pairwise coprimality
-/


/-- A predicate stating that the given tuple's numbers are pairwise coprime. -/
abbrev PairwiseCoprime {n : ℕ} (a : Fin n → ℤ) : Prop :=
  Pairwise fun i j ↦ IsCoprime (a i) (a j)

open Finset in
lemma gcd_one_of_pairwiseCoprime {n : ℕ} (hn : 2 ≤ n) {a : Fin n → ℤ} (ha : PairwiseCoprime a) :
    univ.gcd a = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨_, (Nat.sub_add_cancel hn).symm⟩
  specialize ha Fin.zero_ne_one
  rw [Int.isCoprime_iff_gcd_eq_one] at ha
  rw [← union_compl {0, 1}, gcd_union, gcd_insert, Finset.gcd, Finset.fold_singleton, ← gcd_assoc,
    ← Int.coe_gcd (a 0), ha, Nat.cast_one, gcd_one_left, gcd_one_left]
