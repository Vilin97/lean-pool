/-
Copyright (c) 2026 Command Master. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Command Master
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Utility lemmas for the Lean Bourgain extractor formalization

A small collection of lemmas used throughout the Bourgain extractor proof:
`exists_eq_card_filter_of_card_le_one`, `min_sq`, and `half_le_floor_of_one_le`.
-/

namespace LeanPool.LeanBourgain

lemma exists_eq_card_filter_of_card_le_one {α : Type*}
    {p : α → Prop} [DecidablePred p] (A : Finset α) (h : (A.filter p).card ≤ 1) :
    (if ∃ a ∈ A, p a then 1 else 0) = (A.filter p).card := by
  split
  · rename_i h2
    obtain ⟨a, ha, pa⟩ := h2
    apply le_antisymm
    · refine Finset.Nonempty.card_pos ?_
      exact ⟨a, by simp [ha, pa]⟩
    · exact h
  · rename_i h2
    rw [Eq.comm, Finset.card_eq_zero]
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    simp only [Finset.mem_filter] at hx
    exact h2 ⟨x, hx.1, hx.2⟩

lemma min_sq (a b : ℚ) (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) : (min a b) ^ 2 = min (a ^ 2) (b ^ 2) := by
  rcases le_or_gt a b with hab | hab
  · rw [min_eq_left hab, min_eq_left (by gcongr)]
  · rw [min_eq_right hab.le, min_eq_right (by gcongr)]

open Real

lemma half_le_floor_of_one_le (a : ℝ) (h : 1 ≤ a) :
    a / 2 ≤ ⌊a⌋₊ := by
  by_cases h' : a < 2
  · calc a / 2
        _ ≤ 1 := by linarith
        _ ≤ (⌊a⌋₊ : ℝ) := by
              have : 1 ≤ ⌊a⌋₊ := Nat.one_le_iff_ne_zero.mpr (by
                intro he
                have := Nat.floor_eq_zero.mp he
                linarith)
              exact_mod_cast this
  · simp only [not_lt] at h'
    calc a / 2
        _ ≤ a - 1 := by linarith
        _ ≤ (⌊a⌋₊ : ℝ) := le_of_lt (Nat.sub_one_lt_floor _)

end LeanPool.LeanBourgain
