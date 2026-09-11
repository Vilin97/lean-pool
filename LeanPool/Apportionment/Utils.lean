/-
Copyright (c) 2026 Michał Dobranowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Dobranowski
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Lift
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Measurability
public import Mathlib.Tactic.Abel

/-!
# Utils

Utility lemmas for the Apportionment library: a positivity criterion for the sum of a
vector of natural numbers, and a closed form for the sum of a length-four vector.
-/

@[expose] public section

/-- A vector of natural numbers has positive sum iff at least one component is positive. -/
lemma sum_pos_iff_exists_pos {n : ℕ} {v : Vector ℕ n} :
    0 < v.sum ↔ ∃ i : Fin n, 0 < v[i] := by
  constructor
  · contrapose!
    intro h_nonpos
    rw [nonpos_iff_eq_zero]
    unfold Vector.sum
    rw [← Array.sum_toList]
    apply List.sum_eq_zero_iff.mpr
    intro x hx
    obtain ⟨i, hi⟩ : ∃ i : Fin n, x = v[i] := by
      apply List.mem_iff_get.mp hx |> fun ⟨i, hi⟩ => ⟨⟨i, by grind⟩, by simp [← hi]⟩
    exact hi.trans (nonpos_iff_eq_zero.mp (h_nonpos i))
  · intro ⟨i, hi⟩
    refine lt_of_lt_of_le hi ?_
    unfold Vector.sum
    rw [← Array.sum_toList]
    exact List.le_sum_of_mem (by simp)

/-- The sum of a length-4 vector equals the sum of its components. -/
lemma Vector.sum_four (v : Vector ℕ 4) : v.sum = v[0] + v[1] + v[2] + v[3] := by
  have h : v.toArray = #[v[0], v[1], v[2], v[3]] := by grind
  simp [Vector.sum, h, Array.sum]
  abel
