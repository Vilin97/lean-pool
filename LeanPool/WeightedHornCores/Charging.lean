/-
Copyright (c) 2026 Weighted Horn Cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weighted Horn Cores contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite clock charging

A predicate that ceases to hold within `d` steps of its first occurrence holds at most `d`
times. Exchanging the time and clause sums turns such occurrence counts into a weighted budget.
-/

@[expose] public section

namespace WeightedHornCores

open scoped BigOperators

/-- If an occurrence rules out all occurrences at least `d` steps later, there are at most
`d` occurrences in the observation window. -/
theorem card_le_of_close {t d : ℕ} {P : ℕ → Prop} [DecidablePred P]
    (hclose : ∀ i ∈ Finset.range t, P i → ∀ j ∈ Finset.range t, i + d ≤ j → ¬ P j) :
    ((Finset.range t).filter P).card ≤ d := by
  let s := (Finset.range t).filter P
  change s.card ≤ d
  rcases s.eq_empty_or_nonempty with he | hs
  · simp [he]
  · let i := s.min' hs
    have hi : i ∈ Finset.range t ∧ P i := Finset.mem_filter.mp (s.min'_mem hs)
    have hsub : s ⊆ Finset.Ico i (i + d) := by
      intro j hj
      obtain ⟨hjt, hPj⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_Ico.mpr ⟨s.min'_le j hj,
        lt_of_not_ge fun h => hclose i hi.1 hi.2 j hjt h hPj⟩
    simpa [Nat.card_Ico] using Finset.card_le_card hsub

/-- If every time step charges at least `τ`, and each clause `c` is charged at most `cost c`
times, the total weighted budget pays for all `T` steps. -/
theorem weighted_clock_bound {ι : Type*} (F : Finset ι) (w : ι → ℝ) (cost : ι → ℕ)
    (bad : ℕ → ι → Prop) [∀ t c, Decidable (bad t c)] (T : ℕ) (τ : ℝ)
    (hw : ∀ c ∈ F, 0 ≤ w c)
    (hgap : ∀ t ∈ Finset.range T, τ ≤ ∑ c ∈ F, if bad t c then w c else 0)
    (hcount : ∀ c ∈ F, ((Finset.range T).filter (fun t => bad t c)).card ≤ cost c) :
    (T : ℝ) * τ ≤ ∑ c ∈ F, (cost c : ℝ) * w c := by
  calc
    (T : ℝ) * τ = ∑ _t ∈ Finset.range T, τ := by simp [nsmul_eq_mul]
    _ ≤ ∑ t ∈ Finset.range T, ∑ c ∈ F, if bad t c then w c else 0 := Finset.sum_le_sum hgap
    _ = ∑ c ∈ F, ∑ t ∈ Finset.range T, if bad t c then w c else 0 := Finset.sum_comm
    _ ≤ ∑ c ∈ F, (cost c : ℝ) * w c := by
      refine Finset.sum_le_sum fun c hc => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcount c hc)) (hw c hc)

end WeightedHornCores
