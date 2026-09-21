/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanPool.RearrangementNumber.NonMRR.Series
import Mathlib.Algebra.BigOperators.Group.Finset.Preimage

/-!
# Inserting zero terms along an eventually increasing injection

An arbitrary reordering of finitely many initial terms is harmless. Consequently
an injective placement that is increasing beyond a finite index preserves the
natural sum of a series, and inserting zeros preserves failure of absolute
convergence.
-/

open Filter Finset Topology

namespace NonMRR

private theorem eq_range_card_of_downward_closed (s : Finset ℕ)
    (hs : ∀ n ∈ s, ∀ m ≤ n, m ∈ s) : s = range s.card := by
  apply eq_of_subset_of_card_le _ (by simp)
  intro n hn
  apply mem_range.mpr
  have hsub : range (n + 1) ⊆ s := by
    intro m hm
    exact hs n hn m (Nat.le_of_lt_succ (mem_range.mp hm))
  have hcard := card_le_card hsub
  simpa using hcard

/-- The finite set of original indices visited before position `j`. -/
noncomputable def paddingPreimage (t : ℕ → ℕ) (ht : Function.Injective t) (j : ℕ) :
    Finset ℕ := (range j).preimage t ht.injOn

@[simp] theorem mem_paddingPreimage (t : ℕ → ℕ) (ht : Function.Injective t) (j n : ℕ) :
    n ∈ paddingPreimage t ht j ↔ t n < j := by
  simp [paddingPreimage]

theorem eventually_range_subset_paddingPreimage
    (t : ℕ → ℕ) (ht : Function.Injective t) (N : ℕ) :
    ∀ᶠ j in atTop, range N ⊆ paddingPreimage t ht j := by
  apply (eventually_all_finset (range N)).mpr
  intro n _
  simpa using (eventually_gt_atTop (t n))

theorem tendsto_card_paddingPreimage (t : ℕ → ℕ) (ht : Function.Injective t) :
    Tendsto (fun j ↦ (paddingPreimage t ht j).card) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_range_subset_paddingPreimage t ht N] with j hj
  simpa using card_le_card hj

/-- Beyond the finitely many exceptional positions, the original indices already
visited form an initial segment. -/
theorem eventually_paddingPreimage_eq_range
    (t : ℕ → ℕ) (ht : Function.Injective t) (N : ℕ)
    (hmono : ∀ n ≥ N, ∀ m, n < m → t n < t m) :
    ∀ᶠ j in atTop,
      paddingPreimage t ht j = range (paddingPreimage t ht j).card := by
  filter_upwards [eventually_range_subset_paddingPreimage t ht N] with j hj
  apply eq_range_card_of_downward_closed
  intro n hn m hmn
  by_cases hm : m < N
  · exact hj (mem_range.mpr hm)
  · rcases hmn.eq_or_lt with rfl | hmn
    · exact hn
    · apply (mem_paddingPreimage t ht j m).mpr
      exact lt_trans (hmono m (Nat.le_of_not_lt hm) n hmn)
        ((mem_paddingPreimage t ht j n).mp hn)

theorem partialSum_extend_eq_preimage
    (b : ℕ → ℝ) (t : ℕ → ℕ) (ht : Function.Injective t) (j : ℕ) :
    partialSum (Function.extend t b 0) j = ∑ n ∈ paddingPreimage t ht j, b n := by
  simpa only [partialSum, paddingPreimage, ht.extend_apply] using
    (sum_preimage t (range j) ht.injOn (Function.extend t b 0)
      (fun x _ hx ↦ by
        have hx' : ¬ ∃ n, t n = x := hx
        simp [hx'])).symm

/-- Inserting zeros along an eventually increasing injection preserves the natural sum. -/
theorem tendsto_partialSum_extend
    (b : ℕ → ℝ) (t : ℕ → ℕ) (ht : Function.Injective t) (N : ℕ)
    (hmono : ∀ n ≥ N, ∀ m, n < m → t n < t m)
    (s : ℝ) (hb : Tendsto (partialSum b) atTop (𝓝 s)) :
    Tendsto (partialSum (Function.extend t b 0)) atTop (𝓝 s) := by
  have hbase := hb.comp (tendsto_card_paddingPreimage t ht)
  apply hbase.congr'
  filter_upwards [eventually_paddingPreimage_eq_range t ht N hmono] with j hj
  rw [partialSum_extend_eq_preimage b t ht j, hj]
  rfl

/-- Inserting zeros along an injection preserves failure of absolute convergence. -/
theorem not_summable_abs_extend
    (b : ℕ → ℝ) (t : ℕ → ℕ) (ht : Function.Injective t)
    (hb : ¬ Summable (fun n ↦ |b n|)) :
    ¬ Summable (fun n ↦ |Function.extend t b 0 n|) := by
  intro ha
  apply hb
  simpa only [Function.comp_def, ht.extend_apply] using ha.comp_injective ht

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
