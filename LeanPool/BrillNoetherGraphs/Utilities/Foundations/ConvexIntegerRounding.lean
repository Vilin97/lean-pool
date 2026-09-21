/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.CommonOffsetRounding

/-!
# Sampling and rounding a convex integer path

On each block of `N` consecutive edges, the endpoint height difference lies
between `N` times the first and last slopes. Common-offset floor division
therefore gives a coarse edge slope between those same slopes. Consecutive
coarse slopes remain nondecreasing.
-/

namespace Utilities.ConvexIntegerRounding

open Finset CommonOffsetRounding

/-- The forward slope on an integer path. -/
def slope (v : ℕ → ℤ) (i : ℕ) : ℤ := v (i + 1) - v i

/-- Successive slope comparisons give all slope comparisons before `L`. -/
theorem slopes_mono_of_adjacent (v : ℕ → ℤ) (L : ℕ)
    (hStep : ∀ i, i + 1 < L → slope v i ≤ slope v (i + 1)) :
    ∀ a b, a ≤ b → b < L → slope v a ≤ slope v b := by
  intro a b hab
  induction hab with
  | refl => exact fun _ => le_rfl
  | @step b hab ih =>
    intro hb
    exact le_trans (ih (by omega)) (hStep b hb)

/-- Forward slopes telescope along every finite block. -/
theorem sum_slopes (v : ℕ → ℤ) (start count : ℕ) :
    (∑ i ∈ range count, slope v (start + i)) =
      v (start + count) - v start := by
  simpa only [slope, Nat.add_assoc, Nat.add_zero] using
    Finset.sum_range_sub (fun i => v (start + i)) count

/-- A convex block's height difference lies between its length times the
first slope and its length times the last slope. -/
theorem block_difference_bounds (v : ℕ → ℤ) (L : ℕ)
    (hMono : ∀ a b, a ≤ b → b < L → slope v a ≤ slope v b)
    (start count : ℕ) (hCount : 0 < count) (hEnd : start + count ≤ L) :
    (count : ℤ) * slope v start ≤ v (start + count) - v start ∧
      v (start + count) - v start ≤
        (count : ℤ) * slope v (start + count - 1) := by
  constructor
  · calc
      (count : ℤ) * slope v start = ∑ _i ∈ range count, slope v start := by
        simp
      _ ≤ ∑ i ∈ range count, slope v (start + i) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        exact hMono start (start + i) (by omega) (by omega)
      _ = v (start + count) - v start := sum_slopes v start count
  · calc
      v (start + count) - v start =
          ∑ i ∈ range count, slope v (start + i) := (sum_slopes v start count).symm
      _ ≤ ∑ _i ∈ range count, slope v (start + count - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        exact hMono (start + i) (start + count - 1) (by omega) (by omega)
      _ = (count : ℤ) * slope v (start + count - 1) := by simp

/-- Rounding the endpoints of a convex length-`N` block gives a slope
between the first and last source slopes. -/
theorem rounded_block_slope_bounds (N : ℕ) (hN : 0 < N) (k : Fin N)
    (v : ℕ → ℤ) (L : ℕ)
    (hMono : ∀ a b, a ≤ b → b < L → slope v a ≤ slope v b)
    (j : ℕ) (hBlock : N * (j + 1) ≤ L) :
    slope v (N * j) ≤ slope (fun i => round N k (v (N * i))) j ∧
      slope (fun i => round N k (v (N * i))) j ≤
        slope v (N * (j + 1) - 1) := by
  have hEnd : N * j + N ≤ L := by
    simpa only [Nat.mul_add, Nat.mul_one] using hBlock
  obtain ⟨hlower, hupper⟩ := block_difference_bounds v L hMono (N * j) N hN hEnd
  simpa only [slope, Nat.mul_add, Nat.mul_one] using
    round_sub_bounds N hN k (v (N * j)) (v (N * j + N))
      (slope v (N * j)) (slope v (N * j + N - 1)) hlower hupper

/-- Consecutive coarse slopes remain ordered after common-offset rounding
of a convex integer path. -/
theorem rounded_slopes_nondecreasing (N : ℕ) (hN : 0 < N) (k : Fin N)
    (v : ℕ → ℤ) (L : ℕ)
    (hMono : ∀ a b, a ≤ b → b < L → slope v a ≤ slope v b)
    (j : ℕ) (hTwo : N * (j + 2) ≤ L) :
    slope (fun i => round N k (v (N * i))) j ≤
      slope (fun i => round N k (v (N * i))) (j + 1) := by
  have hTwo' : N * j + N + N ≤ L := by
    simpa only [Nat.mul_add, Nat.mul_two, Nat.add_assoc] using hTwo
  have hFirst : N * (j + 1) ≤ L := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hSecond : N * (j + 1 + 1) ≤ L := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hTwo
  have hMiddle : N * (j + 1) < L := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hLeft := (rounded_block_slope_bounds N hN k v L hMono j hFirst).2
  have hRight := (rounded_block_slope_bounds N hN k v L hMono (j + 1) hSecond).1
  exact le_trans hLeft (le_trans
    (hMono _ _ (Nat.sub_le _ _) hMiddle) hRight)

end Utilities.ConvexIntegerRounding
