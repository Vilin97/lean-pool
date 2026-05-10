/-
Copyright (c) 2026 Math Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Inc.
-/
import LeanPool.Erdos1196.Basic
import Mathlib.Algebra.Order.Floor.Div

/-!
# First-entry row data

This file packages the row-wise data for the first-entry contribution to the normalization
constant. It introduces the threshold selecting admissible first jumps from a parent state `m`,
the resulting tail sum, and the pairwise weights used later in the fiberwise reindexing of
`B_x`.

## Main definitions

* `entryThreshold`
* `firstEntryTail`
* `firstEntryPairWeight`
-/

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

/-- The least threshold satisfying both `q ≥ Y` and `x ≤ m * q`. -/
def entryThreshold (x Y m : ℕ) : ℕ :=
  max Y (x ⌈/⌉ m)

/-- The first-entry tail sum starting from a parent state `m`. -/
noncomputable def firstEntryTail (x Y m : ℕ) : ℝ :=
  ∑' q : ℕ,
    if entryThreshold x Y m ≤ q then
      Λ q / ((q : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)
    else 0

/-- The pairwise weight indexed by a parent state `m` and jump factor `q`
for the first-entry contribution to `B_x`. -/
noncomputable def firstEntryPairWeight (x Y : ℕ) (mq : ℕ × ℕ) : ℝ :=
  if 1 ≤ mq.1 ∧ mq.1 < x ∧ entryThreshold x Y mq.1 ≤ mq.2 then
    Λ mq.2 / (((mq.1 * mq.2 : ℕ) : ℝ) * (Real.log ((mq.1 * mq.2 : ℕ) : ℝ)) ^ 2)
  else 0

/-- The lower-threshold condition is exactly the conjunction `q ≥ Y` and `x ≤ m * q`. -/
lemma entryThreshold_le_iff (x Y m q : ℕ) (hm : 0 < m) :
    entryThreshold x Y m ≤ q ↔ Y ≤ q ∧ x ≤ m * q := by
  rw [entryThreshold, max_le_iff]
  constructor
  · rintro ⟨hY, hq⟩
    exact ⟨hY, (ceilDiv_le_iff_le_mul hm).1 hq⟩
  · rintro ⟨hY, hxq⟩
    exact ⟨hY, (ceilDiv_le_iff_le_mul hm).2 hxq⟩

/-- For a parent state already known to satisfy `1 ≤ m < x`, the pairwise first-entry weight is
the corresponding scaled tail summand. -/
lemma firstEntryPairWeight_eq {x Y m q : ℕ} (hm1 : 1 ≤ m) (hmx : m < x) :
    firstEntryPairWeight x Y (m, q) =
      (1 / (m : ℝ)) *
        (if entryThreshold x Y m ≤ q then
          Λ q / ((q : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)
        else 0) := by
  by_cases hq : entryThreshold x Y m ≤ q
  · rw [firstEntryPairWeight, if_pos ⟨hm1, hmx, hq⟩, if_pos hq]
    rw [Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv]
    ring_nf
  · rw [firstEntryPairWeight, if_neg, if_neg hq]
    · simp
    · exact fun h => hq h.2.2

/-- For a fixed parent state `m`, the first-entry row is either the scaled tail summand row when
`1 ≤ m < x`, or identically zero otherwise. -/
lemma firstEntryPairWeight_row (x Y m : ℕ) :
    (fun q : ℕ => firstEntryPairWeight x Y (m, q)) =
      if 1 ≤ m ∧ m < x then
        fun q : ℕ =>
          (1 / (m : ℝ)) *
            (if entryThreshold x Y m ≤ q then
              Λ q / ((q : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)
            else 0)
      else fun _ : ℕ => 0 := by
  by_cases hm : 1 ≤ m ∧ m < x
  · rcases hm with ⟨hm1, hmx⟩
    funext q
    simp [firstEntryPairWeight_eq (x := x) (Y := Y) (m := m) (q := q) hm1 hmx, hm1, hmx]
  · funext q
    by_cases hm1 : 1 ≤ m
    · have hmx : ¬ m < x := by
        intro hmx
        exact hm ⟨hm1, hmx⟩
      simp [firstEntryPairWeight, hm1, hmx]
    · simp [firstEntryPairWeight, hm1]

end PrimitiveSetsAboveX
