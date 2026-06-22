/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

import LeanPool.PentagonalNumberTheorem.PowerSeries
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Order.Lemmas

/-!
# LeanPool.PentagonalNumberTheorem.Partition

Imported Lean Pool material for `LeanPool.PentagonalNumberTheorem.Partition`.
-/

theorem two_pentagonal (k : ℤ) : 2 * (k * (3 * k - 1) / 2) = k * (3 * k - 1) := by
  refine Int.two_mul_ediv_two_of_even ?_
  obtain h | h := Int.even_or_odd k
  · exact Even.mul_right h (3 * k - 1)
  · refine Even.mul_left ?_ _
    refine Int.even_sub_one.mpr ?_
    refine Int.not_even_iff_odd.mpr ?_
    refine Odd.mul ?_ h
    decide

theorem pentagonal_nonneg (k : ℤ) : 0 ≤ k * (3 * k - 1) / 2 := by
  suffices 0 ≤ 2 * (k * (3 * k - 1) / 2) by simpa
  rw [two_pentagonal]
  obtain h | h := lt_or_ge 0 k
  · exact mul_nonneg h.le (by linarith)
  · exact mul_nonneg_of_nonpos_of_nonpos h (by linarith)

theorem two_pentagonal_inj {x y : ℤ} (h : x * (3 * x - 1) = y * (3 * y - 1)) : x = y := by
  simp_rw [mul_sub_one] at h
  rw [sub_eq_sub_iff_sub_eq_sub] at h
  rw [mul_left_comm x, mul_left_comm y] at h
  rw [← mul_sub] at h
  rw [mul_self_sub_mul_self] at h
  rw [← mul_assoc] at h
  rw [← sub_eq_zero, ← sub_one_mul] at h
  rw [mul_eq_zero] at h
  obtain h | h := h
  · obtain h' := Int.eq_of_mul_eq_one <| eq_of_sub_eq_zero h
    simp [← h'] at h
  · exact eq_of_sub_eq_zero h

theorem pentagonal_injective : Function.Injective (fun (k : ℤ) ↦ k * (3 * k - 1) / 2) := by
  intro a b h
  have : a * (3 * a - 1) = b * (3 * b - 1) := by
    rw [← two_pentagonal a, ← two_pentagonal b]
    simp [h]
  apply two_pentagonal_inj this

theorem pentagonal_toNat_injective :
    Function.Injective (fun (k : ℤ) ↦ (k * (3 * k - 1) / 2).toNat) := by
  intro a b h
  apply pentagonal_injective
  zify at h
  simpa [pentagonal_nonneg] using h

namespace Nat.Partition

variable (R : Type*) [CommRing R] [TopologicalSpace R] [T2Space R]
open PowerSeries Finset
open scoped PowerSeries.WithPiTopology

theorem hasProd_powerSeriesMk_card_partition [IsTopologicalSemiring R] :
    HasProd (fun i ↦ ∑' j : ℕ, X ^ ((i + 1) * j))
    (PowerSeries.mk fun n ↦ (Fintype.card n.Partition : R)) := by
  convert hasProd_powerSeriesMk_card_restricted R (fun _ ↦ True)
  · rfl
  · simp
  · simp [restricted]

theorem powerSeriesMk_card_partition_mul_tprod_one_sub_pow [Nontrivial R]
    [IsTopologicalRing R] [NoZeroDivisors R] :
    (PowerSeries.mk fun n ↦ (Fintype.card n.Partition : R)) * ∏' i : ℕ, (1 - X ^ (i + 1)) = 1 := by
  rw [← (hasProd_powerSeriesMk_card_partition R).tprod_eq]
  rw [← (hasProd_powerSeriesMk_card_partition R).multipliable.tprod_mul
    (WithPiTopology.multipliable_one_sub_X_pow _)]
  simp [pow_mul, PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero]

/-- The finite set of integers `k` for which the pentagonal number `k * (3 * k - 1) / 2` is
at most `n`. Used to express the pentagonal recurrence for the partition function. -/
noncomputable def kSet (n : ℤ) : Finset ℤ :=
  Finset.Icc (-(((1 + 24 * n).sqrt - 1) / 6)) (((1 + 24 * n).sqrt + 1) / 6)

theorem mem_kSet_iff {n k : ℤ} :
    k ∈ kSet n ↔ k * (3 * k - 1) / 2 ≤ n := by
  obtain hneg | hpos := lt_or_ge n 0
  · trans False
    · simp only [kSet, Finset.mem_Icc, iff_false]
      by_contra! h
      obtain h' := h.1.trans h.2
      have : (1 + 24 * n).toNat = 0 := by
        simp only [Int.toNat_eq_zero]
        linarith
      simp [Int.sqrt, this] at h'
    · simp only [false_iff, not_le]
      exact hneg.trans_le (pentagonal_nonneg k)
  symm
  calc
    k * (3 * k - 1) / 2 ≤ n ↔ 12 * (2 * (k * (3 * k - 1) / 2)) ≤ 24 * n := by
      rw [← mul_assoc]
      norm_num
    _ ↔ 36 * k ^ 2 - 12 * k ≤ 24 * n := by
      rw [two_pentagonal]
      ring_nf
    _ ↔ 36 * k ^ 2 - 12 * k + 1 ≤ 24 * n + 1 := (Int.add_le_add_iff_right 1).symm
    _ ↔ (6 * k - 1) ^ 2 ≤ 1 + 24 * n := by ring_nf
    _ ↔ |6 * k - 1| ≤ (1 + 24 * n).sqrt := (Int.abs_le_sqrt_iff_sq_le (by linarith)).symm
    _ ↔ -(1 + 24 * n).sqrt ≤ 6 * k - 1 ∧ 6 * k - 1 ≤ (1 + 24 * n).sqrt := abs_le
    _ ↔ (-k) * 6 ≤ (1 + 24 * n).sqrt - 1 ∧ k * 6 ≤ (1 + 24 * n).sqrt + 1 := by
      grind
    _ ↔ -k ≤ ((1 + 24 * n).sqrt - 1) / 6 ∧ k ≤ ((1 + 24 * n).sqrt + 1) / 6 := by
      rw [Int.le_ediv_iff_mul_le (by simp)]
      rw [Int.le_ediv_iff_mul_le (by simp)]
    _ ↔ - (((1 + 24 * n).sqrt - 1) / 6) ≤ k ∧ k ≤ ((1 + 24 * n).sqrt + 1) / 6 := by
      grind
    _ ↔ k ∈ kSet n := by
      simp [kSet]


/--
The recurrence relation of (non-distinct) partition function $p(n)$:

$$\sum_{k \in \mathbb{Z}} (-1)^k p(n - k(3k-1)/2) = 0 \quad (n > 0)$$

Note that this is a finite sum, as the term for $k$ outside $n - k(3k-1)/2 ≥ 0$ vanishes.
Here we explicitly restrict the set of $k$.
-/
theorem sum_partition (n : ℕ) (hn : n ≠ 0) :
    ∑ k ∈ kSet n, (Int.negOnePow k) *
    (Fintype.card (Nat.Partition (n - (k * (3 * k - 1) / 2).toNat)) : ℤ) = 0 := by
  convert PowerSeries.ext_iff.mp (powerSeriesMk_card_partition_mul_tprod_one_sub_pow ℤ) n
  · rw [coeff_mul, pentagonalNumberTheorem_intPos_powerSeries]
    conv in fun (_: ℕ × ℕ) ↦ _ =>
      ext _
      rw [(summable_pentagonalRhs_intPos_powerSeries _).map_tsum _
        (WithPiTopology.continuous_coeff _ _)]
    simp_rw [← zsmul_eq_mul]
    refine Finset.sum_of_injOn (fun k ↦ (n - (k * (3 * k - 1) / 2).toNat,
      (k * (3 * k - 1) / 2).toNat)) ?_ ?_ ?_ ?_
    · intro k hk l hl h
      obtain h := (Prod.ext_iff.mp h).2
      simp only at h
      exact pentagonal_toNat_injective h
    · intro k hk
      simp only [mem_coe, mem_antidiagonal]
      rw [Nat.sub_add_cancel ?_]
      suffices k * (3 * k - 1) / 2 ≤ (n : ℤ) by simpa
      rw [← mem_kSet_iff]
      simpa using hk
    · intro i hi hmem
      rw [mem_antidiagonal] at hi
      apply mul_eq_zero_of_right
      convert tsum_zero with k
      suffices i.2 ≠ (k * (3 * k - 1) / 2).toNat by
        change (k.negOnePow : ℤ) • (coeff i.2 (X ^ (k * (3 * k - 1) / 2).toNat : ℤ⟦X⟧)) = 0
        simp [coeff_X_pow, this]
      contrapose! hmem with hi2
      simp_rw [Set.mem_image, mem_coe]
      refine ⟨k, mem_kSet_iff.mpr ?_, ?_⟩
      · rw [← hi, hi2]
        simp [pentagonal_nonneg]
      · simp [← hi, ← hi2]
    · intro k hk
      rw [tsum_eq_single k ?_]
      · change (k.negOnePow : ℤ) * _ =
          _ * ((k.negOnePow : ℤ) • coeff _ (X ^ (k * (3 * k - 1) / 2).toNat : ℤ⟦X⟧))
        simp [mul_comm (k.negOnePow : ℤ)]
      intro i h
      change ((i.negOnePow : ℤ) • coeff _ (X ^ (i * (3 * i - 1) / 2).toNat : ℤ⟦X⟧)) = 0
      simpa [coeff_X_pow] using pentagonal_toNat_injective.eq_iff.ne.mpr h.symm
  · simp [hn]

end Nat.Partition
