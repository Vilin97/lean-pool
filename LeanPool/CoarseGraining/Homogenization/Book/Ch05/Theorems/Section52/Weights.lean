/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.ScalarAlgebra

/-! # Weights -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section
/-!
# Section 5.2 internals: Weights

Large-scale weights and finite/tail decompositions.
-/

/--
The large scales appearing after the Section 5.2 Jensen split.

For a cube `cu_m`, a `q = 1` series index `l < m` corresponds to the absolute
scale `m - l`, hence to one of the manuscript large scales `1, ..., m`.
-/
def section52LargeScaleSet (m : ℕ) : Finset ℤ :=
  (Finset.range m).image fun l : ℕ => (m : ℤ) - (l : ℤ)

/-- The `q = 1` geometric weight transported from series depth to absolute scale. -/
noncomputable def section52LargeScaleWeight (s : ℝ) (m : ℕ) (n : ℤ) : ℝ :=
  geometricWeight s 1 (Int.toNat ((m : ℤ) - n))

theorem section52LargeScaleSet_mem_nonneg {m : ℕ} {n : ℤ}
    (hn : n ∈ section52LargeScaleSet m) :
    0 ≤ n := by
  rcases Finset.mem_image.mp hn with ⟨l, hl, rfl⟩
  have hl_le : l ≤ m := Nat.le_of_lt (Finset.mem_range.mp hl)
  omega

theorem section52LargeScaleSet_mem_pos {m : ℕ} {n : ℤ}
    (hn : n ∈ section52LargeScaleSet m) :
    1 ≤ n := by
  rcases Finset.mem_image.mp hn with ⟨l, hl, rfl⟩
  have hl_lt : l < m := Finset.mem_range.mp hl
  omega

theorem section52LargeScaleSet_mem_le_m {m : ℕ} {n : ℤ}
    (hn : n ∈ section52LargeScaleSet m) :
    n ≤ (m : ℤ) := by
  rcases Finset.mem_image.mp hn with ⟨l, _hl, rfl⟩
  omega

theorem section52LargeScaleWeight_nonneg {s : ℝ} (m : ℕ)
    (hs : 0 ≤ s) (n : ℤ) :
    0 ≤ section52LargeScaleWeight s m n := by
  exact geometricWeight_nonneg _ (by simpa using hs)

theorem section52LargeScaleSet_injOn (m : ℕ) :
    Set.InjOn (fun l : ℕ => (m : ℤ) - (l : ℤ)) (↑(Finset.range m) : Set ℕ) := by
  intro l _hl k _hk h
  have hcast : (l : ℤ) = (k : ℤ) := by linarith
  exact Int.ofNat.inj hcast

theorem section52LargeScaleWeight_sum_eq_prefix_sum (s : ℝ) (m : ℕ) :
    (∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n) =
      ∑ l ∈ Finset.range m, geometricWeight s 1 l := by
  classical
  change (section52LargeScaleSet m).sum (section52LargeScaleWeight s m) =
    ∑ l ∈ Finset.range m, geometricWeight s 1 l
  unfold section52LargeScaleSet
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl ?_
    intro l _hl
    have htoNat : Int.toNat ((m : ℤ) - ((m : ℤ) - (l : ℤ))) = l := by
      have hdiff : (m : ℤ) - ((m : ℤ) - (l : ℤ)) = (l : ℤ) := by ring
      simp [hdiff]
    rw [section52LargeScaleWeight, htoNat]
  · exact section52LargeScaleSet_injOn m

theorem section52LargeScaleWeight_sum_le_one {s : ℝ} (hs : 0 < s) (m : ℕ) :
    (∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n) ≤ 1 := by
  rw [section52LargeScaleWeight_sum_eq_prefix_sum]
  calc
    (∑ l ∈ Finset.range m, geometricWeight s 1 l) ≤
        ∑' l : ℕ, geometricWeight s 1 l :=
          (summable_geometricWeight_one hs).sum_le_tsum (Finset.range m)
            (fun l _hl => geometricWeight_nonneg l (by simpa using hs.le))
    _ = 1 := tsum_geometricWeight_one_eq_one hs

/-- Reindex a finite `q = 1` depth-prefix sum as a sum over large absolute scales. -/
theorem section52LargeScaleSet_weighted_sum_eq_prefix_sum
    (s : ℝ) (m : ℕ) (F : ℤ → ℝ) :
    (∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n * F n) =
      ∑ l ∈ Finset.range m,
        geometricWeight s 1 l * F ((m : ℤ) - (l : ℤ)) := by
  classical
  unfold section52LargeScaleSet
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl ?_
    intro l _hl
    simp [section52LargeScaleWeight]
  · exact section52LargeScaleSet_injOn m

/--
Exact large/small split of a `q = 1` depth-indexed weighted series.

The first term is the finite manuscript large-scale sum over absolute scales
`1, ..., m`; the second term is the small-scale tail beginning at series depth
`m`.
-/
theorem section52_tsum_weighted_scale_function_eq_largeScaleSet_sum_add_tail
    (s : ℝ) (m : ℕ) (F : ℤ → ℝ)
    (hsum :
      Summable (fun l : ℕ =>
        geometricWeight s 1 l * F ((m : ℤ) - (l : ℤ)))) :
    (∑' l : ℕ, geometricWeight s 1 l * F ((m : ℤ) - (l : ℤ))) =
      (∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n * F n) +
        ∑' l : ℕ,
          geometricWeight s 1 (l + m) *
            F ((m : ℤ) - ((l + m : ℕ) : ℤ)) := by
  let f : ℕ → ℝ := fun l =>
    geometricWeight s 1 l * F ((m : ℤ) - (l : ℤ))
  have hsplit :
      (∑ l ∈ Finset.range m, f l) + ∑' l : ℕ, f (l + m) =
        ∑' l : ℕ, f l := by
    simpa [f] using hsum.sum_add_tsum_nat_add m
  calc
    (∑' l : ℕ, geometricWeight s 1 l * F ((m : ℤ) - (l : ℤ))) =
        (∑ l ∈ Finset.range m,
            geometricWeight s 1 l * F ((m : ℤ) - (l : ℤ))) +
          ∑' l : ℕ,
            geometricWeight s 1 (l + m) *
              F ((m : ℤ) - ((l + m : ℕ) : ℤ)) := by
          simpa [f] using hsplit.symm
      _ =
          (∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n * F n) +
            ∑' l : ℕ,
              geometricWeight s 1 (l + m) *
                F ((m : ℤ) - ((l + m : ℕ) : ℤ)) := by
            congr 1
            exact (section52LargeScaleSet_weighted_sum_eq_prefix_sum s m F).symm

noncomputable def section52SmallTailWeight (s : ℝ) (m : ℕ) : ℝ :=
  ∑' j : ℕ, geometricWeight s 1 (j + m)

theorem section52SmallTailWeight_nonneg {s : ℝ} (hs : 0 ≤ s) (m : ℕ) :
    0 ≤ section52SmallTailWeight s m := by
  unfold section52SmallTailWeight
  exact tsum_nonneg fun j => geometricWeight_nonneg (j + m) (by simpa using hs)

theorem section52LargeScaleWeight_sum_add_smallTailWeight_eq_one
    {s : ℝ} (hs : 0 < s) (m : ℕ) :
    (∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n) +
        section52SmallTailWeight s m = 1 := by
  let F : ℤ → ℝ := fun _ => 1
  have hsum :
      Summable (fun l : ℕ =>
        geometricWeight s 1 l * F ((m : ℤ) - (l : ℤ))) := by
    simpa [F] using summable_geometricWeight_one hs
  have hsplit :=
    section52_tsum_weighted_scale_function_eq_largeScaleSet_sum_add_tail
      s m F hsum
  have hleft :
      (∑' l : ℕ, geometricWeight s 1 l * F ((m : ℤ) - (l : ℤ))) = 1 := by
    simpa [F] using tsum_geometricWeight_one_eq_one hs
  have htail :
      (∑' l : ℕ,
          geometricWeight s 1 (l + m) *
            F ((m : ℤ) - ((l + m : ℕ) : ℤ))) =
        section52SmallTailWeight s m := by
    simp [section52SmallTailWeight, F]
  have h := hsplit
  rw [hleft, htail] at h
  simpa [F] using h.symm

theorem section52SmallTailWeight_pos {s : ℝ} (hs : 0 < s) (m : ℕ) :
    0 < section52SmallTailWeight s m := by
  have hsum_total := section52LargeScaleWeight_sum_add_smallTailWeight_eq_one hs m
  have hprefix_succ_le_one :
      (∑ l ∈ Finset.range (m + 1), geometricWeight s 1 l) ≤ 1 :=
    calc
      (∑ l ∈ Finset.range (m + 1), geometricWeight s 1 l) ≤
          ∑' l : ℕ, geometricWeight s 1 l :=
        (summable_geometricWeight_one hs).sum_le_tsum (Finset.range (m + 1))
          (fun l _hl => geometricWeight_nonneg l (by simpa using hs.le))
      _ = 1 := tsum_geometricWeight_one_eq_one hs
  have hlast_pos : 0 < geometricWeight s 1 m :=
    geometricWeight_pos m (by simpa using hs)
  have hprefix_succ_eq :
      (∑ l ∈ Finset.range (m + 1), geometricWeight s 1 l) =
        (∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n) +
          geometricWeight s 1 m := by
    rw [Finset.sum_range_succ]
    rw [← section52LargeScaleWeight_sum_eq_prefix_sum]
  have hW_lt_one :
      (∑ n ∈ section52LargeScaleSet m, section52LargeScaleWeight s m n) < 1 := by
    linarith
  linarith

end

end Section52
end Ch05
end Book
end Homogenization
