/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Example.Plane

/-!
# Covering the graph over an interval

The graph over `[a, b)` is covered, at level `n`, by the graphs over the level-`n` cells meeting
`[a, b)`.  There are at most `(b - a) / cellLength n + 2` of them, each of diameter at most
`2 * cellLength n`, so the Hausdorff measure of the graph over `[a, b)` is at most `2 (b - a)`.
The constant `2` is crude but is all that is needed: the sharp value `1` is never used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LeanPool.Besicovitch.Example

/-- The number of level-`n` cells meeting `[a, b)`: from the cell of `a` to the cell of `b`. -/
def cellCount (n : ℕ) (a b : ℝ) : ℕ := (cellIndex n b - cellIndex n a + 1).toNat

theorem cellCount_le (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    (cellCount n a b : ℝ) ≤ (b - a) / cellLength n + 2 := by
  have hpos := cellLength_pos n
  have h1 := Int.floor_le (b / cellLength n)
  have h2 := Int.lt_floor_add_one (a / cellLength n)
  have hdiv : a / cellLength n ≤ b / cellLength n := by gcongr
  have hnn : 0 ≤ cellIndex n b - cellIndex n a + 1 := by
    have : cellIndex n a ≤ cellIndex n b := Int.floor_mono hdiv
    omega
  have hcast : (cellCount n a b : ℝ) = ((cellIndex n b - cellIndex n a + 1 : ℤ) : ℝ) := by
    rw [cellCount, ← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  rw [hcast]
  unfold cellIndex
  push_cast
  rw [sub_div]
  linarith

/-- Every point of `[a, b)` lies in one of the counted cells. -/
theorem exists_cell_of_mem {n : ℕ} {a b x : ℝ} (hx : x ∈ Ico a b) :
    ∃ k : Fin (cellCount n a b), x ∈ cell n (cellIndex n a + k) := by
  have hpos := cellLength_pos n
  have hlo : cellIndex n a ≤ cellIndex n x := Int.floor_mono (by gcongr; exact hx.1)
  have hhi : cellIndex n x ≤ cellIndex n b := Int.floor_mono (by gcongr; exact hx.2.le)
  refine ⟨⟨(cellIndex n x - cellIndex n a).toNat, ?_⟩, ?_⟩
  · unfold cellCount; omega
  · rw [mem_cell_iff]
    simp only
    rw [Int.toNat_of_nonneg (by omega)]
    ring

/-- The graph over `[a, b)` at level `n ≥ 1` is covered by `cellCount` cylinders. -/
theorem graphMap_image_Ico_subset {n : ℕ} (a b : ℝ) :
    graphMap '' Ico a b ⊆
      ⋃ k : Fin (cellCount n a b), graphMap '' cell n (cellIndex n a + k) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨k, hk⟩ := exists_cell_of_mem (n := n) hx
  exact mem_iUnion.mpr ⟨k, mem_image_of_mem _ hk⟩

/-- **(B≤ on intervals)** The graph over `[a, b)` has Hausdorff measure at most `2 (b - a)`. -/
theorem hausdorffMeasure_graphMap_image_Ico_le {a b : ℝ} (hab : a ≤ b) :
    μH[1] (graphMap '' Ico a b) ≤ ENNReal.ofReal (2 * (b - a)) := by
  -- covering at level `n`, with diameters `≤ 2 * cellLength n → 0`
  have hr : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (2 * cellLength n)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    simpa using tendsto_cellLength.const_mul 2
  have key := Measure.hausdorffMeasure_le_liminf_sum 1 (graphMap '' Ico a b)
    (fun n : ℕ ↦ ENNReal.ofReal (2 * cellLength n)) hr
    (fun n (k : Fin (cellCount n a b)) ↦ graphMap '' cell n (cellIndex n a + k))
    ((eventually_ge_atTop 1).mono fun n hn k ↦ diam_graphMap_image_cell_le hn _)
    (Eventually.of_forall fun n ↦ graphMap_image_Ico_subset a b)
  refine key.trans ?_
  -- each level-`n` sum is at most `cellCount * 2 cellLength ≤ 2 (b - a) + 4 cellLength n`
  have hsum : ∀ n : ℕ, 1 ≤ n →
      ∑ k : Fin (cellCount n a b),
        Metric.ediam (graphMap '' cell n (cellIndex n a + k)) ^ (1 : ℝ) ≤
        ENNReal.ofReal (2 * (b - a) + 4 * cellLength n) := by
    intro n hn
    calc ∑ k : Fin (cellCount n a b),
          Metric.ediam (graphMap '' cell n (cellIndex n a + k)) ^ (1 : ℝ)
        ≤ ∑ _k : Fin (cellCount n a b), ENNReal.ofReal (2 * cellLength n) := by
          gcongr with k
          rw [ENNReal.rpow_one]; exact diam_graphMap_image_cell_le hn _
      _ = (cellCount n a b : ℝ≥0∞) * ENNReal.ofReal (2 * cellLength n) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ENNReal.ofReal ((cellCount n a b : ℝ) * (2 * cellLength n)) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (2 * (b - a) + 4 * cellLength n) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hc := cellCount_le n hab
          have hpos := cellLength_pos n
          calc (cellCount n a b : ℝ) * (2 * cellLength n)
              ≤ ((b - a) / cellLength n + 2) * (2 * cellLength n) := by gcongr
            _ = 2 * (b - a) + 4 * cellLength n := by field_simp; ring
  -- and the right-hand sides tend to `2 (b - a)`
  have hlim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (2 * (b - a) + 4 * cellLength n)) atTop
      (𝓝 (ENNReal.ofReal (2 * (b - a)))) := by
    refine ENNReal.tendsto_ofReal ?_
    simpa using (tendsto_cellLength.const_mul 4).const_add (2 * (b - a))
  calc liminf (fun n : ℕ ↦ ∑ k : Fin (cellCount n a b),
        Metric.ediam (graphMap '' cell n (cellIndex n a + k)) ^ (1 : ℝ)) atTop
      ≤ liminf (fun n : ℕ ↦ ENNReal.ofReal (2 * (b - a) + 4 * cellLength n)) atTop :=
        liminf_le_liminf ((eventually_ge_atTop 1).mono hsum)
    _ = ENNReal.ofReal (2 * (b - a)) := hlim.liminf_eq

end LeanPool.Besicovitch.Example
