/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Example.Cover
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# The Hausdorff measure of the graph over an arbitrary set

An open set is the increasing union of the cells it contains; the graph over such a union of
level-`n` cells has Hausdorff measure at most twice its Lebesgue measure by the cell bound, and
the monotone-union limit carries this to the open set.  Outer regularity of Lebesgue measure
then gives `μH[1] (graphMap '' A) ≤ 2 * volume A` for every `A ⊆ ℝ`; in particular the
graph over a Lebesgue-null set is `μH[1]`-null.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LeanPool.Besicovitch.Example

/-- The union of the level-`n` cells contained in `U`. -/
def cellHull (n : ℕ) (U : Set ℝ) : Set ℝ := ⋃ i ∈ {i : ℤ | cell n i ⊆ U}, cell n i

theorem cellHull_subset (n : ℕ) (U : Set ℝ) : cellHull n U ⊆ U := by
  intro x hx
  simp only [cellHull, mem_iUnion, mem_setOf_eq, exists_prop] at hx
  obtain ⟨i, hi, hx⟩ := hx
  exact hi hx

/-- A finer cell meeting a coarser one is contained in it. -/
theorem cell_subset_of_mem {m n : ℕ} (hmn : m ≤ n) {i j : ℤ} {x : ℝ}
    (hx : x ∈ cell n j) (hx' : x ∈ cell m i) : cell n j ⊆ cell m i := by
  intro y hy
  rw [mem_cell_iff] at hx hx' hy ⊢
  rw [← hx']
  exact cellIndex_eq_of_le hmn (hy.trans hx.symm)

theorem cellHull_subset_succ (n : ℕ) (U : Set ℝ) : cellHull n U ⊆ cellHull (n + 1) U := by
  intro x hx
  simp only [cellHull, mem_iUnion, mem_setOf_eq, exists_prop] at hx ⊢
  obtain ⟨i, hi, hx⟩ := hx
  exact ⟨cellIndex (n + 1) x,
    (cell_subset_of_mem (Nat.le_succ n) (mem_cell_cellIndex _ _) hx).trans hi,
    mem_cell_cellIndex _ _⟩

theorem monotone_cellHull (U : Set ℝ) : Monotone fun n ↦ cellHull n U :=
  monotone_nat_of_le_succ fun n ↦ cellHull_subset_succ n U

/-- The cell of `x` lies within `cellLength n` of `x`. -/
theorem cell_subset_ball (n : ℕ) (x : ℝ) :
    cell n (cellIndex n x) ⊆ Metric.ball x (cellLength n) := by
  intro y hy
  have hx := mem_cell_cellIndex n x
  simp only [cell, mem_Ico] at hx hy
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem iUnion_cellHull_of_isOpen {U : Set ℝ} (hU : IsOpen U) : ⋃ n, cellHull n U = U := by
  refine subset_antisymm (iUnion_subset fun n ↦ cellHull_subset n U) fun x hx ↦ ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨n, hn⟩ := (tendsto_cellLength.eventually (gt_mem_nhds hε)).exists
  refine mem_iUnion.mpr ⟨n, ?_⟩
  simp only [cellHull, mem_iUnion, mem_setOf_eq, exists_prop]
  exact ⟨cellIndex n x,
    (cell_subset_ball n x).trans ((Metric.ball_subset_ball hn.le).trans hball),
    mem_cell_cellIndex n x⟩

theorem volume_cellHull (n : ℕ) (U : Set ℝ) :
    volume (cellHull n U) = ∑' i : {i : ℤ // cell n i ⊆ U}, volume (cell n i) := by
  unfold cellHull
  refine measure_biUnion (Set.to_countable _) ?_ fun i _ ↦ measurableSet_Ico
  intro i _ j _ hij
  exact cell_disjoint hij

/-- The graph over a level-`n ≥ 1` cell has Hausdorff measure at most twice the cell's length. -/
theorem hausdorffMeasure_graphMap_image_cell_le {n : ℕ} (i : ℤ) :
    μH[1] (graphMap '' cell n i) ≤ 2 * volume (cell n i) := by
  have hpos := cellLength_pos n
  have h := hausdorffMeasure_graphMap_image_Ico_le
    (a := i * cellLength n) (b := (i + 1) * cellLength n) (by nlinarith)
  have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (cellLength n) =
      ENNReal.ofReal (2 * cellLength n) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [volume_cell, h2]
  refine h.trans (le_of_eq ?_)
  congr 1; ring

theorem hausdorffMeasure_graphMap_image_cellHull_le (n : ℕ) (U : Set ℝ) :
    μH[1] (graphMap '' cellHull n U) ≤ 2 * volume (cellHull n U) := by
  unfold cellHull
  rw [image_iUnion₂]
  calc μH[1] (⋃ i ∈ {i : ℤ | cell n i ⊆ U}, graphMap '' cell n i)
      ≤ ∑' i : {i : ℤ // cell n i ⊆ U}, μH[1] (graphMap '' cell n i) :=
        measure_biUnion_le _ (Set.to_countable _) _
    _ ≤ ∑' i : {i : ℤ // cell n i ⊆ U}, 2 * volume (cell n i) := by
        gcongr with i; exact hausdorffMeasure_graphMap_image_cell_le _
    _ = 2 * volume (⋃ i ∈ {i : ℤ | cell n i ⊆ U}, cell n i) := by
        rw [ENNReal.tsum_mul_left, ← volume_cellHull]; rfl

/-- **(B≤ on open sets)** -/
theorem hausdorffMeasure_graphMap_image_le_of_isOpen {U : Set ℝ} (hU : IsOpen U) :
    μH[1] (graphMap '' U) ≤ 2 * volume U := by
  have hmono : Monotone fun n ↦ graphMap '' cellHull n U :=
    fun m n hmn ↦ image_mono (monotone_cellHull U hmn)
  have hlim := tendsto_measure_iUnion_atTop (μ := μH[1]) hmono
  rw [← image_iUnion, iUnion_cellHull_of_isOpen hU] at hlim
  refine le_of_tendsto' hlim fun n ↦ ?_
  calc μH[1] (graphMap '' cellHull n U) ≤ 2 * volume (cellHull n U) :=
        hausdorffMeasure_graphMap_image_cellHull_le n U
    _ ≤ 2 * volume U := by gcongr; exact cellHull_subset n U

/-- **(B≤)** The graph over any set has Hausdorff measure at most twice its Lebesgue measure. -/
theorem hausdorffMeasure_graphMap_image_le (A : Set ℝ) :
    μH[1] (graphMap '' A) ≤ 2 * volume A := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hfin ↦ ?_
  have hA : volume A ≠ ∞ := by
    intro h
    rw [h, ENNReal.mul_top (by norm_num)] at hfin
    exact absurd hfin (lt_irrefl _)
  have hε' : (ε : ℝ≥0∞) / 2 ≠ 0 :=
    (ENNReal.div_pos_iff.mpr ⟨(ENNReal.coe_pos.mpr hε).ne', by norm_num⟩).ne'
  have hlt : volume A < volume A + ε / 2 := ENNReal.lt_add_right hA hε'
  obtain ⟨U, hAU, hUopen, hU⟩ := Set.exists_isOpen_lt_of_lt A _ hlt
  calc μH[1] (graphMap '' A) ≤ μH[1] (graphMap '' U) := measure_mono (image_mono hAU)
    _ ≤ 2 * volume U := hausdorffMeasure_graphMap_image_le_of_isOpen hUopen
    _ ≤ 2 * (volume A + ε / 2) := by gcongr
    _ = 2 * volume A + ε := by
        have h2 : (2 : ℝ≥0∞) * ((ε : ℝ≥0∞) / 2) = ε :=
          ENNReal.mul_div_cancel' (by norm_num) (by norm_num)
        rw [mul_add, h2]

/-- The graph over a Lebesgue-null set is `μH[1]`-null. -/
theorem hausdorffMeasure_graphMap_image_eq_zero {A : Set ℝ} (hA : volume A = 0) :
    μH[1] (graphMap '' A) = 0 := by
  have := hausdorffMeasure_graphMap_image_le A
  rw [hA, mul_zero] at this
  exact nonpos_iff_eq_zero.mp this

end LeanPool.Besicovitch.Example
