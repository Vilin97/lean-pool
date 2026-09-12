/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Example.Graph
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Besicovitch's set in the plane

The graph `Π = {(x, g x) : x ∈ [0, 1]}` of Besicovitch's function, as a subset of
`EuclideanSpace ℝ (Fin 2)`, together with the elementary metric facts used later: the distance
formula on the graph, the first-coordinate projection is `1`-Lipschitz (so the Hausdorff measure
of a piece of the graph is at least the Lebesgue measure of its base), and the graph over a
level-`n` cell has diameter at most twice the cell length.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LeanPool.Besicovitch.Example

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The graph map `x ↦ (x, g x)`. -/
def graphMap (x : ℝ) : Plane := !₂[x, besicovitchFun x]

/-- Besicovitch's set: the graph of `g` over `[0, 1]`. -/
def besicovitchSet : Set Plane := graphMap '' Icc 0 1

@[simp] theorem graphMap_apply_zero (x : ℝ) : graphMap x 0 = x := by simp [graphMap]

@[simp] theorem graphMap_apply_one (x : ℝ) : graphMap x 1 = besicovitchFun x := by simp [graphMap]

theorem graphMap_injective : Function.Injective graphMap := fun x y h ↦ by
  simpa using congrArg (· 0) h

/-- The distance between two points of the graph. -/
theorem dist_graphMap (x y : ℝ) :
    dist (graphMap x) (graphMap y) =
      √((x - y) ^ 2 + (besicovitchFun x - besicovitchFun y) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- The first coordinate is `1`-Lipschitz. -/
theorem lipschitzWith_proj : LipschitzWith 1 (fun p : Plane ↦ p 0) := by
  refine LipschitzWith.of_dist_le_mul fun p q ↦ ?_
  rw [EuclideanSpace.dist_eq, NNReal.coe_one, one_mul, Real.dist_eq]
  simp only [Fin.sum_univ_two]
  rw [Real.le_sqrt (abs_nonneg _) (by positivity), sq_abs, Real.dist_eq, Real.dist_eq,
    sq_abs, sq_abs]
  nlinarith [sq_nonneg (p 1 - q 1)]

/-- The first coordinate recovers the base of a piece of the graph. -/
theorem proj_image_graphMap_image (A : Set ℝ) :
    (fun p : Plane ↦ p 0) '' (graphMap '' A) = A := by
  rw [image_image]; simp

/-- **(B≥)** The Hausdorff measure of a piece of the graph is at least the measure of its base. -/
theorem volume_le_hausdorffMeasure_graphMap_image (A : Set ℝ) :
    volume A ≤ μH[1] (graphMap '' A) := by
  calc volume A = μH[1] A := by rw [hausdorffMeasure_real]
    _ = μH[1] ((fun p : Plane ↦ p 0) '' (graphMap '' A)) := by rw [proj_image_graphMap_image]
    _ ≤ ((1 : ℝ≥0) : ℝ≥0∞) ^ (1 : ℝ) * μH[1] (graphMap '' A) :=
        lipschitzWith_proj.hausdorffMeasure_image_le zero_le_one _
    _ = μH[1] (graphMap '' A) := by simp

/-! ### Cells -/

/-- The level-`n` cell with index `i`. -/
def cell (n : ℕ) (i : ℤ) : Set ℝ := Ico (i * cellLength n) ((i + 1) * cellLength n)

theorem mem_cell_iff {n : ℕ} {i : ℤ} {x : ℝ} : x ∈ cell n i ↔ cellIndex n x = i := by
  have hpos := cellLength_pos n
  rw [cell, cellIndex, mem_Ico, Int.floor_eq_iff, le_div_iff₀ hpos, div_lt_iff₀ hpos]

theorem mem_cell_cellIndex (n : ℕ) (x : ℝ) : x ∈ cell n (cellIndex n x) :=
  mem_cell_iff.mpr rfl

theorem volume_cell (n : ℕ) (i : ℤ) : volume (cell n i) = ENNReal.ofReal (cellLength n) := by
  rw [cell, Real.volume_Ico]; congr 1; ring

theorem cell_disjoint {n : ℕ} {i j : ℤ} (h : i ≠ j) : Disjoint (cell n i) (cell n j) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_cell_iff] at hx hx'
  exact h (hx.symm.trans hx')

/-- The graph over a level-`n ≥ 1` cell has diameter at most twice the cell length. -/
theorem diam_graphMap_image_cell_le {n : ℕ} (hn : 1 ≤ n) (i : ℤ) :
    Metric.ediam (graphMap '' cell n i) ≤ ENNReal.ofReal (2 * cellLength n) := by
  refine Metric.ediam_le ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [edist_dist, dist_graphMap]
  refine ENNReal.ofReal_le_ofReal ?_
  have hxy : cellIndex n x = cellIndex n y := by
    rw [mem_cell_iff] at hx hy; rw [hx, hy]
  have h1 : |x - y| < cellLength n := by
    -- both lie in an interval of length `cellLength n`
    simp only [cell, mem_Ico] at hx hy
    rw [abs_lt]; constructor <;> nlinarith
  have h2 := abs_besicovitchFun_sub_le hxy
  have h3 : 4 * cellLength (n + 1) / (n + 1) ≤ cellLength n := by
    have hr := cellLength_succ_le_of_pos hn
    have hpos' := cellLength_pos (n + 1)
    have hn' : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    calc 4 * cellLength (n + 1) / (n + 1) ≤ 4 * cellLength (n + 1) :=
          div_le_self (by linarith) hn'
      _ ≤ cellLength n := by linarith
  have hpos := cellLength_pos n
  have ha : (x - y) ^ 2 ≤ cellLength n ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1.le 2
  have hb : (besicovitchFun x - besicovitchFun y) ^ 2 ≤ cellLength n ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h2.trans h3) 2
  calc √((x - y) ^ 2 + (besicovitchFun x - besicovitchFun y) ^ 2)
      ≤ √((2 * cellLength n) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = 2 * cellLength n := Real.sqrt_sq (by positivity)

end LeanPool.Besicovitch.Example
