/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Example.Plane
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Where a Lipschitz piece of the graph can live

If `g` is `L`-Lipschitz on a set `A`, then `A` cannot meet both sides of a level-`n` grid point
within `margin L n = cellLength n / (2 n (L + 1))`: two such points sit in adjacent cells, so `g`
jumps by at least `cellLength n / n` between them by (E2), while the Lipschitz bound allows less.

`avoid L n` is the set of points at distance at least `margin L n` from every level-`n` grid
point.  Its intersection with any cell of level `m ≥ n` is order-connected, because every
level-`n` grid point is a level-`m` grid point and hence lies outside the interior of that cell.
-/

@[expose] public section

noncomputable section

open Set
open scoped NNReal

namespace LeanPool.Besicovitch.Example

/-- Half the width of the strip around a level-`n` grid point that `A` cannot straddle. -/
def margin (L : ℝ) (n : ℕ) : ℝ := cellLength n / (2 * n * (L + 1))

/-- The level-`n` grid point with index `i`. -/
def gridPoint (n : ℕ) (i : ℤ) : ℝ := i * cellLength n

/-- Points at distance at least `margin L n` from every level-`n` grid point. -/
def avoid (L : ℝ) (n : ℕ) : Set ℝ := {x | ∀ i : ℤ, margin L n ≤ |x - gridPoint n i|}

theorem margin_pos {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 1 ≤ n) : 0 < margin L n := by
  unfold margin
  have : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_pos (cellLength_pos n) (by positivity)

theorem margin_le_half {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 1 ≤ n) :
    margin L n ≤ cellLength n / 2 := by
  unfold margin
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos := cellLength_pos n
  have h2 : (2 : ℝ) ≤ 2 * n * (L + 1) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n) hL]
  exact div_le_div_of_nonneg_left hpos.le (by norm_num) h2

/-- The Lipschitz bound across a strip of width `2 * margin` is below the jump
`cellLength n / n`. -/
theorem lipschitz_strip_lt {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 1 ≤ n) :
    L * (2 * margin L n) < cellLength n / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos := cellLength_pos n
  have hL1 : (0 : ℝ) < L + 1 := by linarith
  have h : L * (2 * margin L n) = cellLength n / n * (L / (L + 1)) := by
    unfold margin; field_simp
  rw [h]
  have : L / (L + 1) < 1 := (div_lt_one hL1).mpr (by linarith)
  exact mul_lt_of_lt_one_right (by positivity) this

/-- **Key lemma.** A set on which `g` is `L`-Lipschitz meets at most one side of a grid point. -/
theorem not_both_sides {L : ℝ≥0} {A : Set ℝ} (hg : LipschitzOnWith L besicovitchFun A)
    {n : ℕ} (hn : 1 ≤ n) (i : ℤ) {x y : ℝ} (hx : x ∈ A) (hy : y ∈ A)
    (hx' : x ∈ Ioo (gridPoint n i - margin L n) (gridPoint n i))
    (hy' : y ∈ Ico (gridPoint n i) (gridPoint n i + margin L n)) : False := by
  have hL : (0 : ℝ) ≤ L := L.coe_nonneg
  have hm := margin_le_half hL hn
  have hpos := cellLength_pos n
  -- `x` lies in cell `i - 1` and `y` in cell `i`
  have hcx : cellIndex n x = i - 1 := by
    rw [← mem_cell_iff, cell, mem_Ico]
    simp only [gridPoint, mem_Ioo] at hx'
    push_cast
    constructor <;> nlinarith
  have hcy : cellIndex n y = i := by
    rw [← mem_cell_iff, cell, mem_Ico]
    simp only [gridPoint, mem_Ico] at hy'
    constructor <;> nlinarith
  have hadj : cellIndex n y = cellIndex n x + 1 ∨ cellIndex n x = cellIndex n y + 1 :=
    Or.inl (by rw [hcx, hcy]; ring)
  have hjump := le_abs_besicovitchFun_sub hn hadj
  have hlip := hg.dist_le_mul x hx y hy
  rw [Real.dist_eq, Real.dist_eq] at hlip
  have hxy : |x - y| < 2 * margin L n := by
    simp only [gridPoint, mem_Ioo, mem_Ico] at hx' hy'
    rw [abs_lt]; constructor <;> linarith
  have := lipschitz_strip_lt hL hn
  have hL' : (L : ℝ) * |x - y| ≤ L * (2 * margin L n) := by gcongr
  linarith

/-! ### Order-connectedness inside coarser cells -/

/-- A level-`n` grid point is a level-`m` grid point for every `m ≥ n`. -/
theorem gridPoint_eq_gridPoint {n m : ℕ} (hnm : n ≤ m) (i : ℤ) :
    ∃ k : ℤ, gridPoint n i = gridPoint m k := by
  refine ⟨i * (2 ^ (m ^ 2 - n ^ 2) : ℕ), ?_⟩
  unfold gridPoint
  rw [cellLength_eq_mul hnm]
  push_cast
  ring

/-- A level-`m` grid point is not strictly inside a level-`m` cell. -/
theorem gridPoint_le_or_ge (m : ℕ) (k j : ℤ) :
    gridPoint m k ≤ j * cellLength m ∨ (j + 1) * cellLength m ≤ gridPoint m k := by
  unfold gridPoint
  have hpos := cellLength_pos m
  rcases le_or_gt k j with h | h
  · left; exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) hpos.le
  · right; exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) hpos.le

/-- The avoided set meets every coarser cell in an order-connected set. -/
theorem ordConnected_avoid_inter_cell (L : ℝ) {n m : ℕ} (hnm : n ≤ m) (j : ℤ) :
    (avoid L n ∩ cell m j).OrdConnected := by
  refine ⟨fun x hx z hz y hy ↦ ⟨fun i ↦ ?_, ?_⟩⟩
  · -- the grid point lies to the left of `x` or to the right of `z`
    obtain ⟨k, hk⟩ := gridPoint_eq_gridPoint hnm i
    have hx1 := hx.1 i
    have hz1 := hz.1 i
    have hxc := hx.2; have hzc := hz.2
    simp only [cell, mem_Ico] at hxc hzc
    rcases hy with ⟨hxy, hyz⟩
    rcases gridPoint_le_or_ge m k j with h | h <;> rw [← hk] at h
    · -- `p ≤ j α ≤ x ≤ y`, so `|y - p| ≥ |x - p|`
      have : gridPoint n i ≤ x := h.trans hxc.1
      rw [abs_of_nonneg (by linarith)] at hx1 ⊢
      linarith
    · -- `y ≤ z < (j+1) α ≤ p`, so `|y - p| ≥ |z - p|`
      have : z ≤ gridPoint n i := hzc.2.le.trans h
      rw [abs_of_nonpos (by linarith)] at hz1 ⊢
      linarith
  · exact ordConnected_Ico.out hx.2 hz.2 hy

theorem isClosed_avoid (L : ℝ) (n : ℕ) : IsClosed (avoid L n) := by
  unfold avoid
  rw [setOf_forall]
  exact isClosed_iInter fun i ↦
    isClosed_le continuous_const (continuous_id.sub continuous_const).abs

theorem measurableSet_avoid (L : ℝ) (n : ℕ) : MeasurableSet (avoid L n) :=
  (isClosed_avoid L n).measurableSet

end LeanPool.Besicovitch.Example
