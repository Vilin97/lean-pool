/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Example.Plane
public import LeanPool.Besicovitch.Statement

/-!
# The lower density of Besicovitch's set is at least `1/2`

At an interior point `graphMap x` of the graph, the ball of radius `r` contains the graph over an
interval of length at least `θ * r`, for every `θ < 1` and every small `r`: let `n` be the last
level with `r ≤ cellLength n`; inside the level-`n` cell of `x` the function `g` varies by at
most `4 * cellLength (n+1) / (n+1) < 4 * r / (n+1)`, which is below `(1 - θ) * r` once `n` is
large.  Since the first-coordinate projection is `1`-Lipschitz, the Hausdorff measure of the
graph over that interval is at least `θ * r`, so the lower density (normalised by the diameter
`2 * r` of the ball) is at least `θ / 2`.  Letting `θ → 1` gives `1/2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace LeanPool.Besicovitch.Example

/-- Below any positive radius `r ≤ cellLength n₀` there is a level `n ≥ n₀` with
`cellLength (n + 1) < r ≤ cellLength n`. -/
theorem exists_cellLength_lt_le {r : ℝ} (hr : 0 < r) {n₀ : ℕ}
    (hr₀ : r ≤ cellLength n₀) :
    ∃ n, n₀ ≤ n ∧ cellLength (n + 1) < r ∧ r ≤ cellLength n := by
  classical
  have hex : ∃ m, cellLength m < r := (tendsto_cellLength.eventually (gt_mem_nhds hr)).exists
  have hspec := Nat.find_spec hex
  have hlt : n₀ < Nat.find hex := by
    by_contra h
    have h' := cellLength_antitone (not_lt.mp h)
    exact lt_irrefl _ (hspec.trans_le (hr₀.trans h'))
  obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨n, by omega, ?_, not_lt.mp (Nat.find_min hex (by omega))⟩
  rwa [hn] at hspec

/-- A point of the level-`n` cell of `x` at horizontal distance `< θ * r` from `x` lies within
distance `r` of `graphMap x` on the graph, once `4 / (n + 1) ≤ 1 - θ` and
`cellLength (n + 1) < r`. -/
theorem dist_graphMap_lt {θ r : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (hr : 0 < r) {n : ℕ}
    (hn : 4 / ((n : ℝ) + 1) ≤ 1 - θ) (hrn : cellLength (n + 1) < r) {x y : ℝ}
    (hxy : cellIndex n x = cellIndex n y) (hd : |x - y| < θ * r) :
    dist (graphMap x) (graphMap y) < r := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hpos := cellLength_pos (n + 1)
  have h1 := abs_besicovitchFun_sub_le hxy
  have h2 : 4 * cellLength (n + 1) / (n + 1) < (1 - θ) * r := by
    calc 4 * cellLength (n + 1) / (n + 1) = 4 / ((n : ℝ) + 1) * cellLength (n + 1) := by ring
      _ ≤ (1 - θ) * cellLength (n + 1) := mul_le_mul_of_nonneg_right hn hpos.le
      _ < (1 - θ) * r := mul_lt_mul_of_pos_left hrn (by linarith)
  have ha : (x - y) ^ 2 < (θ * r) ^ 2 := by
    rw [← sq_abs]; exact pow_lt_pow_left₀ hd (abs_nonneg _) two_ne_zero
  have hb : (besicovitchFun x - besicovitchFun y) ^ 2 < ((1 - θ) * r) ^ 2 := by
    rw [← sq_abs]; exact pow_lt_pow_left₀ (h1.trans_lt h2) (abs_nonneg _) two_ne_zero
  rw [dist_graphMap, Real.sqrt_lt' hr]
  nlinarith [mul_pos (mul_pos hr hr) (mul_pos hθ0 (sub_pos.2 hθ1))]

/-- **The key estimate.** For every `θ < 1` and every sufficiently small `r`, the ball of radius
`r` about the interior graph point `graphMap x` meets the graph in a set of Hausdorff measure at
least `θ * r`. -/
theorem eventually_ofReal_le_hausdorffMeasure_inter_ball {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (θ * r) ≤ μH[1] (besicovitchSet ∩ Metric.ball (graphMap x) r) := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hs : 0 < 1 - θ := by linarith
  -- a level beyond which `4 / (n + 1) ≤ 1 - θ`
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (4 / (1 - θ))
  have hn₀' : 4 / ((n₀ : ℝ) + 1) ≤ 1 - θ := by
    rw [div_lt_iff₀ hs] at hn₀
    rw [div_le_iff₀ (by positivity)]
    linarith
  -- all the smallness conditions hold below `r₀`
  have hr₀pos : 0 < min (cellLength n₀) (min x (1 - x)) := by
    simp only [lt_min_iff]
    exact ⟨cellLength_pos n₀, hx0, by linarith⟩
  filter_upwards [Ioo_mem_nhdsGT hr₀pos] with r hr
  obtain ⟨hr0, hrr₀⟩ := hr
  have hr1 : r ≤ cellLength n₀ := hrr₀.le.trans (min_le_left _ _)
  have hrx : r < x := hrr₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrx' : r < 1 - x := hrr₀.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hθr' : θ * r ≤ r := mul_le_of_le_one_left hr0.le hθ1.le
  have hθr0 : 0 < θ * r := mul_pos hθ0 hr0
  -- the last level `n` with `r ≤ cellLength n`
  obtain ⟨n, hn₀n, hlt, hle⟩ := exists_cellLength_lt_le hr0 hr1
  have hn : 4 / ((n : ℝ) + 1) ≤ 1 - θ := by
    refine le_trans ?_ hn₀'
    have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn₀n
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hθr : θ * r ≤ cellLength n := hθr'.trans hle
  -- the part of the cell of `x` within `θ * r` of `x` is the interval `Ioo a b`
  have hxc := mem_cell_cellIndex n x
  simp only [cell, mem_Ico] at hxc
  obtain ⟨a, ha⟩ : ∃ a, a = max (x - θ * r) (cellIndex n x * cellLength n) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = min (x + θ * r) ((cellIndex n x + 1) * cellLength n) :=
    ⟨_, rfl⟩
  have ha1 : x - θ * r ≤ a := by rw [ha]; exact le_max_left _ _
  have ha2 : cellIndex n x * cellLength n ≤ a := by rw [ha]; exact le_max_right _ _
  have hb1 : b ≤ x + θ * r := by rw [hb]; exact min_le_left _ _
  have hb2 : b ≤ (cellIndex n x + 1) * cellLength n := by rw [hb]; exact min_le_right _ _
  -- its length is at least `θ * r`
  have hab : θ * r ≤ b - a := by
    rw [ha, hb]
    rcases le_total (x - θ * r) (cellIndex n x * cellLength n) with h1 | h1 <;>
      rcases le_total (x + θ * r) ((cellIndex n x + 1) * cellLength n) with h2 | h2
    · rw [max_eq_right h1, min_eq_left h2]; linarith
    · rw [max_eq_right h1, min_eq_right h2]; linarith
    · rw [max_eq_left h1, min_eq_left h2]; linarith
    · rw [max_eq_left h1, min_eq_right h2]; linarith
  -- the graph over it lies in the set and in the ball
  have hsub : graphMap '' Ioo a b ⊆ besicovitchSet ∩ Metric.ball (graphMap x) r := by
    rintro _ ⟨y, ⟨hya, hyb⟩, rfl⟩
    refine ⟨⟨y, ⟨by linarith, by linarith⟩, rfl⟩, ?_⟩
    rw [Metric.mem_ball, dist_comm]
    refine dist_graphMap_lt ⟨hθ0, hθ1⟩ hr0 hn hlt ?_ ?_
    · have hy : y ∈ cell n (cellIndex n x) := by
        simp only [cell, mem_Ico]; constructor <;> linarith
      exact (mem_cell_iff.mp hy).symm
    · rw [abs_lt]; constructor <;> linarith
  calc ENNReal.ofReal (θ * r) ≤ ENNReal.ofReal (b - a) := ENNReal.ofReal_le_ofReal hab
    _ = volume (Ioo a b) := Real.volume_Ioo.symm
    _ ≤ μH[1] (graphMap '' Ioo a b) := volume_le_hausdorffMeasure_graphMap_image _
    _ ≤ μH[1] (besicovitchSet ∩ Metric.ball (graphMap x) r) := measure_mono hsub

/-- For every `θ < 1`, the lower density of the graph at an interior graph point is at least
`θ / 2`. -/
theorem ofReal_half_le_lowerOneDensity_graphMap {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    ENNReal.ofReal (θ / 2) ≤ lowerOneDensity besicovitchSet (graphMap x) := by
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ofReal_le_hausdorffMeasure_inter_ball hx hθ,
    self_mem_nhdsWithin] with r hr hr0
  rw [mem_Ioi] at hr0
  have h2r : ENNReal.ofReal (2 * r) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  rw [ENNReal.le_div_iff_mul_le (Or.inl h2r) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul (by linarith [hθ.1])]
  calc ENNReal.ofReal (θ / 2 * (2 * r)) = ENNReal.ofReal (θ * r) := by congr 1; ring
    _ ≤ _ := hr

/-- **The lower density of Besicovitch's set is at least `1/2`** at every interior point of the
graph. -/
theorem one_half_le_lowerOneDensity_graphMap {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ENNReal.ofReal (1 / 2) ≤ lowerOneDensity besicovitchSet (graphMap x) := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  have hct : c ≠ ⊤ := ne_top_of_lt hc
  have hcr : c.toReal < 1 / 2 := (ENNReal.lt_ofReal_iff_toReal_lt hct).mp hc
  have hc0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  -- a `θ < 1` with `c ≤ θ / 2`
  have hθ : (2 * c.toReal + 1) / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by linarith⟩
  calc c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hct).symm
    _ ≤ ENNReal.ofReal ((2 * c.toReal + 1) / 2 / 2) := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ lowerOneDensity besicovitchSet (graphMap x) :=
        ofReal_half_le_lowerOneDensity_graphMap hx hθ

end LeanPool.Besicovitch.Example
