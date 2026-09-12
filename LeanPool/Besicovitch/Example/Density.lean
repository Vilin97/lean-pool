/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Example.Avoid
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# From a one-sided hole to two-sided avoidance

If `g` is `L`-Lipschitz on `A`, then near every level-`n` grid point `A` misses an interval of
length `margin L n` on one of the two sides.  A single such hole is a vanishing fraction of any
ball, so it cannot by itself force `A` to be null.  What it does force is that a *density point*
of `A` cannot sit within `margin L n` of a level-`n` grid point for infinitely many `n`: such a
point has a hole of relative size `1/4` in the ball of radius `2 * margin L n` about it, so its
density along that sequence of radii is at most `3/4`.

Hence almost every point of `A` eventually avoids the grid on *both* sides, and the nested
recursion of `LeanPool.Besicovitch.Example.Zero` applies to the resulting sets.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace LeanPool.Besicovitch.Example

/-- A point within `margin` of a grid point has a hole of relative size `1/4` about it. -/
theorem measure_inter_closedBall_le {L : ℝ≥0} {A : Set ℝ}
    (hg : LipschitzOnWith L besicovitchFun A) {n : ℕ} (hn : 1 ≤ n) {x : ℝ} {i : ℤ}
    (hx : |x - gridPoint n i| < margin L n) :
    volume (A ∩ Metric.closedBall x (2 * margin L n)) ≤
      ENNReal.ofReal (3 * margin L n) := by
  set m := margin L n with hm
  set p := gridPoint n i with hp
  have hmpos : 0 < m := margin_pos L.coe_nonneg hn
  have hball : Metric.closedBall x (2 * m) = Icc (x - 2 * m) (x + 2 * m) := by
    rw [Real.closedBall_eq_Icc]
  -- one of the two sides of `p` misses `A`
  have hside : A ∩ Ioo (p - m) p = ∅ ∨ A ∩ Ico p (p + m) = ∅ := by
    by_contra hcon
    rw [not_or, ← Ne, ← Ne, ← Set.nonempty_iff_ne_empty,
      ← Set.nonempty_iff_ne_empty] at hcon
    obtain ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ := hcon
    exact not_both_sides hg hn i hy.1 hz.1 hy.2 hz.2
  rw [abs_lt] at hx
  -- in either case a set `J` of measure `m` inside the ball misses `A`
  obtain ⟨J, hJmeas, hJvol, hJsub, hJdisj⟩ :
      ∃ J : Set ℝ, MeasurableSet J ∧ volume J = ENNReal.ofReal m ∧
        J ⊆ Metric.closedBall x (2 * m) ∧ Disjoint A J := by
    rcases hside with h | h
    · refine ⟨Ioo (p - m) p, measurableSet_Ioo, ?_, ?_, ?_⟩
      · rw [Real.volume_Ioo]; congr 1; ring
      · rw [hball]; rintro y ⟨hy1, hy2⟩; constructor <;> [linarith; linarith]
      · rw [Set.disjoint_iff_inter_eq_empty]; exact h
    · refine ⟨Ico p (p + m), measurableSet_Ico, ?_, ?_, ?_⟩
      · rw [Real.volume_Ico]; congr 1; ring
      · rw [hball]; rintro y ⟨hy1, hy2⟩; constructor <;> [linarith; linarith]
      · rw [Set.disjoint_iff_inter_eq_empty]; exact h
  -- so `A ∩ ball` and `J` are disjoint subsets of the ball
  have hunion : volume (A ∩ Metric.closedBall x (2 * m)) + volume J ≤
      volume (Metric.closedBall x (2 * m)) := by
    rw [← measure_union (hJdisj.mono_left inter_subset_left) hJmeas]
    exact measure_mono (union_subset inter_subset_right hJsub)
  rw [hJvol, Real.volume_closedBall] at hunion
  have hcalc : ENNReal.ofReal (2 * (2 * m)) = ENNReal.ofReal (3 * m) + ENNReal.ofReal m := by
    rw [← ENNReal.ofReal_add (by positivity) hmpos.le]; congr 1; ring
  rw [hcalc] at hunion
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hunion

/-- The margins tend to zero. -/
theorem tendsto_margin (L : ℝ) (hL : 0 ≤ L) : Tendsto (margin L) atTop (𝓝 0) := by
  refine squeeze_zero' ((eventually_ge_atTop 1).mono fun n hn ↦ (margin_pos hL hn).le)
    ((eventually_ge_atTop 1).mono fun n hn ↦ ?_) tendsto_cellLength
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (1 : ℝ) ≤ 2 * n * (L + 1) := by nlinarith
  exact div_le_self (cellLength_pos n).le h2

/-- Almost every point of a set on which `g` is Lipschitz eventually avoids the grid. -/
theorem ae_eventually_mem_avoid {L : ℝ≥0} {A : Set ℝ}
    (hg : LipschitzOnWith L besicovitchFun A) :
    ∀ᵐ x ∂(volume.restrict A), ∀ᶠ n in atTop, x ∈ avoid (L : ℝ) n := by
  filter_upwards [_root_.Besicovitch.ae_tendsto_measure_inter_div volume A] with x hx
  by_contra hcon
  rw [not_eventually] at hcon
  -- the density exceeds `4/5` at all small radii
  have hdens : ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal (4 / 5) <
      volume (A ∩ Metric.closedBall x r) / volume (Metric.closedBall x r) :=
    hx.eventually (eventually_gt_nhds (ENNReal.ofReal_lt_one.mpr (by norm_num)))
  obtain ⟨ρ, hρ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hdens
  rw [mem_Ioi] at hρ
  -- pick a bad level whose margin is small
  have hsmall : ∀ᶠ n in atTop, 1 ≤ n ∧ 2 * margin (L : ℝ) n < ρ := by
    refine (eventually_ge_atTop 1).and ?_
    have := (tendsto_margin (L : ℝ) L.coe_nonneg).const_mul 2
    rw [mul_zero] at this
    exact this.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨n, hbad, hn1, hnρ⟩ := (hcon.and_eventually hsmall).exists
  set m := margin (L : ℝ) n with hm
  have hmpos : 0 < m := margin_pos L.coe_nonneg hn1
  -- at radius `2 * m` the density is at most `3/4`
  obtain ⟨i, hi⟩ : ∃ i : ℤ, |x - gridPoint n i| < m := by
    simpa [avoid, not_forall, not_le] using hbad
  have hkey := measure_inter_closedBall_le hg hn1 hi
  have hballvol : volume (Metric.closedBall x (2 * m)) = ENNReal.ofReal (4 * m) := by
    rw [Real.volume_closedBall]; congr 1; ring
  have hmem : 2 * m ∈ Ioo 0 ρ := ⟨by linarith, hnρ⟩
  have hlt := hsub hmem
  simp only [Set.mem_setOf_eq] at hlt
  rw [hballvol, ENNReal.lt_div_iff_mul_lt (Or.inl (by simp [hmpos]))
    (Or.inl ENNReal.ofReal_ne_top)] at hlt
  rw [← ENNReal.ofReal_mul (by norm_num)] at hlt
  have hcontra := hlt.trans_le hkey
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hcontra
  linarith

end LeanPool.Besicovitch.Example
