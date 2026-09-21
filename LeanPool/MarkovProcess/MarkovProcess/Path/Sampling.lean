/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Path.ExitTime

/-!
# Uniform sampling of a continuous path

A continuous path is uniformly continuous on every bounded time interval, so for each accuracy
`h > 0` a uniform partition of `[0, T]` fine enough makes every consecutive pair of samples closer
than `h` (`ContinuousPath.exists_uniform_sampling`).  Three variants are recorded for use with the
exit time from a set `U`: when the horizon `T` is strictly before the exit time, every sample time
is too (`ContinuousPath.exists_uniform_sampling_lt_exitTime`), so the samples witness a family of
visited sets before the exit; and when the exit time is finite and positive there are times
strictly before it at which the path is within `h` of its exit position
(`ContinuousPath.exists_lt_exitTime_dist_coordinate_exitTime_lt`).  For an open `U` the exit
position lies on `frontier U`, and the third variant carries that conclusion with it
(`ContinuousPath.exists_lt_exitTime_mem_frontier_dist_lt`): a positive exit time already forces
`omega 0 ∈ U`, the hypothesis of `ContinuousPath.coordinate_exitTime_mem_frontier`, so no extra
hypothesis is needed.  The exit position is spelled `(exitTime U omega).toNNReal` throughout, as
in `Path/ExitTime.lean`; `ContinuousPath.untopD_exitTime` converts the `WithTop.untopD` spelling.

No lattice, no covering family and no discrete geometry appears here: the sampling is purely
metric.
-/

open Set
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- **Uniform sampling of a continuous path.**  For every horizon `T` and every accuracy `h > 0`
there is a uniform partition of `[0, T]` into `M` parts along which consecutive samples of the
path are at distance less than `h`. -/
theorem exists_uniform_sampling (omega : ContinuousPath alpha) (T : NNReal) (h : ℝ) (hh : 0 < h) :
    ∃ M : ℕ, 0 < M ∧ ∀ k < M,
      dist (omega ((k : NNReal) * T / (M : NNReal)))
        (omega (((k : NNReal) + 1) * T / (M : NNReal))) < h := by
  obtain ⟨delta, hdelta, hd⟩ :=
    Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous
        (omega.continuous.continuousOn (s := Set.Icc (0 : NNReal) T))) h hh
  obtain ⟨n, hn⟩ := exists_nat_gt ((T : ℝ) / delta)
  refine ⟨n + 1, Nat.succ_pos n, fun k hk ↦ ?_⟩
  have hMR : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
  have hMN : (0 : NNReal) < ((n + 1 : ℕ) : NNReal) := by
    rw [← NNReal.coe_pos]
    push_cast
    positivity
  have hmem : ∀ j : ℕ, j ≤ n + 1 →
      (j : NNReal) * T / ((n + 1 : ℕ) : NNReal) ∈ Set.Icc (0 : NNReal) T := by
    intro j hj
    refine ⟨zero_le, ?_⟩
    rw [div_le_iff₀ hMN]
    calc
      (j : NNReal) * T ≤ ((n + 1 : ℕ) : NNReal) * T :=
        mul_le_mul_left (Nat.cast_le.mpr hj) T
      _ = T * ((n + 1 : ℕ) : NNReal) := mul_comm _ _
  have hstep : (T : ℝ) / ((n : ℝ) + 1) < delta := by
    rw [div_lt_iff₀ hMR]
    have hTn : (T : ℝ) < (n : ℝ) * delta := by
      rw [div_lt_iff₀ hdelta] at hn
      exact hn
    calc
      (T : ℝ) < (n : ℝ) * delta := hTn
      _ ≤ delta * ((n : ℝ) + 1) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (by linarith only []) hdelta.le
  have hdistR : dist ((k : NNReal) * T / ((n + 1 : ℕ) : NNReal))
      (((k : NNReal) + 1) * T / ((n + 1 : ℕ) : NNReal)) = (T : ℝ) / ((n : ℝ) + 1) := by
    have hnonneg : (0 : ℝ) ≤ (T : ℝ) / ((n : ℝ) + 1) := by positivity
    have hexpand : (k : ℝ) * (T : ℝ) / ((n : ℝ) + 1) -
        ((k : ℝ) + 1) * (T : ℝ) / ((n : ℝ) + 1) = -((T : ℝ) / ((n : ℝ) + 1)) := by
      field_simp
      ring
    rw [NNReal.dist_eq]
    push_cast
    rw [hexpand, abs_neg, abs_of_nonneg hnonneg]
  refine hd _ (hmem k (by omega)) _ (?_) ?_
  · have : ((k : NNReal) + 1) = ((k + 1 : ℕ) : NNReal) := by push_cast; ring
    rw [this]
    exact hmem (k + 1) (by omega)
  · rw [hdistR]
    exact hstep

/-- Sampling admissible before an exit: when the horizon lies strictly before the exit time from
`U`, so does every sample time of a uniform partition of `[0, T]`. -/
theorem exists_uniform_sampling_lt_exitTime (U : Set alpha) (omega : ContinuousPath alpha)
    (T : NNReal) (hT : (T : ℝ≥0∞) < exitTime U omega) (h : ℝ) (hh : 0 < h) :
    ∃ M : ℕ, 0 < M ∧
      (∀ k ≤ M, (((k : NNReal) * T / (M : NNReal) : NNReal) : ℝ≥0∞) < exitTime U omega) ∧
      ∀ k < M, dist (omega ((k : NNReal) * T / (M : NNReal)))
        (omega (((k : NNReal) + 1) * T / (M : NNReal))) < h := by
  obtain ⟨M, hM, hsample⟩ := exists_uniform_sampling omega T h hh
  refine ⟨M, hM, fun k hk ↦ ?_, hsample⟩
  have hMN : (0 : NNReal) < ((M : ℕ) : NNReal) := by
    rw [← NNReal.coe_pos]
    have : (0 : ℕ) < M := hM
    push_cast
    exact_mod_cast this
  have hle : (k : NNReal) * T / (M : NNReal) ≤ T := by
    rw [div_le_iff₀ hMN]
    calc
      (k : NNReal) * T ≤ ((M : ℕ) : NNReal) * T := mul_le_mul_left (Nat.cast_le.mpr hk) T
      _ = T * ((M : ℕ) : NNReal) := mul_comm _ _
  exact lt_of_le_of_lt (by exact_mod_cast hle) hT

/-- Approaching a finite exit position from inside: if the exit time from `U` is positive and
finite, then arbitrarily close to it, and strictly before it, the path is within `h` of its
position at the exit time. -/
theorem exists_lt_exitTime_dist_coordinate_exitTime_lt (U : Set alpha)
    (omega : ContinuousPath alpha) (hpos : 0 < exitTime U omega) (hfin : exitTime U omega ≠ ⊤)
    (h : ℝ) (hh : 0 < h) :
    ∃ T : NNReal, (T : ℝ≥0∞) < exitTime U omega ∧
      dist (omega T) (omega ((exitTime U omega).toNNReal)) < h := by
  set tau : NNReal := (exitTime U omega).toNNReal with htau
  have hcoe : ((tau : NNReal) : ℝ≥0∞) = exitTime U omega := by
    rw [htau]
    exact ENNReal.coe_toNNReal hfin
  have htaupos : 0 < tau := by
    rw [← ENNReal.coe_pos, hcoe]
    exact hpos
  obtain ⟨delta, hdelta, hd⟩ :=
    Metric.continuousAt_iff.mp (omega.continuous.continuousAt (x := tau)) h hh
  set c : NNReal := min (Real.toNNReal (delta / 2)) (tau / 2)
  have hcpos : 0 < c := by
    refine lt_min ?_ ?_
    · rw [← NNReal.coe_pos, Real.coe_toNNReal _ (by positivity)]
      positivity
    · exact half_pos htaupos
  have hcle : c ≤ tau := by
    refine le_trans (min_le_right _ _) ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    linarith only [tau.coe_nonneg]
  refine ⟨tau - c, ?_, ?_⟩
  · rw [← hcoe, ENNReal.coe_lt_coe]
    exact tsub_lt_self htaupos hcpos
  · refine hd ?_
    rw [NNReal.dist_eq, NNReal.coe_sub hcle]
    have hval : |(tau : ℝ) - (c : ℝ) - (tau : ℝ)| = (c : ℝ) := by
      rw [show (tau : ℝ) - (c : ℝ) - (tau : ℝ) = -(c : ℝ) by ring, abs_neg,
        abs_of_nonneg c.coe_nonneg]
    rw [hval]
    calc
      (c : ℝ) ≤ ((Real.toNNReal (delta / 2) : NNReal) : ℝ) := by
        exact_mod_cast min_le_left (Real.toNNReal (delta / 2)) (tau / 2)
      _ = delta / 2 := Real.coe_toNNReal _ (by positivity)
      _ < delta := by linarith only [hdelta]

/-- Approaching the exit position on the frontier: for an open `U`, a positive finite exit time
is approached from strictly inside, and the position at the exit time lies on `frontier U`.  This
is `ContinuousPath.exists_lt_exitTime_dist_coordinate_exitTime_lt` with the conclusion of
`ContinuousPath.coordinate_exitTime_mem_frontier` folded in; the hypothesis `omega 0 ∈ U` of the
latter comes from the positivity of the exit time. -/
theorem exists_lt_exitTime_mem_frontier_dist_lt (U : Set alpha) (hU : IsOpen U)
    (omega : ContinuousPath alpha) (hpos : 0 < exitTime U omega) (hfin : exitTime U omega ≠ ⊤)
    (h : ℝ) (hh : 0 < h) :
    ∃ T : NNReal, (T : ℝ≥0∞) < exitTime U omega ∧
      omega ((exitTime U omega).toNNReal) ∈ frontier U ∧
      dist (omega T) (omega ((exitTime U omega).toNNReal)) < h := by
  obtain ⟨T, hT, hdist⟩ := exists_lt_exitTime_dist_coordinate_exitTime_lt U omega hpos hfin h hh
  have h0 : omega 0 ∈ U :=
    mem_of_lt_exitTime U omega 0 (by simpa only [ENNReal.coe_zero] using hpos)
  exact ⟨T, hT, coordinate_exitTime_mem_frontier U hU omega h0 hfin, hdist⟩

end ContinuousPath

end MarkovProcess
