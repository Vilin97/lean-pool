/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Path.ClosedSetDetection
import LeanPool.MarkovProcess.MarkovProcess.Lifetime.ExitTime
import Mathlib.Probability.Process.Stopping

/-!
# Exit times of open sets on continuous-path space

For an open set `U` this file studies `ContinuousPath.exitTime U`, the first time a continuous
path leaves `U`, in the `WithTop`-valued form `ContinuousPath.exitTimeTop U` demanded by
Mathlib's stopping-time convention.  The main consumer facts are: the exit time is a stopping
time for the canonical filtration; it is finite exactly when the path leaves `U` at some time;
at a finite exit time the path sits on the frontier of `U` when it started inside; and its
truncation `exitTimeTrunc U K` at a deterministic horizon is an `NNReal`-valued stopping time,
which is the form the finite-stopping-time API of this library consumes.  The generic time-set
identities `survivalSet_top`, `survivalSet_ne_top`, and `survivalSet` identify the positive real
times below an extended nonnegative horizon.

The route is the closed-set detection of `Path/ClosedSetDetection.lean`: the event
`{exitTime ≤ t}` is the event of hitting the closed set `Uᶜ` by time `t`, because a path that
stays in the open set `U` throughout `[0, t]` stays in it slightly beyond `t`.

This file constructs no probability law and proves no probabilistic statement; in particular it
does not claim that the exit time is almost surely finite for any process.
-/

noncomputable section PortComputability

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MarkovProcess

namespace ContinuousPath

section

section SurvivalSets

/-- The survival set below an infinite extended horizon is the positive half-line. -/
theorem survivalSet_top :
    {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ⊤} ∩ Set.Ioi 0 = Set.Ioi 0 := by
  ext t
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioi]
  exact and_iff_right ENNReal.coe_lt_top

/-- The survival set below a finite extended horizon is an ordinary open interval. -/
theorem survivalSet_ne_top (tau : ℝ≥0∞) (htau : tau ≠ ⊤) :
    {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau} ∩ Set.Ioi 0 =
      Set.Ioo 0 tau.toReal := by
  ext t
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioi, Set.mem_Ioo]
  constructor
  · rintro ⟨httau, ht⟩
    refine ⟨ht, ?_⟩
    have hcoe : ((Real.toNNReal t : NNReal) : ℝ≥0∞) = ENNReal.ofReal t := rfl
    rw [hcoe] at httau
    exact (ENNReal.ofReal_lt_iff_lt_toReal ht.le htau).mp httau
  · rintro ⟨ht, httau⟩
    refine ⟨?_, ht⟩
    have hcoe : ((Real.toNNReal t : NNReal) : ℝ≥0∞) = ENNReal.ofReal t := rfl
    rw [hcoe]
    exact (ENNReal.ofReal_lt_iff_lt_toReal ht.le htau).mpr httau

/-- The time set on which the nonnegative-time coordinate remains below an extended horizon. -/
theorem survivalSet (tau : ℝ≥0∞) :
    {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau} ∩ Set.Ioi 0 =
      if tau = ⊤ then Set.Ioi 0 else Set.Ioo 0 tau.toReal := by
  by_cases htau : tau = ⊤
  · rw [ite_eq_left htau, htau]
    exact survivalSet_top
  · rw [ite_eq_right htau]
    exact survivalSet_ne_top tau htau

end SurvivalSets

variable {alpha : Type*} [PseudoMetricSpace alpha]

section Order

/-- A time at which the path is outside `U` bounds the exit time from above. -/
theorem exitTime_le_of_notMem (U : Set alpha) (omega : ContinuousPath alpha) (t : NNReal)
    (ht : omega t ∉ U) : exitTime U omega ≤ (t : ℝ≥0∞) := by
  apply sInf_le
  exact ⟨t, rfl, ht⟩

/-- Strictly before the exit time the path is inside `U`. -/
theorem mem_of_lt_exitTime (U : Set alpha) (omega : ContinuousPath alpha) (t : NNReal)
    (ht : (t : ℝ≥0∞) < exitTime U omega) : omega t ∈ U := by
  by_contra htU
  exact absurd (exitTime_le_of_notMem U omega t htU) (not_le_of_gt ht)

/-- The exit time from `U` is infinite exactly when the path never leaves `U`. -/
theorem exitTime_eq_top_iff (U : Set alpha) (omega : ContinuousPath alpha) :
    exitTime U omega = ⊤ ↔ ∀ t : NNReal, omega t ∈ U := by
  constructor
  · intro htop t
    by_contra ht
    have hle := exitTime_le_of_notMem U omega t ht
    rw [htop, top_le_iff] at hle
    exact ENNReal.coe_ne_top hle
  · intro hmem
    have hempty : {s : ℝ≥0∞ | ∃ t : NNReal, s = (t : ℝ≥0∞) ∧ omega t ∉ U} = ∅ := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro u _
      exact fun hu ↦ hu (hmem u)
    rw [exitTime, hempty, sInf_empty]

/-- The exit time from `U` is finite exactly when the path leaves `U` at some time. -/
theorem exitTime_lt_top_iff (U : Set alpha) (omega : ContinuousPath alpha) :
    exitTime U omega < ⊤ ↔ ∃ t : NNReal, omega t ∉ U := by
  rw [lt_top_iff_ne_top, Ne, exitTime_eq_top_iff, not_forall]

/-- For an open set `U`, the exit time is at most `t` exactly when the path meets the closed set
`Uᶜ` at or before time `t`.  The forward direction uses openness of `U`: a path inside `U`
throughout `[0, t]` stays inside `U` for a further positive amount of time, so its exit time is
strictly larger than `t`. -/
theorem exitTime_le_iff_mem_hitsSetBy (U : Set alpha) (hU : IsOpen U) (t : NNReal)
    (omega : ContinuousPath alpha) :
    exitTime U omega ≤ (t : ℝ≥0∞) ↔ omega ∈ hitsSetBy t Uᶜ := by
  constructor
  · intro hle
    by_contra hnot
    have hall : ∀ s : NNReal, s ≤ t → omega s ∈ U := by
      intro s hs
      by_contra hsU
      exact hnot ⟨⟨s, Set.mem_Iic.mpr hs⟩, hsU⟩
    have hVopen : IsOpen ((omega : NNReal → alpha) ⁻¹' U) := hU.preimage omega.continuous
    have htV : t ∈ (omega : NNReal → alpha) ⁻¹' U := hall t le_rfl
    obtain ⟨delta, hdelta, hball⟩ := Metric.isOpen_iff.mp hVopen t htV
    have hhalf : (0 : ℝ) < delta / 2 := by linarith only [hdelta]
    set d : NNReal := ⟨delta / 2, le_of_lt hhalf⟩ with hd
    have hdpos : 0 < d := NNReal.coe_pos.mp hhalf
    have hmem : ∀ s : NNReal, s < t + d → omega s ∈ U := by
      intro s hs
      by_cases hst : s ≤ t
      · exact hall s hst
      · apply hball
        rw [Metric.mem_ball, NNReal.dist_eq]
        have hts : (t : ℝ) < (s : ℝ) := by exact_mod_cast lt_of_not_ge hst
        have hsd : (s : ℝ) < (t : ℝ) + delta / 2 := by
          have := hs
          rw [← NNReal.coe_lt_coe, NNReal.coe_add] at this
          exact this
        rw [abs_of_pos (by linarith only [hts])]
        linarith only [hsd, hdelta]
    have hge : ((t + d : NNReal) : ℝ≥0∞) ≤ exitTime U omega := by
      rw [exitTime]
      apply le_sInf
      rintro s ⟨u, rfl, hu⟩
      have hnotlt : ¬ u < t + d := fun h ↦ hu (hmem u h)
      exact_mod_cast not_lt.mp hnotlt
    have hlt : (t : ℝ≥0∞) < ((t + d : NNReal) : ℝ≥0∞) := by
      rw [ENNReal.coe_lt_coe]
      exact lt_add_of_pos_right t hdpos
    exact absurd (hlt.trans_le (hge.trans hle)) (lt_irrefl _)
  · rintro ⟨s, hs⟩
    refine le_trans (exitTime_le_of_notMem U omega s hs) ?_
    exact_mod_cast s.property

end Order

section WithTopValue

/-- The exit time of a continuous path from `U`, read in `WithTop ℝ≥0`: this is the same value as
`ContinuousPath.exitTime U`, presented in the type Mathlib's `IsStoppingTime` expects. -/
def exitTimeTop (U : Set alpha) (omega : ContinuousPath alpha) : WithTop NNReal :=
  exitTime U omega

/-- The `WithTop`-valued exit time is the exit time. -/
theorem exitTimeTop_apply (U : Set alpha) (omega : ContinuousPath alpha) :
    exitTimeTop U omega = exitTime U omega := rfl

/-- The exit time from `U` truncated at the deterministic horizon `K`: an `NNReal`-valued, hence
finite, time, equal to the exit time when that is at most `K` and to `K` otherwise. -/
def exitTimeTrunc (U : Set alpha) (K : NNReal) (omega : ContinuousPath alpha) : NNReal :=
  (min (exitTimeTop U omega) (K : WithTop NNReal)).untopA

/-- The truncated exit time, read in `WithTop ℝ≥0`, is the minimum of the exit time and the
horizon. -/
theorem coe_exitTimeTrunc (U : Set alpha) (K : NNReal) (omega : ContinuousPath alpha) :
    ((exitTimeTrunc U K omega : NNReal) : WithTop NNReal) =
      min (exitTimeTop U omega) (K : WithTop NNReal) := by
  have hne : min (exitTimeTop U omega) (K : WithTop NNReal) ≠ ⊤ := by
    intro htop
    have hle := min_le_right (exitTimeTop U omega) (K : WithTop NNReal)
    rw [htop] at hle
    exact WithTop.coe_ne_top (top_le_iff.mp hle)
  rw [exitTimeTrunc, WithTop.untopA_eq_untop hne, WithTop.coe_untop]

/-- The truncated exit time never exceeds its horizon. -/
theorem exitTimeTrunc_le (U : Set alpha) (K : NNReal) (omega : ContinuousPath alpha) :
    exitTimeTrunc U K omega ≤ K := by
  rw [← WithTop.coe_le_coe, coe_exitTimeTrunc]
  exact min_le_right _ _

end WithTopValue

section Frontier

/-- The exit position is read at the time `(exitTime U omega).toNNReal`.  The `WithTop.untopD`
spelling of that time, which the `WithTop`-valued stopping-time API produces, is the same
value. -/
@[simp]
theorem untopD_exitTime (U : Set alpha) (omega : ContinuousPath alpha) :
    (exitTime U omega).untopD 0 = (exitTime U omega).toNNReal := rfl

/-- At a finite exit time, a path that started inside the open set `U` sits on the frontier of
`U`: it is outside `U`, and it is a limit of points of `U` visited strictly earlier. -/
theorem coordinate_exitTime_mem_frontier (U : Set alpha) (hU : IsOpen U)
    (omega : ContinuousPath alpha) (h0 : omega 0 ∈ U) (hfin : exitTime U omega ≠ ⊤) :
    omega ((exitTime U omega).toNNReal) ∈ frontier U := by
  set tau : NNReal := (exitTime U omega).toNNReal with htau
  have hcoe : (tau : ℝ≥0∞) = exitTime U omega := ENNReal.coe_toNNReal hfin
  have hbefore : ∀ s : NNReal, s < tau → omega s ∈ U := by
    intro s hs
    apply mem_of_lt_exitTime
    rw [← hcoe, ENNReal.coe_lt_coe]
    exact hs
  have hnot : omega tau ∉ U := by
    obtain ⟨s, hs⟩ :=
      (exitTime_le_iff_mem_hitsSetBy U hU tau omega).mp (le_of_eq hcoe.symm)
    have hge : tau ≤ (s : NNReal) := by
      by_contra hlt
      exact hs (hbefore s (lt_of_not_ge hlt))
    have hseq : (s : NNReal) = tau := le_antisymm s.property hge
    rw [← hseq]
    exact hs
  have htau0 : tau ≠ 0 := by
    intro h
    rw [h] at hnot
    exact hnot h0
  have hclosure : omega tau ∈ closure U := by
    have hnebot : (nhdsWithin tau (Set.Iio tau)).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, lt_of_le_of_ne (zero_le : (0 : NNReal) ≤ tau) (Ne.symm htau0)⟩
    have htend : Filter.Tendsto (omega : NNReal → alpha) (nhdsWithin tau (Set.Iio tau))
        (nhds (omega tau)) := (omega.continuous.tendsto tau).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hbefore s hs
  rw [hU.frontier_eq]
  exact ⟨hclosure, hnot⟩

end Frontier

section Stopping

variable [MeasurableSpace alpha] [BorelSpace alpha]

/-- **The exit time from an open set is a stopping time** for the canonical filtration on
continuous paths: the event `{exitTime ≤ t}` is the event of hitting the closed set `Uᶜ` by time
`t`, which is measurable in the canonical filtration at time `t`. -/
theorem isStoppingTime_exitTime (U : Set alpha) (hU : IsOpen U) :
    IsStoppingTime (canonicalFiltration (alpha := alpha)) (exitTimeTop U) := by
  intro t
  have hevent : {omega : ContinuousPath alpha | exitTimeTop U omega ≤ (t : WithTop NNReal)} =
      hitsSetBy t Uᶜ := by
    ext omega
    simp only [Set.mem_ofPred_eq]
    exact exitTime_le_iff_mem_hitsSetBy U hU t omega
  change MeasurableSet[canonicalFiltration (alpha := alpha) t]
    {omega : ContinuousPath alpha | exitTimeTop U omega ≤ (t : WithTop NNReal)}
  rw [hevent]
  exact measurableSet_hitsSetBy t Uᶜ hU.isClosed_compl

/-- **The truncated exit time from an open set is a finite stopping time** for the canonical
filtration, in the `NNReal`-valued form consumed by the finite-stopping-time API of this
library. -/
theorem isStoppingTime_exitTimeTrunc (U : Set alpha) (hU : IsOpen U) (K : NNReal) :
    IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ ((exitTimeTrunc U K omega : NNReal) : WithTop NNReal)) := by
  simp only [coe_exitTimeTrunc]
  exact (isStoppingTime_exitTime U hU).min_const K

end Stopping

end

end ContinuousPath

end MarkovProcess

end PortComputability
