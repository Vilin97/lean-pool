/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/

import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Covering.LiminfLimsup
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
/-!
# LeanPool.SardMoreira.UnifDoublingCover
-/

open MeasureTheory Measure Metric Set

theorem IsUnifLocDoublingMeasure.exists_closedBall_covering_tsum_measure_le_of_measure_zero
     {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
     [SecondCountableTopology X] (μ : Measure X) [IsLocallyFiniteMeasure μ]
     [IsUnifLocDoublingMeasure μ]
     {ε : ENNReal} (hε : ε ≠ 0) (f : X → Set ℝ) (s : Set X) (hμs : μ s = 0)
     (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Set.Ioo 0 δ).Nonempty) :
     ∃ (t : Set X) (r : X → ℝ), t.Countable ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ f x) ∧
        s ⊆ ⋃ x ∈ t, closedBall x (r x) ∧ ∑' x : ↑t, μ (closedBall (↑x) (r ↑x)) ≤ ε := by
  have := s.exists_isOpen_lt_of_lt (ε / scalingConstantOf μ 4) <| by
    rw [hμs]
    exact ENNReal.div_pos hε ENNReal.coe_ne_top
  rcases this with ⟨U, hUs, hUo, hμU⟩
  have : ∀ x ∈ s, ∃ r > 0, r ≤ scalingScaleOf μ 4 ∧ 4 * r ∈ f x ∧ closedBall x r ⊆ U := by
    intro x hx
    rcases nhds_basis_closedBall.mem_iff.mp (hUo.mem_nhds (hUs hx)) with ⟨δ, hδ₀, hδU⟩
    have := scalingScaleOf_pos μ 4
    rcases hf x hx (min δ (4 * scalingScaleOf μ 4)) (by positivity) with ⟨r, hfr, hr₀, hr⟩
    rw [lt_min_iff] at hr
    refine ⟨r / 4, by positivity, ?_, ?_, ?_⟩
    · grw [hr.2]
      field_simp
      rfl
    · field_simp; assumption
    · grw [← hδU]
      gcongr
      linarith
  choose! r hr₀ hr₁ hrf hrU using this
  rcases Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall s id r _ hr₁ 4
    (by norm_num1) with ⟨t, hts, ht_disj, ht_covers⟩
  have htc : t.Countable := by
    refine ht_disj.countable_of_nonempty_interior fun x hx ↦ ?_
    grw [← ball_subset_interior_closedBall, Metric.nonempty_ball]
    exact hr₀ x (hts hx)
  refine ⟨t, (4 * r ·), htc, hts, ?_, ?_, ?_⟩
  · exact fun x hx ↦ hrf x (hts hx)
  · intro x hx
    rcases ht_covers x hx with ⟨y, hyt, hxy⟩
    refine mem_biUnion hyt (hxy ?_)
    simpa using (hr₀ x hx).le
  · calc ∑' x : t, μ (closedBall x (4 * r x))
      _ ≤ ∑' x : t, scalingConstantOf μ 4 * μ (closedBall x (r x)) := by
        gcongr with x
        apply measure_mul_le_scalingConstantOf_mul
        · simp
        · exact hr₁ x (hts x.2)
      _ = scalingConstantOf μ 4 * μ (⋃ x ∈ t, closedBall x (r x)) := by
        rw [measure_biUnion htc, ENNReal.tsum_mul_left]
        · exact ht_disj
        · exact fun _ _ ↦ measurableSet_closedBall
      _ ≤ scalingConstantOf μ 4 * μ U := by
        gcongr
        grw [← hts] at hrU
        simpa
      _ ≤ ε := by
        grw [hμU, ENNReal.mul_div_cancel]
        · simp [(one_pos.trans_le (one_le_scalingConstantOf _ _)).ne']
        · simp
