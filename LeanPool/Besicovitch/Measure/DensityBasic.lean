/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Statement
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Elementary lower-density consequences

Strictly exceeding a lower-density level gives the corresponding ball-mass estimate at every
sufficiently small positive radius.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory Topology

namespace LeanPool.Besicovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Hausdorff measure restricted to a set evaluates balls by intersection with that set. -/
theorem restrict_hausdorffMeasure_ball (s : Set X) (x : X) (r : ℝ) :
    (μH[1].restrict s) (Metric.ball x r) = μH[1] (s ∩ Metric.ball x r) := by
  rw [Measure.restrict_apply measurableSet_ball, inter_comm]

/-- A strict lower-density bound holds as a mass bound on every sufficiently small ball. -/
theorem lowerOneDensity_eventually_ball_measure_gt {s : Set X} {x : X} {β : ℝ}
    (hβ : 0 ≤ β) (h : ENNReal.ofReal β < lowerOneDensity s x) :
    ∃ scale : ℝ, 0 < scale ∧ ∀ r : ℝ, 0 < r → r < scale →
      ENNReal.ofReal (2 * β * r) < μH[1] (s ∩ Metric.ball x r) := by
  have heventually : ∀ᶠ r in 𝓝[>] 0,
      ENNReal.ofReal β <
        μH[1] (s ∩ Metric.ball x r) / ENNReal.ofReal (2 * r) := by
    exact eventually_lt_of_lt_liminf h
  obtain ⟨neighborhood, hneighborhood, hsubset⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp heventually
  obtain ⟨scale, hscale, hball⟩ := Metric.mem_nhds_iff.mp hneighborhood
  refine ⟨scale, hscale, fun r hr hrscale ↦ ?_⟩
  have hr_mem : r ∈ neighborhood ∩ Ioi (0 : ℝ) := by
    refine ⟨hball ?_, hr⟩
    simpa [Real.dist_eq, abs_of_pos hr] using hrscale
  have hratio := hsubset hr_mem
  change ENNReal.ofReal β <
    μH[1] (s ∩ Metric.ball x r) / ENNReal.ofReal (2 * r) at hratio
  have hden_pos : 0 < ENNReal.ofReal (2 * r) := ENNReal.ofReal_pos.2 (by positivity)
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hden_pos.ne') (Or.inl ENNReal.ofReal_ne_top)]
    at hratio
  calc
    ENNReal.ofReal (2 * β * r) = ENNReal.ofReal (β * (2 * r)) := by ring_nf
    _ = ENNReal.ofReal β * ENNReal.ofReal (2 * r) := ENNReal.ofReal_mul hβ
    _ < _ := hratio

end LeanPool.Besicovitch
