/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# `NRR.Multivalued.Separator.Distance` — distance to a closed nonempty set

Thin project wrappers around `Metric.infDist` packaging the metric facts used by the
signed-distance construction: continuity, vanishing on the underlying set, strict positivity
outside a closed nonempty set, the membership characterization of zero distance, and the estimate
by the distance to any chosen point of the set.

All results are stated for a general metric space; no compactness is assumed. Positivity requires
both closedness and nonemptiness of the set.
-/

namespace NRR.MetricTools

variable {Z : Type*} [MetricSpace Z]

/-- Distance to a set is a continuous function of the point (Mathlib's 1-Lipschitz theorem). -/
theorem continuous_infDist
    (S : Set Z) :
    Continuous fun z : Z => Metric.infDist z S :=
  Metric.continuous_infDist_pt S

/-- A point of the set has zero distance to the set. -/
theorem infDist_eq_zero_of_mem
    {S : Set Z} {z : Z} (hz : z ∈ S) :
    Metric.infDist z S = 0 :=
  Metric.infDist_zero_of_mem hz

/-- Outside a closed nonempty set the distance is strictly positive. -/
theorem infDist_pos_of_not_mem
    {S : Set Z} (hSclosed : IsClosed S) (hSne : S.Nonempty)
    {z : Z} (hz : z ∉ S) :
    0 < Metric.infDist z S :=
  (hSclosed.notMem_iff_infDist_pos hSne).1 hz

/-- For a closed nonempty set, zero distance characterizes membership. -/
theorem infDist_eq_zero_iff
    {S : Set Z} (hSclosed : IsClosed S) (hSne : S.Nonempty)
    {z : Z} :
    Metric.infDist z S = 0 ↔ z ∈ S :=
  (hSclosed.mem_iff_infDist_zero hSne).symm

/-- The distance to the set is bounded by the distance to any of its points. -/
theorem infDist_le_dist_of_mem
    {S : Set Z} {z s : Z} (hs : s ∈ S) :
    Metric.infDist z S ≤ dist z s :=
  Metric.infDist_le_dist_of_mem hs

/-- The absolute value of the distance is bounded by the distance to any point of the set. -/
theorem abs_infDist_le_dist_of_mem
    {S : Set Z} {z s : Z} (hs : s ∈ S) :
    |Metric.infDist z S| ≤ dist z s := by
  rw [abs_of_nonneg Metric.infDist_nonneg]
  exact Metric.infDist_le_dist_of_mem hs

end NRR.MetricTools
