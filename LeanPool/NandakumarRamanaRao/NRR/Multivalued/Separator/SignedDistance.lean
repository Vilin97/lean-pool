/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.Fibers
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.Distance
/-!
# `NRR.Multivalued.Separator.SignedDistance` — signed distance to the carrier

For a top–bottom separator `S` over a metric space `X`, the **signed distance** assigns to each
point of `X × SignedInterval` its distance to the carrier, negated on the lower region:

```text
signedDistance z = if z ∈ S.lower then -infDist z S.carrier else infDist z S.carrier
```

Its absolute value is the ordinary distance to the carrier, its zero set is exactly the carrier,
it is strictly negative on the lower region and strictly positive on the upper region, and it takes
the corresponding strict signs at the bottom and top boundaries. The carrier-point estimate bounds
the absolute value by the distance to any chosen carrier point. Continuity is not treated here.

The carrier is nonempty because `X` is nonempty (via the vertical-fiber theorem), and it is closed
by the separator structure; these two facts drive the sign laws through the `Metric.infDist`
wrappers.
-/

namespace NRR

namespace TopBottomSeparator

variable {X : Type*} [MetricSpace X] [Nonempty X]

open Classical in
/-- The signed distance to the carrier: the distance to the carrier, negated on the lower region. -/
noncomputable def signedDistance
    (S : TopBottomSeparator X)
    (z : X × SignedInterval) : ℝ :=
  if z ∈ S.lower
  then -Metric.infDist z S.carrier
  else Metric.infDist z S.carrier

omit [Nonempty X] in
/-- The absolute value of the signed distance is the distance to the carrier. -/
theorem abs_signedDistance
    (S : TopBottomSeparator X)
    (z : X × SignedInterval) :
    |S.signedDistance z| = Metric.infDist z S.carrier := by
  classical
  unfold signedDistance
  by_cases hz : z ∈ S.lower
  · rw [ite_eq_left hz, abs_neg, abs_of_nonneg Metric.infDist_nonneg]
  · rw [ite_eq_right hz, abs_of_nonneg Metric.infDist_nonneg]

/-- The zero set of the signed distance is exactly the carrier. -/
theorem signedDistance_eq_zero_iff
    (S : TopBottomSeparator X)
    (z : X × SignedInterval) :
    S.signedDistance z = 0 ↔ z ∈ S.carrier := by
  rw [← abs_eq_zero, abs_signedDistance]
  exact NRR.MetricTools.infDist_eq_zero_iff S.isClosed_carrier S.carrier_nonempty

/-- The signed distance vanishes on the carrier. -/
theorem signedDistance_eq_zero_of_mem
    (S : TopBottomSeparator X)
    {z : X × SignedInterval}
    (hz : z ∈ S.carrier) :
    S.signedDistance z = 0 :=
  (S.signedDistance_eq_zero_iff z).2 hz

/-- The signed distance is strictly negative on the lower region. -/
theorem signedDistance_neg_of_mem_lower
    (S : TopBottomSeparator X)
    {z : X × SignedInterval}
    (hz : z ∈ S.lower) :
    S.signedDistance z < 0 := by
  classical
  have hnc : z ∉ S.carrier := S.not_mem_carrier_of_mem_lower hz
  have hpos : 0 < Metric.infDist z S.carrier :=
    NRR.MetricTools.infDist_pos_of_not_mem S.isClosed_carrier S.carrier_nonempty hnc
  unfold signedDistance
  rw [ite_eq_left hz]
  exact neg_neg_iff_pos.2 hpos

/-- The signed distance is strictly positive on the upper region. -/
theorem signedDistance_pos_of_mem_upper
    (S : TopBottomSeparator X)
    {z : X × SignedInterval}
    (hz : z ∈ S.upper) :
    0 < S.signedDistance z := by
  classical
  have hnc : z ∉ S.carrier := S.not_mem_carrier_of_mem_upper hz
  have hnl : z ∉ S.lower := fun hl => S.disjoint_lower_upper.le_bot ⟨hl, hz⟩
  have hpos : 0 < Metric.infDist z S.carrier :=
    NRR.MetricTools.infDist_pos_of_not_mem S.isClosed_carrier S.carrier_nonempty hnc
  unfold signedDistance
  rw [ite_eq_right hnl]
  exact hpos

/-- At the bottom boundary point the signed distance is strictly negative. -/
theorem signedDistance_left_neg
    (S : TopBottomSeparator X) (x : X) :
    S.signedDistance (x, SignedInterval.left) < 0 :=
  S.signedDistance_neg_of_mem_lower (S.bottom_mem_lower x)

/-- At the top boundary point the signed distance is strictly positive. -/
theorem signedDistance_right_pos
    (S : TopBottomSeparator X) (x : X) :
    0 < S.signedDistance (x, SignedInterval.right) :=
  S.signedDistance_pos_of_mem_upper (S.top_mem_upper x)

omit [Nonempty X] in
/-- The absolute value of the signed distance is bounded by the distance to any carrier point. -/
theorem abs_signedDistance_le_dist_of_mem
    (S : TopBottomSeparator X)
    {z s : X × SignedInterval}
    (hs : s ∈ S.carrier) :
    |S.signedDistance z| ≤ dist z s := by
  rw [abs_signedDistance]
  exact NRR.MetricTools.infDist_le_dist_of_mem hs

/-- The signed distance to the carrier is continuous on the whole product. -/
theorem continuous_signedDistance
    (S : TopBottomSeparator X) :
    Continuous S.signedDistance := by
  refine continuous_iff_continuousAt.mpr fun z => ?_
  by_cases hz : z ∈ S.lower
  · -- Lower points: locally `signedDistance = -infDist`.
    refine ContinuousAt.congr_of_eventuallyEq
      (f := fun z' => -Metric.infDist z' S.carrier)
      ((NRR.MetricTools.continuous_infDist S.carrier).neg.continuousAt) ?_
    filter_upwards [S.isOpen_lower.mem_nhds hz] with z' hz' using ite_eq_left hz'
  · by_cases hz' : z ∈ S.upper
    · -- Upper points: locally `signedDistance = infDist` (upper excludes lower).
      refine ContinuousAt.congr_of_eventuallyEq
        (f := fun z' => Metric.infDist z' S.carrier)
        ((NRR.MetricTools.continuous_infDist S.carrier).continuousAt) ?_
      filter_upwards [S.isOpen_upper.mem_nhds hz'] with x hx using
        ite_eq_right fun h => S.disjoint_lower_upper.le_bot ⟨h, hx⟩
    · -- Carrier points: control by the distance estimate.
      have hzc : z ∈ S.carrier :=
        Classical.not_not.1 fun h =>
          hz <| (S.mem_lower_or_upper_of_not_mem h).resolve_right hz'
      have h_abs : Filter.Tendsto (fun z' => |S.signedDistance z'|) (nhds z) (nhds 0) :=
        squeeze_zero (fun _ => abs_nonneg _)
          (fun _ => S.abs_signedDistance_le_dist_of_mem hzc)
          (Continuous.tendsto' (continuous_id.dist continuous_const) _ _ (by simp))
      exact tendsto_iff_norm_sub_tendsto_zero.mpr
        (by simpa [S.signedDistance_eq_zero_of_mem hzc] using h_abs)

/-- The signed distance packaged as a bundled continuous map. -/
noncomputable def signedDistanceMap
    (S : TopBottomSeparator X) :
    C(X × SignedInterval, ℝ) :=
  ⟨S.signedDistance, S.continuous_signedDistance⟩

@[simp] theorem signedDistanceMap_apply
    (S : TopBottomSeparator X)
    (z : X × SignedInterval) :
    S.signedDistanceMap z = S.signedDistance z :=
  rfl

end TopBottomSeparator

end NRR
