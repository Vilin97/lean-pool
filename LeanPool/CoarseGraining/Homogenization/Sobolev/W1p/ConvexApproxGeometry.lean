/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareSegment
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Convex Approx Geometry -/

namespace Homogenization

/-!
# Convex-domain smoothing geometry

This file isolates the affine sampling map used in the bounded-open-convex
domain smooth approximation strategy. The future smoothing operator will sample
`u` at

`(1 - ε) • x + ε • (x0 - r • z)`,

where `closedBall x0 r ⊆ U` and `‖z‖ ≤ 1`. Convexity keeps this sample point
inside `U`.
-/

/-- The affine sample point used by the convex-domain smoothing operator. -/
def convexApproxSample {d : ℕ} (x0 z : Vec d) (r ε : ℝ) (x : Vec d) : Vec d :=
  (1 - ε) • x + ε • (x0 - r • z)

@[simp] theorem convexApproxSample_apply {d : ℕ} (x0 z : Vec d) (r ε : ℝ) (x : Vec d) :
    convexApproxSample x0 z r ε x = (1 - ε) • x + ε • (x0 - r • z) :=
  rfl

theorem convexApproxSample_eq_segmentBlend {d : ℕ} (x0 z : Vec d) (r ε : ℝ) (x : Vec d) :
    convexApproxSample x0 z r ε x = segmentBlend (x0 - r • z) ε x := by
  rw [convexApproxSample, segmentBlend_eq_smul_add]

theorem continuous_convexApproxSample {d : ℕ} (x0 z : Vec d) (r ε : ℝ) :
    Continuous (convexApproxSample x0 z r ε : Vec d → Vec d) := by
  simpa [convexApproxSample] using!
    ((continuous_const : Continuous (fun _ : Vec d => (1 - ε))).smul
        (continuous_id : Continuous (fun x : Vec d => x))).add
      (continuous_const : Continuous (fun _ : Vec d => ε • (x0 - r • z)))

theorem contDiff_convexApproxSample {d : ℕ} (x0 z : Vec d) (r ε : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (convexApproxSample x0 z r ε : Vec d → Vec d) := by
  simpa [convexApproxSample] using!
    (contDiff_const.smul contDiff_id).add contDiff_const

theorem sub_smul_mem_closedBall {d : ℕ} {x0 z : Vec d} {r : ℝ}
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1) :
    x0 - r • z ∈ Metric.closedBall x0 r := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hsub : (x0 - r • z) - x0 = -(r • z) := by
    abel_nf
  rw [hsub, norm_neg, norm_smul]
  calc
    |r| * ‖z‖ ≤ |r| * 1 := by
      exact mul_le_mul_of_nonneg_left hz (abs_nonneg r)
    _ = r := by
      rw [abs_of_nonneg hr]
      ring

theorem sub_smul_mem_of_closedBall_subset {d : ℕ} {U : Set (Vec d)} {x0 z : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1) :
    x0 - r • z ∈ U :=
  hball (sub_smul_mem_closedBall hr hz)

theorem convexApproxSample_mem_of_isOpenBoundedConvexDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {x x0 z : Vec d} {r ε : ℝ}
    (hx : x ∈ U) (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    convexApproxSample x0 z r ε x ∈ U := by
  have hy : x0 - r • z ∈ U := sub_smul_mem_of_closedBall_subset hball hr hz
  rw [convexApproxSample_eq_segmentBlend]
  exact segmentBlend_mem_of_isOpenBoundedConvexDomain hU hy hx hε0 hε1

theorem convexApproxSample_mapsTo_of_isOpenBoundedConvexDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {x0 z : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Set.MapsTo (convexApproxSample x0 z r ε) U U := by
  intro x hx
  exact convexApproxSample_mem_of_isOpenBoundedConvexDomain hU hx hball hr hz hε0 hε1

theorem norm_convexApproxSample_sub {d : ℕ} (x0 z : Vec d) (r ε : ℝ) (x : Vec d) :
    ‖convexApproxSample x0 z r ε x - x‖ = |ε| * ‖(x0 - r • z) - x‖ := by
  rw [convexApproxSample_eq_segmentBlend, norm_segmentBlend_sub_right]

theorem norm_sub_convexApproxSample {d : ℕ} (x0 z : Vec d) (r ε : ℝ) (x : Vec d) :
    ‖x - convexApproxSample x0 z r ε x‖ = |ε| * ‖(x0 - r • z) - x‖ := by
  rw [norm_sub_rev, norm_convexApproxSample_sub]

theorem norm_convexApproxSample_sub_le {d : ℕ} (x0 z : Vec d) (r ε : ℝ) (x : Vec d)
    (hε0 : 0 ≤ ε) :
    ‖convexApproxSample x0 z r ε x - x‖ ≤ ε * ‖(x0 - r • z) - x‖ := by
  rw [norm_convexApproxSample_sub, abs_of_nonneg hε0]

theorem norm_sub_convexApproxSample_le {d : ℕ} (x0 z : Vec d) (r ε : ℝ) (x : Vec d)
    (hε0 : 0 ≤ ε) :
    ‖x - convexApproxSample x0 z r ε x‖ ≤ ε * ‖(x0 - r • z) - x‖ := by
  rw [norm_sub_convexApproxSample, abs_of_nonneg hε0]

theorem norm_convexApproxSample_sub_le_two_mul_choose {d : ℕ} {U : Set (Vec d)}
    (hU : IsBoundedDomain U) {x x0 z : Vec d} {r ε : ℝ}
    (hx : x ∈ U) (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1) (hε0 : 0 ≤ ε) :
    ‖convexApproxSample x0 z r ε x - x‖ ≤ ε * (2 * Classical.choose hU) := by
  have hy : x0 - r • z ∈ U := sub_smul_mem_of_closedBall_subset hball hr hz
  calc
    ‖convexApproxSample x0 z r ε x - x‖ ≤ ε * ‖(x0 - r • z) - x‖ :=
      norm_convexApproxSample_sub_le x0 z r ε x hε0
    _ ≤ ε * (2 * Classical.choose hU) := by
      exact mul_le_mul_of_nonneg_left (hU.norm_sub_le_two_mul_choose hy hx) hε0

theorem norm_sub_convexApproxSample_le_two_mul_choose {d : ℕ} {U : Set (Vec d)}
    (hU : IsBoundedDomain U) {x x0 z : Vec d} {r ε : ℝ}
    (hx : x ∈ U) (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1) (hε0 : 0 ≤ ε) :
    ‖x - convexApproxSample x0 z r ε x‖ ≤ ε * (2 * Classical.choose hU) := by
  have hy : x0 - r • z ∈ U := sub_smul_mem_of_closedBall_subset hball hr hz
  calc
    ‖x - convexApproxSample x0 z r ε x‖ ≤ ε * ‖(x0 - r • z) - x‖ :=
      norm_sub_convexApproxSample_le x0 z r ε x hε0
    _ ≤ ε * (2 * Classical.choose hU) := by
      exact mul_le_mul_of_nonneg_left (hU.norm_sub_le_two_mul_choose hy hx) hε0

theorem norm_convexApproxSample_sub_le_two_mul_choose_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {x x0 z : Vec d} {r ε : ℝ}
    (hx : x ∈ U) (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1) (hε0 : 0 ≤ ε) :
    ‖convexApproxSample x0 z r ε x - x‖ ≤ ε * (2 * Classical.choose hU.isBoundedDomain) :=
  norm_convexApproxSample_sub_le_two_mul_choose hU.isBoundedDomain hx hball hr hz hε0

theorem norm_sub_convexApproxSample_le_two_mul_choose_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {x x0 z : Vec d} {r ε : ℝ}
    (hx : x ∈ U) (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ 1) (hε0 : 0 ≤ ε) :
    ‖x - convexApproxSample x0 z r ε x‖ ≤ ε * (2 * Classical.choose hU.isBoundedDomain) :=
  norm_sub_convexApproxSample_le_two_mul_choose hU.isBoundedDomain hx hball hr hz hε0

end Homogenization
