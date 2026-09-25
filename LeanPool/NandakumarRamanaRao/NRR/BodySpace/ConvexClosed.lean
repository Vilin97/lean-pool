/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic
public import Mathlib.Topology.MetricSpace.Closeds
public import LeanPool.NandakumarRamanaRao.NRR.BodySpace.Topology

/-!
# Closedness of convexity in the Hausdorff hyperspace

This module proves that the locus of convex nonempty compact planar sets is closed in the
Hausdorff hyperspace `TopologicalSpace.NonemptyCompacts Plane`. This is the geometric ingredient
needed for compactness of `ConvexSubbody K`.

The hyperspace carries the Hausdorff (extended) metric, under which `edist` between nonempty
compact sets equals the Hausdorff extended distance of their carriers. The proof develops two
convergence facts about this metric:

* `mem_limit_of_tendsto_nonemptyCompacts`: if `x m ∈ C m`, `C m → C₀` and `x m → x₀`, then
  `x₀ ∈ C₀` (closed membership under Hausdorff limits);
* `exists_tendsto_points_of_tendsto_nonemptyCompacts`: any point of a limit set `C₀` is the limit
  of a sequence of points chosen from the approximating sets `C m` (point approximation).

Convexity of a limit set (`convex_limit_of_tendsto`) then follows by approximating the two
endpoints of a segment and passing the convex combinations to the limit; closedness
(`isClosed_convex_nonemptyCompacts`) is the sequential packaging of this fact.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology EMetric

open NRR.Geometry

namespace NRR

namespace BodySpace

variable {C : ℕ → TopologicalSpace.NonemptyCompacts Plane}
variable {C₀ : TopologicalSpace.NonemptyCompacts Plane}

/-- The extended distance on `NonemptyCompacts` is the Hausdorff extended distance of the
carriers. -/
private theorem nonemptyCompacts_edist_eq
    (s t : TopologicalSpace.NonemptyCompacts Plane) :
    edist s t = Metric.hausdorffEDist (s : Set Plane) (t : Set Plane) :=
  (TopologicalSpace.NonemptyCompacts.isometry_toCloseds s t).symm.trans
    TopologicalSpace.Closeds.edist_eq

/-- If `x m ∈ C m`, the sets `C m` converge to `C₀` in the Hausdorff hyperspace, and the points
`x m` converge to `x₀`, then `x₀ ∈ C₀`. -/
theorem mem_limit_of_tendsto_nonemptyCompacts
    {x : ℕ → Plane} {x₀ : Plane}
    (hC : Tendsto C atTop (𝓝 C₀))
    (hx : Tendsto x atTop (𝓝 x₀))
    (hmem : ∀ m, x m ∈ (C m : Set Plane)) :
    x₀ ∈ (C₀ : Set Plane) := by
  have hclosed : IsClosed (C₀ : Set Plane) := C₀.isCompact.isClosed
  rw [Metric.mem_iff_infEDist_zero_of_closed hclosed]
  -- The Hausdorff extended distances tend to zero.
  have hHaus : Tendsto (fun m => Metric.hausdorffEDist (C m : Set Plane) (C₀ : Set Plane))
      atTop (𝓝 0) := by
    have hCe : Tendsto (fun m => edist (C m) C₀) atTop (𝓝 0) := by
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      filter_upwards [(EMetric.tendsto_nhds).1 hC ε hε] with m hm using hm.le
    exact hCe.congr fun m => nonemptyCompacts_edist_eq (C m) C₀
  -- The point distances tend to zero.
  have hxe : Tendsto (fun m => edist x₀ (x m)) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    filter_upwards [(EMetric.tendsto_nhds).1 hx ε hε] with m hm
    rw [edist_comm]; exact hm.le
  -- `infEDist x₀ C₀` is dominated by a null sequence, hence zero.
  have hbound : ∀ m, infEDist x₀ (C₀ : Set Plane) ≤
      Metric.hausdorffEDist (C m : Set Plane) (C₀ : Set Plane) + edist x₀ (x m) := by
    intro m
    calc infEDist x₀ (C₀ : Set Plane)
          ≤ infEDist (x m) (C₀ : Set Plane) + edist x₀ (x m) :=
            infEDist_le_infEDist_add_edist
      _ ≤ Metric.hausdorffEDist (C m : Set Plane) (C₀ : Set Plane) + edist x₀ (x m) := by
            gcongr
            exact infEDist_le_hausdorffEDist_of_mem (hmem m)
  have hsum : Tendsto
      (fun m => Metric.hausdorffEDist (C m : Set Plane) (C₀ : Set Plane) + edist x₀ (x m))
      atTop (𝓝 0) := by simpa using hHaus.add hxe
  have hle := le_of_tendsto_of_tendsto tendsto_const_nhds hsum
    (Filter.Eventually.of_forall hbound)
  exact nonpos_iff_eq_zero.mp hle

/-- Every point of a Hausdorff limit set `C₀` is the limit of a sequence of points drawn from the
approximating sets `C m`. -/
theorem exists_tendsto_points_of_tendsto_nonemptyCompacts
    (hC : Tendsto C atTop (𝓝 C₀))
    {x : Plane} (hx : x ∈ (C₀ : Set Plane)) :
    ∃ xseq : ℕ → Plane,
      (∀ m, xseq m ∈ (C m : Set Plane)) ∧
      Tendsto xseq atTop (𝓝 x) := by
  -- Choose in each `C m` a point realizing the distance from `x`.
  choose xseq hxmem hxdist using fun m =>
    (C m).isCompact.exists_infDist_eq_dist (C m).nonempty x
  refine ⟨xseq, hxmem, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  -- Hausdorff extended distances to `C₀` tend to zero.
  have hHaus : Tendsto (fun m => Metric.hausdorffEDist (C₀ : Set Plane) (C m : Set Plane))
      atTop (𝓝 0) := by
    have hCe : Tendsto (fun m => edist C₀ (C m)) atTop (𝓝 0) := by
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      filter_upwards [(EMetric.tendsto_nhds).1 hC ε hε] with m hm
      rw [edist_comm]; exact hm.le
    exact hCe.congr fun m => nonemptyCompacts_edist_eq C₀ (C m)
  -- Pass to real-valued Hausdorff distances.
  have hHausR : Tendsto (fun m => Metric.hausdorffDist (C₀ : Set Plane) (C m : Set Plane))
      atTop (𝓝 0) := by
    have := (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hHaus
    exact this
  -- Squeeze `dist x (xseq m)` between `0` and the Hausdorff distance.
  refine squeeze_zero (fun m => dist_nonneg) (fun m => ?_) hHausR
  rw [dist_comm, ← hxdist m]
  exact Metric.infDist_le_hausdorffDist_of_mem hx
    (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded C₀.nonempty (C m).nonempty
      C₀.isCompact.isBounded (C m).isCompact.isBounded)

/-- The Hausdorff limit of convex nonempty compact sets is convex. -/
theorem convex_limit_of_tendsto
    (hC : Tendsto C atTop (𝓝 C₀))
    (hconv : ∀ m, Convex ℝ (C m : Set Plane)) :
    Convex ℝ (C₀ : Set Plane) := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  obtain ⟨xs, hxmem, hxt⟩ := exists_tendsto_points_of_tendsto_nonemptyCompacts hC hx
  obtain ⟨ys, hymem, hyt⟩ := exists_tendsto_points_of_tendsto_nonemptyCompacts hC hy
  refine mem_limit_of_tendsto_nonemptyCompacts (x := fun m => a • xs m + b • ys m)
    (x₀ := a • x + b • y) hC ((hxt.const_smul a).add (hyt.const_smul b)) (fun m => ?_)
  exact hconv m (hxmem m) (hymem m) ha.le hb.le hab

/-- **Convexity is closed in the Hausdorff hyperspace.** The set of convex nonempty compact planar
sets is closed in `TopologicalSpace.NonemptyCompacts Plane`. -/
theorem isClosed_convex_nonemptyCompacts :
    IsClosed {
      C : TopologicalSpace.NonemptyCompacts Plane |
        Convex ℝ (C : Set Plane)
    } := by
  apply IsSeqClosed.isClosed
  intro C C₀ hmem hC
  exact convex_limit_of_tendsto hC hmem

end BodySpace

end NRR
