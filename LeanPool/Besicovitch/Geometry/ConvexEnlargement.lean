/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Statement
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Convex enlargements

This file records the two elementary enlargements used in the continuum argument: thickening a
set by a multiple of its diameter, and replacing an open set by its open convex hull.
-/

@[expose] public section

noncomputable section

open Bornology Set

namespace LeanPool.Besicovitch

/-- The `p`-diameter thickening of a set. -/
def diameterThickening (p : ℝ) (s : Set (EuclideanSpace ℝ (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  Metric.thickening (p * Metric.diam s) s

/-- Diameter thickenings are open. -/
theorem isOpen_diameterThickening (p : ℝ) (s : Set (EuclideanSpace ℝ (Fin 2))) :
    IsOpen (diameterThickening p s) :=
  Metric.isOpen_thickening

/-- A nonnegative `p`-diameter thickening has diameter at most `(2p + 1)` times the original. -/
theorem diam_diameterThickening_le {p : ℝ} (hp : 0 ≤ p) (s : Set (EuclideanSpace ℝ (Fin 2))) :
    Metric.diam (diameterThickening p s) ≤ (2 * p + 1) * Metric.diam s := by
  rw [diameterThickening]
  calc
    Metric.diam (Metric.thickening (p * Metric.diam s) s) ≤
        Metric.diam s + 2 * (p * Metric.diam s) :=
      Metric.diam_thickening_le s (mul_nonneg hp Metric.diam_nonneg)
    _ = (2 * p + 1) * Metric.diam s := by ring

/-- The extended diameter of a nonnegative diameter thickening obeys the same linear bound. -/
theorem ediam_diameterThickening_le {p : ℝ} (hp : 0 ≤ p) {s : Set (EuclideanSpace ℝ (Fin 2))}
    (hs : IsBounded s) :
    Metric.ediam (diameterThickening p s) ≤
      ENNReal.ofReal (2 * p + 1) * Metric.ediam s := by
  have hthickening : IsBounded (diameterThickening p s) := hs.thickening
  rw [← ENNReal.ofReal_toReal hthickening.ediam_ne_top,
    ← ENNReal.ofReal_toReal hs.ediam_ne_top]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * p + 1)]
  exact ENNReal.ofReal_le_ofReal (diam_diameterThickening_le hp s)

/-- A set is contained in every positive-radius diameter thickening. -/
theorem subset_diameterThickening {p : ℝ} {s : Set (EuclideanSpace ℝ (Fin 2))}
    (hpositive : 0 < p * Metric.diam s) : s ⊆ diameterThickening p s := by
  exact Metric.self_subset_thickening hpositive s

/-- A bounded set meeting `s` lies in the `p`-diameter thickening of `s` when its diameter is
smaller than the thickening radius. -/
theorem subset_diameterThickening_of_inter_nonempty
    {u s : Set (EuclideanSpace ℝ (Fin 2))} {p : ℝ}
    (hu : IsBounded u) (hus : (u ∩ s).Nonempty)
    (hdiam : Metric.diam u < p * Metric.diam s) : u ⊆ diameterThickening p s := by
  obtain ⟨y, hyu, hys⟩ := hus
  intro x hxu
  rw [diameterThickening, Metric.mem_thickening_iff]
  exact ⟨y, hys, (Metric.dist_le_diam_of_mem hu hxu hyu).trans_lt hdiam⟩

/-- The interior of the convex hull of a set. -/
def openConvexHull (s : Set (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2)) :=
  interior (convexHull ℝ s)

/-- The open convex hull is open. -/
theorem isOpen_openConvexHull (s : Set (EuclideanSpace ℝ (Fin 2))) : IsOpen (openConvexHull s) :=
  isOpen_interior

/-- The open convex hull is convex. -/
theorem convex_openConvexHull (s : Set (EuclideanSpace ℝ (Fin 2))) :
    Convex ℝ (openConvexHull s) :=
  (convex_convexHull ℝ s).interior

/-- An open set is contained in its open convex hull. -/
theorem subset_openConvexHull {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : IsOpen s) :
    s ⊆ openConvexHull s := by
  exact hs.subset_interior_iff.mpr (subset_convexHull ℝ s)

/-- Passing from an open set to its open convex hull does not change its extended diameter. -/
theorem ediam_openConvexHull {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : IsOpen s) :
    Metric.ediam (openConvexHull s) = Metric.ediam s := by
  apply le_antisymm
  · exact (Metric.ediam_mono interior_subset).trans_eq (convexHull_ediam s)
  · exact Metric.ediam_mono (subset_openConvexHull hs)

/-- Passing from an open set to its open convex hull does not change its diameter. -/
theorem diam_openConvexHull {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : IsOpen s) :
    Metric.diam (openConvexHull s) = Metric.diam s := by
  have hsubset : s ⊆ openConvexHull s := subset_openConvexHull hs
  by_cases hbounded : IsBounded s
  · have hconvexHull_bounded : IsBounded (convexHull ℝ s) := by simpa using hbounded
    have hopen_bounded : IsBounded (openConvexHull s) :=
      hconvexHull_bounded.subset interior_subset
    apply le_antisymm
    · calc
        Metric.diam (openConvexHull s) ≤ Metric.diam (convexHull ℝ s) :=
          Metric.diam_mono interior_subset hconvexHull_bounded
        _ = Metric.diam s := convexHull_diam s
    · exact Metric.diam_mono hsubset hopen_bounded
  · have hopen_unbounded : ¬IsBounded (openConvexHull s) := fun h ↦ hbounded (h.subset hsubset)
    rw [Metric.diam_eq_zero_of_unbounded hbounded,
      Metric.diam_eq_zero_of_unbounded hopen_unbounded]

end LeanPool.Besicovitch
