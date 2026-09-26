/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Rectifiability.BadConvexSets
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Compact convex attachments

For each selected hole, the continuum construction attaches the closed convex hull of the core
points in its two-diameter enlargement.
-/

@[expose] public section

noncomputable section

open Bornology Set

namespace LeanPool.Besicovitch

/-- The compact convex piece attached to the core near a selected hole. -/
def convexAttachment (F V : Set (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2)) :=
  closure (convexHull ℝ (F ∩ diameterThickening 2 V))

/-- A convex attachment is closed and convex. -/
theorem isClosed_convexAttachment (F V : Set (EuclideanSpace ℝ (Fin 2))) :
    IsClosed (convexAttachment F V) :=
  isClosed_closure

theorem convex_convexAttachment (F V : Set (EuclideanSpace ℝ (Fin 2))) :
    Convex ℝ (convexAttachment F V) :=
  (convex_convexHull ℝ (F ∩ diameterThickening 2 V)).closure

/-- Attachments to a compact core are compact. -/
theorem isCompact_convexAttachment {F V : Set (EuclideanSpace ℝ (Fin 2))} (hF : IsCompact F) :
    IsCompact (convexAttachment F V) := by
  apply Metric.isCompact_iff_isClosed_bounded.2
  refine ⟨isClosed_convexAttachment F V, ?_⟩
  apply Bornology.IsBounded.closure
  rw [isBounded_convexHull]
  exact hF.isBounded.subset inter_subset_left

/-- Every core point already in a hole belongs to its attachment. -/
theorem inter_subset_convexAttachment {F V : Set (EuclideanSpace ℝ (Fin 2))}
    (hdiam : 0 < Metric.diam V) :
    F ∩ V ⊆ convexAttachment F V := by
  intro x hx
  apply subset_closure
  apply subset_convexHull ℝ
  exact ⟨hx.1, subset_diameterThickening (by positivity) hx.2⟩

/-- An attachment has diameter at most five times the diameter of its hole. -/
theorem diam_convexAttachment_le {F V : Set (EuclideanSpace ℝ (Fin 2))} (hV : IsBounded V) :
    Metric.diam (convexAttachment F V) ≤ 5 * Metric.diam V := by
  calc
    Metric.diam (convexAttachment F V) =
        Metric.diam (convexHull ℝ (F ∩ diameterThickening 2 V)) :=
      Metric.diam_closure _
    _ = Metric.diam (F ∩ diameterThickening 2 V) := convexHull_diam _
    _ ≤ Metric.diam (diameterThickening 2 V) :=
      Metric.diam_mono inter_subset_right hV.thickening
    _ ≤ 5 * Metric.diam V := by
      convert diam_diameterThickening_le (by norm_num : (0 : ℝ) ≤ 2) V using 1
      all_goals norm_num

/-- The same five-fold bound holds for extended diameter. -/
theorem ediam_convexAttachment_le {F V : Set (EuclideanSpace ℝ (Fin 2))} (hV : IsBounded V) :
    Metric.ediam (convexAttachment F V) ≤ ENNReal.ofReal 5 * Metric.ediam V := by
  calc
    Metric.ediam (convexAttachment F V) =
        Metric.ediam (convexHull ℝ (F ∩ diameterThickening 2 V)) :=
      Metric.ediam_closure _
    _ = Metric.ediam (F ∩ diameterThickening 2 V) := convexHull_ediam _
    _ ≤ Metric.ediam (diameterThickening 2 V) := Metric.ediam_mono inter_subset_right
    _ ≤ ENNReal.ofReal 5 * Metric.ediam V := by
      convert ediam_diameterThickening_le (by norm_num : (0 : ℝ) ≤ 2) hV using 1
      all_goals norm_num

/-- For a positive-diameter convex hole, its attachment lies in the three-diameter enlargement. -/
theorem convexAttachment_subset_diameterThickening_three {F V : Set (EuclideanSpace ℝ (Fin 2))}
    (hV_convex : Convex ℝ V) (hdiam : 0 < Metric.diam V) :
    convexAttachment F V ⊆ diameterThickening 3 V := by
  rw [convexAttachment, diameterThickening]
  calc
    closure (convexHull ℝ (F ∩ diameterThickening 2 V)) ⊆
        closure (diameterThickening 2 V) := by
      apply closure_mono
      apply convexHull_min inter_subset_right
      exact hV_convex.thickening _
    _ ⊆ Metric.cthickening (2 * Metric.diam V) V := by
      exact Metric.closure_thickening_subset_cthickening _ _
    _ ⊆ Metric.thickening (3 * Metric.diam V) V := by
      apply Metric.cthickening_subset_thickening'
      · positivity
      · nlinarith

/-- A bad hole has a nonempty compact connected attachment. -/
theorem convexAttachment_isCompact_isConnected
    {mu : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2))}
    {F V : Set (EuclideanSpace ℝ (Fin 2))} {alpha : ℝ} (hF : IsCompact F)
    (halpha : 0 < alpha) (hV : V ∈ badConvexSets mu F alpha) :
    IsCompact (convexAttachment F V) ∧ IsConnected (convexAttachment F V) := by
  have hdiam := diam_pos_of_mem_badConvexSets halpha hV
  have hnonempty : (convexAttachment F V).Nonempty := by
    obtain ⟨x, hxV, hxF⟩ := hV.2.2.1
    exact ⟨x, inter_subset_convexAttachment hdiam ⟨hxF, hxV⟩⟩
  exact ⟨isCompact_convexAttachment hF,
    ⟨hnonempty, (convex_convexAttachment F V).isPreconnected⟩⟩

end LeanPool.Besicovitch
