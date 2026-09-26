/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Tactic
public import LeanPool.OneManifold.OneMfld.ClassifyInterval
public import LeanPool.OneManifold.OneMfld.NiceCharts


/-!
# IntervalCharts

Supporting results for the classification of compact one-dimensional manifolds.
-/

@[expose] public section

namespace OneMfld

/-- A space charted on the half-line with interval targets. -/
class IntervalChartedSpace (M : Type*) [TopologicalSpace M] extends ChartedSpace NNReal M where
  is_interval (φ : OpenPartialHomeomorph M NNReal) (h : φ ∈ atlas) : (∃ x y, (Set.Ioo x y =
      φ.target)) ∨ (∃ x, (Set.Iio x = φ.target))

variable
  {M : Type*}
  [TopologicalSpace M]

theorem ioi_unbounded (x : NNReal) : ¬ Bornology.IsBounded (Set.Ioi x) := by
  intro h
  have h' : BddBelow (Set.Ioi x) ∧ BddAbove (Set.Ioi x) :=
    (isBounded_iff_bddBelow_bddAbove (s := Set.Ioi x)).1 h
  exact (not_bddAbove_Ioi x) h'.2

theorem univ_unbounded : ¬ Bornology.IsBounded (Set.univ : Set NNReal) := by
  intro h
  -- On an `IsOrderBornology`, bounded ⇔ bddBelow ∧ bddAbove.
  have h' :
      BddBelow (Set.univ : Set NNReal) ∧
      BddAbove (Set.univ : Set NNReal) :=
    (isBounded_iff_bddBelow_bddAbove
      (s := (Set.univ : Set NNReal))).1 h
  -- But `univ` is not bounded above on a `NoTopOrder` type like `NNReal`.
  exact not_bddAbove_univ h'.2

/-- Regard an atlas with bounded connected targets as an interval atlas. -/
@[instance_reducible] noncomputable def intervalCharted (ht : NicelyChartedSpace NNReal M) :
    IntervalChartedSpace M where
  chartAt := ht.chartAt
  atlas := ht.atlas
  mem_chart_source := ht.mem_chart_source
  chart_mem_atlas := ht.chart_mem_atlas
  is_interval (φ : OpenPartialHomeomorph M NNReal) := by
    intro h
    have bounded := ht.is_bounded φ h
    have connected := ht.is_connected φ h
    have c := classify_connected_nnreal_interval (φ.target) (φ.open_target)
        (isConnected_iff_connectedSpace.mpr connected)
    rcases c with (h|h|h|h)
    · left; assumption
    · right; assumption
    · exfalso
      rcases h with ⟨x,h⟩
      apply ioi_unbounded x
      rw [h]
      exact bounded
    · exfalso
      apply univ_unbounded
      rw [←h]
      exact bounded

end OneMfld
