/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Tactic
public import LeanPool.OneManifold.OneMfld.IntervalCharts
public import LeanPool.OneManifold.OneMfld.FinitelyCharted


/-!
# FiniteIntervalCharts

Supporting results for the classification of compact one-dimensional manifolds.
-/

@[expose] public section

/-- A space equipped with a finite atlas of interval charts. -/
class FinitelyIntervalChartedSpace (M : Type*) [TopologicalSpace M] extends IntervalChartedSpace
    M where
  is_finite : Set.Finite atlas

variable
  {M : Type*}
  [TopologicalSpace M]
  [CompactSpace M]

/-- Extract a finite interval atlas from compactness. -/
@[instance_reducible] noncomputable def finitelyIntervalCharted (ht : IntervalChartedSpace M) :
    FinitelyIntervalChartedSpace M := by
  have c : { ht' : ChartedSpace NNReal M | Set.Finite ht'.atlas ∧ ht'.atlas ⊆ ht.atlas } :=
      chooseCharts
  rcases c with ⟨ ht', c1, c2 ⟩
  exact { ht' with
          is_finite := c1
        , is_interval := by
            intro x hx
            apply ht.is_interval
            apply c2
            exact hx
         }
