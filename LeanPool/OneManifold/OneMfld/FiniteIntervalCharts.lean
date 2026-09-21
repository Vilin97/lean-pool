/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
import Mathlib
import LeanPool.OneManifold.OneMfld.IntervalCharts
import LeanPool.OneManifold.OneMfld.FinitelyCharted

class FinitelyIntervalChartedSpace (M : Type*) [TopologicalSpace M] extends IntervalChartedSpace M where
  is_finite : Set.Finite atlas

variable
  {M : Type*}
  [TopologicalSpace M]
  [CompactSpace M]

@[instance_reducible] noncomputable def finitely_interval_charted (ht : IntervalChartedSpace M) : FinitelyIntervalChartedSpace M := by
  have c : { ht' : ChartedSpace NNReal M | Set.Finite ht'.atlas ∧ ht'.atlas ⊆ ht.atlas } := choose_charts
  rcases c with ⟨ ht', c1, c2 ⟩

  exact { ht' with
          is_finite := c1
        , is_interval := by
            intro x hx
            apply ht.is_interval
            apply c2
            exact hx
         }
