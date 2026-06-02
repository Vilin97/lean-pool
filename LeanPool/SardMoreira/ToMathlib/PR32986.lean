/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
/-!
Lemmas from https://github.com/leanprover-community/mathlib4/pull/32986
-/

open scoped Topology Filter
open MeasureTheory Measure Metric

instance IsLocallyFiniteMeasure.prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] :
    IsLocallyFiniteMeasure (μ.prod ν) where
  finiteAtNhds := by
    rintro ⟨x, y⟩
    -- TODO: add FiniteAtFilter _ (_ ×ˢ _)
    rcases finiteAt_nhds μ x with ⟨s, hs, hμs⟩
    rcases finiteAt_nhds ν y with ⟨t, ht, hνt⟩
    use s ×ˢ t, prod_mem_nhds hs ht
    grw [prod_prod_le]
    exact ENNReal.mul_lt_top hμs hνt
