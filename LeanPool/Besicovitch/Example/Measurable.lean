/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Example.Graph
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Measurability of Besicovitch's function

Each square wave is a step function, hence measurable, and `g` is a pointwise limit of finite
sums of them.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace LeanPool.Besicovitch.Example

theorem measurable_cellIndex (n : ℕ) : Measurable (cellIndex n) :=
  Measurable.comp Int.measurable_floor (measurable_id.div_const _)

theorem measurable_squareWave (n : ℕ) : Measurable (squareWave n) := by
  unfold squareWave
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurable_cellIndex n) (show MeasurableSet {i : ℤ | Even i} from trivial)

theorem measurable_besicovitchFun : Measurable besicovitchFun := by
  have hpartial : ∀ N : ℕ,
      Measurable fun x ↦ ∑ n ∈ Finset.range N, squareWave (n + 1) x :=
    fun N ↦ Finset.measurable_sum _ fun n _ ↦ measurable_squareWave (n + 1)
  refine measurable_of_tendsto_metrizable hpartial ?_
  rw [tendsto_pi_nhds]
  intro x
  exact (summable_squareWave x).hasSum.tendsto_sum_nat

end LeanPool.Besicovitch.Example
