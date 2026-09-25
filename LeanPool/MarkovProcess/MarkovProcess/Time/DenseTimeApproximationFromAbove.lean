/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Continuity.DenseTimeContinuousExtension


/-!
# Dense-time approximation from above

Every nonnegative real time is the limit of a strictly decreasing sequence of dense times whose
physical values stay strictly above the limit. This includes time zero and times that already
belong to the dense carrier; choosing strict upper approximants gives one uniform API for all
cuts.

This is deterministic order-topological infrastructure and makes no stochastic-process claim.
-/

@[expose] public section

open Filter Topology
open scoped NNReal

namespace MarkovProcess

/-- Every nonnegative real time admits strictly decreasing dense-time approximants whose physical
values remain strictly above it. -/
theorem exists_denseTime_seq_strictAnti_tendsto (s : NNReal) :
    ∃ q : ℕ → DenseTime,
      StrictAnti q ∧
        (∀ n, s < DenseTime.castOrderEmbedding (q n)) ∧
          Tendsto (fun n ↦ DenseTime.castOrderEmbedding (q n)) atTop (nhds s) := by
  obtain ⟨q, hqAnti, hqAbove, hq⟩ :=
    ContinuousPath.denseRange_castOrderEmbedding.exists_seq_strictAnti_tendsto
      DenseTime.castOrderEmbedding.monotone s
  exact ⟨q, hqAnti, fun n ↦ hqAbove n, by
    simpa only [Function.comp_apply] using! hq⟩

end MarkovProcess
