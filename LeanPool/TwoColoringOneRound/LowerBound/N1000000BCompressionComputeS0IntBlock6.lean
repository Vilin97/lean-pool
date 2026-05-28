/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic

import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntGoal

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- This proof is a large `decide` check; we increase `maxHeartbeats` to avoid timeouts.
theorem s0IntGoal_block6 :
    ∀ p q : Fin 3, S0IntGoal (r := (⟨6, by decide⟩ : Block)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
