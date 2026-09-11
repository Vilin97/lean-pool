/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Polyrith
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntGoal

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntBlock4
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- This proof is a large `decide` check; we increase `maxHeartbeats` to avoid timeouts.
theorem s0IntGoal_block4 :
    ∀ p q : Fin 3, S0IntGoal (r := (⟨4, by decide⟩ : Block)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
