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
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntBlock0
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntBlock1
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntBlock2
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntBlock3
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntBlock4
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntBlock5
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntBlock6

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0Int
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

theorem s0IntGoal_all (r : Block) (p q : Fin 3) : S0IntGoal r p q := by
  fin_cases r <;> first
    | simpa using (s0IntGoal_block0 (p := p) (q := q))
    | simpa using (s0IntGoal_block1 (p := p) (q := q))
    | simpa using (s0IntGoal_block2 (p := p) (q := q))
    | simpa using (s0IntGoal_block3 (p := p) (q := q))
    | simpa using (s0IntGoal_block4 (p := p) (q := q))
    | simpa using (s0IntGoal_block5 (p := p) (q := q))
    | simpa using (s0IntGoal_block6 (p := p) (q := q))

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound

