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
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock1
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock2
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock3
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock4
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock5
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock6

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiInt
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

theorem siIntGoal_all :
    ∀ r : Block, ∀ i : Var, ∀ p q : Fin 3, SiIntGoal (r := r) (i := i) p q := by
  intro r i p q
  fin_cases r
  · simpa using (siIntGoal_block0 (i := i) (p := p) (q := q))
  · simpa using (siIntGoal_block1 (i := i) (p := p) (q := q))
  · simpa using (siIntGoal_block2 (i := i) (p := p) (q := q))
  · simpa using (siIntGoal_block3 (i := i) (p := p) (q := q))
  · simpa using (siIntGoal_block4 (i := i) (p := p) (q := q))
  · simpa using (siIntGoal_block5 (i := i) (p := p) (q := q))
  · simpa using (siIntGoal_block6 (i := i) (p := p) (q := q))

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
