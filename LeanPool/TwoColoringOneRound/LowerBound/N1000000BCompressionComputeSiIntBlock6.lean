/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic

import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock6Vars0to3
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock6Vars4to7
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock6Vars8to11
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock6Vars12to15
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock6Vars16to19
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock6Vars20to22

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

theorem siIntGoal_block6 :
    ∀ i : Var, ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := i) p q := by
  intro i p q
  fin_cases i
  · simpa using (siIntGoal_block6_var0 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var1 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var2 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var3 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var4 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var5 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var6 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var7 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var8 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var9 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var10 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var11 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var12 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var13 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var14 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var15 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var16 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var17 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var18 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var19 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var20 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var21 (p := p) (q := q))
  · simpa using (siIntGoal_block6_var22 (p := p) (q := q))

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
