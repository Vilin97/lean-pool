/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic

import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock4Vars0to3
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock4Vars4to7
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock4Vars8to11
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock4Vars12to15
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock4Vars16to19
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock4Vars20to22

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

theorem siIntGoal_block4 :
    ∀ i : Var, ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := i) p q := by
  intro i p q
  fin_cases i
  · simpa using (siIntGoal_block4_var0 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var1 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var2 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var3 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var4 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var5 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var6 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var7 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var8 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var9 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var10 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var11 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var12 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var13 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var14 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var15 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var16 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var17 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var18 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var19 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var20 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var21 (p := p) (q := q))
  · simpa using (siIntGoal_block4_var22 (p := p) (q := q))

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
