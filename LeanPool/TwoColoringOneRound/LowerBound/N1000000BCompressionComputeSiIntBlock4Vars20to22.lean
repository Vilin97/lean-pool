/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic

import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `20`.
theorem siIntGoal_block4_var20 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨20, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `21`.
theorem siIntGoal_block4_var21 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨21, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `22`.
theorem siIntGoal_block4_var22 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨22, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
