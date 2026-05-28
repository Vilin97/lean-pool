/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic

import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `8`.
theorem siIntGoal_block2_var8 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨8, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `9`.
theorem siIntGoal_block2_var9 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨9, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `10`.
theorem siIntGoal_block2_var10 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨10, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `11`.
theorem siIntGoal_block2_var11 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨11, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
