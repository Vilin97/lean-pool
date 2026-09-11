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

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0Vars12to15
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `12`.
theorem siIntGoal_block0_var12 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨12, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `13`.
theorem siIntGoal_block0_var13 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨13, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `14`.
theorem siIntGoal_block0_var14 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨14, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `15`.
theorem siIntGoal_block0_var15 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨15, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
