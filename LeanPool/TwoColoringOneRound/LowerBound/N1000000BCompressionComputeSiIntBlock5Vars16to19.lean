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
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock5Vars16to19
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `16`.
theorem siIntGoal_block5_var16 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨16, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `17`.
theorem siIntGoal_block5_var17 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨17, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `18`.
theorem siIntGoal_block5_var18 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨18, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `19`.
theorem siIntGoal_block5_var19 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨19, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
